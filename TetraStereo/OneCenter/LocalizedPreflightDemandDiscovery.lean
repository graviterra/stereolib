import TetraStereo.OneCenter.LocalizedExtendedDemandDiscovery
import TetraStereo.OneCenter.LocalizedRule3PreflightDemand
import TetraStereo.Certificate.WeightedDemandGraph

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand








































/-! ## The preflight-pruned weighted demand graph -/

/-- The actual preflight-pruned extended demand graph.  Ordinary cut-neighborhood children keep
weight one; each remaining potential endpoint request keeps the additive frame-plus-key weight
two.  This is the concrete instantiation of `TetraStereo.Certificate.WeightedDemand.Graph` on the
narrow request list proved sound by `LocalizedRule3PreflightDemand`. -/
def preflightExtendedWeightedDemandGraph (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    Graph (input.LocalizedRerootCursor fuel) where
  children := fun cursor => input.executableLocalizedRerootChildren cursor
  requests := fun cursor => input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence

@[simp] theorem preflightExtendedWeightedDemandGraph_children
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.preflightExtendedWeightedDemandGraph fuel).children cursor =
      input.executableLocalizedRerootChildren cursor := rfl

@[simp] theorem preflightExtendedWeightedDemandGraph_requests
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.preflightExtendedWeightedDemandGraph fuel).requests cursor =
      input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence := rfl

/-- The generic conservative successors of the pruned graph are exactly the executable children
together with the flattened preflight requests. -/
theorem preflightExtendedWeightedDemandGraph_successors
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (cursor : input.LocalizedRerootCursor fuel) :
    successors (input.preflightExtendedWeightedDemandGraph fuel) cursor =
      input.executableLocalizedRerootChildren cursor ++
        (input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence).flatten := rfl

/-! ## Inclusion in the existing extended graph -/

/-- Every successor of the pruned weighted graph is an extended-graph successor: the child lists
coincide and the preflight requests are a pointwise subset of the existing extended requests. -/
theorem preflightExtendedWeightedDemandSuccessors_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    ∀ child ∈ successors (input.preflightExtendedWeightedDemandGraph fuel) cursor,
      child ∈ input.extendedRule3DemandSuccessors cursor := by
  intro child present
  change child ∈ input.executableLocalizedRerootChildren cursor ++
    (input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence).flatten at present
  change child ∈ input.executableLocalizedRerootChildren cursor ++
    (input.rule3ExtendedNodeCallbackRequests cursor.occurrence).flatten
  rcases List.mem_append.mp present with childPresent | callbackPresent
  · exact List.mem_append_left _ childPresent
  · refine List.mem_append_right _ ?_
    exact flatten_subset_of_mem_subset
      (fun request requested =>
        input.rule3PreflightExtendedNodeCallbackRequests_subset
          cursor.occurrence request requested)
      child callbackPresent

/-- Every edge of the pruned weighted graph is an actual extended demand edge. -/
theorem preflightWeightedEdge_subset_extended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {parent child : input.LocalizedRerootCursor fuel}
    (edge : Edge (input.preflightExtendedWeightedDemandGraph fuel) parent child) :
    input.ExtendedRule3DemandEdge parent child :=
  input.preflightExtendedWeightedDemandSuccessors_subset parent child edge

/-- Pruned reachability is contained in extended reachability, path by path. -/
theorem preflightWeightedReachable_subset_extended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (cursor : input.LocalizedRerootCursor fuel)
    (reachable : Reachable (input.preflightExtendedWeightedDemandGraph fuel) roots cursor) :
    input.ExtendedRule3DemandReachable roots cursor := by
  obtain ⟨root, member, path⟩ := reachable
  exact ⟨root, member, Relation.ReflTransGen.mono
    (fun _ _ edge => input.preflightWeightedEdge_subset_extended edge) path⟩

/-- Acyclicity of the existing extended graph implies acyclicity of the pruned graph.  Only this
direction holds: the preflight relation removes edges and therefore can only destroy cycles. -/
theorem preflightExtendedWeightedDemandAcyclic_of_extended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : input.ExtendedRule3DemandAcyclic roots) :
    Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots := by
  intro cursor reachable cycle
  exact acyclic cursor
    (input.preflightWeightedReachable_subset_extended roots cursor reachable)
    (Relation.TransGen.mono
      (fun _ _ edge => input.preflightWeightedEdge_subset_extended edge) cycle)

/-! ## Rank stability for the unchanged extended evaluator -/

private theorem preflightDemandMapM_congr_on {α β : Type} (before after : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, before value = after value) →
      values.mapM before = values.mapM after
  | [], _ => rfl
  | value :: values, agree => by
    have head := agree value (by simp)
    have tail := preflightDemandMapM_congr_on before after values
      (fun value present => agree value (by simp [present]))
    simp [head, tail]

/-- A checked generic rank certificate for the preflight-pruned graph stabilizes the complete
recursive extended key result at every larger budget.  The strong induction follows the stored
rank, crossing executable children and the remaining endpoint callbacks.  At every node it uses
`rule3PreflightExtendedNode_callback_local`, which supplies locality for the *existing* extended
node evaluator from agreement on the pruned request list only.  The auxiliary view, the exclusion
list and every refusal branch are preserved; no successful callback or geometry is assumed. -/
theorem preflightCertificateKeyStable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : RankCertificate (input.preflightExtendedWeightedDemandGraph fuel))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ certificate.vertices)
    (first second : Nat) (firstEnough : certificate.height cursor ≤ first)
    (secondEnough : certificate.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view first excluded cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view second excluded cursor := by
  generalize rankEq : certificate.height cursor = rank at firstEnough secondEnough
  induction rank using Nat.strong_induction_on generalizing cursor first second excluded with
  | h rank ih =>
    have positive := certificate.positive cursor member
    cases first with
    | zero => omega
    | succ first =>
      cases second with
      | zero => omega
      | succ second =>
        have callbackEq : input.Rule3CallbackAgreesOn
            (input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence)
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view first)
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view second) := by
          intro request requested
          obtain ⟨covered, bounded⟩ := certificate.callbacks cursor member request requested
          cases first with
          | zero => omega
          | succ first =>
            cases second with
            | zero => omega
            | succ second =>
              apply input.extendedRule3Frame_succ_congr_keys target view first second request
              intro cancelled reference present
              have heightBound := listHeight_mem certificate.height request reference present
              apply ih (certificate.height reference) (by omega) reference (covered reference present)
                first second cancelled rfl (by omega) (by omega)
        have nodeEq := input.rule3PreflightExtendedNode_callback_local target cursor.occurrence view _ _
          callbackEq excluded
        have childrenEq : (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view first excluded) =
          (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view second excluded) := by
          apply preflightDemandMapM_congr_on
          intro child present
          obtain ⟨covered, bounded⟩ := certificate.children cursor member child present
          apply ih (certificate.height child) (by omega) child covered first second
            excluded rfl (by omega) (by omega)
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          executableLocalizedRerootChildren?_eq_some, bind, Option.bind, nodeEq, childrenEq]

/-- The computed maximum rank plus one suffices for a complete two-pass extended frame, with
every refusal branch preserved.  Every frame cursor must belong to the checked closed graph. -/
theorem preflightCertificateFrameStable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : RankCertificate (input.preflightExtendedWeightedDemandGraph fuel))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor fuel))
    (covered : ∀ cursor ∈ cursors, cursor ∈ certificate.vertices)
    (first second : Nat)
    (firstEnough : listHeight certificate.height cursors + 1 ≤ first)
    (secondEnough : listHeight certificate.height cursors + 1 ≤ second) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view first cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view second cursors := by
  cases first with
  | zero => omega
  | succ first =>
    cases second with
    | zero => omega
    | succ second =>
      apply input.extendedRule3Frame_succ_congr_keys target view first second cursors
      intro excluded cursor present
      have heightBound := listHeight_mem certificate.height cursors cursor present
      exact preflightCertificateKeyStable certificate target view cursor (covered cursor present)
        first second (by omega) (by omega) excluded

/-! ## Executable discovery with the input-derived structural budget -/

/-- Uniform structural traversal budget, identical to the concrete extended constructor:
`occurrenceCount * (occurrenceCount + 1) + 1`.  It is derived from the finite occurrence carrier
of the input and does not depend on any desired result. -/
def preflightExtendedDemandTraversalBudget (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Nat :=
  let occurrenceCount := (input.localizedOccurrenceCarrier fuel).length
  occurrenceCount * (occurrenceCount + 1) + 1




def preparePreflightExtendedDemandPlan (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) :
    Except (DiscoveryFailure (input.LocalizedRerootCursor fuel))
      (Plan (input.preflightExtendedWeightedDemandGraph fuel) roots) :=
  prepare (input.preflightExtendedWeightedDemandGraph fuel)
    (input.preflightExtendedDemandTraversalBudget fuel) roots





theorem preparePreflightExtendedDemandPlan_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (succeeds : ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan) :
    Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots := by
  obtain ⟨plan, _⟩ := succeeds
  exact plan.acyclic


def preflightExtendedDemandEvaluate
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : Plan (input.preflightExtendedWeightedDemandGraph fuel) roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view plan.bound roots

/-- The checked bound preserves the full optional extended frame at every larger budget,
including topology ambiguity and every failed recursive key. -/
theorem preflightExtendedDemandEvaluate_eq_above
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : Plan (input.preflightExtendedWeightedDemandGraph fuel) roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    preflightExtendedDemandEvaluate plan target view =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots :=
  preflightCertificateFrameStable plan.ranks target view roots plan.covers plan.bound budget
    (Nat.le_refl _) enough

/-- Successful evaluation at the checked bound has the existing declarative frame meaning. -/
theorem preflightExtendedDemandEvaluate_sound
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : Plan (input.preflightExtendedWeightedDemandGraph fuel) roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : preflightExtendedDemandEvaluate plan target view = some frame) :
    input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots frame :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound target view plan.bound roots frame
    computed








/-- The ranks of an existing checked extended certificate certify the preflight-pruned graph
unchanged.  Child edges are identical; each pruned request is first embedded into the extended
request list, and only the generic list maximum is transported. -/
def ExtendedRule3DemandRankCertificate.toPreflightRankCertificate
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel) :
    RankCertificate (input.preflightExtendedWeightedDemandGraph fuel) where
  vertices := certificate.vertices
  height := certificate.height
  positive := certificate.positive
  children := certificate.children
  callbacks := by
    intro cursor member request requested
    have requested' : request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence :=
      input.rule3PreflightExtendedNodeCallbackRequests_subset cursor.occurrence request requested
    obtain ⟨covered, bounded⟩ := certificate.callbacks cursor member request requested'
    refine ⟨covered, ?_⟩
    rw [weightedListHeight_eq_rule3CursorListHeight]
    exact bounded



def ExtendedRule3DemandPlan.toPreflightPlan
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots) :
    Plan (input.preflightExtendedWeightedDemandGraph fuel) roots where
  ranks := plan.ranks.toPreflightRankCertificate
  covers := plan.covers


theorem ExtendedRule3DemandPlan.toPreflightPlan_bound
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots) :
    (plan.toPreflightPlan (fuel := fuel)).bound = plan.bound := by
  show listHeight plan.ranks.height roots + 1 =
    rule3CursorListHeight plan.ranks.height roots + 1
  rw [weightedListHeight_eq_rule3CursorListHeight]



theorem ExtendedRule3DemandPlan.preflightAcyclic
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots) :
    Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots :=
  plan.toPreflightPlan.acyclic

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
