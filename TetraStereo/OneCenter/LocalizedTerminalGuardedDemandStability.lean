import TetraStereo.OneCenter.LocalizedTerminalGuardedRecursiveRule3Key
import TetraStereo.OneCenter.LocalizedTerminalGuardedDemandDiscovery
import TetraStereo.OneCenter.LocalizedExtendedDemandDiscovery
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand





























































/-! ## Rank data pairing the matching guarded certificate with its callback boundary -/

/-- A checked weighted rank of the *matching* terminal-guarded demand graph, accompanied by the
checked extended rank that certifies the actual evaluator's unguarded predecessor callback at the
same vertices and the same heights.

The `ranks` field is an ordinary `RankCertificate` of
`terminalGuardedWeightedDemandGraph input target view`: the weight-`1` child edges and weight-`2`
guarded callback edges are the graph's own checked edges.  The `boundary` field is *not* an
additional evaluation hypothesis; it is the existing closed extended rank whose callback field
covers precisely the larger demand that the old frame callback can still traverse on fallback
branches.  `vertices_eq` and `height_eq` make the two rank functions literally the same assignment,
so the stability induction runs on the guarded rank while the callback budget is read from the
boundary at the same height. -/
structure TerminalGuardedDemandRankCertificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) where
  /-- The checked weighted rank of the matching terminal-guarded demand graph. -/
  ranks : RankCertificate (terminalGuardedWeightedDemandGraph input target view)
  /-- The checked extended rank certifying the old predecessor frame callback actually invoked by
  the guarded key evaluator. -/
  boundary : input.ExtendedRule3DemandRankCertificate fuel
  /-- Both ranks use exactly the same closed vertex set. -/
  vertices_eq : ranks.vertices = boundary.vertices
  /-- Both ranks use exactly the same height assignment. -/
  height_eq : ranks.height = boundary.height

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedDemandRankCertificate

/-- An existing checked extended rank certificate, transported along the pruning inclusion, yields
the rank pair.  The matching guarded certificate is the existing
`toTerminalGuardedRankCertificate` transfer, so its vertices and heights are definitionally the
extended ones; no new discovery or evaluation is performed. -/
def TerminalGuardedDemandRankCertificate.ofExtended
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    TerminalGuardedDemandRankCertificate input target view where
  ranks := certificate.toTerminalGuardedRankCertificate target view
  boundary := certificate
  vertices_eq := rfl
  height_eq := rfl

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedDemandRankCertificate.ofExtended




def TerminalGuardedDemandRankCertificate.ofExtendedPlan
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    TerminalGuardedDemandRankCertificate input target view :=
  ofExtended plan.ranks target view

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedDemandRankCertificate.ofExtendedPlan

/-! ## Request-local weight transfer from the boundary certificate -/

/-- Every request retained by the matching guarded graph is an actual extended-node request, so
the boundary certificate closes all its references and charges the exact two-fuel callback step at
the same cursor height.  This is the request-local bridge between the pruned guarded graph and the
unguarded predecessor callback; it is derived, not assumed, and it holds for arbitrary target,
view and cursor. -/
theorem terminalGuardedDemandRequest_extended_weight
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel)
    (member : cursor ∈ certificate.vertices)
    (request : List (input.LocalizedRerootCursor fuel))
    (requested : request ∈
      (terminalGuardedWeightedDemandGraph input target view).requests cursor) :
    (∀ reference ∈ request, reference ∈ certificate.vertices) ∧
      rule3CursorListHeight certificate.height request + 2 ≤ certificate.height cursor := by
  have extendedRequested : request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence := by
    apply terminalGuardedNodeCallbackRequests_subset input target view cursor.occurrence request
    simpa only [terminalGuardedWeightedDemandGraph_requests] using requested
  exact certificate.callbacks cursor member request extendedRequested

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedDemandRequest_extended_weight

/-! ## Stability of the actual guarded recursive key -/

private theorem terminalGuardedDemandMapM_congr_on {α β : Type} (before after : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, before value = after value) →
      values.mapM before = values.mapM after
  | [], _ => rfl
  | value :: values, agree => by
    have head := agree value (by simp)
    have tail := terminalGuardedDemandMapM_congr_on before after values
      (fun value present => agree value (by simp [present]))
    simp [head, tail]

/-- The actual terminal-guarded recursive key stabilizes above the boundary rank at every larger
budget, for every target, every dependency view and every exclusion list.

The induction is strong induction on the height of the matching guarded rank (identified with the
boundary height by `height_eq` when this is invoked through the wrapper).  At each successor
cursor:

* structural children are consumed through the weight-`1` child field, with the induction
  hypothesis at each child;
* the actual guarded node is invoked with the old unguarded frame callback, so its two callback
  arguments are compared only on the *guarded* request list, using
  `terminalGuardedWeightedDemandGraph_node_local`;
* for each surviving request, `terminalGuardedDemandRequest_extended_weight` reads the boundary
  callback edge, and the predecessor induction hypothesis at the request references yields the
  pointwise key agreement required by the old frame's own two-pass stability
  (`ExtendedRule3DemandRankCertificate.frame_stable`).

Thus the comparison is request-local and derived from certificate edges and the induction
hypothesis; no global callback congruence and no evaluator equality is assumed. -/
theorem terminalGuardedRecursiveRule3Key_stable_of_extended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel)
    (member : cursor ∈ certificate.vertices)
    (first second : Nat) (firstEnough : certificate.height cursor ≤ first)
    (secondEnough : certificate.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec? target view first excluded cursor =
      input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec? target view second excluded cursor := by
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
            ((terminalGuardedWeightedDemandGraph input target view).requests cursor)
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view first)
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view second) := by
          intro request requested
          obtain ⟨covered, bounded⟩ := terminalGuardedDemandRequest_extended_weight
            certificate target view cursor member request requested
          exact certificate.frame_stable target view request covered first second
            (by omega) (by omega)
        have nodeEq := terminalGuardedWeightedDemandGraph_node_local input target cursor.occurrence
          view _ _ cursor rfl callbackEq excluded
        have childrenEq : (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
              target view first excluded) =
          (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
              target view second excluded) := by
          apply terminalGuardedDemandMapM_congr_on
          intro child present
          obtain ⟨covered, bounded⟩ := certificate.children cursor member child present
          exact ih (certificate.height child) (by omega) child covered first second excluded rfl
            (by omega) (by omega)
        simp only [buildLocalizedTerminalGuardedRecursiveRule3KeyExec?,
          executableLocalizedRerootChildren?_eq_some, bind, Option.bind, nodeEq, childrenEq]

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedRecursiveRule3Key_stable_of_extended

/-- Key stability stated directly above the *matching guarded weighted rank certificate* carried
by `certificate.ranks`.  The boundary fields only supply the old-callback weight that the pruned
graph itself does not contain; `vertices_eq` and `height_eq` transfer membership and the height
bounds from the guarded rank to that boundary. -/
theorem TerminalGuardedDemandRankCertificate.key_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    (certificate : TerminalGuardedDemandRankCertificate input target view)
    (cursor : input.LocalizedRerootCursor fuel)
    (member : cursor ∈ certificate.ranks.vertices)
    (first second : Nat) (firstEnough : certificate.ranks.height cursor ≤ first)
    (secondEnough : certificate.ranks.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec? target view first excluded cursor =
      input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec? target view second excluded cursor := by
  have member' : cursor ∈ certificate.boundary.vertices := by
    simpa only [certificate.vertices_eq] using member
  have firstEnough' : certificate.boundary.height cursor ≤ first := by
    simpa only [certificate.height_eq] using firstEnough
  have secondEnough' : certificate.boundary.height cursor ≤ second := by
    simpa only [certificate.height_eq] using secondEnough
  exact terminalGuardedRecursiveRule3Key_stable_of_extended input certificate.boundary target view
    cursor member' first second firstEnough' secondEnough' excluded

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedDemandRankCertificate.key_stable

/-! ## Stability of the actual guarded two-pass frame -/

/-- The actual guarded two-pass frame at budget `first + 1` equals the one at `second + 1`
whenever the guarded key agrees at every cursor of the frame and every exclusion list.

Both raw and rebuilt passes are compared by the same pointwise key agreement; the coupled-topology
resolution and the excluded-unit computation are applied to identical raw-key lists, so they do
not need any separate congruence hypothesis.  Full `Option` equality is preserved, including a
refused topology resolution or a failed key in either pass. -/
theorem terminalGuardedFrame_succ_congr_keys
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (first second : Nat)
    (cursors : List (input.LocalizedRerootCursor fuel))
    (agree : ∀ excluded cursor, cursor ∈ cursors →
      input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec? target view first excluded cursor =
        input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec? target view second excluded cursor) :
    input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view (first + 1) cursors =
      input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view (second + 1) cursors := by
  have mapped : ∀ excluded, cursors.mapM
      (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec? target view first excluded) =
        cursors.mapM
          (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec? target view second excluded) :=
    fun excluded => terminalGuardedDemandMapM_congr_on _ _ cursors (agree excluded)
  simp only [buildLocalizedTerminalGuardedExtendedRule3FrameExec?, mapped]

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedFrame_succ_congr_keys

/-- The actual guarded frame stabilizes above the boundary rank with the computed maximum rank
plus one as the sufficient budget.  Every frame cursor must belong to the common closed vertex
set; no successful key or topology is assumed. -/
theorem terminalGuardedExtendedFrame_stable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor fuel))
    (covered : ∀ cursor ∈ cursors, cursor ∈ certificate.vertices)
    (first second : Nat)
    (firstEnough : rule3CursorListHeight certificate.height cursors + 1 ≤ first)
    (secondEnough : rule3CursorListHeight certificate.height cursors + 1 ≤ second) :
    input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view first cursors =
      input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view second cursors := by
  cases first with
  | zero => omega
  | succ first =>
    cases second with
    | zero => omega
    | succ second =>
      apply terminalGuardedFrame_succ_congr_keys input target view first second cursors
      intro excluded cursor present
      have heightBound := rule3CursorListHeight_mem certificate.height cursors cursor present
      exact terminalGuardedRecursiveRule3Key_stable_of_extended input certificate target view cursor
        (covered cursor present) first second (by omega) (by omega) excluded

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedExtendedFrame_stable

/-- Frame stability stated directly above the *matching guarded weighted rank certificate*.
The generic list maximum is converted to the concrete cursor list height with the existing
`weightedListHeight_eq_rule3CursorListHeight`; membership and the height assignment are transferred
through `vertices_eq` and `height_eq`. -/
theorem TerminalGuardedDemandRankCertificate.frame_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    (certificate : TerminalGuardedDemandRankCertificate input target view)
    (cursors : List (input.LocalizedRerootCursor fuel))
    (covered : ∀ cursor ∈ cursors, cursor ∈ certificate.ranks.vertices)
    (first second : Nat)
    (firstEnough : listHeight certificate.ranks.height cursors + 1 ≤ first)
    (secondEnough : listHeight certificate.ranks.height cursors + 1 ≤ second) :
    input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view first cursors =
      input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view second cursors := by
  have covered' : ∀ cursor ∈ cursors, cursor ∈ certificate.boundary.vertices := by
    intro cursor present
    simpa only [certificate.vertices_eq] using covered cursor present
  have firstEnough' :
      rule3CursorListHeight certificate.boundary.height cursors + 1 ≤ first := by
    rw [← weightedListHeight_eq_rule3CursorListHeight]
    simpa only [certificate.height_eq] using firstEnough
  have secondEnough' :
      rule3CursorListHeight certificate.boundary.height cursors + 1 ≤ second := by
    rw [← weightedListHeight_eq_rule3CursorListHeight]
    simpa only [certificate.height_eq] using secondEnough
  exact terminalGuardedExtendedFrame_stable input certificate.boundary target view cursors covered'
    first second firstEnough' secondEnough'

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedDemandRankCertificate.frame_stable






theorem ExtendedRule3DemandPlan.terminalGuardedFrame_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view plan.bound roots =
      input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view budget roots :=
  terminalGuardedExtendedFrame_stable input plan.ranks target view roots plan.covers
    plan.bound budget (Nat.le_refl _) enough

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedRule3DemandPlan.terminalGuardedFrame_stable




def ExtendedRule3DemandPlan.guardedEvaluate
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view
    (plan.toTerminalGuardedPlan target view).bound roots

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedRule3DemandPlan.guardedEvaluate






theorem ExtendedRule3DemandPlan.guardedEvaluate_eq_above
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (budget : Nat)
    (enough : (plan.toTerminalGuardedPlan target view).bound ≤ budget) :
    plan.guardedEvaluate target view =
      input.buildLocalizedTerminalGuardedExtendedRule3FrameExec? target view budget roots := by
  unfold ExtendedRule3DemandPlan.guardedEvaluate
  rw [ExtendedRule3DemandPlan.toTerminalGuardedPlan_bound]
  exact plan.terminalGuardedFrame_stable target view budget (by
    simpa only [ExtendedRule3DemandPlan.toTerminalGuardedPlan_bound] using enough)

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedRule3DemandPlan.guardedEvaluate_eq_above

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
