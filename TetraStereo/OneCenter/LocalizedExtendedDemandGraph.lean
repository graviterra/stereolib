import TetraStereo.OneCenter.LocalizedExtendedDemandRankAdapter
import TetraStereo.OneCenter.LocalizedRule3DemandDiscoveryAcyclic
import TetraStereo.OneCenter.LocalizedRule3DemandDiscoveryStructural
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitFuelStability

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Actual recursive demand graph of the extended Rule 3 evaluator

The extended evaluator `buildLocalizedRerootExtendedShortCircuitRule3KeyExec?` recurses along two
kinds of edges:

* the executable cut-neighborhood `executableLocalizedRerootChildren`, and
* every cursor listed by an actual potential endpoint request
  `rule3ExtendedNodeCallbackRequests`.

The definitions below are the demand graph of exactly those two sources.  They are the extended
analogue of `Rule3DemandEdge`, `Rule3DemandReachable` and `Rule3DemandAcyclic`, which use the
pre-extension request list `rule3NodeCallbackRequests`.

The first group of results transfers the existing graph analysis: the extended request list is a
subset of the previous one (`rule3ExtendedNodeCallbackRequests_subset`), hence every extended edge
is a previous edge, and previous acyclicity implies extended acyclicity.

The second group proves extended acyclicity directly, without any proposed rank table, desired
output or successful evaluation: a whole-carrier
`LocalizedExtendedRule3NoCallbackCertificate` removes the callback edges entirely, and the
structural cursor budget `localizedRerootCursorBudget` strictly decreases along executable
children.
-/

/-- Actual recursive successors of the extended evaluator at one cursor: the executable
cut-neighborhood together with the flattened potential recursive endpoint requests of the extended
node evaluator. -/
def extendedRule3DemandSuccessors (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : List (input.LocalizedRerootCursor fuel) :=
  input.executableLocalizedRerootChildren cursor ++
    (input.rule3ExtendedNodeCallbackRequests cursor.occurrence).flatten

/-- One actual recursive dependency edge of the extended evaluator: the child is an executable
child or a recursively requested endpoint cursor. -/
def ExtendedRule3DemandEdge (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (parent child : input.LocalizedRerootCursor fuel) : Prop :=
  child ∈ input.extendedRule3DemandSuccessors parent

/-- Reachability from a requested frame in the actual extended demand graph. -/
def ExtendedRule3DemandReachable (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  ∃ root ∈ roots, Relation.ReflTransGen input.ExtendedRule3DemandEdge root cursor

/-- Acyclicity of the part of the extended graph that is reachable from the requested frame.
Cursors outside the reachable closure impose no condition. -/
def ExtendedRule3DemandAcyclic (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) : Prop :=
  ∀ cursor, input.ExtendedRule3DemandReachable roots cursor →
    ¬ Relation.TransGen input.ExtendedRule3DemandEdge cursor cursor

/-! ## Inclusion in the previous demand graph -/

/-- Flattening is monotone with respect to membership of the outer list. -/
theorem flatten_subset_of_mem_subset {α : Type}
    {outer inner : List (List α)}
    (contains : ∀ part ∈ outer, part ∈ inner) :
    ∀ item ∈ outer.flatten, item ∈ inner.flatten := by
  intro item present
  obtain ⟨part, partMember, itemMember⟩ := List.mem_flatten.mp present
  exact List.mem_flatten.mpr ⟨part, contains part partMember, itemMember⟩

/-- Every extended successor is a previous demand successor: the child lists coincide and the
extended callback requests are contained in `rule3NodeCallbackRequests`. -/
theorem extendedRule3DemandSuccessors_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    ∀ child ∈ input.extendedRule3DemandSuccessors cursor,
      child ∈ input.rule3DemandSuccessors cursor := by
  intro child present
  change child ∈ input.executableLocalizedRerootChildren cursor ++
    (input.rule3ExtendedNodeCallbackRequests cursor.occurrence).flatten at present
  change child ∈ input.executableLocalizedRerootChildren cursor ++
    (input.rule3NodeCallbackRequests cursor.occurrence).flatten
  rcases List.mem_append.mp present with childPresent | callbackPresent
  · exact List.mem_append_left _ childPresent
  · refine List.mem_append_right _ ?_
    exact flatten_subset_of_mem_subset
      (fun request requested =>
        input.rule3ExtendedNodeCallbackRequests_subset cursor.occurrence request requested)
      child callbackPresent

/-- Every actual extended demand edge is an edge of the previous demand graph. -/
theorem extendedRule3DemandEdge_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (parent child : input.LocalizedRerootCursor fuel)
    (edge : input.ExtendedRule3DemandEdge parent child) :
    input.Rule3DemandEdge parent child :=
  input.extendedRule3DemandSuccessors_subset parent child edge

/-- Extended reachability is contained in previous demand reachability, path by path. -/
theorem extendedRule3DemandReachable_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (cursor : input.LocalizedRerootCursor fuel)
    (reachable : input.ExtendedRule3DemandReachable roots cursor) :
    input.Rule3DemandReachable roots cursor := by
  obtain ⟨root, member, path⟩ := reachable
  refine ⟨root, member, ?_⟩
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge ih => exact ih.tail (input.extendedRule3DemandEdge_subset _ _ edge)

/-- A strict closure inclusion lifts to transitive closure. -/
theorem transGen_mono {α : Type} {edge previous : α → α → Prop}
    (step : ∀ parent child, edge parent child → previous parent child) :
    ∀ {parent child}, Relation.TransGen edge parent child →
      Relation.TransGen previous parent child := by
  intro parent child path
  induction path with
  | single edgeStep => exact Relation.TransGen.single (step _ _ edgeStep)
  | tail _ edgeStep ih => exact ih.tail (step _ _ edgeStep)

/-- Previous-graph acyclicity implies acyclicity of the extended graph. -/
theorem extendedRule3DemandAcyclic_of_rule3DemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : input.Rule3DemandAcyclic roots) :
    input.ExtendedRule3DemandAcyclic roots := by
  intro cursor reachable cycle
  exact acyclic cursor (input.extendedRule3DemandReachable_subset roots cursor reachable)
    (transGen_mono
      (fun parent child edge => input.extendedRule3DemandEdge_subset parent child edge) cycle)

/-! ## Acyclicity from a strictly decreasing measure -/

/-- A relation whose every step stays in a domain and strictly decreases a natural measure has no
reachable cycle.  This is the relation-generic core of `rule3DemandAcyclic_of_decreasing`, stated
for an arbitrary edge so that it applies to the extended graph as well. -/
theorem acyclic_reachable_of_decreasing {α : Type}
    (edge : α → α → Prop) (roots : List α)
    (domain : α → Prop) (measure : α → Nat)
    (rootDomain : ∀ root ∈ roots, domain root)
    (decreases : ∀ parent, domain parent → ∀ child, edge parent child →
      domain child ∧ measure child < measure parent) :
    ∀ cursor, (∃ root ∈ roots, Relation.ReflTransGen edge root cursor) →
      ¬ Relation.TransGen edge cursor cursor := by
  have pathClosed : ∀ {parent child}, domain parent →
      Relation.ReflTransGen edge parent child → domain child := by
    intro parent child present path
    induction path with
    | refl => exact present
    | tail _ edgeStep ih => exact (decreases _ ih _ edgeStep).1
  have pathDecreases : ∀ {parent child}, domain parent →
      Relation.TransGen edge parent child →
        domain child ∧ measure child < measure parent := by
    intro parent child present path
    induction path with
    | single edgeStep => exact decreases _ present _ edgeStep
    | tail _ edgeStep ih =>
      obtain ⟨valid, smaller⟩ := decreases _ ih.1 _ edgeStep
      exact ⟨valid, smaller.trans ih.2⟩
  intro cursor reachable cycle
  obtain ⟨root, member, path⟩ := reachable
  exact Nat.lt_irrefl _ (pathDecreases (pathClosed (rootDomain root member) path) cycle).2

/-! ## Acyclicity from the whole-carrier no-callback certificate -/





theorem extendedRule3DemandAcyclic_of_noCallbacks
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root)
    (noCallbacks : ∀ occurrence : input.LocalizedCIPOccurrence fuel,
      input.rule3ExtendedNodeCallbackRequests occurrence = []) :
    input.ExtendedRule3DemandAcyclic roots := by
  apply acyclic_reachable_of_decreasing input.ExtendedRule3DemandEdge roots
    input.LocalizedRerootCursorValid input.localizedRerootCursorBudget rootValid
  intro parent valid child edge
  have cleared : input.extendedRule3DemandSuccessors parent =
      input.executableLocalizedRerootChildren parent := by
    unfold extendedRule3DemandSuccessors
    rw [noCallbacks parent.occurrence, List.flatten_nil, List.append_nil]
  have childMember : child ∈ input.executableLocalizedRerootChildren parent := by
    simpa only [ExtendedRule3DemandEdge, cleared] using edge
  have derived := input.executableLocalizedRerootChildren_declarative parent
  exact ⟨input.localizedRerootChild_valid parent child
      (input.executableLocalizedRerootChildren parent) derived childMember,
    input.localizedRerootChild_budget_lt parent child
      (input.executableLocalizedRerootChildren parent) valid derived childMember⟩

/-- The whole-carrier, input-derived `LocalizedExtendedRule3NoCallbackCertificate`, together with
cursor validity of every requested root, proves the actual extended demand graph acyclic. -/
theorem extendedRule3DemandAcyclic_of_certificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (ready : input.LocalizedExtendedRule3NoCallbackCertificate fuel)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    input.ExtendedRule3DemandAcyclic roots :=
  input.extendedRule3DemandAcyclic_of_noCallbacks roots rootValid ready.empty

/-- On the no-double-bond-record domain the existing callback analysis forces every extended
request list empty, so the whole-carrier certificate holds without any extra input. -/
def localizedExtendedRule3NoCallbackCertificate_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (fuel : Nat) :
    input.LocalizedExtendedRule3NoCallbackCertificate fuel :=
  { empty := fun occurrence => by
      rw [List.eq_nil_iff_forall_not_mem]
      intro request present
      have inOld := input.rule3ExtendedNodeCallbackRequests_subset occurrence request present
      rw [input.rule3NodeCallbackRequests_nil_of_noDoubleRecords noDouble occurrence] at inOld
      simp at inOld }

/-- Consequently the actual extended demand graph is acyclic on the no-double-bond-record domain
for every list of valid requested roots. -/
theorem extendedRule3DemandAcyclic_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {fuel : Nat} (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    input.ExtendedRule3DemandAcyclic roots :=
  input.extendedRule3DemandAcyclic_of_certificate
    (input.localizedExtendedRule3NoCallbackCertificate_of_noDoubleRecords noDouble fuel)
    roots rootValid

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
