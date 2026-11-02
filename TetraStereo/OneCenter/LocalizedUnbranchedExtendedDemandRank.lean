import TetraStereo.OneCenter.LocalizedExtendedDemandDiscovery
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.LocalizedRule3DoubleBondEdgeDecidable
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput



































































/-- The proved rank bound `6 * (fuel + 1) + 2`. -/
def extendedDemandRankBound (fuel : Nat) : Nat :=
  6 * (fuel + 1) + 2



def extendedDemandRank (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : Nat :=
  3 * input.localizedRerootCursorBudget cursor +
    (if input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence then 2 else 0)



theorem extendedDemandRank_le_bound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.extendedDemandRank cursor ≤ extendedDemandRankBound fuel := by
  have budget := input.localizedRerootCursorBudget_le_twice cursor
  have flag : (if input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence
      then 2 else 0) ≤ 2 := by
    split <;> omega
  unfold extendedDemandRank extendedDemandRankBound
  omega

/-- Strict form of the rank bound: every rank fits in the discovery budget
`6 * (fuel + 1) + 3`. -/
theorem extendedDemandRank_lt_bound_succ
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.extendedDemandRank cursor < extendedDemandRankBound fuel + 1 := by
  have bounded := input.extendedDemandRank_le_bound cursor
  omega

/-! ## Structural child edges (weight `1`) -/




theorem extendedDemandRank_child
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    input.extendedDemandRank child + 1 ≤ input.extendedDemandRank cursor := by
  have derived := input.executableLocalizedRerootChildren_declarative cursor
  have budgetLt := input.localizedRerootChild_budget_lt cursor child
    (input.executableLocalizedRerootChildren cursor) valid derived present
  have flag : (if input.LocalizedOccurrenceHasRule3DoubleBondEdge child.occurrence
      then 2 else 0) ≤ 2 := by
    split <;> omega
  unfold extendedDemandRank
  omega

/-! ## Actual callback references (weight `2`) -/




inductive ExtendedDemandRequestStep (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor reference : input.LocalizedRerootCursor fuel) : Prop where
  /-- The reference resets outward or enters a no-cut source: its budget drops by at least `2`. -/
  | reset
      (below : input.localizedRerootCursorBudget reference + 2 ≤
        input.localizedRerootCursorBudget cursor)
  /-- The reference is outward at reduced budget (a deeper request) and is not a physical
  double-bond edge. -/
  | outwardNonDouble
      (below : input.localizedRerootCursorBudget reference + 1 ≤
        input.localizedRerootCursorBudget cursor)
      (phase : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge reference.occurrence)
  /-- The reference retains the parent budget (same-depth outward request), the parent is a
  physical double-bond edge, and the reference is not. -/
  | sameDepthPhase
      (same : input.localizedRerootCursorBudget reference =
        input.localizedRerootCursorBudget cursor)
      (parentPhase : input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence)
      (phase : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge reference.occurrence)

/-- Any request reference satisfying one of the three exact situations pays the callback weight
`2`: `rank reference + 2 ≤ rank cursor`. -/
theorem extendedDemandRank_request
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {cursor reference : input.LocalizedRerootCursor fuel}
    (step : input.ExtendedDemandRequestStep cursor reference) :
    input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor := by
  rcases step with below | ⟨below, phase⟩ | ⟨same, parentPhase, phase⟩
  · unfold extendedDemandRank
    split <;> split <;> omega
  · unfold extendedDemandRank
    rw [if_neg phase]
    split <;> omega
  · unfold extendedDemandRank
    rw [if_neg phase, if_pos parentPhase]
    omega

/-! ## Explicit unbranched graph domain -/

/-- Distinct graph neighbors of `atom` joined by a double bond (bond order exactly `2`).  This is
the molecule-level branching measure; `neighborFinset` already excludes the atom itself because
the bond diagonal is zero. -/
def localizedDoubleBondNeighbourFinset (input : CertifiedLocalizedCIPInput)
    (atom : input.Atom) : Finset input.Atom :=
  (input.moleculeGraph.neighborFinset atom).filter fun neighbour =>
    input.moleculeGraph.bond atom neighbour = 2

/-- The explicit unbranched graph domain: every atom has at most two distinct double-bond
neighbors.  This is an input-graph predicate.  The branched `S(=CH2)3` fixture has a sulfur atom
with three such neighbors, so it lies outside this domain. -/
def LocalizedUnbranchedDoubleBondNeighbourDomain
    (input : CertifiedLocalizedCIPInput) : Prop :=
  ∀ atom : input.Atom, (input.localizedDoubleBondNeighbourFinset atom).card ≤ 2




def LocalizedUnbranchedExtendedDemandDomain
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  input.LocalizedRerootCursorValid cursor




structure ExtendedDemandRankPhase (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (domain : input.LocalizedRerootCursor fuel → Prop) : Prop where
  /-- The molecule-level unbranched graph hypothesis. -/
  unbranched : input.LocalizedUnbranchedDoubleBondNeighbourDomain
  /-- Every cursor in the domain is a valid reroot orientation. -/
  valid : ∀ cursor, domain cursor → input.LocalizedRerootCursorValid cursor
  /-- Executable children stay in the domain. -/
  childDomain : ∀ cursor, domain cursor →
    ∀ child ∈ input.executableLocalizedRerootChildren cursor, domain child
  /-- Every actual request reference stays in the domain. -/
  requestDomain : ∀ cursor, domain cursor →
    ∀ request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence,
      ∀ reference ∈ request, domain reference

  requestStep : ∀ cursor, domain cursor →
    ∀ request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence,
      ∀ reference ∈ request, input.ExtendedDemandRequestStep cursor reference

/-! ## Successor decrease and actual callback corollary -/

/-- Every actual extended demand successor stays in the domain and strictly decreases the rank.
Child edges use weight `1`; request references use weight `2`. -/
theorem extendedDemandRank_successor_decreases
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain)
    (cursor : input.LocalizedRerootCursor fuel) (member : domain cursor)
    (child : input.LocalizedRerootCursor fuel)
    (edge : child ∈ input.extendedRule3DemandSuccessors cursor) :
    domain child ∧ input.extendedDemandRank child < input.extendedDemandRank cursor := by
  simp only [extendedRule3DemandSuccessors, List.mem_append] at edge
  rcases edge with childEdge | requestEdge
  · refine ⟨phase.childDomain cursor member child childEdge, ?_⟩
    have bound := input.extendedDemandRank_child cursor child
      (phase.valid cursor member) childEdge
    omega
  · obtain ⟨request, requested, reference⟩ := List.mem_flatten.mp requestEdge
    refine ⟨phase.requestDomain cursor member request requested child reference, ?_⟩
    have bound := input.extendedDemandRank_request
      (phase.requestStep cursor member request requested child reference)
    omega

/-- Actual callback weight `2`: every reference of every actual extended request pays the full
frame-plus-key weight against the weighted rank. -/
theorem extendedDemandRank_actualCallback
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain)
    (cursor : input.LocalizedRerootCursor fuel) (member : domain cursor)
    (request : List (input.LocalizedRerootCursor fuel))
    (requested : request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence)
    (reference : input.LocalizedRerootCursor fuel)
    (inRequest : reference ∈ request) :
    input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor :=
  input.extendedDemandRank_request
    (phase.requestStep cursor member request requested reference inRequest)

/-! ## Discovery totality at the actual extended demand measure -/

/-- The existing generic discovery totality theorem instantiated at the actual extended demand
graph and the weighted rank.  This is not a new algorithm: it is
`discoverExtendedRule3DemandRoots_total_of_measure` with `measure := extendedDemandRank`. -/
theorem discoverExtendedRule3DemandRanks_total_of_extendedDemandRank
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain)
    (budget : Nat) (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, domain root)
    (bounded : ∀ root ∈ roots, input.extendedDemandRank root < budget) :
    ∃ table,
      roots.foldlM (fun known root =>
        input.discoverExtendedRule3DemandRanks budget [] known root) [] = .ok table ∧
      input.ExtendedRule3DemandRankTableValid table ∧
      (∀ root ∈ roots, root ∈ table.map Prod.fst) :=
  input.discoverExtendedRule3DemandRoots_total_of_measure domain input.extendedDemandRank
    (fun cursor member child edge =>
      input.extendedDemandRank_successor_decreases phase cursor member child edge)
    budget roots rootDomain bounded

/-- Discovery totality at the proved rank bound: the budget `6 * (fuel + 1) + 3` exceeds every
rank by `extendedDemandRank_le_bound`. -/
theorem discoverExtendedRule3DemandRanks_total_of_extendedDemandRank_at_bound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, domain root) :
    ∃ table,
      roots.foldlM (fun known root =>
        input.discoverExtendedRule3DemandRanks (6 * (fuel + 1) + 3) [] known root) [] =
          .ok table ∧
      input.ExtendedRule3DemandRankTableValid table ∧
      (∀ root ∈ roots, root ∈ table.map Prod.fst) := by
  refine input.discoverExtendedRule3DemandRanks_total_of_extendedDemandRank phase
    (6 * (fuel + 1) + 3) roots rootDomain ?_
  intro root _rootPresent
  have bounded := input.extendedDemandRank_le_bound root
  unfold extendedDemandRankBound at bounded
  omega



/-- The actual extended demand graph reachable from `roots` is acyclic, proved from the strict rank
decrease.  No acyclicity, cycle absence, or solver success is assumed. -/
theorem extendedRule3DemandAcyclic_of_extendedDemandRank
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, domain root) :
    input.ExtendedRule3DemandAcyclic roots := by
  intro cursor reachable
  exact acyclic_reachable_of_decreasing input.ExtendedRule3DemandEdge roots domain
    input.extendedDemandRank rootDomain
    (fun parent member child edge =>
      input.extendedDemandRank_successor_decreases phase parent member child edge)
    cursor reachable

/-- Generic weighted-demand acyclicity of the actual extended instantiation, derived from the
rank certificate. -/
theorem weightedExtendedDemandAcyclic_of_extendedDemandRank
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, domain root) :
    TetraStereo.Certificate.WeightedDemand.Acyclic
      (input.extendedWeightedDemandGraph fuel) roots :=
  (input.extendedWeightedDemandGraph_acyclic fuel roots).mpr
    (input.extendedRule3DemandAcyclic_of_extendedDemandRank phase roots rootDomain)



theorem prepareExtendedRule3DemandPlan_total_of_extendedDemandRank
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, domain root) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    (input.extendedRule3DemandAcyclic_of_extendedDemandRank phase roots rootDomain)

/-! ## Explicit unbranched-domain corollaries for all valid reroot orientations -/





theorem unbranchedExtendedRule3DemandAcyclic_of_phase
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (phase : input.ExtendedDemandRankPhase
      (input.LocalizedUnbranchedExtendedDemandDomain (fuel := fuel)))
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    input.ExtendedRule3DemandAcyclic roots :=
  input.extendedRule3DemandAcyclic_of_extendedDemandRank phase roots rootValid



theorem unbranchedWeightedExtendedDemandAcyclic_of_phase
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (phase : input.ExtendedDemandRankPhase
      (input.LocalizedUnbranchedExtendedDemandDomain (fuel := fuel)))
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    TetraStereo.Certificate.WeightedDemand.Acyclic
      (input.extendedWeightedDemandGraph fuel) roots :=
  input.weightedExtendedDemandAcyclic_of_extendedDemandRank phase roots rootValid



theorem unbranchedExtendedRule3DemandPlan_total_of_phase
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (phase : input.ExtendedDemandRankPhase
      (input.LocalizedUnbranchedExtendedDemandDomain (fuel := fuel)))
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_extendedDemandRank phase roots rootValid




theorem unbranchedExtendedRule3DemandDiscovery_total_of_phase
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (phase : input.ExtendedDemandRankPhase
      (input.LocalizedUnbranchedExtendedDemandDomain (fuel := fuel)))
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ table,
      roots.foldlM (fun known root =>
        input.discoverExtendedRule3DemandRanks (6 * (fuel + 1) + 3) [] known root) [] =
          .ok table ∧
      input.ExtendedRule3DemandRankTableValid table ∧
      (∀ root ∈ roots, root ∈ table.map Prod.fst) :=
  input.discoverExtendedRule3DemandRanks_total_of_extendedDemandRank_at_bound
    phase roots rootValid

/-! ## Generic weighted graph edge decrease and well-foundedness -/

/-- Every generic weighted-demand edge of the actual extended instantiation decreases the rank. -/
theorem weightedExtendedDemandRank_edge_decreases
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain)
    (parent : input.LocalizedRerootCursor fuel) (member : domain parent)
    (child : input.LocalizedRerootCursor fuel)
    (edge : TetraStereo.Certificate.WeightedDemand.Edge
      (input.extendedWeightedDemandGraph fuel) parent child) :
    input.extendedDemandRank child < input.extendedDemandRank parent := by
  have edge' : child ∈ input.extendedRule3DemandSuccessors parent := by
    rw [← input.extendedWeightedDemandGraph_successors fuel parent]
    exact edge
  exact (input.extendedDemandRank_successor_decreases phase parent member child edge').2

/-- The actual extended demand rank is well-founded on the certified valid reroot domain. -/
theorem extendedDemandRank_wellFounded
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {domain : input.LocalizedRerootCursor fuel → Prop}
    (phase : input.ExtendedDemandRankPhase domain) :
    WellFounded (fun child parent :
      {cursor : input.LocalizedRerootCursor fuel // domain cursor} =>
        input.ExtendedRule3DemandEdge parent.1 child.1) := by
  have wf : WellFounded (InvImage (fun a b : Nat => a < b)
      (fun cursor : {cursor : input.LocalizedRerootCursor fuel // domain cursor} =>
        input.extendedDemandRank cursor.1)) :=
    InvImage.wf _ Nat.lt_wfRel.wf
  exact Subrelation.wf
    (fun {child parent} edge =>
      (input.extendedDemandRank_successor_decreases phase parent.1 parent.2 child.1 edge).2)
    wf

/-! ## Inhabited special case: no actual callbacks -/




theorem extendedDemandRankPhase_of_noCallbacks
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (unbranched : input.LocalizedUnbranchedDoubleBondNeighbourDomain)
    (noCallbacks : ∀ occurrence : input.LocalizedCIPOccurrence fuel,
      input.rule3ExtendedNodeCallbackRequests occurrence = []) :
    input.ExtendedDemandRankPhase
      (fun cursor : input.LocalizedRerootCursor fuel =>
        input.LocalizedRerootCursorValid cursor) where
  unbranched := unbranched
  valid := fun _cursor valid => valid
  childDomain := by
    intro cursor valid child present
    exact input.localizedRerootChild_valid cursor child
      (input.executableLocalizedRerootChildren cursor)
      (input.executableLocalizedRerootChildren_declarative cursor) present
  requestDomain := by
    intro cursor _valid request requested _reference _inRequest
    rw [noCallbacks cursor.occurrence] at requested
    simp at requested
  requestStep := by
    intro cursor _valid request requested _reference _inRequest
    rw [noCallbacks cursor.occurrence] at requested
    simp at requested



theorem prepareExtendedRule3DemandPlan_total_of_noCallbacks_unbranched
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (unbranched : input.LocalizedUnbranchedDoubleBondNeighbourDomain)
    (noCallbacks : ∀ occurrence : input.LocalizedCIPOccurrence fuel,
      input.rule3ExtendedNodeCallbackRequests occurrence = [])
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_extendedDemandRank
    (input.extendedDemandRankPhase_of_noCallbacks unbranched noCallbacks)
    roots rootValid

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRankBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank_le_bound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank_lt_bound_succ
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank_child
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedDemandRequestStep
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank_request
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDoubleBondNeighbourFinset
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedUnbranchedDoubleBondNeighbourDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedUnbranchedExtendedDemandDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedDemandRankPhase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank_successor_decreases
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank_actualCallback
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.discoverExtendedRule3DemandRanks_total_of_extendedDemandRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.discoverExtendedRule3DemandRanks_total_of_extendedDemandRank_at_bound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedRule3DemandAcyclic_of_extendedDemandRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.weightedExtendedDemandAcyclic_of_extendedDemandRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prepareExtendedRule3DemandPlan_total_of_extendedDemandRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedExtendedRule3DemandAcyclic_of_phase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedWeightedExtendedDemandAcyclic_of_phase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedExtendedRule3DemandPlan_total_of_phase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedExtendedRule3DemandDiscovery_total_of_phase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.weightedExtendedDemandRank_edge_decreases
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank_wellFounded
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRankPhase_of_noCallbacks
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prepareExtendedRule3DemandPlan_total_of_noCallbacks_unbranched

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
