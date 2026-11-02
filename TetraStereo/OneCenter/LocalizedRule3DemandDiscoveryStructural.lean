import TetraStereo.OneCenter.LocalizedRule3DemandDiscoveryExactness
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.LocalizedNoDoubleRule3ChemicalCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- A molecularly justified decreasing measure discharges graph acyclicity without testing
particular molecules or assuming that a checked rank table has already been found. -/
theorem rule3DemandAcyclic_of_decreasing
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (domain : input.LocalizedRerootCursor fuel → Prop)
    (measure : input.LocalizedRerootCursor fuel → Nat)
    (rootDomain : ∀ root ∈ roots, domain root)
    (decreases : ∀ parent, domain parent → ∀ child, input.Rule3DemandEdge parent child →
      domain child ∧ measure child < measure parent) : input.Rule3DemandAcyclic roots := by
  have pathClosed : ∀ {parent child}, domain parent →
      Relation.ReflTransGen input.Rule3DemandEdge parent child → domain child := by
    intro parent child present path
    induction path with
    | refl => exact present
    | tail _ edge ih => exact (decreases _ ih _ edge).1
  have pathDecreases : ∀ {parent child}, domain parent →
      Relation.TransGen input.Rule3DemandEdge parent child →
        domain child ∧ measure child < measure parent := by
    intro parent child present path
    induction path with
    | single edge => exact decreases _ present _ edge
    | tail _ edge ih =>
      obtain ⟨valid, smaller⟩ := decreases _ ih.1 _ edge
      exact ⟨valid, smaller.trans ih.2⟩
  intro cursor reachable cycle
  obtain ⟨root, member, path⟩ := reachable
  exact Nat.lt_irrefl _ (pathDecreases (pathClosed (rootDomain root member) path) cycle).2




theorem rule3DemandAcyclic_of_noCallbacks
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root)
    (noCallbacks : ∀ cursor : input.LocalizedRerootCursor fuel,
      input.LocalizedRerootCursorValid cursor → input.rule3NodeCallbackRequests cursor.occurrence = []) :
    input.Rule3DemandAcyclic roots := by
  apply input.rule3DemandAcyclic_of_decreasing roots input.LocalizedRerootCursorValid
    input.localizedRerootCursorBudget rootValid
  intro parent valid child edge
  have childMember : child ∈ input.executableLocalizedRerootChildren parent := by
    simpa only [Rule3DemandEdge, rule3DemandSuccessors, noCallbacks parent valid,
      List.flatten_nil, List.append_nil] using edge
  have derived := input.executableLocalizedRerootChildren_declarative parent
  exact ⟨input.localizedRerootChild_valid parent child _ derived childMember,
    input.localizedRerootChild_budget_lt parent child _ valid derived childMember⟩

theorem rule3NodeCallbackRequests_nil_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.rule3NodeCallbackRequests occurrence = [] := by
  have notEdge := input.localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords noDouble occurrence
  simp [rule3NodeCallbackRequests, localizedRule3OrdinaryRouteCertificate?,
    rule3OriginalNodeCallbackRequests, notEdge]

/-- The acyclicity premise is derived directly from source bond records for this entire
domain, including rings, arbitrary comparison depth and triple bonds. -/
theorem rule3DemandAcyclic_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {fuel : Nat} (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    input.Rule3DemandAcyclic roots :=
  input.rule3DemandAcyclic_of_noCallbacks roots rootValid
    (fun cursor _ => input.rule3NodeCallbackRequests_nil_of_noDoubleRecords noDouble cursor.occurrence)

theorem prepareRule3DemandPlan_total_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {fuel : Nat} (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ plan, input.prepareRule3DemandPlan roots = .ok plan :=
  input.prepareRule3DemandPlan_total_of_acyclic roots
    (input.rule3DemandAcyclic_of_noDoubleRecords noDouble roots rootValid)

/-- Starting from any molecular occurrences supplies valid cursors automatically. No graph,
rank function, per-molecule acyclicity proof or successful evaluation is an input. -/
theorem prepareRule3DemandPlan_occurrences_total_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {fuel : Nat} (occurrences : List (input.LocalizedCIPOccurrence fuel)) :
    ∃ plan, input.prepareRule3DemandPlan
      (occurrences.map fun occurrence => { occurrence, previous? := none }) = .ok plan := by
  apply input.prepareRule3DemandPlan_total_of_noDoubleRecords noDouble
  intro cursor present
  obtain ⟨occurrence, _, equal⟩ := List.mem_map.mp present
  subst cursor
  trivial

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
