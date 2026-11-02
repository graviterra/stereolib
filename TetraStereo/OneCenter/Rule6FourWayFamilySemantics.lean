import TetraStereo.OneCenter.Rule6FourWayFamilyCore
import TetraStereo.OneCenter.ProductionCIPRule6ReferenceExecutionCompleteness

set_option autoImplicit false

/- The representation-independent declarations are re-exported from Rule6FourWayFamilyCore. -/

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456
open Rule6FourWayFamilySemantics

namespace DescriptorBranchingRule6CIPFrame

/-- Once the two dependent promoted traces are fixed, the literal occurrence implementation is
definitionally the pure three-condition evaluator. -/
theorem rankOccurrenceFourWayReferences_eq_evaluateFourWayCarrier
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    {parity : TetrahedralInputParity} {ligands sorted : List Nat}
    {firstPosition secondPosition : Nat} {first second : Rule6TrackedRanking}
    (firstPositionEq : sorted[0]? = some firstPosition)
    (firstTrace : PromotedRankingTrace (mol := mol) state fuel roots ligands sorted
      firstPosition first)
    (secondPositionEq : first.positions[1]? = some secondPosition)
    (secondTrace : PromotedRankingTrace (mol := mol) state fuel roots ligands first.positions
      secondPosition second) :
    rankOccurrenceFourWayReferences? (mol := mol) state fuel roots parity ligands sorted =
      evaluateFourWayCarrier? parity first second := by
  unfold rankOccurrenceFourWayReferences? evaluateFourWayCarrier?
  simp [firstPositionEq, firstTrace.sound, secondPositionEq, secondTrace.sound]

/-- With both promoted computations present, literal four-way refusal has exactly one of the three
explicit semantic failure witnesses. -/
theorem rankOccurrenceFourWayReferences_eq_none_iff_failure
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    {parity : TetrahedralInputParity} {ligands sorted : List Nat}
    {firstPosition secondPosition : Nat} {first second : Rule6TrackedRanking}
    (firstPositionEq : sorted[0]? = some firstPosition)
    (firstTrace : PromotedRankingTrace (mol := mol) state fuel roots ligands sorted
      firstPosition first)
    (secondPositionEq : first.positions[1]? = some secondPosition)
    (secondTrace : PromotedRankingTrace (mol := mol) state fuel roots ligands first.positions
      secondPosition second) :
    rankOccurrenceFourWayReferences? (mol := mol) state fuel roots parity ligands sorted = none ↔
      HasFourWayCarrierFailure parity first second := by
  rw [rankOccurrenceFourWayReferences_eq_evaluateFourWayCarrier firstPositionEq firstTrace
    secondPositionEq secondTrace]
  exact evaluateFourWayCarrier?_eq_none_iff_failure parity first second

/-- On an exact structural frame, the two rankings and their explicit failure classification
always exist.  Hence no lookup, traversal, or fuel failure remains hidden in four-way `none`. -/
theorem fourWayReferenceFailureClassification_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (parity : TetrahedralInputParity) :
    ∃ firstPosition first secondPosition second,
      sorted[0]? = some firstPosition ∧
      PromotedRankingTrace (mol := mol) state fuel roots frame.ligands sorted
        firstPosition first ∧
      first.positions[1]? = some secondPosition ∧
      PromotedRankingTrace (mol := mol) state fuel roots frame.ligands first.positions
        secondPosition second ∧
      (rankOccurrenceFourWayReferences? (mol := mol) state fuel roots parity frame.ligands
          sorted = none ↔ HasFourWayCarrierFailure parity first second) := by
  rcases frame.fourWayReferenceExecution_exists sorting with
    ⟨firstPosition, first, secondPosition, second,
      firstPositionEq, firstTrace, secondPositionEq, secondTrace⟩
  exact ⟨firstPosition, first, secondPosition, second, firstPositionEq, firstTrace,
    secondPositionEq, secondTrace,
    rankOccurrenceFourWayReferences_eq_none_iff_failure firstPositionEq firstTrace
      secondPositionEq secondTrace⟩

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
