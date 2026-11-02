import TetraStereo.OneCenter.ProductionCIPRule6CompleteKeyApplicability
import TetraStereo.OneCenter.Rule6FourWayFamilySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456

namespace DescriptorBranchingRule6CIPFrame

/-!
# Complete-key applicability of the dependent four-way Rule-6 carrier

The four-way path promotes the first position of the Rules-1--5 order, sorts by the complete key,
then promotes position one of that new order and sorts again.  The proposition below states this
construction using only the pure complete-key order.  It contains neither option-valued ranking
calls nor production uniqueness Booleans.
-/

/-- Independent complete-key meaning of one successful four-way Rule-6 descriptor. -/
structure CompleteKeyRule6FourWayDescriptor
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (sorted : List Nat) (parity : TetrahedralInputParity) (descriptor : RS) where
  firstReference : Nat
  first_reference : sorted[0]? = some firstReference
  firstOrder : List Nat
  first_order : firstOrder = frame.completeKeyRule6Ordering firstReference sorted
  secondReference : Nat
  second_reference : firstOrder[1]? = some secondReference
  secondOrder : List Nat
  second_order : secondOrder = frame.completeKeyRule6Ordering secondReference firstOrder
  orders_different : firstOrder ≠ secondOrder
  molecular_descriptor_agrees :
    RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven firstOrder) =
      RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven secondOrder)
  separation_status_agrees :
    sorted.Pairwise (frame.PromotedPositionNE firstReference) ↔
      firstOrder.Pairwise (frame.PromotedPositionNE secondReference)
  descriptor_eq :
    (firstOrder.Pairwise (frame.PromotedPositionNE secondReference) ∧
        descriptor = RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven secondOrder)) ∨
      (¬ firstOrder.Pairwise (frame.PromotedPositionNE secondReference) ∧
        descriptor = RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven secondOrder)))

/-- The independent dependent-key construction is sufficient for the literal four-way helper,
including the exact quotient-swapped descriptor in the non-strict case. -/
theorem rankOccurrenceFourWayReferences?_success_with_descriptor_of_completeKey
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (parity : TetrahedralInputParity) (descriptor : RS)
    (applicable : frame.CompleteKeyRule6FourWayDescriptor sorted parity descriptor) :
    ∃ agreement,
      rankOccurrenceFourWayReferences? (mol := mol) state fuel roots parity frame.ligands sorted =
          some agreement ∧
        agreement.descriptor = descriptor := by
  rcases applicable with
    ⟨specifiedFirstReference, specifiedFirstReferenceEq,
      specifiedFirstOrder, specifiedFirstOrderEq,
      specifiedSecondReference, specifiedSecondReferenceEq,
      specifiedSecondOrder, specifiedSecondOrderEq,
      ordersDifferent, molecularDescriptorAgrees, separationStatusAgrees, descriptorEq⟩
  rcases frame.fourWayReferenceExecution_exists sorting with
    ⟨firstReference, first, secondReference, second,
      firstReferenceEq, firstTrace, secondReferenceEq, secondTrace⟩
  have firstReferenceIdentity : specifiedFirstReference = firstReference :=
    Option.some.inj (specifiedFirstReferenceEq.symm.trans firstReferenceEq)
  subst specifiedFirstReference
  have sorted_lt : ∀ position, position ∈ sorted → position < 4 := by
    intro position member
    exact List.mem_range.mp (sorting.perm.mem_iff.mp member)
  have firstReferenceMem : firstReference ∈ sorted :=
    List.mem_iff_getElem?.2 ⟨0, firstReferenceEq⟩
  have firstReferenceLt : firstReference < 4 := sorted_lt firstReference firstReferenceMem
  have firstPositionsEq := frame.promoted_ranking_positions_eq_model firstReference
    firstReferenceLt sorted sorted_lt first firstTrace.sound
  have firstOrderIdentity : first.positions = specifiedFirstOrder :=
    firstPositionsEq.trans specifiedFirstOrderEq.symm
  rw [← firstOrderIdentity] at specifiedSecondReferenceEq
  rw [← firstOrderIdentity] at specifiedSecondOrderEq
  rw [← firstOrderIdentity] at ordersDifferent
  rw [← firstOrderIdentity] at molecularDescriptorAgrees
  rw [← firstOrderIdentity] at separationStatusAgrees
  rw [← firstOrderIdentity] at descriptorEq
  have secondReferenceIdentity : specifiedSecondReference = secondReference :=
    Option.some.inj (specifiedSecondReferenceEq.symm.trans secondReferenceEq)
  subst specifiedSecondReference
  have firstPositions_lt : ∀ position, position ∈ first.positions → position < 4 := by
    intro position member
    exact sorted_lt position (firstTrace.positions_perm.mem_iff.mp member)
  have secondReferenceMem : secondReference ∈ first.positions :=
    List.mem_iff_getElem?.2 ⟨1, secondReferenceEq⟩
  have secondReferenceLt : secondReference < 4 :=
    firstPositions_lt secondReference secondReferenceMem
  have secondPositionsEq := frame.promoted_ranking_positions_eq_model secondReference
    secondReferenceLt first.positions firstPositions_lt second secondTrace.sound
  have secondOrderIdentity : second.positions = specifiedSecondOrder :=
    secondPositionsEq.trans (by
      simpa [completeKeyRule6Ordering] using specifiedSecondOrderEq.symm)
  rw [← secondOrderIdentity] at ordersDifferent molecularDescriptorAgrees descriptorEq
  have firstUniqueIff := frame.promoted_ranking_unique_iff_input_pairwise_ne firstReference
    firstReferenceLt sorted sorted_lt first firstTrace.sound
  have secondUniqueIff := frame.promoted_ranking_unique_iff_input_pairwise_ne secondReference
    secondReferenceLt first.positions firstPositions_lt second secondTrace.sound
  have sameUnique : first.unique = second.unique := by
    cases firstUniqueEq : first.unique <;> cases secondUniqueEq : second.unique
    · rfl
    · have secondSeparated := secondUniqueIff.mp secondUniqueEq
      have firstSeparated := separationStatusAgrees.mpr secondSeparated
      have contradiction := firstUniqueIff.mpr firstSeparated
      simp [firstUniqueEq] at contradiction
    · have firstSeparated := firstUniqueIff.mp firstUniqueEq
      have secondSeparated := separationStatusAgrees.mp firstSeparated
      have contradiction := secondUniqueIff.mpr secondSeparated
      simp [secondUniqueEq] at contradiction
    · rfl
  let agreement : Rule6FourWayAgreement :=
    { firstRanking := first
      secondRanking := second
      descriptor := descriptor }
  have production : Rule6FourWayAgreementCertificate parity agreement := by
    refine ⟨ordersDifferent, molecularDescriptorAgrees, sameUnique, ?_⟩
    rcases descriptorEq with strictDescriptor | nonStrictDescriptor
    · have secondUnique : second.unique = true := secondUniqueIff.mpr strictDescriptor.1
      simpa [agreement, secondUnique] using strictDescriptor.2
    · have secondUnique : second.unique = false := by
        cases uniqueEq : second.unique
        · rfl
        · exact False.elim (nonStrictDescriptor.1 (secondUniqueIff.mp uniqueEq))
      simpa [agreement, secondUnique] using nonStrictDescriptor.2
  have trace : OccurrenceFourWayTrace (mol := mol) state fuel roots parity frame.ligands sorted
      agreement :=
    { firstPosition := firstReference
      first_position := firstReferenceEq
      first_trace := by simpa [agreement] using firstTrace
      second_trace := by simpa [agreement, secondReferenceEq] using secondTrace
      production := production }
  exact ⟨agreement, trace.sound, rfl⟩

/-- Exact four-way boundary: the literal dependent helper succeeds with a specified descriptor
if and only if the corresponding pure two-stage complete-key certificate is inhabited. -/
theorem rankOccurrenceFourWayReferences?_success_with_descriptor_iff_completeKey
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (parity : TetrahedralInputParity) (descriptor : RS) :
    (∃ agreement,
      rankOccurrenceFourWayReferences? (mol := mol) state fuel roots parity frame.ligands sorted =
          some agreement ∧
        agreement.descriptor = descriptor) ↔
      Nonempty (frame.CompleteKeyRule6FourWayDescriptor sorted parity descriptor) := by
  constructor
  · rintro ⟨agreement, computed, agreementDescriptor⟩
    rcases occurrenceFourWayTrace_complete state fuel roots parity frame.ligands sorted agreement
        computed with ⟨trace⟩
    rcases agreement with ⟨first, second, agreementOutput⟩
    rcases trace.production with
      ⟨ordersDifferent, molecularDescriptorAgrees, uniqueAgrees, outputEq⟩
    have sorted_lt : ∀ position, position ∈ sorted → position < 4 := by
      intro position member
      exact List.mem_range.mp (sorting.perm.mem_iff.mp member)
    have firstReferenceMem : trace.firstPosition ∈ sorted :=
      List.mem_iff_getElem?.2 ⟨0, trace.first_position⟩
    have firstReferenceLt : trace.firstPosition < 4 :=
      sorted_lt trace.firstPosition firstReferenceMem
    have firstPositionsEq := frame.promoted_ranking_positions_eq_model trace.firstPosition
      firstReferenceLt sorted sorted_lt first trace.first_trace.sound
    have firstPositions_lt : ∀ position, position ∈ first.positions → position < 4 := by
      intro position member
      exact sorted_lt position (trace.first_trace.positions_perm.mem_iff.mp member)
    have firstPositionsLength : first.positions.length = 4 := by
      calc
        first.positions.length = sorted.length := trace.first_trace.positions_perm.length_eq
        _ = (List.range 4).length := sorting.perm.length_eq
        _ = 4 := by simp
    have secondIndex : 1 < first.positions.length := by omega
    let secondReference := first.positions[1]
    have secondReferenceEq : first.positions[1]? = some secondReference :=
      List.getElem?_eq_getElem secondIndex
    have secondReferenceMem : secondReference ∈ first.positions :=
      List.getElem_mem secondIndex
    have secondReferenceLt : secondReference < 4 :=
      firstPositions_lt secondReference secondReferenceMem
    have secondComputed :
        rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots frame.ligands
          first.positions secondReference = some second := by
      simpa [secondReference, secondReferenceEq] using trace.second_trace.sound
    have secondPositionsEq := frame.promoted_ranking_positions_eq_model secondReference
      secondReferenceLt first.positions firstPositions_lt second secondComputed
    have firstUniqueIff := frame.promoted_ranking_unique_iff_input_pairwise_ne
      trace.firstPosition firstReferenceLt sorted sorted_lt first trace.first_trace.sound
    have secondUniqueIff := frame.promoted_ranking_unique_iff_input_pairwise_ne
      secondReference secondReferenceLt first.positions firstPositions_lt second secondComputed
    have separationStatusAgrees :
        sorted.Pairwise (frame.PromotedPositionNE trace.firstPosition) ↔
          first.positions.Pairwise (frame.PromotedPositionNE secondReference) := by
      constructor
      · intro firstSeparated
        have firstUnique : first.unique = true := firstUniqueIff.mpr firstSeparated
        have secondUnique : second.unique = true := by
          rw [← uniqueAgrees]
          exact firstUnique
        exact secondUniqueIff.mp secondUnique
      · intro secondSeparated
        have secondUnique : second.unique = true := secondUniqueIff.mpr secondSeparated
        have firstUnique : first.unique = true := by
          rw [uniqueAgrees]
          exact secondUnique
        exact firstUniqueIff.mp firstUnique
    have finalDescriptor :
        (first.positions.Pairwise (frame.PromotedPositionNE secondReference) ∧
            descriptor = RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven second.positions)) ∨
          (¬ first.positions.Pairwise (frame.PromotedPositionNE secondReference) ∧
            descriptor = RS.swap (RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven second.positions))) := by
      cases secondUniqueEq : second.unique
      · right
        refine ⟨?_, ?_⟩
        · intro separated
          have contradiction : second.unique = true := secondUniqueIff.mpr separated
          simp [secondUniqueEq] at contradiction
        · exact agreementDescriptor.symm.trans (by
            simpa [secondUniqueEq] using outputEq)
      · left
        refine ⟨secondUniqueIff.mp secondUniqueEq, ?_⟩
        exact agreementDescriptor.symm.trans (by
          simpa [secondUniqueEq] using outputEq)
    refine ⟨{
      firstReference := trace.firstPosition
      first_reference := trace.first_position
      firstOrder := first.positions
      first_order := by simpa [completeKeyRule6Ordering] using firstPositionsEq
      secondReference := secondReference
      second_reference := secondReferenceEq
      secondOrder := second.positions
      second_order := by simpa [completeKeyRule6Ordering] using secondPositionsEq
      orders_different := ordersDifferent
      molecular_descriptor_agrees := molecularDescriptorAgrees
      separation_status_agrees := separationStatusAgrees
      descriptor_eq := finalDescriptor }⟩
  · rintro ⟨applicable⟩
    exact frame.rankOccurrenceFourWayReferences?_success_with_descriptor_of_completeKey sorting
      parity descriptor applicable

/-- Full four-way production composition from independent complete-key applicability to the final
`rule6Result?` descriptor. -/
theorem rule6Result?_fourWay_success_of_completeKey
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (comparisons : Rule6InitialAdjacentDerivation (mol := mol) state fuel roots sorted adjacent)
    (adjacent_not_lt : some Ordering.lt ∉ adjacent)
    (partition : Rule6InitialCompletePartitionCertificate (mol := mol) state fuel roots sorted
      adjacent)
    (odd_false : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      some false)
    (group_one : rule6GroupCount adjacent = 1)
    (descriptor : RS)
    (applicable : frame.CompleteKeyRule6FourWayDescriptor sorted frame.parity descriptor) :
    ∃ result,
      rule6Result? (mol := mol) state fuel node roots = some result ∧
        result.fact.descriptor = descriptor := by
  rcases frame.rankOccurrenceFourWayReferences?_success_with_descriptor_of_completeKey sorting
      frame.parity descriptor applicable with ⟨agreement, ranked, agreementDescriptor⟩
  rcases occurrenceFourWayTrace_complete state fuel roots frame.parity frame.ligands sorted
      agreement ranked with ⟨trace⟩
  let carrier : Rule6FrameCertificate (mol := mol) state fuel node roots :=
    frame.toRule6FrameCertificateOfOddFalse sorting comparisons adjacent_not_lt partition
      odd_false
  let result : OccurrenceRule6Result :=
    { fact :=
        { key := canonicalOccurrenceKey node
          atom := node.atom
          descriptor := agreement.descriptor
          uppercase := agreement.secondRanking.pseudoComparisons != 1
          priorityPositions := agreement.secondRanking.positions }
      parity := frame.parity
      ligands := frame.ligands
      roots := roots
      sorted := sorted
      adjacent := adjacent
      groupCount := rule6GroupCount adjacent
      oddTopology? := some false
      carrier := .fourWay agreement }
  have derived : Rule6ResultDerivation (mol := mol) state fuel node roots result := by
    apply Rule6ResultDerivation.fourWay (result := result) carrier
        (by simpa [carrier] using group_one) agreement
    · simpa [carrier] using trace
    · rfl
  exact ⟨result, derived.production_eq, by simpa [result] using agreementDescriptor⟩

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
