import TetraStereo.OneCenter.ProductionCIPRule6CompleteKeyApplicability

set_option autoImplicit false

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456

namespace DescriptorBranchingRule6CIPFrame

/-!
# Complete-key applicability of the three-group Rule-6 carrier

The three-group branch uses the position at rank one as its sole reference and reverses the raw
promoted-order descriptor.  The judgment below states that result directly in terms of the pure
complete-key order.  It contains neither an option-valued ranking call nor a production
uniqueness Boolean.
-/

/-- Independent complete-key meaning of the final descriptor emitted by the three-group branch.
The four promoted keys must be pairwise separated, and the final descriptor is the reversal of
the descriptor read from their pure complete-key order. -/
def CompleteKeyRule6ThreeGroupDescriptor
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (positions : List Nat) (parity : TetrahedralInputParity)
    (referencePosition : Nat) (descriptor : RS) : Prop :=
  positions.Pairwise (frame.PromotedPositionNE referencePosition) ∧
    RS.swap
        (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven
            (frame.completeKeyRule6Ordering referencePosition positions))) =
      descriptor

/-- Exact singleton-reference bridge for the three-group branch. -/
theorem rankOccurrenceEquivalentReferences?_singleton_success_with_descriptor_iff_completeKey
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {positions : List Nat} (positions_perm : positions.Perm (List.range 4))
    (parity : TetrahedralInputParity) (referencePosition : Nat)
    (reference_lt : referencePosition < 4) (descriptor : RS) :
    (∃ ranking,
      rankOccurrenceEquivalentReferences? (mol := mol) state fuel roots parity frame.ligands
          positions [referencePosition] = some ranking ∧
        RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions)) = descriptor) ↔
      frame.CompleteKeyRule6ThreeGroupDescriptor positions parity referencePosition descriptor := by
  let rawDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven
      (frame.completeKeyRule6Ordering referencePosition positions))
  have singletonBoundary :=
    frame.rankOccurrenceEquivalentReferences?_success_with_descriptor_iff_completeKeyFamily
      positions_perm parity [referencePosition]
      (by
        intro candidate member
        have candidateEq : candidate = referencePosition := by simpa using member
        simpa [candidateEq] using reference_lt)
      rawDescriptor
  constructor
  · rintro ⟨ranking, ranked, finalDescriptorEq⟩
    let rankingRawDescriptor := RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven ranking.positions)
    have rankingBoundary :=
      frame.rankOccurrenceEquivalentReferences?_success_with_descriptor_iff_completeKeyFamily
        positions_perm parity [referencePosition]
        (by
          intro candidate member
          have candidateEq : candidate = referencePosition := by simpa using member
          simpa [candidateEq] using reference_lt)
        rankingRawDescriptor
    have rawSuccess :
        ∃ ranking,
          rankOccurrenceEquivalentReferences? (mol := mol) state fuel roots parity frame.ligands
              positions [referencePosition] = some ranking ∧
            RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven ranking.positions) = rankingRawDescriptor :=
      ⟨ranking, ranked, rfl⟩
    have family := rankingBoundary.1 rawSuccess
    have referenceComplete :
        frame.CompleteKeyRule6ReferenceDescriptor positions parity referencePosition
          rankingRawDescriptor := family.2 referencePosition (by simp)
    refine ⟨referenceComplete.1, ?_⟩
    calc
      RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven
            (frame.completeKeyRule6Ordering referencePosition positions))) =
          RS.swap rankingRawDescriptor := congrArg RS.swap referenceComplete.2
      _ = descriptor := by simpa [rankingRawDescriptor] using finalDescriptorEq
  · rintro ⟨separated, finalDescriptorEq⟩
    have family : frame.CompleteKeyRule6FamilyDescriptor positions parity [referencePosition]
        rawDescriptor := by
      refine ⟨by simp, ?_⟩
      intro candidate member
      have candidateEq : candidate = referencePosition := by simpa using member
      subst candidate
      exact ⟨separated, rfl⟩
    rcases singletonBoundary.2 family with ⟨ranking, ranked, rankingDescriptor⟩
    refine ⟨ranking, ranked, ?_⟩
    calc
      RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions)) =
          RS.swap rawDescriptor := congrArg RS.swap rankingDescriptor
      _ = descriptor := by simpa [rawDescriptor] using finalDescriptorEq

/-- Full three-group production composition from the independent single-reference complete-key
judgment to the exact final `rule6Result?` descriptor. -/
theorem rule6Result?_threeGroup_success_of_completeKey
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
    (group_three : rule6GroupCount adjacent = 3)
    (referencePosition : Nat) (reference_position : sorted[1]? = some referencePosition)
    (referenceRoot : CanonicalRerootCursor)
    (reference_root : roots[referencePosition]? = some referenceRoot)
    (middle_tie : adjacent[1]?.getD none = some Ordering.eq)
    (local_reference : occurrenceBranchHasLocalReference (mol := mol) state fuel
      [referenceRoot] = true)
    (descriptor : RS)
    (applicable : frame.CompleteKeyRule6ThreeGroupDescriptor sorted frame.parity
      referencePosition descriptor) :
    ∃ result,
      rule6Result? (mol := mol) state fuel node roots = some result ∧
        result.fact.descriptor = descriptor := by
  have referenceMem : referencePosition ∈ sorted :=
    List.mem_iff_getElem?.2 ⟨1, reference_position⟩
  have referenceLt : referencePosition < 4 :=
    List.mem_range.mp (sorting.perm.mem_iff.mp referenceMem)
  rcases
      (frame.rankOccurrenceEquivalentReferences?_singleton_success_with_descriptor_iff_completeKey
        sorting.perm frame.parity referencePosition referenceLt descriptor).2 applicable with
    ⟨ranking, ranked, rankingDescriptor⟩
  rcases occurrenceEquivalentReferencesTrace_complete state fuel roots frame.parity frame.ligands
      sorted [referencePosition] ranking ranked with ⟨trace⟩
  let carrier : Rule6FrameCertificate (mol := mol) state fuel node roots :=
    frame.toRule6FrameCertificateOfOddFalse sorting comparisons adjacent_not_lt partition
      odd_false
  let result : OccurrenceRule6Result :=
    { fact :=
        { key := canonicalOccurrenceKey node
          atom := node.atom
          descriptor := RS.swap (RawMolecule.descriptorOfParity frame.parity
            (RawMolecule.permutationIsEven ranking.positions))
          uppercase := true
          priorityPositions := ranking.positions }
      parity := frame.parity
      ligands := frame.ligands
      roots := roots
      sorted := sorted
      adjacent := adjacent
      groupCount := rule6GroupCount adjacent
      oddTopology? := some false
      carrier := .threeGroup referencePosition ranking }
  have referenceDefault : sorted[1]?.getD 0 = referencePosition := by
    simp [reference_position]
  have derived : Rule6ResultDerivation (mol := mol) state fuel node roots result := by
    exact Rule6ResultDerivation.threeGroup (result := result) carrier
      (by simpa [carrier] using group_three) referencePosition
      (by simpa [carrier] using referenceDefault.symm) referenceRoot
      (by simpa [carrier] using reference_root)
      (by simpa [carrier] using middle_tie)
      (by simpa using local_reference) ranking
      (by simpa [carrier] using trace) rfl
  exact ⟨result, derived.production_eq, by simpa [result] using rankingDescriptor⟩

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
