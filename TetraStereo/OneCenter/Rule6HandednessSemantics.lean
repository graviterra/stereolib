import TetraStereo.OneCenter.Rule6HandednessCore
import TetraStereo.OneCenter.ProductionCIPRule6ReferenceExecutionCompleteness
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false

/- The representation-independent declarations are re-exported from Rule6HandednessCore. -/

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456
open Rule6HandednessSemantics

namespace DescriptorBranchingRule6CIPFrame

/-- Group-theoretic form of one partition-preserving constitutional automorphism admitted by the
production Rule-6 frame. -/
def IsFinFourPartitionPreservingConstitutionAutomorphism
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (permutation : Equiv.Perm (Fin 4)) : Prop :=
  (List.range 4).all (fun index =>
      rule6CompareAt? (mol := mol) state fuel roots index
        ((finFourPermutationList permutation).getD index 0) == some Ordering.eq) = true ∧
    mol.HasSeededConstitutionAutomorphism mol.localizedMancudeEdges
      (oddConstitutionVertices mol node.atom frame.ligands)
      (oddConstitutionSeed node.atom frame.ligands (finFourPermutationList permutation))

/-- Independent odd-automorphism proposition expressed directly in `S₄`. -/
def HasOddFinFourPartitionPreservingConstitutionAutomorphism
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) : Prop :=
  ∃ permutation : Equiv.Perm (Fin 4),
    Equiv.Perm.sign permutation = -1 ∧
    frame.IsFinFourPartitionPreservingConstitutionAutomorphism permutation

/-- The list-enumerated and finite-group odd-automorphism propositions are equivalent. -/
theorem hasOddPartitionPreservingConstitutionAutomorphism_iff_finFour
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    frame.HasOddPartitionPreservingConstitutionAutomorphism ↔
      frame.HasOddFinFourPartitionPreservingConstitutionAutomorphism := by
  unfold HasOddPartitionPreservingConstitutionAutomorphism
    HasOddFinFourPartitionPreservingConstitutionAutomorphism
    IsFinFourPartitionPreservingConstitutionAutomorphism
  constructor
  · rintro ⟨values, member, odd, partition, automorphism⟩
    rcases exists_finFourEquiv_permutationList_eq values member with
      ⟨permutation, valuesEq⟩
    subst values
    exact ⟨permutation, (finFourPermutationIsOdd_iff_sign_negOne permutation).mp odd,
      partition, automorphism⟩
  · rintro ⟨permutation, odd, partition, automorphism⟩
    exact ⟨finFourPermutationList permutation,
      finFourPermutationList_mem_permutations permutation,
      (finFourPermutationIsOdd_iff_sign_negOne permutation).mpr odd,
      partition, automorphism⟩

/-- Absence of the production-frame odd automorphism is exactly the assertion that every
admissible finite-group automorphism is even. -/
theorem no_hasOddPartitionPreservingConstitutionAutomorphism_iff_all_even
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ¬ frame.HasOddPartitionPreservingConstitutionAutomorphism ↔
      ∀ permutation,
        frame.IsFinFourPartitionPreservingConstitutionAutomorphism permutation →
        Equiv.Perm.sign permutation = 1 := by
  rw [frame.hasOddPartitionPreservingConstitutionAutomorphism_iff_finFour]
  unfold HasOddFinFourPartitionPreservingConstitutionAutomorphism
  constructor
  · intro noOdd permutation isAutomorphism
    rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with even | odd
    · exact even
    · exact False.elim (noOdd ⟨permutation, odd, isAutomorphism⟩)
  · intro allEven ⟨permutation, odd, isAutomorphism⟩
    have even := allEven permutation isAutomorphism
    rw [odd] at even
    norm_num at even

/-- The topology gate is precisely descriptor invariance under every admissible constitutional
automorphism of the four ligand positions. -/
theorem no_hasOddPartitionPreservingConstitutionAutomorphism_iff_descriptorInvariant
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (parity : TetrahedralInputParity) :
    ¬ frame.HasOddPartitionPreservingConstitutionAutomorphism ↔
      DescriptorInvariantUnder
        frame.IsFinFourPartitionPreservingConstitutionAutomorphism parity := by
  rw [frame.no_hasOddPartitionPreservingConstitutionAutomorphism_iff_all_even]
  exact (descriptorInvariantUnder_iff_all_even
    frame.IsFinFourPartitionPreservingConstitutionAutomorphism parity).symm

/-- End-to-end meaning of the production negative topology Boolean: on exact written-neighbour
data it returns `some false` exactly when `R/S` is invariant under every admitted constitutional
automorphism of the four-ligand carrier. -/
theorem oddTopologyDecision_eq_false_iff_descriptorInvariant
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact) (parity : TetrahedralInputParity) :
    hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some false ↔
      DescriptorInvariantUnder
        frame.IsFinFourPartitionPreservingConstitutionAutomorphism parity := by
  rw [frame.oddTopologyDecision_eq_false_iff_no_hasOddPartitionPreservingAutomorphism
    writtenExact]
  exact frame.no_hasOddPartitionPreservingConstitutionAutomorphism_iff_descriptorInvariant parity

/-- Any two orderings related by an admitted constitutional automorphism carry the same descriptor
once production has established the negative topology result. -/
theorem descriptor_eq_of_constitutionally_related_orderings
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact) (parity : TetrahedralInputParity)
    (oddFalse : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      some false)
    (first second : Equiv.Perm (Fin 4))
    (related : ∃ permutation,
      frame.IsFinFourPartitionPreservingConstitutionAutomorphism permutation ∧
      second = first.trans permutation) :
    descriptorOfFinFourOrdering parity second = descriptorOfFinFourOrdering parity first := by
  rcases related with ⟨permutation, isAutomorphism, rfl⟩
  exact (frame.oddTopologyDecision_eq_false_iff_descriptorInvariant writtenExact parity).mp
    oddFalse first permutation isAutomorphism

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
