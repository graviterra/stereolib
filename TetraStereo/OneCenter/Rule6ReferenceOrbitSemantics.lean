import TetraStereo.OneCenter.Rule6ReferenceFamilySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter.Rule6ReferenceOrbitSemantics

/-!
# Constitutional-orbit semantics for Rule-6 reference rankings

The all-reference checker can only compare descriptors produced by its promoted rankings.  The
topology gate, by contrast, proves descriptor invariance on the quotient by partition-preserving
constitutional automorphisms.  This module states and proves the exact bridge between those two
facts.

A family of promoted rankings is in one constitutional orbit when there is one four-position
base ordering and every listed reference computes an ordering obtained from that base by an
admitted constitutional automorphism.  If the topology gate is negative and every ranking is
strict, the whole family necessarily has one common descriptor.  No assumption that a Rules-1--5
tie is itself a constitutional automorphism is hidden in the theorem.
-/

open RawMolecule
open Rule6HandednessSemantics
open Rule6ReferenceFamilySemantics

/-- Every completed ranking in a reference family is strict. -/
def StrictRule6ReferenceFamily (backend : ProductionRule6RankingBackend)
    (references : List Nat) : Prop :=
  ∀ reference, reference ∈ references → ∀ ranking,
    backend reference = some ranking → ranking.unique = true

end TetraStereo.OneCenter.Rule6ReferenceOrbitSemantics

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456
open Rule6HandednessSemantics
open Rule6ReferenceFamilySemantics
open Rule6ReferenceOrbitSemantics

namespace DescriptorBranchingRule6CIPFrame

/-- The promoted rankings computed for all listed references form one orbit under the
partition-preserving constitutional automorphisms admitted by the exact Rule-6 frame. -/
def ReferenceRankingsFormConstitutionalOrbit
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (backend : ProductionRule6RankingBackend) (references : List Nat) : Prop :=
  ∃ baseOrdering : Equiv.Perm (Fin 4),
    ∀ reference, reference ∈ references →
      ∃ ranking ordering symmetry,
        backend reference = some ranking ∧
        finFourPermutationList ordering = ranking.positions ∧
        frame.IsFinFourPartitionPreservingConstitutionAutomorphism symmetry ∧
        ordering = baseOrdering.trans symmetry

/-- A negative topology result makes the production descriptor constant on any explicitly proved
constitutional orbit of promoted reference rankings. -/
theorem commonRule6Descriptor_of_constitutionalOrbit
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact) (parity : TetrahedralInputParity)
    (backend : ProductionRule6RankingBackend) (references : List Nat)
    (referencesNonempty : references ≠ [])
    (oddFalse : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      some false)
    (strict : StrictRule6ReferenceFamily backend references)
    (orbit : frame.ReferenceRankingsFormConstitutionalOrbit backend references) :
    ∃ descriptor, CommonRule6Descriptor backend parity references descriptor := by
  rcases orbit with ⟨baseOrdering, orbit⟩
  let descriptor := descriptorOfFinFourOrdering parity baseOrdering
  refine ⟨descriptor, referencesNonempty, ?_⟩
  intro reference member
  rcases orbit reference member with
    ⟨ranking, ordering, symmetry, rankingEq, positionsEq, isAutomorphism, orderingEq⟩
  refine ⟨ranking, rankingEq, strict reference member ranking rankingEq, ?_⟩
  have invariant := frame.descriptor_eq_of_constitutionally_related_orderings writtenExact parity
    oddFalse baseOrdering ordering ⟨symmetry, isAutomorphism, orderingEq⟩
  simpa [descriptor, descriptorOfFinFourOrdering, positionsEq] using invariant

/-- Under the same orbit and strictness facts, the literal all-reference checker succeeds. -/
theorem rankProductionRule6EquivalentReferencesWithBackend?_success_of_constitutionalOrbit
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact) (parity : TetrahedralInputParity)
    (backend : ProductionRule6RankingBackend) (references : List Nat)
    (referencesNonempty : references ≠ [])
    (oddFalse : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      some false)
    (strict : StrictRule6ReferenceFamily backend references)
    (orbit : frame.ReferenceRankingsFormConstitutionalOrbit backend references) :
    ∃ first,
      rankProductionRule6EquivalentReferencesWithBackend? backend parity references =
        some first := by
  apply (rankProductionRule6EquivalentReferencesWithBackend?_success_iff_commonDescriptor
    backend parity references).mpr
  exact frame.commonRule6Descriptor_of_constitutionalOrbit writtenExact parity backend references
    referencesNonempty oddFalse strict orbit

/-- Production specialization: once the generated two-group references are proved to be one
constitutional orbit and their completed rankings are strict, structural execution plus the
negative topology gate force the production reference check to return a ranking. -/
theorem rankOccurrenceEquivalentReferences_success_of_constitutionalOrbit
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (parity : TetrahedralInputParity)
    (oddFalse : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      some false)
    (strict : StrictRule6ReferenceFamily
      (productionOccurrenceRule6RankingBackend (mol := mol) state fuel roots frame.ligands sorted)
      (rule6EquivalentReferencePositions sorted adjacent))
    (orbit : frame.ReferenceRankingsFormConstitutionalOrbit
      (productionOccurrenceRule6RankingBackend (mol := mol) state fuel roots frame.ligands sorted)
      (rule6EquivalentReferencePositions sorted adjacent)) :
    ∃ first,
      rankOccurrenceEquivalentReferences? (mol := mol) state fuel roots parity frame.ligands sorted
        (rule6EquivalentReferencePositions sorted adjacent) = some first := by
  let references := rule6EquivalentReferencePositions sorted adjacent
  let backend := productionOccurrenceRule6RankingBackend (mol := mol) state fuel roots
    frame.ligands sorted
  rcases frame.twoGroupReferenceExecutionCertificate_nonempty
      (adjacent := adjacent) sorting with ⟨execution⟩
  have referencePresent : references.head?.isSome = true := by
    simpa [references] using execution.references_nonempty
  have referencesNonempty : references ≠ [] := by
    intro referencesEq
    simp [referencesEq] at referencePresent
  have success := frame.rankProductionRule6EquivalentReferencesWithBackend?_success_of_constitutionalOrbit
    writtenExact parity backend references referencesNonempty oddFalse
    (by simpa [backend, references] using strict)
    (by simpa [backend, references] using orbit)
  simpa [rankOccurrenceEquivalentReferences?, backend, references] using success

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
