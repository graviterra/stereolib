import TetraStereo.OneCenter.Rule6ReferenceFamilyCore
import TetraStereo.OneCenter.Rule6HandednessSemantics

set_option autoImplicit false

/- The representation-independent declarations are re-exported from Rule6ReferenceFamilyCore. -/

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456
open Rule6ReferenceFamilySemantics

namespace DescriptorBranchingRule6CIPFrame

/-- On the exact two-group reference enumeration, structural execution removes all operational
failure modes. The production checker returns `none` exactly for a completed non-strict ranking or
a completed cross-reference descriptor conflict. -/
theorem rankOccurrenceEquivalentReferences_eq_none_iff_failureWitness
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (parity : TetrahedralInputParity) :
    rankOccurrenceEquivalentReferences? (mol := mol) state fuel roots parity frame.ligands sorted
        (rule6EquivalentReferencePositions sorted adjacent) = none ↔
      HasNonStrictRule6Reference
          (productionOccurrenceRule6RankingBackend (mol := mol) state fuel roots frame.ligands
            sorted)
          (rule6EquivalentReferencePositions sorted adjacent) ∨
        HasRule6ReferenceDescriptorConflict
          (productionOccurrenceRule6RankingBackend (mol := mol) state fuel roots frame.ligands
            sorted)
          parity (rule6EquivalentReferencePositions sorted adjacent) := by
  let references := rule6EquivalentReferencePositions sorted adjacent
  let backend := productionOccurrenceRule6RankingBackend (mol := mol) state fuel roots
    frame.ligands sorted
  let execution := frame.twoGroupReferenceExecutionCertificate_nonempty
    (adjacent := adjacent) sorting
  rcases execution with ⟨execution⟩
  have referencePresent : references.head?.isSome = true := by
    simpa [references] using execution.references_nonempty
  have referencesNonempty : references ≠ [] := by
    intro referencesEq
    simp [referencesEq] at referencePresent
  have rankingTotal : ∀ reference, reference ∈ references →
      ∃ ranking, backend reference = some ranking := by
    intro reference member
    rcases execution.promoted_trace reference member with ⟨ranking, trace⟩
    exact ⟨ranking, by
      simpa [backend, productionOccurrenceRule6RankingBackend] using trace.sound⟩
  simpa [rankOccurrenceEquivalentReferences?, backend, references] using
    (rankProductionRule6EquivalentReferencesWithBackend?_eq_none_iff_failureWitness
      backend parity references referencesNonempty rankingTotal)

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
