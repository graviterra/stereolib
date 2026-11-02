import TetraStereo.OneCenter.LocalizedRuleMajorOwnMolecularEvidence
import TetraStereo.OneCenter.LocalizedRuleMajorPairComparison
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent reference selection and Rule-4b readings of the revised pipeline's
own generated state. No map, labels, successful build or reader equality is supplied. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP LocalizedCumulativeDecoratedTree Rule4aTableBridge
noncomputable section

theorem generated_referenceSelection (input : Input) (center : input.certified.TetrahedralCenter)
    (index : Fin 4) (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    ∃ (arm : input.certified.OriginalRootArm center index .rule4a
        (input.certified.molecularReader (descriptorMap input)
          (ActualReaderPhysicalBranchInverse.topTarget input center)))
      (compound : input.certified.LocalizedRerootCompoundRule45Key),
      input.certified.buildActualRuleMajorCompoundRule45Key?
          (ActualReaderPhysicalBranchInverse.topTarget input center)
          (input.certified.localizedDependencyView (referenceState input)
            (ActualReaderPhysicalBranchInverse.topTarget input center))
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center index) = some compound ∧
        compound.prior.references =
          toReferenceList (referenceSelection input.certified.moleculeGraph (descriptorMap input)
            (input.certified.topUnit center) (armGraph arm)) := by
  have selected := actualRuleMajorCompound_references_eq_referenceSelection input
    (index := index) (descriptorMap input) (descriptorMap_tetrahedral input)
    (ActualReaderPhysicalBranchInverse.topTarget input center)
    (ActualReaderPhysicalBranchInverse.topTarget_root input center)
    (ActualReaderPhysicalBranchInverse.topTarget_address input center) singleBonded acyclic
  rw [molecularView_eq_generatedView input singleBonded acyclic] at selected
  exact selected

theorem generated_rule4b_reading (input : Input) (center : input.certified.TetrahedralCenter)
    (index : Fin 4) (reference : RS)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    ∃ arm : input.certified.RuleMajorRootArm center index (.rule4b reference)
        (input.certified.localizedDependencyLabel
          (ActualReaderPhysicalBranchInverse.topTarget input center)
          (input.certified.localizedDependencyView (referenceState input)
            (ActualReaderPhysicalBranchInverse.topTarget input center))),
      input.certified.buildRuleMajorCumulativeWithReadExec? (.rule4b reference)
          (input.certified.localizedDependencyLabel
            (ActualReaderPhysicalBranchInverse.topTarget input center)
            (input.certified.localizedDependencyView (referenceState input)
              (ActualReaderPhysicalBranchInverse.topTarget input center)))
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center index) = some arm.key ∧
      OrdinaryCanonicalAddressing input.certified.moleculeGraph
        (readingEvidence input.certified.moleculeGraph (descriptorMap input)
          (input.certified.topUnit center) (ruleMajorArmGraph arm) (senseOf reference))
        (toOfficialSourceTree arm.tree).declarativeAddressing ∧
      Represents4b (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
        (reading input.certified.moleculeGraph (descriptorMap input)
          (input.certified.topUnit center) (ruleMajorArmGraph arm) (senseOf reference)) arm.key := by
  have built := exists_ruleMajor_executable_reading_of_treeLike input.certified center index reference
    (descriptorMap input) (descriptorMap_tetrahedral input)
    (ActualReaderPhysicalBranchInverse.topTarget input center)
    (ActualReaderPhysicalBranchInverse.topTarget_root input center)
    (ActualReaderPhysicalBranchInverse.topTarget_address input center) singleBonded acyclic
  rw [molecularReader_eq_generatedReader input singleBonded acyclic] at built
  exact built

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_referenceSelection
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_rule4b_reading
