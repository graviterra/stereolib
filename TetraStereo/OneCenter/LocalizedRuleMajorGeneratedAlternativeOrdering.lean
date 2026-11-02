import TetraStereo.OneCenter.LocalizedRuleMajorActualAlternativeOrdering
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The complete alternative comparator on the revised evaluator's own generated labels.
All five stage builds are constructed from the actual molecular input. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
noncomputable section

theorem generated_complete_alternative_comparison (input : Input)
    (center : input.certified.TetrahedralCenter) (index : Fin 4)
    (leftReference rightReference : RS)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    let target := ActualReaderPhysicalBranchInverse.topTarget input center
    let reader := input.certified.localizedDependencyLabel target
      (input.certified.localizedDependencyView (referenceState input) target)
    ∃ (a : input.certified.RuleMajorRootArm center index .rule4a reader)
      (bL : input.certified.RuleMajorRootArm center index (.rule4b leftReference) reader)
      (cL : input.certified.RuleMajorRootArm center index (.rule4c leftReference) reader)
      (bR : input.certified.RuleMajorRootArm center index (.rule4b rightReference) reader)
      (cR : input.certified.RuleMajorRootArm center index (.rule4c rightReference) reader),
      ∀ W D : Nat,
        (ruleMajorArmGraph bL).width ≤ W → (ruleMajorArmGraph bL).height ≤ D →
        (ruleMajorArmGraph cL).width ≤ W → (ruleMajorArmGraph cL).height ≤ D →
        (ruleMajorArmGraph bR).width ≤ W → (ruleMajorArmGraph bR).height ≤ D →
        (ruleMajorArmGraph cR).width ≤ W → (ruleMajorArmGraph cR).height ≤ D →
        input.certified.compareRule4bcReadingsComplete
            { reference? := some leftReference, rule4bKey := bL.key, rule4cKey := cL.key }
            { reference? := some rightReference, rule4bKey := bR.key, rule4cKey := cR.key } =
          compare
            (completeReadingAt input.certified.moleculeGraph (descriptorMap input)
              (input.certified.topUnit center) (ruleMajorArmGraph a) W D
              (some (senseOf leftReference)))
            (completeReadingAt input.certified.moleculeGraph (descriptorMap input)
              (input.certified.topUnit center) (ruleMajorArmGraph a) W D
              (some (senseOf rightReference))) := by
  dsimp only
  rw [← molecularReader_eq_generatedReader input singleBonded acyclic]
  let target := ActualReaderPhysicalBranchInverse.topTarget input center
  let reader := input.certified.molecularReader (descriptorMap input) target
  obtain ⟨a⟩ := input.certified.exists_ruleMajorRootArm center index .rule4a reader
  obtain ⟨bL⟩ := input.certified.exists_ruleMajorRootArm center index (.rule4b leftReference) reader
  obtain ⟨cL⟩ := input.certified.exists_ruleMajorRootArm center index (.rule4c leftReference) reader
  obtain ⟨bR⟩ := input.certified.exists_ruleMajorRootArm center index (.rule4b rightReference) reader
  obtain ⟨cR⟩ := input.certified.exists_ruleMajorRootArm center index (.rule4c rightReference) reader
  refine ⟨a, bL, cL, bR, cR, ?_⟩
  intro W D widthBL depthBL widthCL depthCL widthBR depthBR widthCR depthCR
  exact actual_ruleMajor_completeReading_compare (descriptorMap input)
    (descriptorMap_tetrahedral input) target
    (ActualReaderPhysicalBranchInverse.topTarget_root input center)
    (ActualReaderPhysicalBranchInverse.topTarget_address input center)
    singleBonded acyclic a bL cL bR cR (ruleMajorArmGraph a) a.faithful
    widthBL depthBL widthCL depthCL widthBR depthBR widthCR depthCR

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_complete_alternative_comparison
