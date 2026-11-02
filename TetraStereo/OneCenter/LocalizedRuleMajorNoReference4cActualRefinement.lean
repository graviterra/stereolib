import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceRule4cCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorRule4cActualRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual molecular readback and independent refinement for the no-reference Rule-4c stage.
The stage is valid with lowercase auxiliary labels; none of the theorems erase them or assume
their absence. The own-state endpoint supplies its map from the revised executable evaluator. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
open Rule4cObservationBridge
noncomputable section

theorem ruleMajorReadbackNoReference4c_of_treeLike
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index .rule4cNoReference
      (input.molecularReader descriptorMap target)) :
    RuleMajorTreeReadbackNoReference4c arm.tree descriptorMap (input.topUnit center) := by
  have readback := ruleMajor_molecularReader_arm_observations descriptorMap target arm
    targetRoot targetAddress singleBonded acyclic
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro node actual lookup
    obtain ⟨actual', lookup', label, _⟩ := readback node
    rw [decoratedSubtreeAt?_eq_subtreeAt?] at lookup
    cases Option.some.inj (lookup.symm.trans lookup')
    exact label
  · intro node
    exact occurrenceReading_tetrahedral_of_map _ _ _ _ tetrahedral node
  · intro node
    obtain ⟨_, _, _, available⟩ := readback node
    exact available
  · apply rule4acOnly_noReferenceEvidence4c_of_single
    intro atom other
    rcases Nat.eq_zero_or_pos (input.moleculeGraph.bond atom other) with zero | positive
    · rw [zero]; exact Nat.zero_le 1
    · exact le_of_eq (singleBonded atom other positive)

theorem exists_ruleMajor_executable_noReference4c_of_treeLike
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic) :
    ∃ arm : input.RuleMajorRootArm center index .rule4cNoReference
        (input.molecularReader descriptorMap target),
      input.buildRuleMajorCumulativeWithReadExec? .rule4cNoReference
          (input.molecularReader descriptorMap target)
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index) = some arm.key ∧
      OrdinaryCanonicalAddressing input.moleculeGraph
        (noReferenceEvidence4c input.moleculeGraph descriptorMap (input.topUnit center)
          (ruleMajorArmGraph arm))
        (toOfficialSourceTree arm.tree).declarativeAddressing ∧
      Represents4c (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          (ruleMajorArmGraph arm) (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
          none)).2 arm.key := by
  obtain ⟨arm⟩ := input.exists_ruleMajorRootArm center index .rule4cNoReference
    (input.molecularReader descriptorMap target)
  have readback := ruleMajorReadbackNoReference4c_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic arm
  refine ⟨arm, ?_, ruleMajorRootArm_ordinaryCanonicalAddressing_noReference4c arm readback,
    ruleMajorRootArm_root_represents4c_noReference arm readback⟩
  rw [input.buildRuleMajorCumulativeWithReadExec_eq]
  exact arm.built

theorem ruleMajor_noReference4c_represents_every_faithful
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index .rule4cNoReference
      (input.molecularReader descriptorMap target))
    (graph : RootedDigraph input.Atom)
    (faithful : graph.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center index))
    {W D : Nat} (width : (ruleMajorArmGraph arm).width ≤ W)
    (depth : (ruleMajorArmGraph arm).height ≤ D) :
    Represents4c W D
      (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
        graph W D none)).2 arm.key := by
  have hyp := ruleMajorReadbackNoReference4c_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic arm
  have represented := (ruleMajorRootArm_node_bridge_noReference4c arm hyp width depth
    (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.2
  change Represents4c W D
    (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
      (ruleMajorArmGraph arm) W D none)).2 arm.key at represented
  rw [completeReadingAt_eq_of_faithful input.moleculeGraph descriptorMap (input.topUnit center)
    center.1 (input.canonicalLigandAtom center index) arm.faithful faithful W D none] at represented
  exact represented

end
end TetraStereo.OneCenter.Rule4aTableBridge

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule4aTableBridge Rule4cObservationBridge
noncomputable section

/-- No-reference Rule-4c refinement from the actual revised state, with no supplied labels,
build success, canonicality or readback premises. -/
theorem generated_noReference4c_reading (input : Input) (center : input.certified.TetrahedralCenter)
    (index : Fin 4) (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    let target := ActualReaderPhysicalBranchInverse.topTarget input center
    let reader := input.certified.localizedDependencyLabel target
      (input.certified.localizedDependencyView (referenceState input) target)
    ∃ arm : input.certified.RuleMajorRootArm center index .rule4cNoReference reader,
      input.certified.buildRuleMajorCumulativeWithReadExec? .rule4cNoReference reader
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center index) = some arm.key ∧
      OrdinaryCanonicalAddressing input.certified.moleculeGraph
        (noReferenceEvidence4c input.certified.moleculeGraph (descriptorMap input)
          (input.certified.topUnit center) (ruleMajorArmGraph arm))
        (toOfficialSourceTree arm.tree).declarativeAddressing ∧
      Represents4c (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
        (ofLex (completeReadingAt input.certified.moleculeGraph (descriptorMap input)
          (input.certified.topUnit center) (ruleMajorArmGraph arm)
          (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height none)).2 arm.key := by
  have result := exists_ruleMajor_executable_noReference4c_of_treeLike input.certified center index
    (descriptorMap input) (descriptorMap_tetrahedral input)
    (ActualReaderPhysicalBranchInverse.topTarget input center)
    (ActualReaderPhysicalBranchInverse.topTarget_root input center)
    (ActualReaderPhysicalBranchInverse.topTarget_address input center) singleBonded acyclic
  rw [molecularReader_eq_generatedReader input singleBonded acyclic] at result
  exact result

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorReadbackNoReference4c_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.exists_ruleMajor_executable_noReference4c_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajor_noReference4c_represents_every_faithful
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_noReference4c_reading
