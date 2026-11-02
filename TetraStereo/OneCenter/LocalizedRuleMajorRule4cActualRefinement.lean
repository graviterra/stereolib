import TetraStereo.OneCenter.LocalizedRuleMajorRule4cCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorOwnMolecularEvidence
import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingSignature
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Molecular discharge of the complete Rule-4c readback obligations. All labels are read
from the actual graph and molecular map; the generated-map instance uses the revised evaluator's
own fixed point. Lowercase labels and arbitrary reference populations remain permitted. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
open Rule4cObservationBridge
noncomputable section

theorem ruleMajorReadback4c_of_treeLike
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {reference : RS} (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index (.rule4c reference)
      (input.molecularReader descriptorMap target)) :
    RuleMajorTreeReadback4c arm.tree descriptorMap (input.topUnit center) reference := by
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
  · apply rule4abcOnly_readingEvidence4c_of_single
    intro atom other
    rcases Nat.eq_zero_or_pos (input.moleculeGraph.bond atom other) with zero | positive
    · rw [zero]; exact Nat.zero_le 1
    · exact le_of_eq (singleBonded atom other positive)

theorem ruleMajorReadback4c_of_generatedState
    (input : LocalizedRuleMajorReference.Input) (center : input.certified.TetrahedralCenter)
    (index : Fin 4) (reference : RS)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (arm : input.certified.RuleMajorRootArm center index (.rule4c reference)
      (input.certified.molecularReader (LocalizedRuleMajorReference.descriptorMap input)
        (ActualReaderPhysicalBranchInverse.topTarget input center))) :
    RuleMajorTreeReadback4c arm.tree (LocalizedRuleMajorReference.descriptorMap input)
      (input.certified.topUnit center) reference :=
  ruleMajorReadback4c_of_treeLike (LocalizedRuleMajorReference.descriptorMap input)
    (LocalizedRuleMajorReference.descriptorMap_tetrahedral input)
    (ActualReaderPhysicalBranchInverse.topTarget input center)
    (ActualReaderPhysicalBranchInverse.topTarget_root input center)
    (ActualReaderPhysicalBranchInverse.topTarget_address input center) singleBonded acyclic arm

/-- Actual executable expansion, canonical sibling addressing and complete independent Rule-4c
reading, with every molecular-readback obligation derived. No successful-build premise is used. -/
theorem exists_ruleMajor_executable_reading4c_of_treeLike
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    (reference : RS) (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic) :
    ∃ arm : input.RuleMajorRootArm center index (.rule4c reference)
        (input.molecularReader descriptorMap target),
      input.buildRuleMajorCumulativeWithReadExec? (.rule4c reference)
          (input.molecularReader descriptorMap target)
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index) = some arm.key ∧
      OrdinaryCanonicalAddressing input.moleculeGraph
        (readingEvidence4c input.moleculeGraph descriptorMap (input.topUnit center)
          (ruleMajorArmGraph arm) (senseOf reference))
        (toOfficialSourceTree arm.tree).declarativeAddressing ∧
      Represents4c (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          (ruleMajorArmGraph arm) (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
          (some (senseOf reference)))).2 arm.key := by
  obtain ⟨arm⟩ := input.exists_ruleMajorRootArm center index (.rule4c reference)
    (input.molecularReader descriptorMap target)
  have readback := ruleMajorReadback4c_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic arm
  refine ⟨arm, ?_, ruleMajorRootArm_ordinaryCanonicalAddressing_readingEvidence4c arm readback,
    ruleMajorRootArm_root_represents4c arm readback⟩
  rw [input.buildRuleMajorCumulativeWithReadExec_eq]
  exact arm.built

/-- The actual complete Rule-4c observation is independent of which faithful exact expansion
is used to state the molecular specification. Layout bounds do not impose a fixed depth. -/
theorem ruleMajor_reading4c_represents_every_faithful
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {reference : RS} (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index (.rule4c reference)
      (input.molecularReader descriptorMap target))
    (graph : RootedDigraph input.Atom)
    (faithful : graph.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center index))
    {W D : Nat} (width : (ruleMajorArmGraph arm).width ≤ W)
    (depth : (ruleMajorArmGraph arm).height ≤ D) :
    Represents4c W D
      (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
        graph W D (some (senseOf reference)))).2 arm.key := by
  have hyp := ruleMajorReadback4c_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic arm
  have represented := (ruleMajorRootArm_node_bridge4c arm hyp width depth
    (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.2.2
  change Represents4c W D
    (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
      (ruleMajorArmGraph arm) W D (some (senseOf reference)))).2 arm.key at represented
  rw [completeReadingAt_eq_of_faithful input.moleculeGraph descriptorMap (input.topUnit center)
    center.1 (input.canonicalLigandAtom center index) arm.faithful faithful W D
    (some (senseOf reference))] at represented
  exact represented

end
end TetraStereo.OneCenter.Rule4aTableBridge

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule4aTableBridge Rule4cObservationBridge
noncomputable section

/-- The complete Rule-4c reading of the revised evaluator's own generated state. The only
domain hypotheses are simple bonds and acyclicity. No label map, reference-selection result or
sorting result is supplied. The reference parameter ranges over either candidate sense. -/
theorem generated_rule4c_reading (input : Input) (center : input.certified.TetrahedralCenter)
    (index : Fin 4) (reference : RS)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    ∃ arm : input.certified.RuleMajorRootArm center index (.rule4c reference)
        (input.certified.localizedDependencyLabel
          (ActualReaderPhysicalBranchInverse.topTarget input center)
          (input.certified.localizedDependencyView (referenceState input)
            (ActualReaderPhysicalBranchInverse.topTarget input center))),
      input.certified.buildRuleMajorCumulativeWithReadExec? (.rule4c reference)
          (input.certified.localizedDependencyLabel
            (ActualReaderPhysicalBranchInverse.topTarget input center)
            (input.certified.localizedDependencyView (referenceState input)
              (ActualReaderPhysicalBranchInverse.topTarget input center)))
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center index) = some arm.key ∧
      OrdinaryCanonicalAddressing input.certified.moleculeGraph
        (readingEvidence4c input.certified.moleculeGraph (descriptorMap input)
          (input.certified.topUnit center) (ruleMajorArmGraph arm) (senseOf reference))
        (toOfficialSourceTree arm.tree).declarativeAddressing ∧
      Represents4c (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
        (ofLex (completeReadingAt input.certified.moleculeGraph (descriptorMap input)
          (input.certified.topUnit center) (ruleMajorArmGraph arm)
          (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
          (some (senseOf reference)))).2 arm.key := by
  have result := exists_ruleMajor_executable_reading4c_of_treeLike input.certified center index reference
    (descriptorMap input) (descriptorMap_tetrahedral input)
    (ActualReaderPhysicalBranchInverse.topTarget input center)
    (ActualReaderPhysicalBranchInverse.topTarget_root input center)
    (ActualReaderPhysicalBranchInverse.topTarget_address input center) singleBonded acyclic
  rw [molecularReader_eq_generatedReader input singleBonded acyclic] at result
  exact result

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorReadback4c_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorReadback4c_of_generatedState
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.exists_ruleMajor_executable_reading4c_of_treeLike
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_rule4c_reading
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajor_reading4c_represents_every_faithful
