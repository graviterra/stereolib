import TetraStereo.OneCenter.LocalizedRuleMajorCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorMolecularReadback
import TetraStereo.OneCenter.DeclarativeCIPLigandSignatureLayout
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Actual whole-rule Rule-4b readings without physical rigidity

For every finite acyclic single-bond certified input and every tetrahedral molecular descriptor
map, the actual executable rule-major builder succeeds at the structural budget. Its actual
occurrence tree is faithful, its addressing is ordinary-canonical for the independent reading
evidence, and its Rule-4b column represents that independent reading.

The map may contain R, S, r, s or absent entries. No sibling-kind, non-root rigid/twin,
reference-count, strictness or successful-computation premise is used. This is a comparison-data
refinement theorem; it does not assert that an arbitrary supplied map is chemically correct.
The generated ordered map is an unconditional instance of the tetrahedral-map condition.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical

theorem ruleMajorReadback4b_of_treeLike
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {ρ : RS} (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index (.rule4b ρ)
      (input.molecularReader descriptorMap target)) :
    RuleMajorTreeReadback4b arm.tree descriptorMap (input.topUnit center) ρ := by
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
  · apply rule4abOnly_readingEvidence_of_single
    intro atom other
    rcases Nat.eq_zero_or_pos (input.moleculeGraph.bond atom other) with zero | positive
    · rw [zero]; exact Nat.zero_le 1
    · exact le_of_eq (singleBonded atom other positive)

/-- Actual canonicality with every molecular readback obligation discharged. -/
theorem ruleMajorArm_ordinaryCanonical_of_treeLike
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {ρ : RS} (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index (.rule4b ρ)
      (input.molecularReader descriptorMap target)) :
    OrdinaryCanonicalAddressing input.moleculeGraph
      (readingEvidence input.moleculeGraph descriptorMap (input.topUnit center)
        (ruleMajorArmGraph arm) (senseOf ρ))
      (toOfficialSourceTree arm.tree).declarativeAddressing :=
  ruleMajorRootArm_ordinaryCanonicalAddressing_readingEvidence arm
    (ruleMajorReadback4b_of_treeLike descriptorMap tetrahedral target targetRoot targetAddress
      singleBonded acyclic arm)

/-- Actual molecular input to executable expansion and independent complete Rule-4b reading.
The expansion, addressing and representation refer to the same built tree and key. -/
theorem exists_ruleMajor_executable_reading_of_treeLike
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    (ρ : RS) (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic) :
    ∃ arm : input.RuleMajorRootArm center index (.rule4b ρ)
        (input.molecularReader descriptorMap target),
      input.buildRuleMajorCumulativeWithReadExec? (.rule4b ρ)
          (input.molecularReader descriptorMap target)
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index) = some arm.key ∧
      OrdinaryCanonicalAddressing input.moleculeGraph
        (readingEvidence input.moleculeGraph descriptorMap (input.topUnit center)
          (ruleMajorArmGraph arm) (senseOf ρ))
        (toOfficialSourceTree arm.tree).declarativeAddressing ∧
      Represents4b (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
        (reading input.moleculeGraph descriptorMap (input.topUnit center)
          (ruleMajorArmGraph arm) (senseOf ρ)) arm.key := by
  obtain ⟨arm⟩ := input.exists_ruleMajorRootArm center index (.rule4b ρ)
    (input.molecularReader descriptorMap target)
  have readback := ruleMajorReadback4b_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic arm
  refine ⟨arm, ?_, ruleMajorRootArm_ordinaryCanonicalAddressing_readingEvidence arm readback,
    ruleMajorRootArm_root_represents4b arm readback⟩
  rw [input.buildRuleMajorCumulativeWithReadExec_eq]
  exact arm.built

/-- The generated ordered state supplies the molecular map, including any lowercase entries.
Only acyclicity and single bonds are required for this comparison-data connection. -/
theorem exists_ruleMajor_generated_reading_of_treeLike
    (input : LocalizedUniversalReference.Input) (center : input.certified.TetrahedralCenter)
    (index : Fin 4) (ρ : RS)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    ∃ arm : input.certified.RuleMajorRootArm center index (.rule4b ρ)
        (input.certified.molecularReader (actualOrderedReferenceDescriptorMap input) target),
      input.certified.buildRuleMajorCumulativeWithReadExec? (.rule4b ρ)
          (input.certified.molecularReader (actualOrderedReferenceDescriptorMap input) target)
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center index) = some arm.key ∧
      OrdinaryCanonicalAddressing input.certified.moleculeGraph
        (readingEvidence input.certified.moleculeGraph (actualOrderedReferenceDescriptorMap input)
          (input.certified.topUnit center) (ruleMajorArmGraph arm) (senseOf ρ))
        (toOfficialSourceTree arm.tree).declarativeAddressing ∧
      Represents4b (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
        (reading input.certified.moleculeGraph (actualOrderedReferenceDescriptorMap input)
          (input.certified.topUnit center) (ruleMajorArmGraph arm) (senseOf ρ)) arm.key :=
  exists_ruleMajor_executable_reading_of_treeLike input.certified center index ρ
    (actualOrderedReferenceDescriptorMap input)
    (actualOrderedReferenceDescriptorMap_tetrahedral input) target targetRoot targetAddress
    singleBonded acyclic


/-- The actual column reads the same independent complete reading on every faithful exact
expansion of this molecular ligand, not only on the builder's chosen expansion. -/
theorem ruleMajor_reading_represents_every_faithful
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {ρ : RS} (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index (.rule4b ρ)
      (input.molecularReader descriptorMap target))
    (graph : RootedDigraph input.Atom)
    (faithful : graph.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center index))
    {W D : Nat} (width : (ruleMajorArmGraph arm).width ≤ W)
    (depth : (ruleMajorArmGraph arm).height ≤ D) :
    Represents4b W D
      (readingAt input.moleculeGraph descriptorMap (input.topUnit center) graph W D (senseOf ρ))
      arm.key := by
  have hyp := ruleMajorReadback4b_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic arm
  have represented := (ruleMajorRootArm_node_bridge4b arm hyp width depth
    (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.2
  change Represents4b W D
    (readingAt input.moleculeGraph descriptorMap (input.topUnit center)
      (ruleMajorArmGraph arm) W D (senseOf ρ)) arm.key at represented
  rw [readingAt_eq_of_faithful input.moleculeGraph descriptorMap (input.topUnit center)
    center.1 (input.canonicalLigandAtom center index) arm.faithful faithful W D (senseOf ρ)]
    at represented
  exact represented

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorReadback4b_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorArm_ordinaryCanonical_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.exists_ruleMajor_executable_reading_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.exists_ruleMajor_generated_reading_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajor_reading_represents_every_faithful
