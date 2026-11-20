import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPriorTie
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Physical mirror transport derives the actual prior tie of the two oxygen arms.
The raw state is first identified with its recursively generated auxiliary facts. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingDoubleC3Domain (cfg calibrated)
open LocalizedChemicalRingJointPreparedDoubleC3Pseudo
  (detectedExchange detected_exchange_negative)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip (exchange_coe)
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootData
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts (twoFacts actual_root_facts)
open LocalizedChemicalRingInheritedRefusalCases (referenceAt)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedRetainedStateReader (rawStateDescriptorMap_tetrahedral)
open LocalizedMarkedRetainedOrdinaryRanking (rawStateKeys)
open RootedTetrahedralBranchSymmetry (MirrorTransport)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign_eq_iff)

noncomputable section

theorem root_address : data.target.1.address = [] := by
  rw [data_target]
  rfl

theorem root_state : sideState input mol root (inputGeometry input) [] false = twoFacts :=
  actual_root_facts

theorem oxygen_mirror_transport : MirrorTransport input.detectedMultiCenterMolecule cfg center
    (data.ligandOf 2) (data.ligandOf 3) := by
  have fixed : input.detectedMultiCenterMolecule.centerPerm detectedExchange center = center := by
    apply Subtype.ext
    exact LocalizedChemicalRingJointPreparedDoubleC3Pseudo.detected_exchange_fixed
  refine ⟨detectedExchange, fixed, ?_, ?_⟩
  · apply input.detectedMultiCenterMolecule.ligandAtomAt_injective center
    have moved := input.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt
      detectedExchange center (data.ligandOf 2)
    rw [fixed] at moved
    apply moved.trans
    change (detectedExchange : Equiv.Perm input.Atom)
        (referenceAt input mol center root data 2) = referenceAt input mol center root data 3
    rw [reference_slot, reference_slot, exchange_coe]
    rfl
  · intro other _
    exact (relativeSign_eq_iff input.detectedMultiCenterMolecule cfg detectedExchange other (-1)).mp
      (detected_exchange_negative other)

theorem retained_prior_tie :
    (ofLex (rawStateKeys input single_bonded twoFacts data.target data.real unit rfl 2)).1 =
      (ofLex (rawStateKeys input single_bonded twoFacts data.target data.real unit rfl 3)).1 := by
  have actual := LocalizedChemicalRingJointPreparedRootPhysicalPriorTie.priorTie_of_mirrorTransport
    input mol (structure_agreement true) admissible supported single_bonded cfg calibrated center
    data root_address 2 3 oxygen_mirror_transport
  change (ofLex (rawStateKeys input single_bonded
      (sideState input mol root (inputGeometry input) [] false) data.target data.real unit rfl 2)).1 =
    (ofLex (rawStateKeys input single_bonded
      (sideState input mol root (inputGeometry input) [] false) data.target data.real unit rfl 3)).1 at actual
  simpa only [root_state] using actual

theorem compound_prior_tie :
    input.compareLocalizedRerootCompoundRule4bcKeys
      ((execution twoFacts).compounds 2).prior ((execution twoFacts).compounds 3).prior = .eq := by
  have comparison := (execution twoFacts).priorComparison
    (rawStateDescriptorMap_tetrahedral input twoFacts) single_bonded unit rfl 2 3
  exact comparison.trans ((completeLigandPriorKey_compare_eq_iff _ _).mpr retained_prior_tie)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie.root_address
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie.root_state
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie.oxygen_mirror_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie.retained_prior_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie.compound_prior_tie
