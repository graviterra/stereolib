import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleRoot
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The concrete report covers every detected centre of a nonrigid cyclic molecule. Its
lowercase outputs agree with the independently proved physical mirror-pair counts. The exact
letter here is an execution result; this example does not replace a general chemical refinement
theorem or supply an independent absolute-priority proof for arbitrary rings. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleReport

open LocalizedChemicalRingCyclicExampleInput LocalizedChemicalRingCyclicExamplePhysical
open LocalizedChemicalRingCyclicExampleRoot
open RootedTetrahedralBranchSymmetry

theorem reported_inventory :
    (LocalizedPhysicalMarkedDistantEvaluator.assign mol ops geom).map Prod.fst = [0, 2, 4] := by
  rw [whole_report]
  rfl

theorem every_detected_center (center : physical.Center) :
    (center.1.val, .pseudoasymmetric .s) ∈ LocalizedPhysicalMarkedDistantEvaluator.assign mol ops geom ∧
    physicalEnantiomorphicPairCount physical cfg center = 1 := by
  refine ⟨?_, mirror_pair_count center⟩
  have member : center.1 ∈ certified.tetrahedralCenterSet := center.2
  rw [detected_inventory] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rw [whole_report]
  have atomCount : certified.certified.input.molecule.atomCount = 9 := rfl
  rcases member with h | h | h <;> simp [h, atomCount]

theorem every_center_nonrigid (center : physical.Center) :
    ¬ ConstitutionallyRigid physical center ∧ physical.PairwiseProperDistinguishable cfg center ∧
    (center.1.val, .pseudoasymmetric .s) ∈ LocalizedPhysicalMarkedDistantEvaluator.assign mol ops geom ∧
    physicalEnantiomorphicPairCount physical cfg center = 1 :=
  ⟨no_constitutionally_rigid_center center, proper_distinct center, every_detected_center center⟩

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleReport.reported_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleReport.every_detected_center
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleReport.every_center_nonrigid
