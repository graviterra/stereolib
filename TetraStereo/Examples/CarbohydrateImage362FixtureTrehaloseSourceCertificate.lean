import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

open OneCenter

/-- The production parser identifies exactly the ten Trehalose tetrahedral centers. -/
theorem rawAnnotatedCenters_eq_expectedAtoms :
    rawAnnotatedCenters normalized = [1, 2, 3, 4, 5, 8, 9, 10, 11, 12] := by
  rfl

/-- Every annotated Trehalose center already has its descriptor-independent seed fact. -/
theorem unresolvedAnnotatedCenters_eq_nil :
    (rawAnnotatedCenters normalized).filter
        (fun center => (expectedDescriptorState.factAt? center).isNone) = [] := by
  rw [rawAnnotatedCenters_eq_expectedAtoms]
  rfl

/-- One proved fixed-point pass is enough for the bounded stabilization gate to accept the seed. -/
theorem stabilizationGate_eq_expected :
    stabilizedRawDescriptorState? normalized expanded 100 fuel
        (normalized.parsed.atomCount + 1) expectedDescriptorState =
      some expectedDescriptorState := by
  rw [atomCount_eq]
  simp [stabilizedRawDescriptorState?, discoverRawDescriptorsFromCertified,
    descriptorDiscoveryPass_eq_expected]

/-- With no unresolved annotated centers, auxiliary discovery preserves the proved fixed point. -/
theorem solveAuxiliaryDescriptorDependencies_eq_expected :
    solveAuxiliaryDescriptorDependencies normalized expanded 100 fuel expectedDescriptorState =
      expectedDescriptorState := by
  unfold solveAuxiliaryDescriptorDependencies
  rw [unresolvedAnnotatedCenters_eq_nil]
  rfl

/-- The bounded exact auxiliary solver also has no unresolved Trehalose work to perform. -/
theorem solveExactAuxiliaryDescriptorDependencies_eq_expected :
    solveExactAuxiliaryDescriptorDependencies normalized expanded 100 fuel
        expectedDescriptorState = expectedDescriptorState := by
  unfold solveExactAuxiliaryDescriptorDependencies
  rw [unresolvedAnnotatedCenters_eq_nil]
  rfl

/-- The final exact-source stage therefore preserves the same certified state. -/
theorem finishRawDescriptorSource_eq_expected :
    finishRawDescriptorSource normalized expanded fuel expectedDescriptorState =
      expectedDescriptorState := by
  unfold finishRawDescriptorSource
  rw [unresolvedAnnotatedCenters_eq_nil]
  simp [solveExactAuxiliaryDescriptorDependencies_eq_expected]

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
