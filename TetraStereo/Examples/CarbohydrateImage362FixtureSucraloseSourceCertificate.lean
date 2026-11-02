import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

open OneCenter

theorem rawAnnotatedCenters_eq_expectedAtoms :
    rawAnnotatedCenters normalized = [1, 2, 3, 4, 5, 8, 9, 10, 11] := by
  rfl

theorem unresolvedAnnotatedCenters_eq_nil :
    (rawAnnotatedCenters normalized).filter
        (fun center => (expectedDescriptorState.factAt? center).isNone) = [] := by
  rw [rawAnnotatedCenters_eq_expectedAtoms]
  rfl

theorem stabilizationGate_eq_expected :
    stabilizedRawDescriptorState? normalized expanded 100 fuel
        (normalized.parsed.atomCount + 1) expectedDescriptorState =
      some expectedDescriptorState := by
  rw [atomCount_eq]
  simp [stabilizedRawDescriptorState?, discoverRawDescriptorsFromCertified,
    descriptorDiscoveryPass_eq_expected]

theorem solveAuxiliaryDescriptorDependencies_eq_expected :
    solveAuxiliaryDescriptorDependencies normalized expanded 100 fuel expectedDescriptorState =
      expectedDescriptorState := by
  unfold solveAuxiliaryDescriptorDependencies
  rw [unresolvedAnnotatedCenters_eq_nil]
  rfl

theorem solveExactAuxiliaryDescriptorDependencies_eq_expected :
    solveExactAuxiliaryDescriptorDependencies normalized expanded 100 fuel
        expectedDescriptorState = expectedDescriptorState := by
  unfold solveExactAuxiliaryDescriptorDependencies
  rw [unresolvedAnnotatedCenters_eq_nil]
  rfl

theorem finishRawDescriptorSource_eq_expected :
    finishRawDescriptorSource normalized expanded fuel expectedDescriptorState =
      expectedDescriptorState := by
  unfold finishRawDescriptorSource
  rw [unresolvedAnnotatedCenters_eq_nil]
  simp [solveExactAuxiliaryDescriptorDependencies_eq_expected]

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
