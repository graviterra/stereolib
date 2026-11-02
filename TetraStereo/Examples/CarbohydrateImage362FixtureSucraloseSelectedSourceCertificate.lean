import TetraStereo.Examples.CarbohydrateImage362FixtureSelectorCertificateSupport
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseSourceCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

open OneCenter

theorem certifiedConstructiveRawDescriptorSource_val_eq_expected :
    (certifiedConstructiveRawDescriptorSource normalized expanded fuel
      expectedDescriptorState).val = expectedDescriptorState :=
  DescriptorCertificateSupport.certifiedConstructiveRawDescriptorSource_val_eq_of_noop
    normalized expanded fuel expectedDescriptorState stabilizationGate_eq_expected
    solveAuxiliaryDescriptorDependencies_eq_expected finishRawDescriptorSource_eq_expected

theorem expectedDescriptorState_isEmpty_eq_false : expectedDescriptorState.isEmpty = false := by
  rfl

theorem certifiedRawDescriptorSource_val_eq_expected :
    (certifiedRawDescriptorSource normalized expanded fuel).val = expectedDescriptorState := by
  calc
    (certifiedRawDescriptorSource normalized expanded fuel).val =
        (certifiedConstructiveRawDescriptorSource normalized expanded fuel
          expectedDescriptorState).val :=
      DescriptorCertificateSupport.certifiedRawDescriptorSource_val_eq_constructive_of_initial_eq
        normalized expanded fuel expectedDescriptorState initialDescriptorState_eq_expected
          expectedDescriptorState_isEmpty_eq_false
    _ = expectedDescriptorState := certifiedConstructiveRawDescriptorSource_val_eq_expected

theorem discoverRawDescriptorSource_eq_expected :
    discoverRawDescriptorSource normalized expanded fuel = expectedDescriptorState := by
  unfold discoverRawDescriptorSource
  exact certifiedRawDescriptorSource_val_eq_expected

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
