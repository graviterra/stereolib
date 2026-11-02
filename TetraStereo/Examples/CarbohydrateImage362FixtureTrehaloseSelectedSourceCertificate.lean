import TetraStereo.Examples.CarbohydrateImage362FixtureSelectorCertificateSupport
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseSourceCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

open OneCenter

/-- The certified constructive selector returns the already proved Trehalose fixed point. -/
theorem certifiedConstructiveRawDescriptorSource_val_eq_expected :
    (certifiedConstructiveRawDescriptorSource normalized expanded fuel
      expectedDescriptorState).val = expectedDescriptorState :=
  DescriptorCertificateSupport.certifiedConstructiveRawDescriptorSource_val_eq_of_noop
    normalized expanded fuel expectedDescriptorState stabilizationGate_eq_expected
      solveAuxiliaryDescriptorDependencies_eq_expected finishRawDescriptorSource_eq_expected

/-- The Rules 1--3 Trehalose seed is nonempty, so production takes the constructive path. -/
theorem expectedDescriptorState_isEmpty_eq_false : expectedDescriptorState.isEmpty = false := by
  rfl

/-- The provenance-carrying production selector returns the exact certified Trehalose state. -/
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

/-- The public pre-normalization discovery source is the exact certified Trehalose state. -/
theorem discoverRawDescriptorSource_eq_expected :
    discoverRawDescriptorSource normalized expanded fuel = expectedDescriptorState := by
  unfold discoverRawDescriptorSource
  exact certifiedRawDescriptorSource_val_eq_expected

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
