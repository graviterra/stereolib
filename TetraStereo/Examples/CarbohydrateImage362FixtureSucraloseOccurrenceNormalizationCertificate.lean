import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseSelectedSourceCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

open OneCenter

theorem occurrenceFrameNormalization_eq_expected :
    normalizeTwoCyclicRule6AnchorCarrier expanded fuel expectedDescriptorState =
      expectedDescriptorState := by
  rfl

theorem discoverRawDescriptors_eq_expected :
    discoverRawDescriptors normalized expanded fuel = expectedDescriptorState := by
  unfold discoverRawDescriptors
  rw [discoverRawDescriptorSource_eq_expected]
  exact occurrenceFrameNormalization_eq_expected

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
