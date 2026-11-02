import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseSelectedSourceCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

open OneCenter

/-- Every fact in the exact Sucrose source is uppercase, so the lowercase two-anchor Rule-6
carrier transport has no applicable branch and preserves all nine facts simultaneously. -/
theorem occurrenceFrameNormalization_eq_expected :
    normalizeTwoCyclicRule6AnchorCarrier expanded fuel expectedDescriptorState =
      expectedDescriptorState := by
  rfl

/-- The complete production descriptor discovery, including occurrence-frame normalization,
returns exactly the nine certified Sucrose descriptors. -/
theorem discoverRawDescriptors_eq_expected :
    discoverRawDescriptors normalized expanded fuel = expectedDescriptorState := by
  unfold discoverRawDescriptors
  rw [discoverRawDescriptorSource_eq_expected]
  exact occurrenceFrameNormalization_eq_expected

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
