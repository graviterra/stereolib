import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

theorem fact12 : initialFactAt 12 = some (expectedFact 12 .R [2, 0, 3, 1]) := by rfl
theorem fact13 : initialFactAt 13 = none := by rfl

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
