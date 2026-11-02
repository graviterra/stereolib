import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

theorem fact8 : initialFactAt 8 = some (expectedFact 8 .R [0, 2, 3, 1]) := by rfl
theorem fact9 : initialFactAt 9 = some (expectedFact 9 .R [3, 0, 2, 1]) := by rfl

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
