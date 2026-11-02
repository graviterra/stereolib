import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

theorem fact8 : initialFactAt 8 = some (expectedFact 8 .R [0, 1, 3, 2]) := by rfl
theorem fact9 : initialFactAt 9 = some (expectedFact 9 .S [3, 0, 2, 1]) := by rfl

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
