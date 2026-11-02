import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

theorem fact10 : initialFactAt 10 = some (expectedFact 10 .S [3, 2, 0, 1]) := by rfl
theorem fact11 : initialFactAt 11 = some (expectedFact 11 .S [2, 3, 0, 1]) := by rfl

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
