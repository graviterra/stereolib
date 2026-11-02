import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

theorem fact2 : initialFactAt 2 = some (expectedFact 2 .S [3, 0, 2, 1]) := by rfl
theorem fact3 : initialFactAt 3 = some (expectedFact 3 .S [3, 2, 0, 1]) := by rfl

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
