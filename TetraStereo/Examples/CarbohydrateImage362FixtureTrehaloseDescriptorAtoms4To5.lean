import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

theorem fact4 : initialFactAt 4 = some (expectedFact 4 .R [3, 2, 0, 1]) := by rfl
theorem fact5 : initialFactAt 5 = some (expectedFact 5 .R [3, 2, 0, 1]) := by rfl

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
