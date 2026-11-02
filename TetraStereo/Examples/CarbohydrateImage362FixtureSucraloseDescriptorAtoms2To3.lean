import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

theorem fact2 : initialFactAt 2 = some (expectedFact 2 .R [3, 0, 2, 1]) := by rfl
theorem fact3 : initialFactAt 3 = some (expectedFact 3 .R [3, 0, 2, 1]) := by rfl

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
