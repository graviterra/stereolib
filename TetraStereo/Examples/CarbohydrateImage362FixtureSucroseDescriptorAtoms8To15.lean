import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

open OneCenter

theorem fact8 : initialFactAt 8 = some (expectedFact 8 .S [0, 1, 2, 3]) := by rfl
theorem fact9 : initialFactAt 9 = some (expectedFact 9 .S [3, 0, 2, 1]) := by rfl
theorem fact10 : initialFactAt 10 = some (expectedFact 10 .S [3, 2, 0, 1]) := by rfl
theorem fact11 : initialFactAt 11 = some (expectedFact 11 .R [2, 0, 3, 1]) := by rfl
theorem fact12 : initialFactAt 12 = none := by rfl
theorem fact13 : initialFactAt 13 = none := by rfl
theorem fact14 : initialFactAt 14 = none := by rfl
theorem fact15 : initialFactAt 15 = none := by rfl

theorem facts8To15 :
    atomRange8To15.filterMap initialFactAt = expectedDescriptorState8To15 := by
  simp only [atomRange8To15, List.filterMap_cons, List.filterMap_nil,
    fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15,
    expectedDescriptorState8To15]

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
