import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

open OneCenter

theorem fact0 : initialFactAt 0 = none := by rfl
theorem fact1 : initialFactAt 1 = some (expectedFact 1 .R [2, 3, 0, 1]) := by rfl
theorem fact2 : initialFactAt 2 = some (expectedFact 2 .S [3, 0, 2, 1]) := by rfl
theorem fact3 : initialFactAt 3 = some (expectedFact 3 .S [3, 2, 0, 1]) := by rfl
theorem fact4 : initialFactAt 4 = some (expectedFact 4 .R [3, 2, 0, 1]) := by rfl
theorem fact5 : initialFactAt 5 = some (expectedFact 5 .R [3, 2, 0, 1]) := by rfl
theorem fact6 : initialFactAt 6 = none := by rfl
theorem fact7 : initialFactAt 7 = none := by rfl

theorem facts0To7 :
    atomRange0To7.filterMap initialFactAt = expectedDescriptorState0To7 := by
  simp only [atomRange0To7, List.filterMap_cons, List.filterMap_nil,
    fact0, fact1, fact2, fact3, fact4, fact5, fact6, fact7,
    expectedDescriptorState0To7]

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
