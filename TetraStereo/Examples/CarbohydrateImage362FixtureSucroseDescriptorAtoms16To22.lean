import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseDescriptorCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

theorem fact16 : initialFactAt 16 = none := by rfl
theorem fact17 : initialFactAt 17 = none := by rfl
theorem fact18 : initialFactAt 18 = none := by rfl
theorem fact19 : initialFactAt 19 = none := by rfl
theorem fact20 : initialFactAt 20 = none := by rfl
theorem fact21 : initialFactAt 21 = none := by rfl
theorem fact22 : initialFactAt 22 = none := by rfl

theorem facts16To22 :
    atomRange16To22.filterMap initialFactAt = expectedDescriptorState16To22 := by
  simp only [atomRange16To22, List.filterMap_cons, List.filterMap_nil,
    fact16, fact17, fact18, fact19, fact20, fact21, fact22,
    expectedDescriptorState16To22]

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
