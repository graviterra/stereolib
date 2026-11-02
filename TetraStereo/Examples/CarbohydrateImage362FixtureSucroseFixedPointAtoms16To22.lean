import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseFixedPointCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

theorem update16 : updateExpectedAt expectedDescriptorState 16 = expectedDescriptorState := by rfl
theorem update17 : updateExpectedAt expectedDescriptorState 17 = expectedDescriptorState := by rfl
theorem update18 : updateExpectedAt expectedDescriptorState 18 = expectedDescriptorState := by rfl
theorem update19 : updateExpectedAt expectedDescriptorState 19 = expectedDescriptorState := by rfl
theorem update20 : updateExpectedAt expectedDescriptorState 20 = expectedDescriptorState := by rfl
theorem update21 : updateExpectedAt expectedDescriptorState 21 = expectedDescriptorState := by rfl
theorem update22 : updateExpectedAt expectedDescriptorState 22 = expectedDescriptorState := by rfl

theorem updates16To22 :
    atomRange16To22.foldl updateExpectedAt expectedDescriptorState = expectedDescriptorState := by
  simp only [atomRange16To22, List.foldl_cons, List.foldl_nil,
    update16, update17, update18, update19, update20, update21, update22]

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
