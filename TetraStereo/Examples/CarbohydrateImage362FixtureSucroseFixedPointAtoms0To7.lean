import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseFixedPointCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

theorem update0 : updateExpectedAt expectedDescriptorState 0 = expectedDescriptorState := by rfl
theorem update1 : updateExpectedAt expectedDescriptorState 1 = expectedDescriptorState := by rfl
theorem update2 : updateExpectedAt expectedDescriptorState 2 = expectedDescriptorState := by rfl
theorem update3 : updateExpectedAt expectedDescriptorState 3 = expectedDescriptorState := by rfl
theorem update4 : updateExpectedAt expectedDescriptorState 4 = expectedDescriptorState := by rfl
theorem update5 : updateExpectedAt expectedDescriptorState 5 = expectedDescriptorState := by rfl
theorem update6 : updateExpectedAt expectedDescriptorState 6 = expectedDescriptorState := by rfl
theorem update7 : updateExpectedAt expectedDescriptorState 7 = expectedDescriptorState := by rfl

theorem updates0To7 :
    atomRange0To7.foldl updateExpectedAt expectedDescriptorState = expectedDescriptorState := by
  simp only [atomRange0To7, List.foldl_cons, List.foldl_nil,
    update0, update1, update2, update3, update4, update5, update6, update7]

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
