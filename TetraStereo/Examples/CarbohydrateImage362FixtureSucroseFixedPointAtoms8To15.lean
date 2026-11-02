import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseFixedPointCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

theorem update8 : updateExpectedAt expectedDescriptorState 8 = expectedDescriptorState := by rfl
theorem update9 : updateExpectedAt expectedDescriptorState 9 = expectedDescriptorState := by rfl
theorem update10 : updateExpectedAt expectedDescriptorState 10 = expectedDescriptorState := by rfl
theorem update11 : updateExpectedAt expectedDescriptorState 11 = expectedDescriptorState := by rfl
theorem update12 : updateExpectedAt expectedDescriptorState 12 = expectedDescriptorState := by rfl
theorem update13 : updateExpectedAt expectedDescriptorState 13 = expectedDescriptorState := by rfl
theorem update14 : updateExpectedAt expectedDescriptorState 14 = expectedDescriptorState := by rfl
theorem update15 : updateExpectedAt expectedDescriptorState 15 = expectedDescriptorState := by rfl

theorem updates8To15 :
    atomRange8To15.foldl updateExpectedAt expectedDescriptorState = expectedDescriptorState := by
  simp only [atomRange8To15, List.foldl_cons, List.foldl_nil,
    update8, update9, update10, update11, update12, update13, update14, update15]

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
