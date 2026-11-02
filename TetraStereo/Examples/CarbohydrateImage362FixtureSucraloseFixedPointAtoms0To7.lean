import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointAtoms0To1
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointAtoms2To3
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointAtoms4To5
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointAtoms6To7

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

theorem updates0To7 :
    atomRange0To7.foldl updateExpectedAt expectedDescriptorState = expectedDescriptorState := by
  simp only [atomRange0To7, List.foldl_cons, List.foldl_nil,
    update0, update1, update2, update3, update4, update5, update6, update7]

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
