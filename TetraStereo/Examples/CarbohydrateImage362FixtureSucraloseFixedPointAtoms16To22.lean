import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointAtoms16To17
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointAtoms18To19
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointAtoms20To21
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseFixedPointAtom22

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

theorem updates16To22 :
    atomRange16To22.foldl updateExpectedAt expectedDescriptorState = expectedDescriptorState := by
  simp only [atomRange16To22, List.foldl_cons, List.foldl_nil,
    update16, update17, update18, update19, update20, update21, update22]

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
