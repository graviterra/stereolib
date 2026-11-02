import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms16To17
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms18To19
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms20To21
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtom22

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

theorem updates16To22 :
    atomRange16To22.foldl updateExpectedAt expectedDescriptorState = expectedDescriptorState := by
  simp only [atomRange16To22, List.foldl_cons, List.foldl_nil,
    update16, update17, update18, update19, update20, update21, update22]

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
