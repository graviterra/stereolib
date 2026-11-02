import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms8To9
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms10To11
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms12To13
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms14To15

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

theorem updates8To15 :
    atomRange8To15.foldl updateExpectedAt expectedDescriptorState = expectedDescriptorState := by
  simp only [atomRange8To15, List.foldl_cons, List.foldl_nil,
    update8, update9, update10, update11, update12, update13, update14, update15]

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
