import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms16To17
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms18To19
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms20To21
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtom22

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

theorem facts16To22 :
    atomRange16To22.filterMap initialFactAt = expectedDescriptorState16To22 := by
  simp only [atomRange16To22, List.filterMap_cons, List.filterMap_nil,
    fact16, fact17, fact18, fact19, fact20, fact21, fact22,
    expectedDescriptorState16To22]

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
