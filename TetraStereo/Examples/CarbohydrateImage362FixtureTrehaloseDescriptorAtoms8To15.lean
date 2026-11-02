import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms8To9
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms10To11
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms12To13
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms14To15

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

open OneCenter

theorem facts8To15 :
    atomRange8To15.filterMap initialFactAt = expectedDescriptorState8To15 := by
  simp only [atomRange8To15, List.filterMap_cons, List.filterMap_nil,
    fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15,
    expectedDescriptorState8To15]

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
