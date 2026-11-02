import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms0To1
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms2To3
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms4To5
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseDescriptorAtoms6To7

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

open OneCenter

theorem facts0To7 :
    atomRange0To7.filterMap initialFactAt = expectedDescriptorState0To7 := by
  simp only [atomRange0To7, List.filterMap_cons, List.filterMap_nil,
    fact0, fact1, fact2, fact3, fact4, fact5, fact6, fact7,
    expectedDescriptorState0To7]

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
