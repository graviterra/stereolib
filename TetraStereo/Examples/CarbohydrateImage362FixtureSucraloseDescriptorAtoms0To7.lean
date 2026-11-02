import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms0To1
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms2To3
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms4To5
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms6To7

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

theorem facts0To7 :
    atomRange0To7.filterMap initialFactAt = expectedDescriptorState0To7 := by
  simp only [atomRange0To7, List.filterMap_cons, List.filterMap_nil,
    fact0, fact1, fact2, fact3, fact4, fact5, fact6, fact7,
    expectedDescriptorState0To7]

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
