import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms8To9
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms10To11
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms12To13
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms14To15

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

theorem facts8To15 :
    atomRange8To15.filterMap initialFactAt = expectedDescriptorState8To15 := by
  simp only [atomRange8To15, List.filterMap_cons, List.filterMap_nil,
    fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15,
    expectedDescriptorState8To15]

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
