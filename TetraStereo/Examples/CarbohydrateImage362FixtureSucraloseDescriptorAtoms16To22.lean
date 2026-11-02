import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms16To17
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms18To19
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtoms20To21
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorAtom22

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

theorem facts16To22 :
    atomRange16To22.filterMap initialFactAt = expectedDescriptorState16To22 := by
  simp only [atomRange16To22, List.filterMap_cons, List.filterMap_nil,
    fact16, fact17, fact18, fact19, fact20, fact21, fact22,
    expectedDescriptorState16To22]

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
