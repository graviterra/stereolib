import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseDescriptorAtoms0To7
import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseDescriptorAtoms8To15
import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseDescriptorAtoms16To22

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

open OneCenter

/-- Kernel-checked Rules 1--3 seed assembled from independently compiled atom certificates. -/
theorem initialDescriptorState_eq_expected :
    initialRawDescriptorState normalized expanded fuel = expectedDescriptorState := by
  rw [initialState_as_filterMap, atomCount_eq]
  change ((atomRange0To7 ++ atomRange8To15 ++ atomRange16To22).filterMap initialFactAt) =
    expectedDescriptorState
  rw [List.filterMap_append, List.filterMap_append, facts0To7, facts8To15, facts16To22] ;
    rfl

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
