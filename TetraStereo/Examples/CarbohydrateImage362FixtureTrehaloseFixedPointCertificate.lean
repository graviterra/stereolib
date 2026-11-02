import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms0To7
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms8To15
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseFixedPointAtoms16To22

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

open OneCenter

/-- The exact Rules 1--3 Trehalose seed is a fixed point of the production discovery pass. -/
theorem descriptorDiscoveryPass_eq_expected :
    runRawDescriptorDiscoveryPass normalized expanded 100 fuel expectedDescriptorState =
      expectedDescriptorState := by
  rw [runRawDescriptorDiscoveryPass_eq_schedule, atomRange_partition]
  unfold runRawDescriptorDiscoverySchedule
  change
    (atomRange0To7 ++ atomRange8To15 ++ atomRange16To22).foldl updateExpectedAt
        expectedDescriptorState = expectedDescriptorState
  rw [List.foldl_append, List.foldl_append, updates0To7, updates8To15, updates16To22]

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
