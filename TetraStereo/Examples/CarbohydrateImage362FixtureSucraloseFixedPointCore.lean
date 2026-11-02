import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseDescriptorCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

open OneCenter

def updateExpectedAt (state : RawDescriptorState) (idx : Nat) : RawDescriptorState :=
  updateRawDescriptorAt normalized expanded 100 fuel state idx

theorem atomRange_partition :
    List.range normalized.parsed.atomCount =
      atomRange0To7 ++ atomRange8To15 ++ atomRange16To22 := by
  rfl

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
