import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseOccurrenceNormalizationCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucraloseDescriptorCertificate

open OneCenter

def expectedAssignment (atom : Nat) (descriptor : RS) : StereoAssignment :=
  { unit := StereoUnit.tetrahedral atom
    outcome := StereoOutcome.tetrahedral descriptor }

def expectedAssignments : List StereoAssignment :=
  [ expectedAssignment 1 .R, expectedAssignment 2 .R,
    expectedAssignment 3 .R, expectedAssignment 4 .R,
    expectedAssignment 5 .R, expectedAssignment 8 .R,
    expectedAssignment 9 .S, expectedAssignment 10 .S,
    expectedAssignment 11 .S ]

theorem tetrahedralAssignments_eq_expected :
    tetrahedralAssignments normalized expanded expectedDescriptorState fuel =
      expectedAssignments := by
  rfl

end SucraloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
