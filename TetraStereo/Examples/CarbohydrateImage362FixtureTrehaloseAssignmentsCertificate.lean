import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseOccurrenceNormalizationCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace TrehaloseDescriptorCertificate

open OneCenter

def expectedAssignment (atom : Nat) (descriptor : RS) : StereoAssignment :=
  { unit := StereoUnit.tetrahedral atom
    outcome := StereoOutcome.tetrahedral descriptor }

def expectedAssignments : List StereoAssignment :=
  [ expectedAssignment 1 .R, expectedAssignment 2 .S,
    expectedAssignment 3 .S, expectedAssignment 4 .R,
    expectedAssignment 5 .R, expectedAssignment 8 .R,
    expectedAssignment 9 .R, expectedAssignment 10 .S,
    expectedAssignment 11 .S, expectedAssignment 12 .R ]

/-- The ordinary-tetrahedral analyzer emits exactly the ten certified Trehalose assignments. -/
theorem tetrahedralAssignments_eq_expected :
    tetrahedralAssignments normalized expanded expectedDescriptorState fuel =
      expectedAssignments := by
  rfl

end TrehaloseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
