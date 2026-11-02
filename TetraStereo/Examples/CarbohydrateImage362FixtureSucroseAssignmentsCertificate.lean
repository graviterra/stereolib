import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseOccurrenceNormalizationCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

open OneCenter

def expectedAssignment (atom : Nat) (descriptor : RS) : StereoAssignment :=
  { unit := StereoUnit.tetrahedral atom
    outcome := StereoOutcome.tetrahedral descriptor }

def expectedAssignments : List StereoAssignment :=
  [ expectedAssignment 1 .R, expectedAssignment 2 .S,
    expectedAssignment 3 .S, expectedAssignment 4 .R,
    expectedAssignment 5 .R, expectedAssignment 8 .S,
    expectedAssignment 9 .S, expectedAssignment 10 .S,
    expectedAssignment 11 .R ]

/-- The complete ordinary-tetrahedral analyzer emits exactly the nine certified Sucrose
assignments from the production descriptor state. -/
theorem tetrahedralAssignments_eq_expected :
    tetrahedralAssignments normalized expanded expectedDescriptorState fuel =
      expectedAssignments := by
  rfl

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
