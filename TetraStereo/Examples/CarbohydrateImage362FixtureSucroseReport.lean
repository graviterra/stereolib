import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseAnalysisBranchesCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures

open OneCenter

namespace Internal

private abbrev sucroseExpectedAssignments : List StereoAssignment :=
  SucroseDescriptorCertificate.expectedAssignments

private theorem sucrose_public_analyzer_assignments :
    analyzeSmiles sucrose.isomericSmiles = .ok sucroseExpectedAssignments := by
  change Except.ok (analyzeNormalized SucroseDescriptorCertificate.normalized) =
    Except.ok SucroseDescriptorCertificate.expectedAssignments
  rw [SucroseDescriptorCertificate.analyzeNormalized_eq_expected]

theorem sucrose_public_analyzer_report :
    analyzeSmilesReport sucrose.isomericSmiles = sucrose.expectedReport := by
  rw [analyzeSmilesReport, sucrose_public_analyzer_assignments]
  decide

end Internal

end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures
