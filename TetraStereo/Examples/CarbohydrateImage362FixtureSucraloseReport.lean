import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseAnalysisBranchesCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures

open OneCenter

namespace Internal

private abbrev sucraloseExpectedAssignments : List StereoAssignment :=
  SucraloseDescriptorCertificate.expectedAssignments

private theorem sucralose_public_analyzer_assignments :
    analyzeSmiles sucralose.isomericSmiles = .ok sucraloseExpectedAssignments := by
  change Except.ok (analyzeNormalized SucraloseDescriptorCertificate.normalized) =
    Except.ok SucraloseDescriptorCertificate.expectedAssignments
  rw [SucraloseDescriptorCertificate.analyzeNormalized_eq_expected]

theorem sucralose_public_analyzer_report :
    analyzeSmilesReport sucralose.isomericSmiles = sucralose.expectedReport := by
  rw [analyzeSmilesReport, sucralose_public_analyzer_assignments]
  decide

end Internal

end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures
