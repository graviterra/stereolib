import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseAnalysisBranchesCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures

open OneCenter

namespace Internal

private abbrev trehaloseExpectedAssignments : List StereoAssignment :=
  TrehaloseDescriptorCertificate.expectedAssignments

private theorem trehalose_public_analyzer_assignments :
    analyzeSmiles trehalose.isomericSmiles = .ok trehaloseExpectedAssignments := by
  change Except.ok (analyzeNormalized TrehaloseDescriptorCertificate.normalized) =
    Except.ok TrehaloseDescriptorCertificate.expectedAssignments
  rw [TrehaloseDescriptorCertificate.analyzeNormalized_eq_expected]

theorem trehalose_public_analyzer_report :
    analyzeSmilesReport trehalose.isomericSmiles = trehalose.expectedReport := by
  rw [analyzeSmilesReport, trehalose_public_analyzer_assignments]
  decide

end Internal

end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures
