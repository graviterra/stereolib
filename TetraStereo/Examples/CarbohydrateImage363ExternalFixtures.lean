import TetraStereo.Examples.CarbohydrateImage363ExternalFixturesCore
import TetraStereo.Examples.CarbohydrateImage363FixtureCount
import TetraStereo.Examples.CarbohydrateImage363FixtureParserNormalization
import TetraStereo.Examples.CarbohydrateImage363FixtureAtomCounts
import TetraStereo.Examples.CarbohydrateImage363FixtureAuthorityBridge
import TetraStereo.Examples.CarbohydrateImage363FixtureBetaMaltoseReport
import TetraStereo.Examples.CarbohydrateImage363FixtureAlphaLactoseReport
import TetraStereo.Examples.CarbohydrateImage363FixtureNAcetyllactosamineReport
import TetraStereo.Examples.CarbohydrateImage363FixtureImageCatalog
import TetraStereo.Examples.CarbohydrateImage363FixturePathDistinctness

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage363ExternalFixtures

open OneCenter

abbrev nAcetyllactosamineExpectedAssignments : List StereoAssignment :=
  Internal.NAcetyllactosamineDescriptorCertificate.expectedAssignments

theorem n_acetyllactosamine_public_analyzer_assignments :
    analyzeSmiles nAcetyllactosamine.isomericSmiles =
      .ok nAcetyllactosamineExpectedAssignments :=
  Internal.n_acetyllactosamine_public_analyzer_assignments

@[simp] theorem public_analyzer_assigns_every_recorded_fixture_center :
    all.all fun fixture => analyzeSmilesReport fixture.isomericSmiles = fixture.expectedReport := by
  simp [all, Internal.beta_maltose_public_analyzer_report,
    Internal.alpha_lactose_public_analyzer_report,
    Internal.n_acetyllactosamine_public_analyzer_report]

/-- Atom 3 is the acetamide nitrogen in the exact PubChem SMILES. The exact public assignment
list contains no tetrahedral unit rooted there. -/
theorem lacNAc_does_not_report_amide_nitrogen :
    ∃ assignments,
      analyzeSmiles nAcetyllactosamine.isomericSmiles = .ok assignments ∧
        assignments.all (fun assignment => assignment.unit != StereoUnit.tetrahedral 3) = true := by
  refine ⟨nAcetyllactosamineExpectedAssignments,
    n_acetyllactosamine_public_analyzer_assignments, ?_⟩
  decide

end TetraStereo.Examples.CarbohydrateImage363ExternalFixtures
