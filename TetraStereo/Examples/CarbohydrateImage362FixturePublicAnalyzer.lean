import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseReport
import TetraStereo.Examples.CarbohydrateImage362FixtureSucraloseReport
import TetraStereo.Examples.CarbohydrateImage362FixtureTrehaloseReport

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures

open OneCenter

@[simp] theorem public_analyzer_assigns_every_recorded_fixture_center :
    all.all fun fixture => analyzeSmilesReport fixture.isomericSmiles = fixture.expectedReport := by
  simp [all, Internal.trehalose_public_analyzer_report,
    Internal.sucrose_public_analyzer_report, Internal.sucralose_public_analyzer_report]

end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures
