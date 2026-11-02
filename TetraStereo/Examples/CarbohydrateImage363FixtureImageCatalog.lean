import TetraStereo.Examples.CarbohydrateImage363ExternalFixturesCore
import TetraStereo.OneCenter.CarbohydrateImageArtifactAudit

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage363ExternalFixtures

open OneCenter

@[simp] theorem all_fixture_images_are_in_frozen_iupac_artifact_catalog :
    all.all fun fixture =>
      Carbohydrate1996ImageAudit.imageArtifacts.any fun artifact =>
        artifact.relativePath = fixture.sourceImagePath := by
  decide

end TetraStereo.Examples.CarbohydrateImage363ExternalFixtures
