import TetraStereo.Examples.CarbohydrateImage362FixtureCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures

theorem fixture_image_paths_are_pairwise_distinct :
    (all.map ExternalIdentityFixture.sourceImagePath).Nodup := by
  decide

end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures
