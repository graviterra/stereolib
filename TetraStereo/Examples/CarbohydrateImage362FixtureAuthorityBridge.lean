import TetraStereo.Examples.CarbohydrateImage362FixtureCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures

@[simp] theorem all_fixtures_cross_format_neutral_authority_bridge :
    all.all fun fixture => (authoritativeInput? fixture).isSome := by
  decide

end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures
