import TetraStereo.Examples.CarbohydrateImage362FixtureCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures

open OneCenter

@[simp] theorem all_fixtures_pass_certified_parser_normalization :
    all.all fun fixture =>
      (parseAndNormalizeOpenSMILESCertified fixture.isomericSmiles).isOk := by
  decide

end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures
