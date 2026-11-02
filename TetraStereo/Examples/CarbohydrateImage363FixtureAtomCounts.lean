import TetraStereo.Examples.CarbohydrateImage363ExternalFixturesCore

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage363ExternalFixtures

@[simp] theorem all_fixtures_have_expected_heavy_and_total_atom_counts :
    all.all fun fixture =>
      parsedHeavyAtomCount fixture = fixture.parsedHeavyAtoms &&
        expandedAtomCount fixture = fixture.totalAtoms := by
  decide

end TetraStereo.Examples.CarbohydrateImage363ExternalFixtures
