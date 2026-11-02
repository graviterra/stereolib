import TetraStereo.Examples.Rule5EssentialInputStage07FullAdjacency

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem fullTargetFact_computed :
    target.sourceNode?.bind
      (occurrenceFact? molecule fuel [sourceFact, otherFact]) = some fullTargetFact := by
  have assembled : occurrenceFact? fixtureMolecule fuel [sourceFact, otherFact]
      (canonicalCenterRoot 1) =
      fixtureFinish (canonicalCenterRoot 1) .anticlockwise [1, 0, 2, 3]
        fixturePseudoDecisions := by
    exact fixture_fact_of_observations fixtureMolecule [sourceFact, otherFact] fuel
      (canonicalCenterRoot 1) (fixtureProfile (canonicalCenterRoot 1))
      (fixtureCarbon .anticlockwise) .anticlockwise fixtureCenterRoots fixtureFullSorted 1
      [1, 0, 2, 3] fixturePseudoDecisions
      fixture_center_profile (by decide +kernel) rfl fixture_center_roots
      fixture_full_sort (by decide +kernel) fixture_full_adjacency
  have finished :
      fixtureFinish (canonicalCenterRoot 1) .anticlockwise [1, 0, 2, 3]
        fixturePseudoDecisions = some fullTargetFact := by
    decide +kernel
  rw [target, finalOccurrence_source, root_center_atom, Option.bind_some, molecule_eq_fixture]
  exact assembled.trans finished

end TetraStereo.Examples.Rule5EssentialDependency
