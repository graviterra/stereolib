import TetraStereo.Examples.Rule5EssentialInputStage05FullArm

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem fixture_full_sort :
    FramedCompleteRuntime.trackedSortComplete? fixtureMolecule
      (fixtureProfile (canonicalCenterRoot 1)) false [sourceFact, otherFact] fuel
      fixtureCenterRoots = some (fixtureFullSorted, 1) := by decide +kernel

end TetraStereo.Examples.Rule5EssentialDependency
