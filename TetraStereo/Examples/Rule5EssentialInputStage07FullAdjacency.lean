import TetraStereo.Examples.Rule5EssentialInputStage06FullSort

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem fixture_full_adjacency :
    (FramedCompleteRuntime.adjacentComplete? fixtureMolecule
      (fixtureProfile (canonicalCenterRoot 1)) false [sourceFact, otherFact] fuel
      fixtureFullSorted).map (fun pairs => pairs.map fun pair => pair.decision) =
      some fixturePseudoDecisions := by decide +kernel

end TetraStereo.Examples.Rule5EssentialDependency
