import TetraStereo.Examples.Rule5EssentialInputStage08aFactComputation

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

def fullTargetLabel : Label discovery :=
  labelOfOrdinaryFact discovery target fullTargetFact fuel [sourceFact, otherFact]
    fullTargetFact_computed

def encodedState : OccurrenceAuxState := [sourceFact, otherFact]
def encodedStateRemoved : OccurrenceAuxState := [otherFact]

end TetraStereo.Examples.Rule5EssentialDependency
