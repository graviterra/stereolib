import TetraStereo.Examples.Rule5EssentialEncodingCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

/-- Assemble an ordinary label from the accepted encoding and exact public fact result.
The parameters remain abstract while the source-node bind and label proof are converted. -/
private theorem ordinaryLabel_of_encoded_fact
    {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) (state : State discovery)
    (target : ProductionCIPOccurrenceDiscovery.Occurrence discovery)
    (aux : OccurrenceAuxState) (fact : OccurrenceAuxFact)
    (bound : target.sourceNode?.bind (occurrenceFact? mol fuel aux) = some fact)
    (encoded : executableStateFor? discovery state target = some aux) :
    ordinaryLabel? discovery fuel state target =
      some (labelOfOrdinaryFact discovery target fact fuel aux bound) := by
  have computed : occurrenceFact? mol fuel aux (sourceNode discovery target) =
      some fact := by
    have boundAtNode := bound
    rw [sourceNode_spec, Option.bind_some] at boundAtNode
    exact boundAtNode
  unfold ordinaryLabel?
  rw [encoded]
  exact ordinaryLabelFromAux?_eq_some discovery fuel aux target fact computed

/-- With both stereogenic branch occurrences present, the actual ordinary evaluator returns R. -/
theorem full_ordinary_label :
    ordinaryLabel? discovery fuel fullState target = some fullTargetLabel := by
  have encoded := executable_state
  rw [encodedState] at encoded
  unfold fullTargetLabel
  exact ordinaryLabel_of_encoded_fact discovery fuel fullState target
    [sourceFact, otherFact] fullTargetFact fullTargetFact_computed encoded

end TetraStereo.Examples.Rule5EssentialDependency
