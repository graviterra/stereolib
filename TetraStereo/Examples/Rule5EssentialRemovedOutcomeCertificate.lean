import TetraStereo.Examples.Rule5EssentialFullOutcomeCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

def removedTargetFact : OccurrenceAuxFact :=
  { key :=
      { history := [1]
        provenance := .realAtom }
    atom := 1
    descriptor := .S
    uppercase := true
    priorityPositions := [1, 0, 3, 2] }

/-- With the source fact removed, Rule 4a observes category 0 against the retained
ordinary category 2; this is an ordinary strict result, not a pseudo flag. -/
theorem fixture_removed_arm_decision :
    FrameRuntime.decisionComplete? fixtureMolecule
      (fixtureProfile (canonicalCenterRoot 1)) false [otherFact] fuel
      (fixtureCenterCursor 3) (fixtureCenterCursor 6) =
      some { ordering := .lt } := by decide +kernel

theorem fixture_removed_sort :
    FramedCompleteRuntime.trackedSortComplete? fixtureMolecule
      (fixtureProfile (canonicalCenterRoot 1)) false [otherFact] fuel fixtureCenterRoots =
      some (fixtureRemovedSorted, 0) := by decide +kernel

theorem fixture_removed_adjacency :
    (FramedCompleteRuntime.adjacentComplete? fixtureMolecule
      (fixtureProfile (canonicalCenterRoot 1)) false [otherFact] fuel
      fixtureRemovedSorted).map (fun pairs => pairs.map fun pair => pair.decision) =
      some fixtureOrdinaryDecisions := by decide +kernel

theorem removedTargetFact_computed :
    target.sourceNode?.bind (occurrenceFact? molecule fuel [otherFact]) =
      some removedTargetFact := by
  have assembled : occurrenceFact? fixtureMolecule fuel [otherFact]
      (canonicalCenterRoot 1) =
      fixtureFinish (canonicalCenterRoot 1) .anticlockwise [1, 0, 3, 2]
        fixtureOrdinaryDecisions := by
    exact fixture_fact_of_observations fixtureMolecule [otherFact] fuel
      (canonicalCenterRoot 1) (fixtureProfile (canonicalCenterRoot 1))
      (fixtureCarbon .anticlockwise) .anticlockwise fixtureCenterRoots fixtureRemovedSorted 0
      [1, 0, 3, 2] fixtureOrdinaryDecisions
      fixture_center_profile (by decide +kernel) rfl fixture_center_roots
      fixture_removed_sort (by decide +kernel) fixture_removed_adjacency
  have finished :
      fixtureFinish (canonicalCenterRoot 1) .anticlockwise [1, 0, 3, 2]
        fixtureOrdinaryDecisions = some removedTargetFact := by
    decide +kernel
  rw [target, finalOccurrence_source, root_center_atom, Option.bind_some, molecule_eq_fixture]
  exact assembled.trans finished

def removedTargetLabel : Label discovery :=
  labelOfOrdinaryFact discovery target removedTargetFact fuel [otherFact]
    removedTargetFact_computed

/-- Assemble an ordinary label from the accepted encoding and exact public fact result.
The parameters remain abstract while the source-node bind and label proof are converted. -/
private theorem removed_ordinaryLabel_of_encoded_fact
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

/-- Removing only the R branch occurrence leaves the S branch and changes the ordinary result
to uppercase S; the retained fact separates the arms at Rule 4a. -/
theorem removed_ordinary_label :
    ordinaryLabel? discovery fuel withoutSource target = some removedTargetLabel := by
  have encoded := executable_state_removed
  rw [encodedStateRemoved] at encoded
  unfold removedTargetLabel
  exact removed_ordinaryLabel_of_encoded_fact discovery fuel withoutSource target
    [otherFact] removedTargetFact removedTargetFact_computed encoded

end TetraStereo.Examples.Rule5EssentialDependency
