import TetraStereo.Examples.Rule5EssentialInputStage03SourceFact

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

def otherFact : OccurrenceAuxFact :=
  { key :=
      { history := [6, 1]
        provenance := .realAtom }
    atom := 6
    descriptor := .S
    uppercase := true
    priorityPositions := [3, 2, 0, 1] }

theorem other_ligand_atom : ligandAtom root otherSlot = 6 := by decide

theorem other_sourceNode_option :
    other.sourceNode? = some (ligandRootNode root otherSlot) := by
  change ((discovery.center root).branch otherSlot).key.sourceNodeAtAddress? [] =
    some (ligandRootNode root otherSlot)
  exact (discovery.center root).branch otherSlot |>.rootedAt

theorem otherFact_computed :
    other.sourceNode?.bind (occurrenceFact? molecule fuel []) = some otherFact := by
  rw [other_sourceNode_option]
  simpa [ligandRootNode, root_center_atom, other_ligand_atom] using
    (show occurrenceFact? molecule fuel [] (RawMolecule.canonicalRoot 1 6) =
        some otherFact by
      rw [molecule_eq_fixture]
      exact fixture_fact_of_observations fixtureMolecule [] fuel
        (RawMolecule.canonicalRoot 1 6) (fixtureProfile (RawMolecule.canonicalRoot 1 6))
        (fixtureCarbon .clockwise) .clockwise
        (fixtureArmRoots 6 10 7 8) (fixtureArmSorted 6 10 7 8) 0
        [3, 2, 0, 1] fixtureOrdinaryDecisions
        fixture_other_profile (by decide +kernel) rfl fixture_other_roots
        fixture_other_sort (by decide +kernel) fixture_other_adjacency)

def otherLabel : Label discovery :=
  labelOfOrdinaryFact discovery other otherFact fuel [] otherFact_computed

end TetraStereo.Examples.Rule5EssentialDependency
