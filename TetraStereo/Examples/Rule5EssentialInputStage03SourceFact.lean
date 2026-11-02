import TetraStereo.Examples.Rule5EssentialInputStage02Occurrences

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem source_ligand_atom : ligandAtom root sourceSlot = 3 := by decide

theorem source_sourceNode_option :
    source.sourceNode? = some (ligandRootNode root sourceSlot) := by
  change ((discovery.center root).branch sourceSlot).key.sourceNodeAtAddress? [] =
    some (ligandRootNode root sourceSlot)
  exact (discovery.center root).branch sourceSlot |>.rootedAt

def sourceFact : OccurrenceAuxFact :=
  { key :=
      { history := [3, 1]
        provenance := .realAtom }
    atom := 3
    descriptor := .R
    uppercase := true
    priorityPositions := [3, 2, 0, 1] }

theorem sourceFact_computed :
    source.sourceNode?.bind (occurrenceFact? molecule fuel []) = some sourceFact := by
  rw [source_sourceNode_option]
  simpa [ligandRootNode, root_center_atom, source_ligand_atom] using
    (show occurrenceFact? molecule fuel [] (RawMolecule.canonicalRoot 1 3) =
        some sourceFact by
      rw [molecule_eq_fixture]
      exact fixture_fact_of_observations fixtureMolecule [] fuel
        (RawMolecule.canonicalRoot 1 3) (fixtureProfile (RawMolecule.canonicalRoot 1 3))
        (fixtureCarbon .anticlockwise) .anticlockwise
        (fixtureArmRoots 3 9 4 5) (fixtureArmSorted 3 9 4 5) 0
        [3, 2, 0, 1] fixtureOrdinaryDecisions
        fixture_source_profile (by decide +kernel) rfl fixture_source_roots
        fixture_source_sort (by decide +kernel) fixture_source_adjacency)

def sourceLabel : Label discovery :=
  labelOfOrdinaryFact discovery source sourceFact fuel [] sourceFact_computed

end TetraStereo.Examples.Rule5EssentialDependency
