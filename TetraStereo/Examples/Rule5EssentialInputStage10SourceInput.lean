import TetraStereo.Examples.Rule5EssentialInputStage09SourceFrame

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem source_input_accepted : inputFact? fullState source = some sourceFact := by
  simp [inputFact?, fullState, sameOccurrence, sourceLabel, labelOfOrdinaryFact, sourceFact,
    factKey, source_node, ligandRootNode, source_ligand_atom, descriptorOfFact,
    descriptorSense, canonicalOccurrenceKey, RawMolecule.canonicalRoot]

end TetraStereo.Examples.Rule5EssentialDependency
