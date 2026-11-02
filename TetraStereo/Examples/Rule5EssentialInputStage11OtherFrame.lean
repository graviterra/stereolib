import TetraStereo.Examples.Rule5EssentialInputStage10SourceInput

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem other_node :
    sourceNode discovery other = ligandRootNode root otherSlot := by
  have exactSource := sourceNode_spec discovery other
  have exactRoot := (discovery.center root).branch otherSlot |>.rootedAt
  change ((discovery.center root).branch otherSlot).key.sourceNodeAtAddress? [] =
    some (sourceNode discovery other) at exactSource
  change ((discovery.center root).branch otherSlot).key.sourceNodeAtAddress? [] =
    some (ligandRootNode root otherSlot) at exactRoot
  exact Option.some.inj (exactSource.symm.trans exactRoot)

theorem other_tetrahedral :
    (molecule.atomAt? 6).any (fun spec => spec.tetrahedral?.isSome) = true := by decide

theorem other_label_capable : labelCapable discovery other = true := by
  simp [labelCapable, other_node, ligandRootNode, other_ligand_atom,
    RawMolecule.canonicalRoot, other_tetrahedral]

end TetraStereo.Examples.Rule5EssentialDependency
