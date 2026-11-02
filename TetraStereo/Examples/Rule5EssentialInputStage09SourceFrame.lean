import TetraStereo.Examples.Rule5EssentialInputStage08FinalFact

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem source_mem_occurrences : source ∈ occurrencesAtRoot discovery root := by
  rw [occurrencesAtRoot]
  apply List.mem_cons_of_mem
  rw [List.mem_flatMap]
  refine ⟨sourceSlot, by simp, ?_⟩
  unfold occurrencesAtSlot
  apply List.mem_map.mpr
  exact ⟨sourceDedupNode, by simp, rfl⟩

theorem other_mem_occurrences : other ∈ occurrencesAtRoot discovery root := by
  rw [occurrencesAtRoot]
  apply List.mem_cons_of_mem
  rw [List.mem_flatMap]
  refine ⟨otherSlot, by simp, ?_⟩
  unfold occurrencesAtSlot
  apply List.mem_map.mpr
  exact ⟨otherDedupNode, by simp, rfl⟩

theorem source_node :
    sourceNode discovery source = ligandRootNode root sourceSlot := by
  have exactSource := sourceNode_spec discovery source
  have exactRoot := (discovery.center root).branch sourceSlot |>.rootedAt
  change ((discovery.center root).branch sourceSlot).key.sourceNodeAtAddress? [] =
    some (sourceNode discovery source) at exactSource
  change ((discovery.center root).branch sourceSlot).key.sourceNodeAtAddress? [] =
    some (ligandRootNode root sourceSlot) at exactRoot
  exact Option.some.inj (exactSource.symm.trans exactRoot)

theorem source_tetrahedral :
    (molecule.atomAt? 3).any (fun spec => spec.tetrahedral?.isSome) = true := by decide

theorem source_label_capable : labelCapable discovery source = true := by
  simp [labelCapable, source_node, ligandRootNode, source_ligand_atom,
    RawMolecule.canonicalRoot, source_tetrahedral]

end TetraStereo.Examples.Rule5EssentialDependency
