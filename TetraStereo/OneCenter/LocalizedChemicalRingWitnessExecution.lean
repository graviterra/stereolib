import TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingGeneratedLabelExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Successful snapshot lookups at history-defined witness nodes are actual descriptor
executions. Reachability of the query is derived from the emitted fact: canonical histories
determine both atom and parent, so the reached producer is the exact queried raw node.
The shared-depth corollary preserves the inherited context and input state. It does not
assert that a label exists, or that descendant snapshots agree under a physical symmetry. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution

open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingGeneratedLabelExecution
open LocalizedChemicalRingSenseTransport (Step factsWith descriptorWith)
open LocalizedMarkedOperationEvaluator (Operations underWith)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope (descendant_reached)
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)
open LocalizedMarkedGeneratedFactUniqueness (factOf_key)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedGenericMarkedRecalculation (Geometry)
open LocalizedMarkedTerminalGaugeFrame (child_parent)
open AuthoritativeCIPMoleculeCursorRanking (CanonicalCenterTreeNode)

theorem rawPathNode_head {n : Nat} (root : Fin n) (path : List (Fin n)) :
    (rawPathNode root path).history.head? = some (rawPathNode root path).atom := by
  simp only [rawPathNode, List.head?_map, List.head?_reverse, List.getLast?_cons,
    Option.map_some]

theorem rawPathNode_parent {n : Nat} (root : Fin n) (path : List (Fin n)) :
    (rawPathNode root path).history.tail.head?.getD (rawPathNode root path).atom =
      (rawPathNode root path).parent := by
  cases path with
  | nil => rfl
  | cons first rest =>
      simp only [rawPathNode, ← List.map_tail, List.tail_reverse, List.dropLast_cons₂,
        List.head?_map, List.head?_reverse, List.getLast?_cons, Option.map_some,
        Option.getD_some]

/-- A canonical generated node's parent is determined by its history, including the
self-parent convention at the original root. -/
theorem generated_parent {mol : RawMolecule} {center : Nat}
    {node : RawMolecule.CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center node) :
    node.history.tail.head?.getD node.atom = node.parent := by
  cases generated with
  | root => rfl
  | child parentGenerated member =>
      rw [mol.canonicalChildren_history _ _ member, List.tail_cons,
        parentGenerated.history_head, Option.getD_some, child_parent mol _ _ member]

/-- Key equality identifies a reached producer with the complete history-defined query.
No reachability, adjacency, or intake agreement is required of the query beforehand. -/
theorem generated_eq_rawPathNode {n : Nat} (root : Fin n) (path : List (Fin n))
    {mol : RawMolecule} {center : Nat} {node : RawMolecule.CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center node)
    (keys : canonicalOccurrenceKey node = canonicalOccurrenceKey (rawPathNode root path)) :
    node = rawPathNode root path := by
  have history : node.history = (rawPathNode root path).history :=
    congrArg CanonicalOccurrenceKey.history keys
  have provenance : node.provenance = (rawPathNode root path).provenance :=
    congrArg CanonicalOccurrenceKey.provenance keys
  have atom : node.atom = (rawPathNode root path).atom := by
    have head := generated.history_head
    rw [history] at head
    exact Option.some.inj (head.symm.trans (rawPathNode_head root path))
  have parent : node.parent = (rawPathNode root path).parent := by
    have recovered := generated_parent generated
    rw [history, atom] at recovered
    exact recovered.symm.trans (rawPathNode_parent root path)
  cases node
  simp only [rawPathNode] at atom parent history provenance ⊢
  simp_all

/-- A successful generated snapshot lookup proves that the queried witness node was
actually reached. An arbitrary raw state would not supply this conclusion. -/
theorem snapshot_path_reached {n : Nat} (root : Fin n) (path : List (Fin n))
    (step : Step) (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (source : RawMolecule.CanonicalBranchNode)
    (sourceReached : Reached mol source) (mark : Nat)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
      (rawPathNode root path)).map factLabel = some label) :
    Reached mol (rawPathNode root path) := by
  obtain ⟨fact, lookup, _⟩ := Option.map_eq_some_iff.mp observed
  have key : fact.key = canonicalOccurrenceKey (rawPathNode root path) := by
    simpa only [beq_iff_eq] using List.find?_some lookup
  obtain ⟨target, _, _, descent, _, _, value⟩ :=
    snapshot_source_budget step mol ops depth geom state source mark fact
      (List.mem_of_find?_eq_some lookup)
  have targetReached : Reached mol target := by
    obtain ⟨child, edge, rest⟩ := descent
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  have same : target = rawPathNode root path := by
    obtain ⟨center, _, reached⟩ := targetReached
    rw [value, factOf_key] at key
    exact generated_eq_rawPathNode root path (generated_of_reachedFrom mol center target reached) key
  rwa [same] at targetReached

/-- The actual descriptor at a witness history, with query reachability derived from the
successful snapshot lookup and remaining depth determined by that history. -/
theorem snapshot_path_execution {n : Nat} (root : Fin n) (path : List (Fin n))
    (step : Step) (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (source : RawMolecule.CanonicalBranchNode)
    (sourceReached : Reached mol source) (mark : Nat)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
      (rawPathNode root path)).map factLabel = some label) :
    descriptorWith step mol ops (depth + source.history.length - (path.length + 1))
      geom state (some mark) (rawPathNode root path) = some label := by
  have reached := snapshot_path_reached root path step mol ops depth geom state source
    sourceReached mark label observed
  simpa only [rawPathNode, List.length_map, List.length_reverse, List.length_cons] using
    snapshot_label_execution step mol ops depth geom state source sourceReached mark
      (rawPathNode root path) reached label observed

/-- Equal successful snapshot labels at equal-length witness paths are actual executions
at one recursive budget. This accepts the optional fact equality supplied by
`fact_labels_eq_of_pathLabelsAgree`; neither query's reachability is assumed. -/
theorem matched_paths_execute {n : Nat} (root : Fin n) (left right : List (Fin n))
    (sameLength : left.length = right.length) (step : Step) (mol : RawMolecule)
    (ops : Operations) (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source) (mark : Nat)
    (matched : ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
      (rawPathNode root left)).map factLabel =
      ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
        (rawPathNode root right)).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
      (rawPathNode root left)).map factLabel = some label) :
    let remaining := depth + source.history.length - (left.length + 1)
    descriptorWith step mol ops remaining geom state (some mark) (rawPathNode root left) =
      some label ∧
      descriptorWith step mol ops remaining geom state (some mark) (rawPathNode root right) =
        some label := by
  refine ⟨snapshot_path_execution root left step mol ops depth geom state source
    sourceReached mark label observed, ?_⟩
  have rightObserved := matched.symm.trans observed
  simpa only [sameLength] using snapshot_path_execution root right step mol ops depth geom
    state source sourceReached mark label rightObserved

end TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution.rawPathNode_head
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution.rawPathNode_parent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution.generated_parent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution.generated_eq_rawPathNode
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution.snapshot_path_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution.snapshot_path_execution
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution.matched_paths_execute
