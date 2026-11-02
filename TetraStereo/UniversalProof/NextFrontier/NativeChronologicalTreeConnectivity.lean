import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalTreePathBridge
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalTreeConnectivity
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeChronologicalTreePathBridge

/-- The actual physical bond graph on natural atom coordinates. Bounds exclude extraneous vertices
from every edge; this contains no supplied connectivity or desired distance field. -/
def physicalGraph (mol : RawMolecule) : SimpleGraph Nat where
  Adj a b := a < mol.atomCount ∧ b < mol.atomCount ∧ 0 < mol.bondOrder a b
  symm := by
    intro a b edge
    refine ⟨edge.2.1, edge.1, ?_⟩
    rw [mol.bondOrder_symm b a]
    exact edge.2.2
  loopless := by
    refine ⟨?_⟩
    intro a edge
    have positive := edge.2.2
    rw [mol.bondOrder_self] at positive
    exact (Nat.lt_irrefl 0) positive

/-- A derived actual raw parent chain realizes a physical walk to zero. -/
theorem parent_path_reachable_zero {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {child : Nat} {vertices : List Nat} (path : ParentPath mol child vertices) :
    (physicalGraph mol).Reachable child 0 := by
  induction path with
  | root => exact SimpleGraph.Reachable.refl 0
  | @step child parent tail edge path ih =>
      have decreasing := parent_edge_decreases tree edge
      have childBound := parent_edge_bound tree edge
      have parentBound := lt_trans decreasing childBound
      have adjacent : (physicalGraph mol).Adj child parent :=
        ⟨childBound, parentBound, parent_edge_physical tree edge⟩
      exact adjacent.reachable.trans ih

/-- No reachability premise: all supported atom coordinates are connected through the actual
terminating raw parent routes derived from the independent chronological inventory. -/
theorem physical_atoms_reachable {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    (start finish : Nat) (startBound : start < mol.atomCount) (finishBound : finish < mol.atomCount) :
    (physicalGraph mol).Reachable start finish := by
  obtain ⟨startVertices, startPath⟩ := parent_path_exists tree start startBound
  obtain ⟨finishVertices, finishPath⟩ := parent_path_exists tree finish finishBound
  exact (parent_path_reachable_zero tree startPath).trans
    (parent_path_reachable_zero tree finishPath).symm

/-- Every vertex in an actual physical walk remains in the raw molecule's supported inventory. -/
theorem physical_walk_support_bounded {mol : RawMolecule} {start finish : Nat}
    (walk : (physicalGraph mol).Walk start finish) (startBound : start < mol.atomCount) :
    ∀ atom ∈ walk.support, atom < mol.atomCount := by
  induction walk with
  | @nil vertex =>
      intro atom member
      have same : atom = vertex := by
        simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using member
      subst atom
      exact startBound
  | @cons start next finish edge walk ih =>
      intro atom member
      rw [SimpleGraph.Walk.support_cons] at member
      rcases List.mem_cons.mp member with same | member
      · subst atom
        exact edge.1
      · exact ih edge.2.1 atom member

/-- Physical walk support follows actual raw positive bond orders. -/
theorem physical_walk_support_bonded {mol : RawMolecule} {start finish : Nat}
    (walk : (physicalGraph mol).Walk start finish) : RawBondedPath mol walk.support := by
  exact walk.isChain_adj_support.imp_of_mem_imp (fun _ _ _ _ adjacent => adjacent.2.2)

/-- A genuine graph path is exactly a supported simple raw path, including its actual endpoints. -/
theorem physical_isPath_supported {mol : RawMolecule} {start finish : Nat}
    (walk : (physicalGraph mol).Walk start finish) (simple : walk.IsPath)
    (startBound : start < mol.atomCount) : RawSupportedPath mol start finish walk.support := by
  refine ⟨simple.support_nodup, physical_walk_support_bonded walk, ?_, ?_,
    physical_walk_support_bounded walk startBound⟩
  · rw [List.head?_eq_some_head walk.support_ne_nil, walk.head_support]
  · rw [List.getLast?_eq_some_getLast walk.support_ne_nil, walk.getLast_support]

/-- Complete connectivity join to the existing actual raw-path ABI. The graph library removes
loops from the derived walk while preserving endpoints; no caller supplies successful paths. -/
theorem chronological_rawPathConnected {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) : RawPathConnected mol := by
  intro start finish startBound finishBound
  obtain ⟨walk, simple⟩ := (physical_atoms_reachable tree start finish startBound finishBound).exists_isPath
  exact ⟨walk.support, physical_isPath_supported walk simple startBound⟩

/-- Actual methyl connectivity is an inhabitant of the general join, not a fake empty interface. -/
theorem methyl_rawPathConnected :
    RawPathConnected TetraStereo.UniversalProof.InteriorMethylDepthCounterexample.molecule :=
  chronological_rawPathConnected methyl_chronological_domain

end TetraStereo.UniversalProof.NativeChronologicalTreeConnectivity
