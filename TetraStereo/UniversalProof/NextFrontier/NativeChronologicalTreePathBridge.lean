import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization
import TetraStereo.OneCenter.ChronologicalPhysicalTree
import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedRealPaths
import TetraStereo.UniversalProof.NextFrontier.NativePhysicalChildTransport
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalTreePathBridge
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeGeneratedRealPaths

/-- Independent actual directed raw bond incidence, not a generated-history conclusion. -/
def ParentEdge (mol : RawMolecule) (child parent : Nat) : Prop :=
  ∃ bond ∈ mol.bonds, bond.target = child ∧ bond.source = parent

/-- Paths constructed only by actual raw parent edges, ending at physical inventory root zero.
This does not assert uniqueness of arbitrary undirected simple paths. -/
inductive ParentPath (mol : RawMolecule) : Nat → List Nat → Prop where
  | root : ParentPath mol 0 [0]
  | step {child parent : Nat} {tail : List Nat}
      (edge : ParentEdge mol child parent) (path : ParentPath mol parent tail) :
      ParentPath mol child (child :: tail)

theorem parent_edge_decreases {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {child parent : Nat} (edge : ParentEdge mol child parent) : parent < child := by
  obtain ⟨bond, member, target, source⟩ := edge
  have ordered := (tree.2.1 bond member).2.1
  simpa only [target, source] using ordered

theorem parent_edge_bound {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {child parent : Nat} (edge : ParentEdge mol child parent) : child < mol.atomCount := by
  obtain ⟨bond, member, target, source⟩ := edge
  have bounded := (tree.2.1 bond member).2.2
  simpa only [target] using bounded

theorem parent_edge_exists {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    (child : Nat) (positive : 0 < child) (bounded : child < mol.atomCount) :
    ∃ parent, ParentEdge mol child parent := by
  obtain ⟨bond, member, target⟩ := List.mem_map.mp (tree.2.2.2 child positive bounded)
  exact ⟨bond.source, bond, member, target, rfl⟩

theorem parent_edge_unique {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {child first second : Nat} (left : ParentEdge mol child first)
    (right : ParentEdge mol child second) : first = second := by
  obtain ⟨a, ha, atarget, asource⟩ := left
  obtain ⟨b, hb, btarget, bsource⟩ := right
  have same : a = b := List.inj_on_of_nodup_map tree.2.2.1 ha hb (atarget.trans btarget.symm)
  exact asource.symm.trans ((congrArg RawBond.source same).trans bsource)

theorem parent_edge_physical {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {child parent : Nat} (edge : ParentEdge mol child parent) :
    0 < mol.bondOrder child parent := by
  have decreasing := parent_edge_decreases tree edge
  obtain ⟨bond, member, target, source⟩ := edge
  apply (RawMolecule.bondOrder_pos_iff_exists_bond mol (ne_of_gt decreasing)).mpr
  exact ⟨bond, member, by simp [RawBond.connects, target, source]⟩

/-- Strong induction on physical atom index terminates at zero: no supplied path field. -/
theorem parent_path_exists {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    (child : Nat) (bounded : child < mol.atomCount) :
    ∃ vertices, ParentPath mol child vertices := by
  induction child using Nat.strong_induction_on with
  | h child ih =>
      by_cases zero : child = 0
      · subst child
        exact ⟨[0], .root⟩
      · obtain ⟨parent, edge⟩ := parent_edge_exists tree child (by omega) bounded
        have decreasing := parent_edge_decreases tree edge
        obtain ⟨tail, path⟩ := ih parent decreasing (lt_trans decreasing bounded)
        exact ⟨child :: tail, .step edge path⟩

/-- Unique directed raw parent chains derive from target-inventory Nodup, not desired metric equality. -/
theorem parent_path_unique {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {child : Nat} {first second : List Nat} (left : ParentPath mol child first)
    (right : ParentPath mol child second) : first = second := by
  induction left generalizing second with
  | root =>
      cases right with
      | root => rfl
      | @step child parent tail edge path =>
          have decreasing := parent_edge_decreases tree edge
          omega
  | @step child parent tail edge path ih =>
      cases right with
      | root =>
          have decreasing := parent_edge_decreases tree edge
          omega
      | @step child other otherTail otherEdge otherPath =>
          have same := parent_edge_unique tree edge otherEdge
          subst other
          have tails := ih otherPath
          exact congrArg (fun xs => child :: xs) tails

/-- Constructed chains are supported simple physical paths; every vertex is below their start. -/
theorem parent_path_supported {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {child : Nat} {vertices : List Nat} (path : ParentPath mol child vertices) :
    RawSupportedPath mol child 0 vertices ∧ (∀ atom ∈ vertices, atom ≤ child) := by
  induction path with
  | root =>
      refine ⟨⟨List.nodup_singleton _, List.isChain_singleton _, rfl, rfl, ?_⟩, ?_⟩
      · intro atom member
        have same : atom = 0 := List.mem_singleton.mp member
        subst atom
        exact tree.1
      · intro atom member
        have same : atom = 0 := List.mem_singleton.mp member
        omega
  | @step child parent tail edge path ih =>
      obtain ⟨supported, inventory⟩ := ih
      obtain ⟨nodup, bonded, head, last, bounds⟩ := supported
      have decreasing := parent_edge_decreases tree edge
      have childBound := parent_edge_bound tree edge
      have fresh : child ∉ tail := by
        intro member
        have le := inventory child member
        omega
      refine ⟨⟨List.Nodup.cons fresh nodup, ?_, rfl, ?_, ?_⟩, ?_⟩
      · cases tail with
        | nil => simp at head
        | cons atom rest =>
            have same : atom = parent := by simpa only [List.head?_cons, Option.some.injEq] using head
            subst atom
            change (child :: parent :: rest).IsChain (fun a b => 0 < mol.bondOrder a b)
            rw [List.isChain_cons_cons]
            exact ⟨parent_edge_physical tree edge, bonded⟩
      · cases tail with
        | nil => simp at head
        | cons atom rest => simpa only [List.getLast?_cons_cons] using last
      · intro atom member
        rcases List.mem_cons.mp member with same | member
        · subst atom; exact childBound
        · exact bounds atom member
      · intro atom member
        rcases List.mem_cons.mp member with same | member
        · subst atom; exact le_rfl
        · exact le_trans (inventory atom member) (Nat.le_of_lt decreasing)

/-- Each supported vertex has a uniquely constructed, simple, raw-bond-supported route to zero. -/
theorem physical_root_path_exists {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    (child : Nat) (bounded : child < mol.atomCount) :
    ∃ vertices, ParentPath mol child vertices ∧ RawSupportedPath mol child 0 vertices := by
  obtain ⟨vertices, path⟩ := parent_path_exists tree child bounded
  exact ⟨vertices, path, (parent_path_supported tree path).1⟩

/-- Explicit chronological decrease also bounds a constructed chain's number of edges. -/
theorem parent_path_length_bound {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {child : Nat} {vertices : List Nat} (path : ParentPath mol child vertices) :
    vertices.length ≤ child + 1 := by
  induction path with
  | root => decide
  | @step child parent tail edge path ih =>
      have decreasing := parent_edge_decreases tree edge
      simp only [List.length_cons]
      omega

open TetraStereo.UniversalProof.InteriorMethylDepthCounterexample

/-- The actual saturated C/H/F methyl fixture inhabits the independent chronological domain. -/
theorem methyl_chronological_domain : molecule.ChronologicalPhysicalTree := by
  refine ⟨by decide, ?_, by decide, ?_⟩
  · intro b member
    simp only [molecule, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro atom positive bounded
    change atom < 11 at bounded
    interval_cases atom <;> simp [molecule, bond]

/-- Rootward existence/uniqueness is inhabited by the actual methyl fixture, not empty support. -/
theorem methyl_rootward_paths :
    ∃ left right, ParentPath molecule 1 left ∧ ParentPath molecule 2 right ∧
      RawSupportedPath molecule 1 0 left ∧ RawSupportedPath molecule 2 0 right := by
  obtain ⟨left, lp, ls⟩ := physical_root_path_exists methyl_chronological_domain 1 (by decide)
  obtain ⟨right, rp, rs⟩ := physical_root_path_exists methyl_chronological_domain 2 (by decide)
  exact ⟨left, right, lp, rp, ls, rs⟩

/-- Concrete domain exclusion: a raw closure into zero cannot be hidden in a chronological tree. -/
theorem raw_root_closure_excluded {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    (bond : RawBond) (member : bond ∈ mol.bonds) : bond.target ≠ 0 :=
  tree.no_root_target bond member

/-- A concrete three-carbon closure fails the independent domain, regardless of path claims. -/
def closureExample : RawMolecule :=
  { atoms := [carbon, carbon, carbon]
    bonds := [bond 0 1, bond 1 2, bond 2 0]
    neighborOrder := [[1,2],[0,2],[1,0]] }

theorem closureExample_not_chronological : ¬ closureExample.ChronologicalPhysicalTree := by
  intro tree
  have member : bond 2 0 ∈ closureExample.bonds := by decide
  have excluded := raw_root_closure_excluded tree (bond 2 0) member
  exact excluded rfl

end TetraStereo.UniversalProof.NativeChronologicalTreePathBridge
