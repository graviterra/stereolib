import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-- Minimal atom label for the CIP priority engine: an atomic number. -/
abbrev AtomicNumber := ℕ

/-- A natural-number bond order: `0` means no bond, `1` single, `2` double, `3` triple, ... -/
abbrev BondOrder := ℕ

/-- A finite molecular graph equipped with atom labels and bond orders.

This is deliberately minimal: bond orders are stored as a symmetric adjacency matrix with
zero diagonal. -/
structure MoleculeGraph (V : Type*) [Fintype V] [DecidableEq V] where
  atomZ : V → AtomicNumber
  /-- Optional isotopic mass number (default `0` = unspecified). -/
  atomMass : V → ℕ := fun _ => 0
  /-- Formal atomic charge.  This is constitutionally relevant for odd mancude systems, whose
  unmatched negatively charged vertex contributes the electron-pair position to the Kekule
  ensemble.  The default preserves existing charge-free mathematical examples. -/
  formalCharge : V → Int := fun _ => 0
  /-- Bond order adjacency matrix. -/
  bond : V → V → BondOrder
  bond_symm : ∀ u v, bond u v = bond v u
  bond_self : ∀ u, bond u u = 0

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two atoms are adjacent when their bond order is positive. -/
def Adj (m : MoleculeGraph V) (u v : V) : Prop :=
  0 < m.bond u v

instance (m : MoleculeGraph V) (u v : V) : Decidable (m.Adj u v) := by
  dsimp [Adj]
  infer_instance

instance (m : MoleculeGraph V) (v : V) : DecidablePred fun u => m.Adj v u := by
  intro u
  infer_instance

theorem adj_symm (m : MoleculeGraph V) {u v : V} : m.Adj u v ↔ m.Adj v u := by
  simp [Adj, m.bond_symm]

/-- The (finite) set of neighbors of `v`. -/
def neighborFinset (m : MoleculeGraph V) (v : V) : Finset V :=
  (Finset.univ : Finset V).filter fun u => m.Adj v u

@[simp] theorem mem_neighborFinset (m : MoleculeGraph V) (v u : V) :
    u ∈ m.neighborFinset v ↔ m.Adj v u := by
  simp [neighborFinset]

/-! ### Underlying simple graph and acyclicity

The molecular graph stores bond orders, so it is richer than a `SimpleGraph`.  For graph-theoretic
notions such as paths, cycles, and acyclicity, we forget the bond order and keep only positive-bond
adjacency.
-/

/-- The underlying simple graph obtained by forgetting bond orders and retaining only adjacency. -/
def underlyingSimpleGraph (m : MoleculeGraph V) : SimpleGraph V where
  Adj := m.Adj
  symm := by
    intro u v h
    exact (m.adj_symm).1 h
  loopless := by
    constructor
    intro v h
    simp [MoleculeGraph.Adj, m.bond_self] at h

@[simp] theorem underlyingSimpleGraph_adj (m : MoleculeGraph V) (u v : V) :
    m.underlyingSimpleGraph.Adj u v ↔ m.Adj u v :=
  Iff.rfl

/-- The molecular graph is acyclic when its underlying simple graph has no cycles. -/
abbrev Acyclic (m : MoleculeGraph V) : Prop :=
  m.underlyingSimpleGraph.IsAcyclic

/-- The molecular graph has only single bonds on every positive adjacency. -/
def SimpleBonded (m : MoleculeGraph V) : Prop :=
  ∀ u v, m.Adj u v → m.bond u v = 1

/-- A tree-like graph for the current CIP engine: no cycles in the underlying simple graph and no
multiple-bond expansion multiplicities. -/
def TreeLike (m : MoleculeGraph V) : Prop :=
  m.Acyclic ∧ m.SimpleBonded

theorem acyclic_path_unique (m : MoleculeGraph V) (h : m.Acyclic) {u v : V}
    (p q : m.underlyingSimpleGraph.Path u v) :
    p = q :=
  h.path_unique p q

/-- In an acyclic graph, a neighbor of the end of a path that is not the path's penultimate vertex
has not already appeared on the path.

This is the local graph-theoretic fact needed by the CIP expansion: after deleting the parent edge,
an acyclic branch cannot jump back to an earlier seen atom. -/
theorem Acyclic.not_mem_support_of_adj_ne_penultimate
    (m : MoleculeGraph V) (h : m.Acyclic) {root parent current child : V}
    {p : m.underlyingSimpleGraph.Walk root current}
    (hp : p.IsPath) (hpen : p.penultimate = parent)
    (hadj : m.Adj current child) (hchild : child ≠ parent) :
    child ∉ p.support := by
  intro hmem
  let G := m.underlyingSimpleGraph
  let q : G.Walk root child := p.takeUntil child hmem
  have hq : q.IsPath := by
    exact hp.takeUntil hmem
  have hadj' : G.Adj child current := by
    simpa [G] using (m.adj_symm).1 hadj
  have hconcat : p = q.concat hadj' := by
    exact h.path_concat (p := q) (q := p) hq hp hadj' hmem
  have hpenChild : p.penultimate = child := by
    rw [hconcat]
    simp [q, SimpleGraph.Walk.penultimate_concat]
  rw [hpen] at hpenChild
  exact hchild hpenChild.symm

end MoleculeGraph

/-- A molecule with a distinguished tetrahedral center and an explicit enumeration of its four
directly attached atoms (the four substituents to be ranked by CIP). -/
structure OneCenterMolecule (V : Type*) [Fintype V] [DecidableEq V] where
  mol : MoleculeGraph V
  center : V
  ligandAtom : Fin 4 → V
  ligandAtom_adj : ∀ i, mol.Adj center (ligandAtom i)
  ligandAtom_injective : Function.Injective ligandAtom
  /-- The four ligand atoms enumerate all neighbors of the stereocenter. -/
  ligandAtom_surjective : ∀ v, mol.Adj center v → ∃ i, ligandAtom i = v

end OneCenter
end TetraStereo
