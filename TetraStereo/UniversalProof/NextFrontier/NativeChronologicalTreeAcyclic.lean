import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalTreeUndirectedPathBridge
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeChronologicalTreeUndirectedPathBridge

/-- Prefix restriction keeps the ambient Nat vertices; excluded vertices are isolated. -/
def prefixGraph (G : SimpleGraph Nat) (bound : Nat) : SimpleGraph Nat where
  Adj a b := G.Adj a b ∧ a < bound ∧ b < bound
  symm := by
    intro a b h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro a h
    exact G.loopless.irrefl a h.1

/-- An isolated newly admitted vertex cannot reach an earlier vertex. -/
theorem new_vertex_not_reachable (G : SimpleGraph Nat) {bound parent : Nat}
    (earlier : parent < bound) : ¬ (prefixGraph G bound).Reachable bound parent := by
  rintro ⟨walk⟩
  cases walk with
  | nil => exact (Nat.lt_irrefl _) earlier
  | cons adjacent tail => exact (Nat.lt_irrefl bound) adjacent.2.1

/-- Ordered graphs with at most one earlier neighbor are forests on every finite prefix.
    The proof adds one isolated vertex and at most one edge, without selecting or rotating cycles. -/
theorem prefix_acyclic (G : SimpleGraph Nat)
    (oneEarlier : ∀ {peak first second : Nat}, first < peak → second < peak →
      G.Adj peak first → G.Adj peak second → first = second) :
    ∀ bound, (prefixGraph G bound).IsAcyclic := by
  intro bound
  induction bound with
  | zero =>
      have empty : prefixGraph G 0 = ⊥ := by
        ext a b
        simp [prefixGraph]
      rw [empty]
      exact SimpleGraph.isAcyclic_bot
  | succ bound previous =>
      classical
      by_cases existsParent : ∃ parent, parent < bound ∧ G.Adj bound parent
      · obtain ⟨parent, earlier, edge⟩ := existsParent
        have added : (prefixGraph G bound ⊔
            SimpleGraph.fromEdgeSet {s(bound, parent)}).IsAcyclic :=
          (SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable bound parent
            (new_vertex_not_reachable G earlier)).mpr previous
        apply added.anti
        intro a b adjacent
        change (prefixGraph G bound).Adj a b ∨
          (SimpleGraph.fromEdgeSet {s(bound, parent)}).Adj a b
        by_cases aEarlier : a < bound
        · by_cases bEarlier : b < bound
          · exact Or.inl ⟨adjacent.1, aEarlier, bEarlier⟩
          · have bNew : b = bound := by
              have := adjacent.2.2
              omega
            have aParent : a = parent := by
              apply oneEarlier aEarlier earlier
              · simpa [bNew] using adjacent.1.symm
              · exact edge
            apply Or.inr
            rw [SimpleGraph.fromEdgeSet_adj]
            constructor
            · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
              exact Or.inr ⟨aParent, bNew⟩
            · exact adjacent.1.ne
        · have aNew : a = bound := by
            have := adjacent.2.1
            omega
          have bEarlier : b < bound := by
            have different := adjacent.1.ne
            have := adjacent.2.2
            omega
          have bParent : b = parent := by
            apply oneEarlier bEarlier earlier
            · simpa [aNew] using adjacent.1
            · exact edge
          apply Or.inr
          rw [SimpleGraph.fromEdgeSet_adj]
          constructor
          · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
            exact Or.inl ⟨aNew, bParent⟩
          · exact adjacent.1.ne
      · apply previous.anti
        intro a b adjacent
        have aEarlier : a < bound := by
          by_contra no
          have aNew : a = bound := by
            have := adjacent.2.1
            omega
          have bEarlier : b < bound := by
            have different := adjacent.1.ne
            have := adjacent.2.2
            omega
          exact existsParent ⟨b, bEarlier, by simpa [aNew] using adjacent.1⟩
        have bEarlier : b < bound := by
          by_contra no
          have bNew : b = bound := by
            have := adjacent.2.2
            omega
          exact existsParent ⟨a, aEarlier, by simpa [bNew] using adjacent.1.symm⟩
        exact ⟨adjacent.1, aEarlier, bEarlier⟩

/-- Actual bounded physical adjacency; unsupported ambient Nat vertices remain isolated. -/
def physicalGraph (mol : RawMolecule) : SimpleGraph Nat where
  Adj a b := a < mol.atomCount ∧ b < mol.atomCount ∧ 0 < mol.bondOrder a b
  symm := by
    intro a b h
    refine ⟨h.2.1, h.1, ?_⟩
    rw [mol.bondOrder_symm b a]
    exact h.2.2
  loopless := by
    constructor
    intro a h
    have positive := h.2.2
    rw [mol.bondOrder_self] at positive
    exact (Nat.lt_irrefl 0) positive

/-- Independent chronological raw inventory entails global acyclicity of actual adjacency. -/
theorem chronological_physicalGraph_acyclic {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) : (physicalGraph mol).IsAcyclic := by
  have forest := prefix_acyclic (physicalGraph mol) (by
    intro peak first second firstSmall secondSmall firstEdge secondEdge
    exact smaller_physical_neighbors_unique tree firstSmall secondSmall
      firstEdge.2.2 secondEdge.2.2) mol.atomCount
  apply forest.anti
  intro a b adjacent
  exact ⟨adjacent, adjacent.1, adjacent.2.1⟩

open TetraStereo.UniversalProof.InteriorMethylDepthCounterexample

/-- A concrete saturated C/H/F fixture inhabits the raw domain used by this theorem. -/
theorem methyl_physicalGraph_acyclic :
    (physicalGraph TetraStereo.UniversalProof.InteriorMethylDepthCounterexample.molecule).IsAcyclic := by
  apply chronological_physicalGraph_acyclic
  refine ⟨by decide, ?_, by decide, ?_⟩
  · intro b member
    simp only [molecule, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro atom positive bounded
    change atom < 11 at bounded
    interval_cases atom <;> simp [molecule, bond]

end TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic
