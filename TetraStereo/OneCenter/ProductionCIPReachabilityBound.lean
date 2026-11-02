import TetraStereo.OneCenter.ProductionCIPReachability
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

open SimpleGraph

/-! A sharp finite-edge bound for the raw BFS relation. -/

/-- The finite simple graph underlying the unblocked raw list relation.  Self-loops are omitted:
they never contribute to connectivity, while every nontrivial unblocked step is retained. -/
def unblockedListGraph (blocked : ℕ × ℕ) (edges : List (ℕ × ℕ)) : SimpleGraph ℕ where
  Adj left right := left ≠ right ∧ UnblockedListEdge blocked edges left right
  symm _ _ hstep := ⟨hstep.1.symm, unblockedListEdge_symm hstep.2⟩
  loopless := ⟨fun _ hstep => hstep.1 rfl⟩

private theorem unblockedListGraph_edgeSet_subset (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) :
    (unblockedListGraph blocked edges).edgeSet ⊆
      ↑((edges.map fun edge => s(edge.1, edge.2)).toFinset) := by
  intro edge hedge
  induction edge using Sym2.ind with
  | _ left right =>
      rw [SimpleGraph.mem_edgeSet] at hedge
      rcases (unblockedListEdge_iff blocked edges left right).mp hedge.2 with
        ⟨rawEdge, hrawEdge, _, horientation⟩
      change s(left, right) ∈ (edges.map fun edge => s(edge.1, edge.2)).toFinset
      rw [List.mem_toFinset, List.mem_map]
      refine ⟨rawEdge, hrawEdge, ?_⟩
      rcases rawEdge with ⟨rawLeft, rawRight⟩
      rcases horientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap

private theorem unblockedListGraph_edgeFinset_card_le (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) [Fintype (unblockedListGraph blocked edges).edgeSet] :
    let graph := unblockedListGraph blocked edges
    let rawEdges := (edges.map fun edge => s(edge.1, edge.2)).toFinset
    graph.edgeFinset.card ≤ rawEdges.card := by
  let graph := unblockedListGraph blocked edges
  let rawEdges := (edges.map fun edge => s(edge.1, edge.2)).toFinset
  apply Finset.card_le_card
  intro edge hedge
  rw [SimpleGraph.mem_edgeFinset] at hedge
  exact unblockedListGraph_edgeSet_subset blocked edges hedge

private theorem unblockedListGraph_reachable_of_reflTransGen (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) {left right : ℕ}
    (hpath : Relation.ReflTransGen (UnblockedListEdge blocked edges) left right) :
    (unblockedListGraph blocked edges).Reachable left right := by
  rw [SimpleGraph.reachable_eq_reflTransGen]
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep inductionHypothesis =>
      rename_i middle final
      by_cases heq : middle = final
      · subst_vars
        exact inductionHypothesis
      · exact inductionHypothesis.tail ⟨heq, hstep⟩

private theorem walk_to_unblockedWalkLength (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) {left right : ℕ}
    (walk : (unblockedListGraph blocked edges).Walk left right) :
    UnblockedWalkLength blocked edges walk.length left right := by
  induction walk with
  | nil => exact UnblockedWalkLength.refl _
  | cons hstep walk inductionHypothesis =>
      exact UnblockedWalkLength.step hstep.2 inductionHypothesis

/-- Every relationally reachable endpoint has a raw unblocked walk using at most as many steps as
there are records in the finite edge list.  This is stronger than the `Nodup` version needed by the
production graph-realization layer: duplicate and reverse-duplicate records are also permitted. -/
theorem exists_unblockedWalkLength_le_edges_length (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) {left right : ℕ}
    (hpath : Relation.ReflTransGen (UnblockedListEdge blocked edges) left right) :
    ∃ length, length ≤ edges.length ∧
      UnblockedWalkLength blocked edges length left right := by
  let graph := unblockedListGraph blocked edges
  let rawEdges := (edges.map fun edge => s(edge.1, edge.2)).toFinset
  have hedgeSetFinite : graph.edgeSet.Finite :=
    Set.Finite.subset rawEdges.finite_toSet (unblockedListGraph_edgeSet_subset blocked edges)
  letI : Fintype graph.edgeSet := hedgeSetFinite.fintype
  have hreachable : graph.Reachable left right :=
    unblockedListGraph_reachable_of_reflTransGen blocked edges hpath
  rcases hreachable.exists_isPath with ⟨walk, hwalk⟩
  refine ⟨walk.length, ?_, walk_to_unblockedWalkLength blocked edges walk⟩
  calc
    walk.length ≤ graph.edgeFinset.card := hwalk.isTrail.length_le_card_edgeFinset
    _ ≤ rawEdges.card := unblockedListGraph_edgeFinset_card_le blocked edges
    _ ≤ (edges.map fun edge => s(edge.1, edge.2)).length :=
      List.toFinset_card_le (edges.map fun edge => s(edge.1, edge.2))
    _ = edges.length := by simp

/-- The sharp finite-fuel fact from an arbitrary singleton start. -/
theorem reachableWithoutEdge_complete_from_start_of_reflTransGen (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) (start : ℕ) {atom : ℕ}
    (hpath : Relation.ReflTransGen
      (UnblockedListEdge blocked edges) start atom) :
    atom ∈ reachableWithoutEdge blocked (edges.length + 1) edges [start] [start] := by
  rcases exists_unblockedWalkLength_le_edges_length blocked edges hpath with
    ⟨length, hlength, hwalk⟩
  exact reachableWithoutEdge_from_start_complete blocked edges start
    (Nat.le_trans hlength (Nat.le_add_right edges.length 1)) hwalk

/-- The exact fuel fact used by production bridge detection. -/
theorem reachableWithoutEdge_complete_of_reflTransGen (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) {atom : ℕ}
    (hpath : Relation.ReflTransGen
      (UnblockedListEdge blocked edges) blocked.1 atom) :
    atom ∈ reachableWithoutEdge blocked (edges.length + 1) edges [blocked.1] [blocked.1] :=
  reachableWithoutEdge_complete_from_start_of_reflTransGen
    blocked edges blocked.1 hpath

end RawMolecule
end OneCenter
end TetraStereo
