import TetraStereo.OneCenter.LocalizedRetainedCoherentSymmetry
import TetraStereo.KernelOnly
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

/-!
# Executable reachability after deleting a retained history

`historyResidualReachSet` computes the component of a source in the graph obtained by deleting
every vertex of a retained history.  Its iteration bound is the number of vertices in the finite
atom type.  The source is rejected when it is itself deleted, matching the first conjunct of
`RetainedCoherentSymmetry.InComponent`.

This module is only the finite reachability primitive.  It imposes no molecular acyclicity,
simple-bondedness, or rigidity assumptions.
-/

namespace TetraStereo.OneCenter.FiniteHistoryResidualReach

open RetainedCoherentSymmetry

variable {V : Type*} [Fintype V] [DecidableEq V]

def frontierStep (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter (fun w => ∃ u ∈ S, G.Adj u w)

def frontierIter (G : SimpleGraph V) [DecidableRel G.Adj] : Nat → Finset V → Finset V
  | 0, S => S
  | n + 1, S => frontierStep G (frontierIter G n S)

theorem subset_frontierStep (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    S ⊆ frontierStep G S := Finset.subset_union_left

theorem frontierIter_mono (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {k k' : Nat}
    (h : k ≤ k') : frontierIter G k S ⊆ frontierIter G k' S := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (subset_frontierStep G _)

theorem frontierIter_sound (G : SimpleGraph V) [DecidableRel G.Adj] (start : V) :
    ∀ (n : Nat) (v : V), v ∈ frontierIter G n {start} →
      Nonempty (G.Walk start v) := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp only [frontierIter, Finset.mem_singleton] at hv
      subst v
      exact ⟨SimpleGraph.Walk.nil⟩
  | succ n ih =>
      intro v hv
      simp only [frontierIter, frontierStep, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] at hv
      rcases hv with hv | ⟨u, hu, hadj⟩
      · exact ih v hv
      · obtain ⟨p⟩ := ih u hu
        exact ⟨p.concat hadj⟩

theorem walk_iter (G : SimpleGraph V) [DecidableRel G.Adj] (start : V) {a b : V}
    (p : G.Walk a b) : ∀ k : Nat, a ∈ frontierIter G k {start} →
      b ∈ frontierIter G (k + p.length) {start} := by
  induction p with
  | nil =>
      intro k ha
      simpa using ha
  | @cons u v w huv p ih =>
      intro k ha
      have hv : v ∈ frontierIter G (k + 1) {start} := by
        show v ∈ frontierStep G (frontierIter G k {start})
        simp only [frontierStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact Or.inr ⟨u, ha, huv⟩
      have htail := ih (k + 1) hv
      rw [SimpleGraph.Walk.length_cons,
        show k + (p.length + 1) = k + 1 + p.length by omega]
      exact htail

def historyResidualReachSet (m : MoleculeGraph V) (history : List V) (start : V) :
    Finset V :=
  if start ∈ history then ∅ else
    frontierIter (residualGraph m history) (Fintype.card V) {start}

theorem mem_historyResidualReachSet_iff (m : MoleculeGraph V) (history : List V)
    (start v : V) :
    v ∈ historyResidualReachSet m history start ↔
      InComponent m history start v := by
  by_cases hstart : start ∈ history
  · simp [historyResidualReachSet, InComponent, hstart]
  · constructor
    · intro hv
      have hv' : v ∈ frontierIter (residualGraph m history) (Fintype.card V) {start} := by
        simpa [historyResidualReachSet, hstart] using hv
      obtain ⟨p⟩ := frontierIter_sound (residualGraph m history) start _ v hv'
      exact ⟨hstart, ⟨p⟩⟩
    · rintro ⟨_, ⟨p⟩⟩
      have hlen : p.bypass.length < Fintype.card V := p.bypass_isPath.length_lt
      have hreach := walk_iter (residualGraph m history) start p.bypass 0
        (by simp [frontierIter])
      have hmem : v ∈ frontierIter (residualGraph m history)
          (0 + p.bypass.length) {start} := by
        simpa using hreach
      have hbounded := frontierIter_mono (residualGraph m history) {start}
        (show 0 + p.bypass.length ≤ Fintype.card V by omega) hmem
      simpa [historyResidualReachSet, hstart] using hbounded

end TetraStereo.OneCenter.FiniteHistoryResidualReach

assert_kernel_only TetraStereo.OneCenter.FiniteHistoryResidualReach.mem_historyResidualReachSet_iff

/-! ## Executable control (separate from the correspondence proof)

This five-member ring keeps the component of atom `2` after deleting both `0` and `1`. Deleting
only the immediate predecessor would incorrectly leave atom `0` reachable around the other side of
the ring. The second check covers a source that belongs to the deleted history.
-/

namespace TetraStereo.OneCenter.FiniteHistoryResidualReach.ExecutionControl

open FiniteHistoryResidualReach

def ringFive : MoleculeGraph (Fin 5) where
  atomZ := fun _ => 6
  bond := fun u v => if
      (u.val + 1) % 5 = v.val ∨ (v.val + 1) % 5 = u.val then 1 else 0
  bond_symm := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide
  bond_self := by
    intro u
    fin_cases u <;> decide

/-- info: true -/
#guard_msgs in
#eval decide (historyResidualReachSet ringFive [0, 1] 2 = {2, 3, 4})

/-- info: true -/
#guard_msgs in
#eval decide (historyResidualReachSet ringFive [0, 1] 0 = ∅)

end TetraStereo.OneCenter.FiniteHistoryResidualReach.ExecutionControl
