import TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
import TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

namespace FixtureGraphDomain

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
open TetraStereo.OneCenter.AcyclicCutBranchAutomorphism

abbrev Atom := input.certified.Atom
abbrev Graph := input.certified.moleculeGraph

/-- The exact source graph has no positive bond whose order exceeds one. -/
theorem simpleBonded : Graph.SimpleBonded := by
  intro u v adjacent
  fin_cases u <;> fin_cases v <;> revert adjacent <;> decide +kernel

/-- Every source atom is formally neutral, hence the graph has constant formal charge. -/
theorem constantFormalCharge : ConstantFormalCharge Graph := by
  refine ⟨0, ?_⟩
  intro a
  fin_cases a <;> decide +kernel

/-- The source record checker establishes that this admitted input carries no localized double
bond records. -/
theorem noLocalizedDoubleBondRecords :
    input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords := by
  exact (source.molecule.noLocalizedDoubleBondRecords?_eq_true_iff).mp source_noDoubleTest

/-- Distance from atom zero in the actual 33-atom source tree. -/
def height (a : Atom) : Nat :=
  match a.val with
  | 0 => 0
  | 1 | 2 | 3 | 18 => 1
  | 4 | 11 | 19 | 26 => 2
  | 5 | 6 | 7 | 12 | 13 | 14 | 20 | 21 | 22 | 27 | 28 | 29 => 3
  | _ => 4

/-- The unique lower-height neighbor in the source tree. -/
def parent (a : Atom) : Atom :=
  match a.val with
  | 1 | 2 | 3 | 18 => ⟨0, by decide⟩
  | 4 | 11 => ⟨3, by decide⟩
  | 5 | 6 | 7 => ⟨4, by decide⟩
  | 8 | 9 | 10 => ⟨7, by decide⟩
  | 12 | 13 | 14 => ⟨11, by decide⟩
  | 15 | 16 | 17 => ⟨14, by decide⟩
  | 19 | 26 => ⟨18, by decide⟩
  | 20 | 21 | 22 => ⟨19, by decide⟩
  | 23 | 24 | 25 => ⟨22, by decide⟩
  | 27 | 28 | 29 => ⟨26, by decide⟩
  | 30 | 31 | 32 => ⟨29, by decide⟩
  | _ => ⟨0, by decide⟩

/-- Every actual source edge changes this rooted-tree height by exactly one, and a downward edge
points to the named parent. -/
theorem adj_height_case {u v : Atom} (h : Graph.Adj u v) :
    height u + 1 = height v ∨ (height v + 1 = height u ∧ v = parent u) := by
  revert h
  fin_cases u <;> fin_cases v <;> decide +kernel

theorem height_adj {u v : Atom} (h : Graph.Adj u v) :
    height u + 1 = height v ∨ height v + 1 = height u := by
  rcases adj_height_case h with forward | ⟨backward, _⟩
  · exact Or.inl forward
  · exact Or.inr backward

theorem eq_parent_of_lower {u v : Atom} (h : Graph.Adj u v)
    (step : height v + 1 = height u) : v = parent u := by
  rcases adj_height_case h with forward | ⟨backward, parentEq⟩
  · omega
  · exact parentEq

theorem height_unique_lower (u v w : Atom) (hv : Graph.Adj u v)
    (hw : Graph.Adj u w) (pv : height v + 1 = height u)
    (pw : height w + 1 = height u) : v = w := by
  rw [eq_parent_of_lower hv pv, eq_parent_of_lower hw pw]

/-- A cycle based at `u` has two distinct adjacent vertices in its support. -/
theorem exists_two_cycle_adjacent {X : Type*} {G : SimpleGraph X} {u : X}
    {c : G.Walk u u} (hc : c.IsCycle) :
    ∃ a b : X, a ≠ b ∧ G.Adj u a ∧ G.Adj u b ∧ a ∈ c.support ∧ b ∈ c.support := by
  have hlen : 3 ≤ c.length := SimpleGraph.Walk.IsCycle.three_le_length hc
  refine ⟨c.getVert 1, c.getVert (c.length - 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro equal
    have h1 : 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
      simp only [Set.mem_setOf_eq]; omega
    have h2 : c.length - 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
      simp only [Set.mem_setOf_eq]; omega
    have same := SimpleGraph.Walk.IsCycle.getVert_injOn hc h1 h2 equal
    omega
  · have step := SimpleGraph.Walk.adj_getVert_succ c (i := 0) (by omega)
    simpa using step
  · have step := SimpleGraph.Walk.adj_getVert_succ c (i := c.length - 1) (by omega)
    have hlast : c.getVert (c.length - 1 + 1) = u := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ c.length)]
      exact SimpleGraph.Walk.getVert_length c
    have backward : G.Adj (c.getVert (c.length - 1)) u := by
      simpa [hlast] using step
    exact G.symm backward
  · exact SimpleGraph.Walk.getVert_mem_support c 1
  · exact SimpleGraph.Walk.getVert_mem_support c (c.length - 1)

/-- A finite cycle has a maximum-height vertex; both distinct cycle-neighbors must be lower. -/
theorem isAcyclic_of_height_unique_lower {X : Type*} [DecidableEq X]
    {G : SimpleGraph X} (rank : X → Nat)
    (rankStep : ∀ {u v}, G.Adj u v → rank u + 1 = rank v ∨ rank v + 1 = rank u)
    (uniqueLower : ∀ u v w, G.Adj u v → G.Adj u w →
      rank v + 1 = rank u → rank w + 1 = rank u → v = w) : G.IsAcyclic := by
  intro u c hc
  classical
  let s : Finset X := c.support.toFinset
  have hs : s.Nonempty := ⟨u, by simp [s]⟩
  obtain ⟨w, hwmem, hwmax⟩ := Finset.exists_mem_eq_sup s hs rank
  have hwSupport : w ∈ c.support := by simpa [s] using hwmem
  have hmax : ∀ x ∈ s, rank x ≤ rank w := by
    intro x hx
    calc rank x ≤ s.sup rank := Finset.le_sup hx
      _ = rank w := hwmax
  have rotatedCycle : (c.rotate hwSupport).IsCycle := hc.rotate hwSupport
  obtain ⟨a, b, hab, hwa, hwb, haMem, hbMem⟩ :=
    exists_two_cycle_adjacent rotatedCycle
  have haSupport : a ∈ c.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c hwSupport]
    exact haMem
  have hbSupport : b ∈ c.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c hwSupport]
    exact hbMem
  have haMemS : a ∈ s := by simpa [s] using haSupport
  have hbMemS : b ∈ s := by simpa [s] using hbSupport
  have haLower : rank a + 1 = rank w := by
    rcases rankStep hwa with up | down
    · have bound := hmax a haMemS
      omega
    · exact down
  have hbLower : rank b + 1 = rank w := by
    rcases rankStep hwb with up | down
    · have bound := hmax b hbMemS
      omega
    · exact down
  exact hab (uniqueLower w a b hwa hwb haLower hbLower)

/-- A cycle's maximum-height vertex would have two distinct lower neighbors, contradicting the
fixture's unique-parent edge table. -/
theorem acyclic : Graph.Acyclic := by
  unfold MoleculeGraph.Acyclic
  exact isAcyclic_of_height_unique_lower height
    (fun {u v} h => height_adj h)
    height_unique_lower

end FixtureGraphDomain

assert_kernel_only FixtureGraphDomain.simpleBonded
assert_kernel_only FixtureGraphDomain.constantFormalCharge
assert_kernel_only FixtureGraphDomain.noLocalizedDoubleBondRecords
assert_kernel_only FixtureGraphDomain.height
assert_kernel_only FixtureGraphDomain.parent
assert_kernel_only FixtureGraphDomain.adj_height_case
assert_kernel_only FixtureGraphDomain.height_adj
assert_kernel_only FixtureGraphDomain.eq_parent_of_lower
assert_kernel_only FixtureGraphDomain.height_unique_lower
assert_kernel_only FixtureGraphDomain.exists_two_cycle_adjacent
assert_kernel_only FixtureGraphDomain.isAcyclic_of_height_unique_lower
assert_kernel_only FixtureGraphDomain.acyclic
