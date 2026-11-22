import TetraStereo.Engine.RingReferenceSchedule

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Publication
open OneCenter Recursive ReferenceDerivation
open InventoryPriority (Entries)

/-- A publication may follow another at any distance unless it is a strict
descendant of the earlier occurrence in this very rooted digraph. -/
def ChildrenFirst (rows : Entries) : Prop :=
  rows.Pairwise fun earlier later => ¬ Below earlier.1 later.1

theorem childrenFirst_of_distance {rows : Entries}
    (h : rows.Pairwise fun a b => b.1.length ≤ a.1.length) : ChildrenFirst rows := by
  apply h.imp
  intro a b le below
  exact Nat.not_lt_of_ge le below.2

theorem childrenFirst_byDistance (es : Entries) : ChildrenFirst (byDistance es) := by
  apply childrenFirst_of_distance
  simpa only [byDistance,decide_eq_true_eq] using (List.pairwise_mergeSort
    (le := fun (a b : List Nat × Option Reading) => decide (b.1.length ≤ a.1.length))
    (fun _ _ _ h1 h2 => decide_eq_true (le_trans (of_decide_eq_true h2) (of_decide_eq_true h1)))
    (fun a b => by simpa only [Bool.or_eq_true_iff,decide_eq_true_eq] using le_total b.1.length a.1.length) es)

/-- Every molecular dependency of the current occurrence is already visible
in the prefix, even if unrelated branches are interleaved at other distances. -/
theorem visible {published before after : Entries} {x : List Nat × Option Reading}
    (all : (before ++ x :: after).Perm published) (order : ChildrenFirst (before ++ x :: after))
    {y} (issued : y ∈ published) (deeper : Below x.1 y.1) : y ∈ before := by
  rcases List.mem_append.mp (all.mem_iff.mpr issued) with h | h
  · exact h
  · rcases List.mem_cons.mp h with rfl | later
    · exact (Nat.lt_irrefl _ deeper.2).elim
    · exact ((List.pairwise_cons.mp (List.pairwise_append.mp order).2.1).1 y later deeper).elim

/-- A signed proof system whose premises are at strict descendant addresses
can issue all its recorded facts from an initially empty store. The property
applies equally to positive facts and proved absences. -/
theorem replay {D : Entries → List Nat → Option Reading → Prop} {published rows : Entries} {p v}
    (localize : ∀ {es path value}, D es path value → ∀ {store : Entries},
      (∀ x ∈ es, Below path x.1 → x ∈ store) → D store path value)
    (root : D published p v) (issued : ∀ x ∈ published, D published x.1 x.2)
    (all : rows.Perm published) (order : ChildrenFirst rows) :
    D rows p v ∧ ∀ before x after, rows = before ++ x :: after → D before x.1 x.2 := by
  refine ⟨localize root (fun _ h _ => all.mem_iff.mpr h),?_⟩
  intro before x after eqn
  subst rows
  have member := all.mem_iff.mp (List.mem_append_right before (List.mem_cons_self (a := x) (l := after)))
  exact localize (issued _ member) (fun _ h deeper => visible all order h deeper)

/-- The original molecular derivation replays on every child-before-parent
order, even one that does not sort by distance. -/
theorem reference {m g p} (c : Certificate m g p) {rows : Entries}
    (all : rows.Perm c.published) (order : ChildrenFirst rows) : Scheduled m g p c.verdict rows :=
  replay (fun {_ _ _} d {_} keep => d.localize keep) c.derived c.issued all order

end TetraStereo.Engine.RingChemicalPriority.Publication

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Publication.visible
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Publication.childrenFirst_byDistance
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Publication.reference
