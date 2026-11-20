import TetraStereo.OneCenter.LocalizedChemicalRingCompoundReplay
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Descending lists align comparison-equivalence classes even when the concrete records differ.
This lets promoted sibling orders from different parent layouts be compared using the shared
actual comparator, without equating their layout-dependent independent keys. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingComparisonClasses

variable {α : Type*} (cmp : α → α → Ordering) [Std.TransCmp cmp]

def tieSetoid : Setoid α where
  r a b := cmp a b = .eq
  iseqv := ⟨fun _ => Std.ReflCmp.compare_self,
    fun h => Std.OrientedCmp.eq_symm h, fun h h' => Std.TransCmp.eq_trans h h'⟩

def classCompare (a b : Quotient (tieSetoid cmp)) : Ordering :=
  Quotient.liftOn₂ a b cmp (by
    intro a b a' b' ha hb
    exact (Std.TransCmp.congr_left ha).trans (Std.TransCmp.congr_right hb))

theorem classes_antisymm (a b : Quotient (tieSetoid cmp))
    (ab : classCompare cmp a b ≠ .lt) (ba : classCompare cmp b a ≠ .lt) : a = b := by
  induction a, b using Quotient.inductionOn₂ with
  | h a b =>
      apply Quotient.sound
      change cmp a b = .eq
      change cmp a b ≠ .lt at ab
      change cmp b a ≠ .lt at ba
      have swapped := Std.OrientedCmp.eq_swap (cmp := cmp) (a := b) (b := a)
      cases h : cmp a b <;> simp_all

theorem sorted_ties_of_perms {left middle right middleRight : List α}
    (perm : left.Perm middle)
    (permR : right.Perm middleRight)
    (matched : List.Forall₂ (fun a b => cmp a b = .eq) middle middleRight)
    (descendingL : left.Pairwise (fun a b => cmp a b ≠ .lt))
    (descendingR : right.Pairwise (fun a b => cmp a b ≠ .lt)) :
    List.Forall₂ (fun a b => cmp a b = .eq) left right := by
  let q : α → Quotient (tieSetoid cmp) := Quotient.mk _
  have equal : middle.map q = middleRight.map q := by
    clear perm permR descendingL descendingR
    induction matched with
    | nil => rfl
    | cons h _ ih =>
        have heads : q _ = q _ := Quotient.sound h
        simp only [List.map_cons, heads, ih]
  have quotientPerm := ((perm.map q).trans (List.Perm.of_eq equal)).trans (permR.symm.map q)
  have lSorted : (left.map q).Pairwise (fun a b => classCompare cmp a b ≠ .lt) := by
    simpa only [List.pairwise_map] using descendingL
  have rSorted : (right.map q).Pairwise (fun a b => classCompare cmp a b ≠ .lt) := by
    simpa only [List.pairwise_map] using descendingR
  have same := List.Perm.eq_of_pairwise
    (le := fun a b => classCompare cmp a b ≠ .lt)
    (fun a b _ _ ha hb => classes_antisymm cmp a b ha hb) lSorted rSorted quotientPerm
  have pairs : List.Forall₂ (fun a b => q a = q b) left right := by
    have mapped : List.Forall₂ Eq (left.map q) (right.map q) := by
      rw [List.forall₂_eq_eq_eq]
      exact same
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using mapped
  exact pairs.imp (fun _ _ h => Quotient.exact h)

theorem sorted_ties {left middle right : List α}
    (perm : left.Perm middle)
    (matched : List.Forall₂ (fun a b => cmp a b = .eq) middle right)
    (descendingL : left.Pairwise (fun a b => cmp a b ≠ .lt))
    (descendingR : right.Pairwise (fun a b => cmp a b ≠ .lt)) :
    List.Forall₂ (fun a b => cmp a b = .eq) left right :=
  sorted_ties_of_perms cmp perm (List.Perm.refl right) matched descendingL descendingR

end TetraStereo.OneCenter.LocalizedChemicalRingComparisonClasses

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComparisonClasses.sorted_ties
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComparisonClasses.sorted_ties_of_perms
