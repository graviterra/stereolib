import TetraStereo.Engine.RingOrdinaryPairRefusal
import TetraStereo.Engine.RingRetainedChemicalPreorder

set_option autoImplicit false

namespace TetraStereo.Engine.RingSingleTieCompletion
open RingActivePairReport (Slot Reader Matrix matrix?)
open RingOrdinaryPairRefusal (score table ids Valid Certificate)
open RingChemicalPriority.ReferenceFrame (orderAt coherent marks)

def unitScore : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

private theorem unit_order (o : Ordering) : compare (unitScore o) 0 = o := by cases o <;> rfl

private theorem unit_zero (o : Ordering) : unitScore o = 0 ↔ o = .eq := by
  cases o <;> decide

private theorem nonlower (o : Ordering) : (o != .lt) = o.isGE := by cases o <;> rfl

private theorem listed (s : Slot) : s.val ∈ ids := by fin_cases s <;> decide

private theorem slot_of_member {n : Nat} (h : n ∈ ids) : ∃ s : Slot, s.val = n := by
  have : n < 4 := by simp [ids] at h; omega
  exact ⟨⟨n,this⟩,rfl⟩

/-- Reversal and transitivity of the molecular priority keys establish the actual
finite preorder checks on the scores. No extra hypothesis about the matrix is needed. -/
theorem keys_coherent {α : Type} [Ord α] [Std.TransOrd α] (key : Slot → α)
    {r : Reader} (m : Matrix r) (rev : Bool)
    (obs : ∀ x y : Slot, orderAt (table m rev) false x.val y.val = some (compare (key x) (key y))) :
    coherent ids (table m rev) false = true := by
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨x,rfl⟩ := slot_of_member hi
  apply List.all_eq_true.mpr
  intro j hj
  obtain ⟨y,rfl⟩ := slot_of_member hj
  simp only [Bool.and_eq_true]
  refine ⟨⟨by rw [obs]; rfl,?_⟩,?_⟩
  · rw [obs,obs,Option.map_some]
    apply beq_iff_eq.mpr
    exact congrArg some (Std.OrientedCmp.eq_swap (cmp := compare))
  · apply List.all_eq_true.mpr
    intro k hk
    obtain ⟨z,rfl⟩ := slot_of_member hk
    simp only [obs,Option.any_some,nonlower]
    have trans := Std.TransOrd.isGE_trans (a := key x) (b := key y) (c := key z)
    cases hxy : (compare (key x) (key y)).isGE <;>
      cases hyz : (compare (key y) (key z)).isGE <;> first | rfl | exact trans hxy hyz

private theorem marked_pair {α : Type} [Ord α] (key : Slot → α)
    {r : Reader} (m : Matrix r) (rev : Bool) {a b : Slot} (ab : a < b)
    (tie : ∀ x y : Slot, x ≠ y →
      (compare (key x) (key y) = .eq ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a)))
    (obs : ∀ x y : Slot, orderAt (table m rev) false x.val y.val = some (compare (key x) (key y))) :
    marks ids (table m rev) = [a.val,b.val] := by
  let marked (n : Nat) := decide (n = a.val ∨ n = b.val)
  have retain : marks ids (table m rev) = ids.filter marked := by
    apply List.filter_congr
    intro n hn
    obtain ⟨x,rfl⟩ := slot_of_member hn
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Bool.and_eq_true,marked,decide_eq_true_eq,bne_iff_ne,beq_iff_eq]
    constructor
    · rintro ⟨j,hj,ne,eqn⟩
      obtain ⟨y,rfl⟩ := slot_of_member hj
      rw [obs] at eqn
      rcases (tie x y (fun h => ne (congrArg Fin.val h))).mp (Option.some.inj eqn) with h | h
      · exact .inl (congrArg Fin.val h.1)
      · exact .inr (congrArg Fin.val h.1)
    · rintro (h|h)
      · have hx : x = a := Fin.ext h
        subst x
        exact ⟨b.val,listed b,ne_of_lt ab,by rw [obs,(tie a b (ne_of_lt ab)).mpr (.inl ⟨rfl,rfl⟩)]⟩
      · have hx : x = b := Fin.ext h
        subst x
        exact ⟨a.val,listed a,(ne_of_lt (show a.val < b.val from ab)).symm,by rw [obs,(tie b a (ne_of_lt ab).symm).mpr (.inr ⟨rfl,rfl⟩)]⟩
  rw [retain]
  change ids.filter (fun n => decide (n = a.val ∨ n = b.val)) = _
  have all : ∀ x y : Slot, x < y →
      ids.filter (fun n => decide (n = x.val ∨ n = y.val)) = [x.val,y.val] := by decide
  exact all a b ab

/-- If every directed source comparison returns its constitutional sign on both
geometries, one indistinguishable pair is sufficient to force a certified refusal
at the executable matrix and refusal entry points. -/
theorem complete {α : Type} [Ord α] [Std.TransOrd α] (key : Slot → α) (r : Reader)
    {a b : Slot} (ab : a < b)
    (tie : ∀ x y : Slot, x ≠ y →
      (compare (key x) (key y) = .eq ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a)))
    (edges : ∀ x y : Slot, x ≠ y →
      let s := unitScore (compare (key x) (key y))
      r x y = some (s,s)) :
    ∃ m : Matrix r, matrix? r = some m ∧ Valid m a b ∧
      ∃ c : Certificate m, RingOrdinaryPairRefusal.find? m = some c := by
  have total := (RingActivePairReport.matrix?_complete r).mpr fun x y ne => by rw [edges x y ne]; rfl
  obtain ⟨m,built⟩ := Option.isSome_iff_exists.mp total
  have raw (rev : Bool) (x y : Slot) : score m rev x y = unitScore (compare (key x) (key y)) := by
    by_cases h : x = y
    · subst y; simp [score,unitScore]
    · have he := Option.some.inj ((m.found x y h).symm.trans (edges x y h))
      cases rev <;> simp [score,h,he]
  have valid : Valid m a b := by
    intro rev
    have obs (x y : Slot) : orderAt (table m rev) false x.val y.val = some (compare (key x) (key y)) := by
      rw [RingOrdinaryPairRefusal.read_table,raw,unit_order]
    exact ⟨keys_coherent key m rev obs,marked_pair key m rev ab tie obs,fun x y ne => by
      rw [raw,unit_zero,tie x y ne]⟩
  exact ⟨m,built,valid,Option.isSome_iff_exists.mp
    ((RingOrdinaryPairRefusal.find_iff m).mpr ⟨a,b,ab,valid⟩)⟩

open RingRetainedChemicalPreorder (Direction keyFor orderWord representative blockSizes)

/-- The measured constitutional block sizes pick out precisely one tied unordered
pair in the original four directions, even with the old parent in a nested frame. -/
theorem single_pair_iff {i : LocalizedChemicalRing.Input} {f : RingRetainedChemicalPreorder.Site i}
    (arms : Slot → Direction i f) :
    blockSizes (representative arms) = [1,1,2] ↔
      ∃ a b : Slot, a < b ∧ ∀ x y : Slot, x ≠ y →
        (compare (orderWord (keyFor (arms x))) (orderWord (keyFor (arms y))) = .eq ↔
          (x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
  have tied (x y : Slot) : compare (orderWord (keyFor (arms x))) (orderWord (keyFor (arms y))) = .eq ↔
      representative arms x = representative arms y := by
    rw [RingRetainedChemicalPreorder.class_iff,RingRetainedChemicalPreorder.table_order]
    simp
  simp only [tied]
  let c := representative arms
  have four : ∀ a b d e : Slot, let groups : Slot → Slot := ![a,b,d,e]
      blockSizes groups = [1,1,2] ↔ ∃ p q : Slot, p < q ∧ ∀ x y : Slot, x ≠ y →
        (groups x = groups y ↔ (x = p ∧ y = q) ∨ (x = q ∧ y = p)) := by decide +kernel
  have eta : representative arms = ![c 0,c 1,c 2,c 3] := by
    funext k; fin_cases k <;> rfl
  rw [eta]
  exact four (c 0) (c 1) (c 2) (c 3)

end TetraStereo.Engine.RingSingleTieCompletion

assert_kernel_only TetraStereo.Engine.RingSingleTieCompletion.keys_coherent
assert_kernel_only TetraStereo.Engine.RingSingleTieCompletion.complete
assert_kernel_only TetraStereo.Engine.RingSingleTieCompletion.single_pair_iff
