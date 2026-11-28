import TetraStereo.Engine.RingUnorderedSphereReading
import Mathlib.Data.Multiset.FinsetOps

/-! Rank intervals of emitting keys in one complete unordered sphere. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingUnorderedRankIntervals
variable {α : Type} [LinearOrder α]

def visible (m : Multiset α) (see : α → Option Bool) := m.filter (fun x => (see x).isSome)

def lower (m : Multiset α) (x : α) := (m.filter (x < ·)).card

def upper (m : Multiset α) (x : α) := (m.filter (x ≤ ·)).card

def bit (m : Multiset α) (see : α → Option Bool) (k : Nat) : Bool :=
  let v := visible m see
  decide (∃ x ∈ v.toFinset, see x = some true ∧ lower v x ≤ k ∧ k < upper v x)

def word (m : Multiset α) (see : α → Option Bool) : List Bool :=
  (List.range (visible m see).card).map (bit m see)

theorem bit_iff (m : Multiset α) (see : α → Option Bool) (k : Nat) :
    bit m see k = true ↔ ∃ x ∈ m, see x = some true ∧
      lower (visible m see) x ≤ k ∧ k < upper (visible m see) x := by
  simp only [bit,decide_eq_true_eq,Multiset.mem_toFinset,visible,Multiset.mem_filter]
  constructor
  · rintro ⟨x,⟨hx,_⟩,out,bounds⟩
    exact ⟨x,hx,out,bounds⟩
  · rintro ⟨x,hx,out,bounds⟩
    exact ⟨x,⟨hx,by simp [out]⟩,out,bounds⟩

private theorem index_iff (xs : List α) (desc : xs.Pairwise (· ≥ ·)) (x : α) (k : Nat) :
    lower (↑xs) x ≤ k ∧ k < upper (↑xs) x ↔ xs[k]? = some x := by
  induction xs generalizing k with
  | nil => simp [lower,upper]
  | cons a xs ih =>
    have pair := List.pairwise_cons.mp desc
    by_cases less : x < a
    · have weak := le_of_lt less
      cases k with
      | zero => simp [lower,upper,less,weak,ne_of_gt less]
      | succ k => simpa [lower,upper,less,weak] using ih pair.2 k
    · by_cases eqn : a = x
      · subst a
        have empty : ((↑xs : Multiset α).filter (x < ·)) = 0 := by
          apply Multiset.eq_zero_of_forall_notMem
          intro y hy
          obtain ⟨mem,lt⟩ := Multiset.mem_filter.mp hy
          exact (not_lt_of_ge (pair.1 y mem)) lt
        have lo : lower (↑xs) x = 0 := congrArg Multiset.card empty
        have headLo : lower (↑(x::xs)) x = 0 := by
          change (Multiset.filter (x < ·) (x ::ₘ ↑xs)).card = 0
          rw [Multiset.filter_cons_of_neg _ (lt_irrefl _),empty]; rfl
        have headHi : upper (↑(x::xs)) x = upper (↑xs) x + 1 := by simp [upper]
        cases k with
        | zero => simp [headLo,headHi]
        | succ k => simpa [headLo,headHi,lo] using ih pair.2 k
      · have weak : ¬ x ≤ a := fun h => eqn (le_antisymm (le_of_not_gt less) h)
        have empty : ((↑xs : Multiset α).filter (x ≤ ·)) = 0 := by
          apply Multiset.eq_zero_of_forall_notMem
          intro y hy
          obtain ⟨mem,le⟩ := Multiset.mem_filter.mp hy
          exact weak (le.trans (pair.1 y mem))
        have absent : x ∉ xs := fun hx => weak (pair.1 x hx)
        have high : upper (↑(a::xs)) x = 0 := by
          change (Multiset.filter (x ≤ ·) (a ::ₘ ↑xs)).card = 0
          rw [Multiset.filter_cons_of_neg _ weak,empty]; rfl
        cases k with
        | zero => simp [high,eqn]
        | succ k =>
          simp only [high,Nat.not_lt_zero,and_false,List.getElem?_cons_succ,false_iff]
          exact fun hit => absent (List.mem_of_getElem? hit)

omit [LinearOrder α] in
private theorem filterMap_eq (see : α → Option Bool) (row : List α)
    (emits : ∀ x ∈ row, (see x).isSome) :
    row.filterMap see = row.map (fun x => (see x).getD false) := by
  induction row with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨value,out⟩ := Option.isSome_iff_exists.mp (emits a (by simp))
    simp [out,ih (fun x hx => emits x (by simp [hx]))]

theorem word_exact (see : α → Option Bool) (xs : List α) :
    word (↑xs) see = RingUnorderedSphereReading.readRow id see xs := by
  let v := visible (↑xs) see
  let row := RingStereoSiblingPass.order id (xs.filter fun x => (see x).isSome)
  have legal := RingStereoSiblingPass.legal_order id (xs.filter fun x => (see x).isSome)
  have desc : row.Pairwise (· ≥ ·) := by simpa [row] using legal.descending
  have same : (↑row : Multiset α) = v := by
    simpa [v,visible,row] using Multiset.coe_eq_coe.mpr legal.perm
  have emits (x : α) (hx : x ∈ row) : (see x).isSome := by
    have mem := legal.perm.mem_iff.mp hx
    exact (List.mem_filter.mp mem).2
  have mapped := filterMap_eq see row emits
  have rhs : RingUnorderedSphereReading.readRow id see xs = row.filterMap see := by
    simp [RingUnorderedSphereReading.readRow,row]
  rw [rhs,mapped]
  apply List.ext_getElem
  · simpa [word,v] using congrArg Multiset.card same.symm
  · intro k hk hl
    have inside : k < row.length := by simpa using hl
    have entry : row[k]? = some row[k] := List.getElem?_eq_getElem inside
    have present := List.getElem_mem inside
    simp only [word,List.getElem_map,List.getElem_range]
    apply Bool.eq_iff_iff.mpr
    rw [bit_iff]
    constructor
    · rintro ⟨x,_,out,bounds⟩
      have idx := (index_iff row desc x k).mp (same.symm ▸ bounds)
      have eqn := Option.some.inj (entry.symm.trans idx)
      simp [eqn,out]
    · intro h
      have has := emits _ present
      obtain ⟨value,out⟩ := Option.isSome_iff_exists.mp has
      have val : value = true := by simpa [out] using h
      have inV : row[k] ∈ v := same ▸ (show row[k] ∈ (↑row : Multiset α) from present)
      exact ⟨row[k],(Multiset.mem_filter.mp inV).1,out.trans (congrArg some val),
        same ▸ (index_iff row desc _ k).mpr entry⟩

end TetraStereo.Engine.RingUnorderedRankIntervals
assert_kernel_only TetraStereo.Engine.RingUnorderedRankIntervals.bit_iff
assert_kernel_only TetraStereo.Engine.RingUnorderedRankIntervals.word_exact
