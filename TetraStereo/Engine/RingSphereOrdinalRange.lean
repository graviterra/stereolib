import TetraStereo.Engine.RingSphereReadings

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereOrdinalRange

open RingNestedActivePair (lowerScore)
open RingSphereReadings (Word across? ord)

private def low (xs : List Nat) := xs.mergeSort (fun a b => decide (a ≤ b))
private def high (xs : List Nat) := xs.mergeSort (fun a b => decide (b ≤ a))

private theorem low_sorted (xs : List Nat) : (low xs).Pairwise (· ≤ ·) := by
  have sorted := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun _ _ _ ab bc => decide_eq_true (le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)))
    (fun a b => by simpa using le_total a b) xs
  exact sorted.imp of_decide_eq_true

private theorem high_sorted (xs : List Nat) : (high xs).Pairwise (· ≥ ·) := by
  have sorted := List.pairwise_mergeSort (le := fun a b : Nat => decide (b ≤ a))
    (fun _ _ _ ab bc => decide_eq_true (le_trans (of_decide_eq_true bc) (of_decide_eq_true ab)))
    (fun a b => by simpa using le_total b a) xs
  exact sorted.imp of_decide_eq_true

private theorem sorted_min {xs ys : List Nat} (sorted : xs.Pairwise (· ≤ ·)) (p : xs.Perm ys) :
    xs ≤ ys := by
  induction xs generalizing ys with
  | nil => obtain rfl := p.symm.eq_nil; rfl
  | cons x xs ih =>
    cases ys with
    | nil => have eqn := p.eq_nil; contradiction
    | cons y ys =>
      by_cases eqn : x = y
      · subst y
        exact List.cons_le_cons _ (ih (List.pairwise_cons.mp sorted).2 p.cons_inv)
      · have member := p.mem_iff.mpr (List.mem_cons_self (a := y) (l := ys))
        have hy := (List.mem_cons.mp member).resolve_left (Ne.symm eqn)
        exact le_of_lt (List.Lex.rel (lt_of_le_of_ne ((List.pairwise_cons.mp sorted).1 y hy) eqn))

private theorem sorted_max {xs ys : List Nat} (sorted : xs.Pairwise (· ≥ ·)) (p : xs.Perm ys) :
    ys ≤ xs := by
  induction xs generalizing ys with
  | nil => obtain rfl := p.symm.eq_nil; rfl
  | cons x xs ih =>
    cases ys with
    | nil => have eqn := p.eq_nil; contradiction
    | cons y ys =>
      by_cases eqn : x = y
      · subst y
        exact List.cons_le_cons _ (ih (List.pairwise_cons.mp sorted).2 p.cons_inv)
      · have member := p.mem_iff.mpr (List.mem_cons_self (a := y) (l := ys))
        have hy := (List.mem_cons.mp member).resolve_left (Ne.symm eqn)
        exact le_of_lt (List.Lex.rel (lt_of_le_of_ne ((List.pairwise_cons.mp sorted).1 y hy) (Ne.symm eqn)))

private theorem append_lt {a b : List Nat} (h : a < b) (same : a.length = b.length) (u v : List Nat) :
    a ++ u < b ++ v := by
  change List.Lex (· < ·) a b at h
  induction h with
  | nil => simp at same
  | rel ab => exact List.Lex.rel ab
  | cons _ ih => exact List.Lex.cons (ih (by simpa using same))

private theorem append_le {a b u v : List Nat} (same : a.length = b.length)
    (ab : a ≤ b) (uv : u ≤ v) : a ++ u ≤ b ++ v := by
  rcases lt_or_eq_of_le ab with lt | rfl
  · exact le_of_lt (append_lt lt same u v)
  · induction a with
    | nil => exact uv
    | cons x xs ih => exact List.cons_le_cons x (ih rfl le_rfl)

/-- Lexicographically least and greatest flattened words realizable while
each projected reading stays inside its original distance sphere. -/
def minimumWord (rows : List (List Nat)) := rows.flatMap low

def maximumWord (rows : List (List Nat)) := rows.flatMap high

private theorem low_perm (xs : List Nat) : (low xs).Perm xs := List.mergeSort_perm ..
private theorem high_perm (xs : List Nat) : (high xs).Perm xs := List.mergeSort_perm ..

theorem attainable (rows : List (List Nat)) : Word rows (minimumWord rows) ∧ Word rows (maximumWord rows) := by
  have choices : List.Forall₂ List.Perm rows (rows.map low) ∧ List.Forall₂ List.Perm rows (rows.map high) := by
    induction rows with
    | nil => exact ⟨.nil,.nil⟩
    | cons x xs ih => exact ⟨.cons (low_perm x).symm ih.1,.cons (high_perm x).symm ih.2⟩
  exact ⟨⟨_,choices.1,rfl⟩,⟨_,choices.2,rfl⟩⟩

theorem bounds {rows : List (List Nat)} {x} (hx : Word rows x) :
    minimumWord rows ≤ x ∧ x ≤ maximumWord rows := by
  obtain ⟨ys,chosen,rfl⟩ := hx
  induction chosen with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | @cons a b as bs p _ ih =>
    have lo := (low_perm a).trans p
    have hi := (high_perm a).trans p
    exact ⟨append_le lo.length_eq (sorted_min (low_sorted a) lo) ih.1,
      append_le hi.length_eq.symm (sorted_max (high_sorted a) hi) ih.2⟩

private theorem word_length {rows : List (List Nat)} {x} (h : Word rows x) : x.length = rows.flatten.length := by
  obtain ⟨_,choice,rfl⟩ := h
  induction choice with
  | nil => rfl
  | cons p _ ih => simp only [List.flatten_cons,List.length_append,p.length_eq,ih]

private theorem score_bounds (x y : List Nat) : -1 ≤ lowerScore x y ∧ lowerScore x y ≤ 1 := by
  induction x generalizing y with
  | nil => simp [lowerScore]
  | cons a as ih =>
    cases y with
    | nil => simp [lowerScore]
    | cons b bs => simp only [lowerScore]; split_ifs <;> first | exact ih bs | decide

private theorem swap (x y : List Nat) : lowerScore x y = -lowerScore y x := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a as ih =>
    cases y with
    | nil => rfl
    | cons b bs =>
      by_cases eqn : a = b
      · subst b; simpa only [lowerScore,if_true] using ih bs
      · simp only [lowerScore,if_neg eqn,if_neg (Ne.symm eqn)]
        split_ifs <;> omega

private theorem mono_left {x y : List Nat} (xy : x ≤ y) (sz : x.length = y.length) (z : List Nat) :
    lowerScore x z ≤ lowerScore y z := by
  induction x generalizing y z with
  | nil => have empty : y = [] := List.length_eq_zero_iff.mp sz.symm; subst y; rfl
  | cons a as ih =>
    cases y with
    | nil => simp at sz
    | cons b bs =>
      by_cases eqn : a = b
      · subst b
        have tail : as ≤ bs := by
          rcases lt_or_eq_of_le xy with lt | equal
          · rcases List.cons_lt_cons_iff.mp lt with less | ⟨_,inner⟩
            · exact False.elim (Nat.lt_irrefl a less)
            · exact le_of_lt inner
          · exact le_of_eq (List.cons.inj equal).2
        cases z with
        | nil => rfl
        | cons c cs =>
          simp only [lowerScore]
          split <;> first | exact ih tail (by simpa using sz) cs | rfl
      · have strict : a < b := by
          rcases lt_or_eq_of_le xy with lt | equal
          · rcases List.cons_lt_cons_iff.mp lt with less | ⟨same,_⟩
            · exact less
            · contradiction
          · exact False.elim (eqn (List.cons.inj equal).1)
        cases z with
        | nil => rfl
        | cons c cs =>
          have lower := score_bounds as cs
          have upper := score_bounds bs cs
          simp only [lowerScore]
          split_ifs <;> omega

private theorem anti_right (x : List Nat) {y z : List Nat} (yz : y ≤ z) (sz : y.length = z.length) :
    lowerScore x z ≤ lowerScore x y := by
  have mono := mono_left yz sz x
  rw [swap x z,swap x y]
  omega

/-- Two comparisons suffice. The endpoint at the least left and greatest
right word gives the minimum signed outcome, and the other endpoint its maximum. -/
def ordinal? (a b : List (List Nat)) : Option Int :=
  let first := lowerScore (minimumWord a) (maximumWord b)
  let last := lowerScore (maximumWord a) (minimumWord b)
  if first = last then some first else none

theorem exact_bounds {a b : List (List Nat)} {x y} (hx : Word a x) (hy : Word b y) :
    lowerScore (minimumWord a) (maximumWord b) ≤ lowerScore x y ∧
    lowerScore x y ≤ lowerScore (maximumWord a) (minimumWord b) := by
  have ax := bounds hx
  have by' := bounds hy
  have al := word_length (attainable a).1
  have au := word_length (attainable a).2
  have bl := word_length (attainable b).1
  have bu := word_length (attainable b).2
  exact ⟨le_trans (mono_left ax.1 (al.trans (word_length hx).symm) _)
      (anti_right _ by'.2 ((word_length hy).trans bu.symm)),
    le_trans (mono_left ax.2 ((word_length hx).trans au.symm) _)
      (anti_right _ by'.1 (bl.trans (word_length hy).symm))⟩

/-- Exact equality with exhaustive enumeration also for unequal flattened
lengths, when the source comparator stops as soon as either word is exhausted. -/
theorem ordinal_eq_across (a b : List (List Nat)) : ordinal? a b = across? ord a b := by
  apply Option.ext
  intro k
  rw [RingSphereReadings.across_iff]
  constructor
  · intro hit x y hx hy
    dsimp only [ordinal?] at hit
    split at hit <;> try contradiction
    rename_i endpoints
    obtain rfl := Option.some.inj hit
    exact congrArg some (le_antisymm ((exact_bounds hx hy).2.trans_eq endpoints.symm) (exact_bounds hx hy).1)
  · intro all
    have lo := Option.some.inj (all _ _ (attainable a).1 (attainable b).2)
    have hi := Option.some.inj (all _ _ (attainable a).2 (attainable b).1)
    simp [ordinal?,lo,hi]

private theorem lift_projection {α β : Type} [DecidableEq α] (f : α → Option β)
    {xs : List α} {ys : List β} (p : (xs.filterMap f).Perm ys) :
    ∃ zs, xs.Perm zs ∧ zs.filterMap f = ys := by
  induction ys generalizing xs with
  | nil => exact ⟨_,.refl _,p.eq_nil⟩
  | cons y ys ih =>
    obtain ⟨a,ha,image⟩ := List.mem_filterMap.mp (p.mem_iff.mpr List.mem_cons_self)
    have pulled := List.perm_cons_erase ha
    have ps := (pulled.filterMap f).symm.trans p
    simp only [List.filterMap_cons,image] at ps
    obtain ⟨zs,q,eqn⟩ := ih ps.cons_inv
    exact ⟨a :: zs,pulled.trans (q.cons a),by simp [image,eqn]⟩

private theorem lift_rows {α β : Type} [DecidableEq α] (f : α → Option β)
    {rows : List (List α)} {ys : List (List β)}
    (h : List.Forall₂ (fun row out => (row.filterMap f).Perm out) rows ys) :
    ∃ chosen, List.Forall₂ List.Perm rows chosen ∧ chosen.map (List.filterMap f) = ys := by
  induction h with
  | nil => exact ⟨[],.nil,rfl⟩
  | cons p _ ih =>
    obtain ⟨x,hx,eqx⟩ := lift_projection f p
    obtain ⟨xs,hxs,eqxs⟩ := ih
    exact ⟨x :: xs,.cons hx hxs,by simp [eqx,eqxs]⟩

/-- Every order of the projected entries lifts to an order of the original
occurrences, even with repeated values or entries suppressed by the rule. -/
theorem projected_word {α β : Type} [DecidableEq α] (f : α → Option β)
    {rows : List (List α)} {w : List β} :
    Word (rows.map (List.filterMap f)) w ↔ ∃ x, Word rows x ∧ x.filterMap f = w := by
  constructor
  · rintro ⟨ys,p,rfl⟩
    obtain ⟨zs,chosen,eqn⟩ := lift_rows f (List.forall₂_map_left_iff.mp p)
    exact ⟨zs.flatten,⟨_,chosen,rfl⟩,by rw [List.filterMap_flatten,eqn]⟩
  · rintro ⟨_,⟨ys,p,rfl⟩,rfl⟩
    refine ⟨ys.map (List.filterMap f),?_,List.filterMap_flatten.symm⟩
    induction p with
    | nil => exact .nil
    | cons hp _ ih => exact .cons (hp.filterMap f) ih

open OneCenter (RS)

private def bit (s : RS) (x : Option RS) : Option Nat := x.map fun d => (d == s).toNat

private theorem bit_eq (s : RS) (xs : List (Option RS)) :
    xs.filterMap (bit s) = ((xs.filterMap id).map (· == s)).map Bool.toNat := by
  induction xs with
  | nil => rfl
  | cons a as ih => cases a <;> simp [bit,ih,List.map_map,Function.comp_def]

private theorem compare_bits (x y : List Bool) :
    RingSeededPairs.compareBits x y = lowerScore (x.map Bool.toNat) (y.map Bool.toNat) := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a as ih =>
    cases y with
    | nil => rfl
    | cons b bs => cases a <;> cases b <;> simp [RingSeededPairs.compareBits,lowerScore,Bool.toNat,ih]

private theorem fixed_eq (s : RS) (x y : List (Option RS)) :
    RingSeededPairs.listSign? s x y =
      if (x.filterMap (bit s)).length = (y.filterMap (bit s)).length then
        ord (x.filterMap (bit s)) (y.filterMap (bit s)) else none := by
  simp [RingSeededPairs.listSign?,bit_eq,ord,compare_bits]

/-- Fixed-reference Rule 5 preserves the source's equal accepted-length gate. -/
def seeded? (s : RS) (a b : List (List (Option RS))) : Option Int :=
  let x := a.map (List.filterMap (bit s))
  let y := b.map (List.filterMap (bit s))
  if x.flatten.length = y.flatten.length then ordinal? x y else none

theorem seeded_eq_across (s : RS) (a b : List (List (Option RS))) :
    seeded? s a b = across? (RingSeededPairs.listSign? s) a b := by
  apply Option.ext
  intro k
  unfold seeded?
  dsimp only
  rw [RingSphereReadings.across_iff]
  split
  next same =>
    rw [ordinal_eq_across,RingSphereReadings.across_iff]
    constructor
    · intro h x y hx hy
      have px := (projected_word (bit s)).mpr ⟨x,hx,rfl⟩
      have py := (projected_word (bit s)).mpr ⟨y,hy,rfl⟩
      rw [fixed_eq,if_pos ((word_length px).trans (same.trans (word_length py).symm))]
      exact h _ _ px py
    · intro h x y px py
      obtain ⟨u,hu,rfl⟩ := (projected_word (bit s)).mp px
      obtain ⟨v,hv,rfl⟩ := (projected_word (bit s)).mp py
      have got := h u v hu hv
      rwa [fixed_eq,if_pos ((word_length px).trans (same.trans (word_length py).symm))] at got
  next diff =>
    constructor
    · intro h; contradiction
    · intro h
      have got := h _ _ (RingSphereReadings.canonical a) (RingSphereReadings.canonical b)
      simpa only [fixed_eq,List.filterMap_flatten,if_neg diff] using got

/-- The retained hand at the nearest occupied distance is invariant under
all sphere orders when Rule 4b's first sphere has a single hand. -/
theorem first_reference {rows : List (List (Option RS))} {x : List (Option RS)}
    (one : RingSphereReadings.oneReference rows = true) (hx : Word rows x) :
    x.findSome? id = rows.flatten.findSome? id := by
  obtain ⟨_,p,rfl⟩ := hx
  induction p with
  | nil => rfl
  | @cons a b as bs p _ ih =>
    have perm := p.filterMap id
    cases h : a.filterMap id with
    | nil =>
      rw [h] at perm
      have hb := perm.symm.eq_nil
      have fa : a.findSome? id = none := by rw [← List.head?_filterMap,h]; rfl
      have fb : b.findSome? id = none := by rw [← List.head?_filterMap,hb]; rfl
      simpa only [List.flatten_cons,List.findSome?_append,fa,fb,Option.none_or] using
        ih (by simpa [RingSphereReadings.oneReference,h] using one)
    | cons v vs =>
      have unif : vs.all (· == v) = true := by simpa [RingSphereReadings.oneReference,h] using one
      rw [h] at perm
      cases hb : b.filterMap id with
      | nil => rw [hb] at perm; cases perm.eq_nil
      | cons w ws =>
        rw [hb] at perm
        have head : w = v := by
          rcases List.mem_cons.mp (perm.mem_iff.mpr List.mem_cons_self) with eqn | member
          · exact eqn
          · exact beq_iff_eq.mp (List.all_eq_true.mp unif w member)
        have fa : a.findSome? id = some v := by rw [← List.head?_filterMap,h]; rfl
        have fb : b.findSome? id = some v := by rw [← List.head?_filterMap,hb,head]; rfl
        simp [List.flatten_cons,fa,fb]

private def localBit (s : RS) (x : Option RS) : Option Nat := some (RingSeededPairs.like s x).toNat

private theorem local_bits (s : RS) (x : List (Option RS)) :
    x.filterMap (localBit s) = (x.map (RingSeededPairs.like s)).map Bool.toNat := by
  induction x with
  | nil => rfl
  | cons a as ih => simp [localBit,ih]

def local? (a b : List (List (Option RS))) : Option Int :=
  match a.flatten.findSome? id,b.flatten.findSome? id with
  | none,none => some 0
  | some s,some t => ordinal? (a.map (List.filterMap (localBit s))) (b.map (List.filterMap (localBit t)))
  | _,_ => none

theorem local_eq_across (a b : List (List (Option RS)))
    (ha : RingSphereReadings.oneReference a = true) (hb : RingSphereReadings.oneReference b = true) :
    local? a b = across? RingSeededPairs.localSign? a b := by
  apply Option.ext
  intro k
  rw [RingSphereReadings.across_iff]
  cases sa : a.flatten.findSome? id <;> cases sb : b.flatten.findSome? id
  · constructor
    · intro result x y hx hy
      simpa [RingSeededPairs.localSign?,first_reference ha hx,first_reference hb hy,local?,sa,sb] using result
    · intro all
      simpa [local?,RingSeededPairs.localSign?,sa,sb] using
        all _ _ (RingSphereReadings.canonical a) (RingSphereReadings.canonical b)
  · constructor
    · intro result
      simp [local?,sa,sb] at result
    · intro all
      simpa [local?,RingSeededPairs.localSign?,sa,sb] using
        all _ _ (RingSphereReadings.canonical a) (RingSphereReadings.canonical b)
  · constructor
    · intro result
      simp [local?,sa,sb] at result
    · intro all
      simpa [local?,RingSeededPairs.localSign?,sa,sb] using
        all _ _ (RingSphereReadings.canonical a) (RingSphereReadings.canonical b)
  next s t =>
    simp only [local?,sa,sb,ordinal_eq_across,RingSphereReadings.across_iff]
    have actual {x y} (hx : Word a x) (hy : Word b y) :
        RingSeededPairs.localSign? x y = ord (x.filterMap (localBit s)) (y.filterMap (localBit t)) := by
      simp [RingSeededPairs.localSign?,(first_reference ha hx).trans sa,(first_reference hb hy).trans sb,
        compare_bits,local_bits,ord]
    constructor
    · intro h x y hx hy
      rw [actual hx hy]
      exact h _ _ ((projected_word _).mpr ⟨_,hx,rfl⟩) ((projected_word _).mpr ⟨_,hy,rfl⟩)
    · intro h x y hx hy
      obtain ⟨u,hu,rfl⟩ := (projected_word _).mp hx
      obtain ⟨v,hv,rfl⟩ := (projected_word _).mp hy
      rw [← actual hu hv]
      exact h _ _ hu hv

end TetraStereo.Engine.RingSphereOrdinalRange

assert_kernel_only TetraStereo.Engine.RingSphereOrdinalRange.attainable
assert_kernel_only TetraStereo.Engine.RingSphereOrdinalRange.bounds
assert_kernel_only TetraStereo.Engine.RingSphereOrdinalRange.exact_bounds
assert_kernel_only TetraStereo.Engine.RingSphereOrdinalRange.ordinal_eq_across
assert_kernel_only TetraStereo.Engine.RingSphereOrdinalRange.projected_word
assert_kernel_only TetraStereo.Engine.RingSphereOrdinalRange.seeded_eq_across
assert_kernel_only TetraStereo.Engine.RingSphereOrdinalRange.first_reference
assert_kernel_only TetraStereo.Engine.RingSphereOrdinalRange.local_eq_across
