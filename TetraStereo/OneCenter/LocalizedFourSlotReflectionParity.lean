import TetraStereo.OneCenter.DeclarativeCIPCompleteRootDescriptor
import TetraStereo.OneCenter.Geometry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Four-slot reflection parity

Injective lexicographic keys on `Fin 4` are compared by `(prior, later)`. Class size at most two
and reversal on equal priors are inputs. When the priors differ, lexicographic order makes the
original and reflected comparisons agree. The unique descending slot permutations then differ by
the product of the tied transpositions, whose sign is `(-1)` to the source pair count.
-/

namespace TetraStereo.OneCenter.LocalizedFourSlotReflectionParity

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open CartesianPoint3
open TetrahedralGeometry
open scoped Classical

noncomputable section

/-- Lexicographic slot key, prior before the reflected tail. -/
def slotKey {P L : Type*} [LinearOrder P] [LinearOrder L]
    (prior : Fin 4 → P) (later : Fin 4 → L) (i : Fin 4) : Lex (P × L) :=
  toLex (prior i, later i)

/-- Distinct slots carrying the same prior. -/
def priorTie {P : Type*} (prior : Fin 4 → P) (i j : Fin 4) : Prop :=
  i ≠ j ∧ prior i = prior j

instance priorTie.decidableRel {P : Type*} [DecidableEq P] (prior : Fin 4 → P) :
    DecidableRel (priorTie prior) :=
  fun _ _ => inferInstance

/-- Source count of unordered equal-prior pairs. Same six-term sum as `completeRule5PairCount`. -/
def priorTieCount {P : Type*} [DecidableEq P] (prior : Fin 4 → P) : ℕ :=
  sourceEnantiomorphicPairCount (priorTie prior)

/-- Increasing representatives whose priors agree. -/
def tieList {P : Type*} [DecidableEq P] (prior : Fin 4 → P) : List (Fin 4 × Fin 4) :=
  sourceUnorderedPairList.filter fun pair => decide (prior pair.1 = prior pair.2)

private theorem filter_decide_congr {α : Type*} (l : List α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (h : ∀ a ∈ l, p a ↔ q a) :
    l.filter (fun a => decide (p a)) = l.filter (fun a => decide (q a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : p a ↔ q a := h a (show a ∈ a :: l from List.mem_cons_self)
    by_cases hp : p a
    · have hq : q a := ha.mp hp
      simp [List.filter, hp, hq, ih fun b hb => h b (List.mem_cons_of_mem a hb)]
    · have hq : ¬ q a := fun hq => hp (ha.mpr hq)
      simp [List.filter, hp, hq, ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem tieList_length {P : Type*} [DecidableEq P] (prior : Fin 4 → P) :
    (tieList prior).length = priorTieCount prior := by
  rw [priorTieCount, sourceEnantiomorphicPairCount_eq_filter_length]
  congr 1
  refine filter_decide_congr sourceUnorderedPairList
    (fun pair => prior pair.1 = prior pair.2) (fun pair => priorTie prior pair.1 pair.2) ?_
  intro pair hpair
  have hlt : pair.1 < pair.2 := (mem_sourceUnorderedPairList_iff pair.1 pair.2).mp hpair
  constructor
  · intro heq
    exact ⟨hlt.ne, heq⟩
  · intro h
    exact h.2

private theorem tie_prior_eq {P : Type*} [DecidableEq P] {prior : Fin 4 → P}
    {pair : Fin 4 × Fin 4} (hpair : pair ∈ tieList prior) : prior pair.1 = prior pair.2 := by
  have hdecide := List.of_mem_filter hpair
  simpa using hdecide

private theorem tieList_source {P : Type*} [DecidableEq P] {prior : Fin 4 → P}
    {pair : Fin 4 × Fin 4} (hpair : pair ∈ tieList prior) : pair ∈ sourceUnorderedPairList :=
  List.mem_of_mem_filter hpair

private theorem pairwise_of_nodup_forall {α : Type*} {l : List α} {R : α → α → Prop}
    (hn : l.Nodup) (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) : l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    refine List.Pairwise.cons ?_ ?_
    · intro b hb
      exact h a (show a ∈ a :: l from List.mem_cons_self) b (List.mem_cons_of_mem a hb) fun heq =>
        (List.nodup_cons.mp hn).1 (heq ▸ hb)
    · exact ih (List.nodup_cons.mp hn).2 fun x hx y hy hne =>
        h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hne

private theorem tieList_nodup {P : Type*} [DecidableEq P] (prior : Fin 4 → P) :
    (tieList prior).Nodup :=
  (nodup_sourceUnorderedPairList).filter _

private theorem tieList_pairwise {P : Type*} [DecidableEq P] (prior : Fin 4 → P)
    (classAtMostTwo : ∀ i j k, prior i = prior j → prior i = prior k →
      i = j ∨ i = k ∨ j = k) :
    (tieList prior).Pairwise fun p q =>
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
  refine pairwise_of_nodup_forall (tieList_nodup prior) ?_
  intro p hp q hq hne
  have hplt : p.1 < p.2 := (mem_sourceUnorderedPairList_iff p.1 p.2).mp (tieList_source hp)
  have hqlt : q.1 < q.2 := (mem_sourceUnorderedPairList_iff q.1 q.2).mp (tieList_source hq)
  have hpeq : prior p.1 = prior p.2 := tie_prior_eq hp
  have hqeq : prior q.1 = prior q.2 := tie_prior_eq hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hshare
    rcases classAtMostTwo p.1 p.2 q.2 (by simpa [hshare] using hpeq)
        (by simpa [hshare] using hqeq) with h1 | h2 | h3
    · exact hplt.ne h1
    · exact hqlt.ne (hshare.symm.trans h2)
    · exact hne (Prod.ext hshare h3)
  · intro hshare
    rcases classAtMostTwo p.1 p.2 q.1 hpeq (by simpa [hshare] using hqeq.symm) with h1 | h2 | h3
    · exact hplt.ne h1
    · exact hqlt.ne (h2.symm.trans hshare)
    · have hcycle : p.1 < p.1 := by
        calc
          p.1 < p.2 := hplt
          _ = q.1 := h3
          _ < q.2 := hqlt
          _ = p.1 := hshare.symm
      exact lt_irrefl _ hcycle
  · intro hshare
    rcases classAtMostTwo p.2 p.1 q.2 hpeq.symm (by simpa [hshare] using hqeq) with h1 | h2 | h3
    · exact hplt.ne.symm h1
    · exact hqlt.ne (hshare.symm.trans h2)
    · have hcycle : p.2 < p.2 := by
        calc
          p.2 = q.1 := hshare
          _ < q.2 := hqlt
          _ = p.1 := h3.symm
          _ < p.2 := hplt
      exact lt_irrefl _ hcycle
  · intro hshare
    rcases classAtMostTwo p.2 p.1 q.1 hpeq.symm (by simpa [hshare] using hqeq.symm) with
      h1 | h2 | h3
    · exact hplt.ne.symm h1
    · exact hqlt.ne (h2.symm.trans hshare)
    · exact hne (Prod.ext h3 hshare)

private theorem mem_flatMap_pair {α : Type*} {x : α} {l : List (α × α)} :
    x ∈ l.flatMap (fun p => [p.1, p.2]) ↔ ∃ p ∈ l, x = p.1 ∨ x = p.2 := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.flatMap_cons, List.mem_append]
    constructor
    · intro hx
      rcases hx with hx | hx
      · rcases List.mem_cons.mp hx with h | hx
        · subst h
          exact ⟨p, List.mem_cons_self, Or.inl rfl⟩
        · rcases List.mem_cons.mp hx with h | hx
          · subst h
            exact ⟨p, List.mem_cons_self, Or.inr rfl⟩
          · cases hx
      · rcases ih.mp hx with ⟨q, hq, hxq⟩
        exact ⟨q, List.mem_cons_of_mem p hq, hxq⟩
    · rintro ⟨q, hq, hx⟩
      rcases List.mem_cons.mp hq with hqp | hq
      · rw [hqp] at hx
        rcases hx with rfl | rfl
        · exact Or.inl List.mem_cons_self
        · exact Or.inl (List.mem_cons_of_mem p.1 (show p.2 ∈ [p.2] from List.mem_cons_self))
      · exact Or.inr (ih.mpr ⟨q, hq, hx⟩)

private theorem length_flatMap_pair (l : List (Fin 4 × Fin 4)) :
    (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp
    omega

private theorem flatMap_pair_nodup (l : List (Fin 4 × Fin 4))
    (hneq : ∀ p ∈ l, p.1 ≠ p.2)
    (hdisj : l.Pairwise fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    (l.flatMap fun p => [p.1, p.2]).Nodup := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    cases hdisj with
    | cons hhead htail =>
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, ?_⟩
        · intro hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact hneq p (show p ∈ p :: ps from List.mem_cons_self) h
          · cases h
        · rw [List.nodup_cons]
          refine ⟨?_, List.Pairwise.nil⟩
          intro h
          cases h
      · exact ih (fun q hq => hneq q (List.mem_cons_of_mem p hq)) htail
      · intro a ha b hb
        rw [mem_flatMap_pair] at hb
        obtain ⟨q, hq, hbe⟩ := hb
        have hd := hhead q hq
        rcases List.mem_cons.mp ha with ha | ha
        · subst ha
          rcases hbe with rfl | rfl
          · exact hd.1
          · exact hd.2.1
        · rcases List.mem_cons.mp ha with ha | ha
          · subst ha
            rcases hbe with rfl | rfl
            · exact hd.2.2.1
            · exact hd.2.2.2
          · cases ha

/-- At most two slots share a prior, so at most two unordered ties occur. -/
theorem priorTieCount_le_two {P : Type*} [DecidableEq P] (prior : Fin 4 → P)
    (classAtMostTwo : ∀ i j k, prior i = prior j → prior i = prior k →
      i = j ∨ i = k ∨ j = k) :
    priorTieCount prior ≤ 2 := by
  let ends := (tieList prior).flatMap fun pair => [pair.1, pair.2]
  have hneq : ∀ pair ∈ tieList prior, pair.1 ≠ pair.2 := by
    intro pair hpair
    exact ((mem_sourceUnorderedPairList_iff pair.1 pair.2).mp (tieList_source hpair)).ne
  have hnodup : ends.Nodup :=
    flatMap_pair_nodup (tieList prior) hneq (tieList_pairwise prior classAtMostTwo)
  have hlen : ends.length = 2 * priorTieCount prior := by
    rw [length_flatMap_pair, tieList_length]
  have hle : ends.length ≤ 4 := by
    have hcard := List.toFinset_card_of_nodup hnodup
    have hsub := Finset.card_le_card (Finset.subset_univ ends.toFinset)
    rw [hcard, Finset.card_univ, Fintype.card_fin] at hsub
    exact hsub
  omega

/-- The abstract prior count is the declarative Rule 5 pair count of the same first components. -/
theorem priorTieCount_completeRule5PairCount (keys : Fin 4 → CompleteLigandRule5Key) :
    priorTieCount (fun i => (ofLex (keys i)).1) = completeRule5PairCount keys := by
  unfold priorTieCount completeRule5PairCount
  refine sourceEnantiomorphicPairCount_congr_of_forall _ _ ?_
  intro i j
  simp [priorTie, CompletePriorPair]

private theorem key_lt_iff_prior_lt {P L : Type*} [LinearOrder P] [LinearOrder L]
    (prior : Fin 4 → P) (later : Fin 4 → L) {i j : Fin 4} (hdiff : prior i ≠ prior j) :
    slotKey prior later i < slotKey prior later j ↔ prior i < prior j := by
  rw [slotKey, slotKey, Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hlt | ⟨heq, _⟩)
    · exact hlt
    · exact (hdiff heq).elim
  · exact Or.inl

/-- Distinct priors compare the same way before and after the tail is replaced. -/
theorem crossPrior_comparison_unchanged {P L : Type*} [LinearOrder P] [LinearOrder L]
    (prior : Fin 4 → P) (later laterReflect : Fin 4 → L) {i j : Fin 4}
    (hdiff : prior i ≠ prior j) :
    (slotKey prior later i < slotKey prior later j) ↔
      (slotKey prior laterReflect i < slotKey prior laterReflect j) :=
  (key_lt_iff_prior_lt prior later hdiff).trans
    (key_lt_iff_prior_lt prior laterReflect hdiff).symm

/-- Number of slots whose key is strictly greater. -/
def greaterCount {α : Type*} [LinearOrder α] (key : Fin 4 → α) (i : Fin 4) : ℕ :=
  (Finset.univ.filter fun j => key i < key j).card

private theorem greaterCount_lt_four {α : Type*} [LinearOrder α] (key : Fin 4 → α) (i : Fin 4) :
    greaterCount key i < 4 := by
  have hsub : Finset.univ.filter (fun j => key i < key j) ⊆ Finset.univ.erase i := by
    intro j hj
    have hlt := (Finset.mem_filter.mp hj).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j⟩
    intro hji
    simp [hji] at hlt
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at hle
  have hle3 : greaterCount key i ≤ 3 := by simpa [greaterCount] using hle
  omega

/-- Descending position of a slot: zero is the greatest key. -/
def posOf {α : Type*} [LinearOrder α] (key : Fin 4 → α) (i : Fin 4) : Fin 4 :=
  ⟨greaterCount key i, greaterCount_lt_four key i⟩

private theorem greaterCount_lt_of_lt {α : Type*} [LinearOrder α] (key : Fin 4 → α)
    {i j : Fin 4} (hij : key i < key j) : greaterCount key j < greaterCount key i := by
  let aboveI := Finset.univ.filter fun k => key i < key k
  let aboveJ := Finset.univ.filter fun k => key j < key k
  have hsub : aboveJ ⊆ aboveI := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, lt_trans hij (Finset.mem_filter.mp hk).2⟩
  have hmem : j ∈ aboveI := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij⟩
  have hnot : j ∉ aboveJ := by
    intro hj
    exact lt_irrefl (key j) (Finset.mem_filter.mp hj).2
  have hne : aboveJ ≠ aboveI := fun hs => hnot (hs ▸ hmem)
  have hss : aboveJ ⊂ aboveI := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  simpa [greaterCount, aboveI, aboveJ] using Finset.card_lt_card hss

private theorem greaterCount_injective {α : Type*} [LinearOrder α] {key : Fin 4 → α}
    (inj : Function.Injective key) : Function.Injective (greaterCount key) := by
  intro i j heq
  by_contra hne
  have hkeys : key i ≠ key j := fun h => hne (inj h)
  rcases lt_or_gt_of_ne hkeys with hij | hji
  · exact ne_of_lt (greaterCount_lt_of_lt key hij) heq.symm
  · exact ne_of_lt (greaterCount_lt_of_lt key hji) heq

private theorem posOf_injective {α : Type*} [LinearOrder α] {key : Fin 4 → α}
    (inj : Function.Injective key) : Function.Injective (posOf key) := by
  intro i j h
  exact greaterCount_injective inj (congrArg Fin.val h)

/-- Slot at each descending position. Position zero carries the greatest key. -/
def descendingOrder {α : Type*} [LinearOrder α] (key : Fin 4 → α)
    (inj : Function.Injective key) : Equiv.Perm (Fin 4) :=
  (Equiv.ofBijective (posOf key) (Finite.injective_iff_bijective.mp (posOf_injective inj))).symm

theorem descendingOrder_posOf {α : Type*} [LinearOrder α] (key : Fin 4 → α)
    (inj : Function.Injective key) (i : Fin 4) :
    descendingOrder key inj (posOf key i) = i := by
  unfold descendingOrder
  exact Equiv.symm_apply_apply
    (Equiv.ofBijective (posOf key) (Finite.injective_iff_bijective.mp (posOf_injective inj))) i

theorem posOf_descendingOrder {α : Type*} [LinearOrder α] (key : Fin 4 → α)
    (inj : Function.Injective key) (p : Fin 4) :
    posOf key (descendingOrder key inj p) = p := by
  unfold descendingOrder
  exact Equiv.apply_symm_apply
    (Equiv.ofBijective (posOf key) (Finite.injective_iff_bijective.mp (posOf_injective inj))) p

private theorem card_filter_position_lt (p : Fin 4) :
    (Finset.univ.filter fun q : Fin 4 => q < p).card = p.val := by
  fin_cases p <;> decide

/-- A strictly descending permutation is the rank permutation. -/
theorem descendingOrder_unique {α : Type*} [LinearOrder α] (key : Fin 4 → α)
    (inj : Function.Injective key) (σ : Equiv.Perm (Fin 4))
    (hdesc : ∀ p q : Fin 4, p < q → key (σ q) < key (σ p)) :
    σ = descendingOrder key inj := by
  apply Equiv.ext
  intro p
  have hpos : posOf key (σ p) = p := by
    apply Fin.ext
    let s := Finset.univ.filter fun q : Fin 4 => q < p
    let t := Finset.univ.filter fun j : Fin 4 => key (σ p) < key j
    have hs : s.card = p.val := card_filter_position_lt p
    have hcard : s.card = t.card := by
      apply Finset.card_bij (fun q (_ : q ∈ s) => σ q)
      · intro q hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdesc q p (Finset.mem_filter.mp hq).2⟩
      · intro a _ b _ heq
        exact σ.injective heq
      · intro j hj
        refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
        have hltj : key (σ p) < key j := (Finset.mem_filter.mp hj).2
        have hq : σ.symm j < p := by
          by_contra hnot
          have hge : p ≤ σ.symm j := le_of_not_gt hnot
          rcases eq_or_lt_of_le hge with heq | hltp
          · have hjEq : j = σ p := by simp [heq]
            simp [hjEq] at hltj
          · have hraw := hdesc p (σ.symm j) hltp
            rw [Equiv.apply_symm_apply] at hraw
            exact lt_asymm hltj hraw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    change greaterCount key (σ p) = p.val
    rw [show greaterCount key (σ p) = t.card from rfl, ← hcard, hs]
  have hback := descendingOrder_posOf key inj (σ p)
  rw [hpos] at hback
  exact hback.symm

theorem descendingOrder_pairwise {α : Type*} [LinearOrder α] (key : Fin 4 → α)
    (inj : Function.Injective key) :
    (List.ofFn (descendingOrder key inj)).Pairwise fun left right => key right < key left := by
  rw [List.pairwise_ofFn]
  intro i j hij
  by_contra hnot
  have hne : descendingOrder key inj i ≠ descendingOrder key inj j := fun h =>
    ne_of_lt hij ((descendingOrder key inj).injective h)
  have hkeys : key (descendingOrder key inj i) ≠ key (descendingOrder key inj j) :=
    fun h => hne (inj h)
  have hlt : key (descendingOrder key inj i) < key (descendingOrder key inj j) :=
    (lt_or_gt_of_ne hkeys).resolve_right hnot
  have hcount := greaterCount_lt_of_lt key hlt
  have hi : greaterCount key (descendingOrder key inj i) = i.val := by
    simpa [posOf] using congrArg Fin.val (posOf_descendingOrder key inj i)
  have hj : greaterCount key (descendingOrder key inj j) = j.val := by
    simpa [posOf] using congrArg Fin.val (posOf_descendingOrder key inj j)
  have : j.val < i.val := by simpa [hi, hj] using hcount
  exact not_lt_of_gt (Fin.lt_def.mp hij) this

theorem descendingOrder_perm_finRange {α : Type*} [LinearOrder α] (key : Fin 4 → α)
    (inj : Function.Injective key) :
    (List.ofFn (descendingOrder key inj)).Perm (List.finRange 4) := by
  rw [List.ofFn_eq_map]
  exact Equiv.Perm.map_finRange_perm (descendingOrder key inj)

/-- A tied pair occupies consecutive descending positions, greater key first. -/
theorem tiedSlots_adjacent {P L : Type*} [LinearOrder P] [LinearOrder L]
    (prior : Fin 4 → P) (later : Fin 4 → L)
    (keyInjective : Function.Injective (slotKey prior later))
    (classAtMostTwo : ∀ i j k, prior i = prior j → prior i = prior k →
      i = j ∨ i = k ∨ j = k)
    {i j : Fin 4} (htie : priorTie prior i j)
    (hlt : slotKey prior later i < slotKey prior later j) :
    posOf (slotKey prior later) j + 1 = posOf (slotKey prior later) i := by
  let key := slotKey prior later
  have hbetween : ∀ k, ¬ (key i < key k ∧ key k < key j) := by
    intro k ⟨hik, hkj⟩
    by_cases hpri : prior k = prior i
    · rcases classAtMostTwo i j k htie.2 hpri.symm with h1 | h2 | h3
      · exact htie.1 h1
      · subst h2
        exact lt_irrefl _ hik
      · subst h3
        exact lt_irrefl _ hkj
    · have hdiff : prior i ≠ prior k := Ne.symm hpri
      have hikP : prior i < prior k :=
        (key_lt_iff_prior_lt prior later hdiff).mp hik
      have hkjDiff : prior k ≠ prior j := Ne.symm (by simpa [htie.2] using hdiff)
      have hkjP : prior k < prior j :=
        (key_lt_iff_prior_lt prior later hkjDiff).mp hkj
      exact lt_asymm hikP (by simpa [htie.2] using hkjP)
  let aboveI := Finset.univ.filter fun k => key i < key k
  let aboveJ := Finset.univ.filter fun k => key j < key k
  have hset : aboveI = insert j aboveJ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, aboveI, aboveJ]
    constructor
    · intro hk
      by_cases hkj : k = j
      · exact Or.inl hkj
      · have hkeys : key k ≠ key j := fun h => hkj (keyInjective h)
        rcases lt_or_gt_of_ne hkeys with hltk | hgtk
        · exact (hbetween k ⟨hk, hltk⟩).elim
        · exact Or.inr hgtk
    · intro hk
      rcases hk with rfl | hk
      · exact hlt
      · exact lt_trans hlt hk
  have hnot : j ∉ aboveJ := by
    intro hj
    exact lt_irrefl (key j) (Finset.mem_filter.mp hj).2
  have hcard : aboveI.card = aboveJ.card + 1 := by
    simpa [hset] using (Finset.card_insert_of_notMem hnot)
  have hcounts : greaterCount key i = greaterCount key j + 1 := by
    simpa [greaterCount, aboveI, aboveJ] using hcard
  apply Fin.ext
  have hlt4 : greaterCount key j + 1 < 4 := by
    rw [← hcounts]
    exact greaterCount_lt_four key i
  simp only [posOf, Fin.val_add]
  have hone : (1 : Fin 4).val = 1 := by decide
  rw [hone, Nat.mod_eq_of_lt hlt4]
  exact hcounts.symm

/-- Product of the tied slot swaps. Disjointness is not used for the sign. -/
def reflectionPartnerPerm {P : Type*} [DecidableEq P] (prior : Fin 4 → P) : Equiv.Perm (Fin 4) :=
  (tieList prior).foldl (fun acc pair => acc * Equiv.swap pair.1 pair.2) 1

private theorem sign_foldl_swap (pairs : List (Fin 4 × Fin 4))
    (hneq : ∀ pair ∈ pairs, pair.1 ≠ pair.2) (acc : Equiv.Perm (Fin 4)) :
    Equiv.Perm.sign (pairs.foldl (fun a pair => a * Equiv.swap pair.1 pair.2) acc) =
      Equiv.Perm.sign acc * (-1 : ℤˣ) ^ pairs.length := by
  induction pairs generalizing acc with
  | nil => simp
  | cons pair ps ih =>
    rw [List.foldl_cons,
      ih (fun q hq => hneq q (List.mem_cons_of_mem pair hq)),
      Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (hneq pair (show pair ∈ pair :: ps from List.mem_cons_self))]
    simp [List.length_cons, pow_succ, mul_comm]

theorem reflectionPartnerPerm_sign {P : Type*} [DecidableEq P] (prior : Fin 4 → P) :
    Equiv.Perm.sign (reflectionPartnerPerm prior) = (-1 : ℤˣ) ^ priorTieCount prior := by
  unfold reflectionPartnerPerm
  have hneq : ∀ pair ∈ tieList prior, pair.1 ≠ pair.2 := by
    intro pair hpair
    exact ((mem_sourceUnorderedPairList_iff pair.1 pair.2).mp (tieList_source hpair)).ne
  rw [sign_foldl_swap (tieList prior) hneq, Equiv.Perm.sign_one, one_mul, tieList_length]

private theorem coe_units_neg_one_pow (n : ℕ) :
    (((-1 : ℤˣ) ^ n : ℤˣ) : ℝ) = (-1 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    simp

theorem reflectionPartnerPerm_handedness {P : Type*} [DecidableEq P] (prior : Fin 4 → P) :
    permHandedness (reflectionPartnerPerm prior) = (-1 : ℝ) ^ priorTieCount prior := by
  rw [permHandedness, reflectionPartnerPerm_sign, coe_units_neg_one_pow]

private theorem mem_split {α : Type*} {a : α} {l : List α} (h : a ∈ l) :
    ∃ s t, l = s ++ a :: t := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact ⟨[], l, rfl⟩
    · obtain ⟨s, t, hs⟩ := ih hmem
      exact ⟨b :: s, t, by simp [hs]⟩

private theorem foldl_swap_preserves_value (pairs : List (Fin 4 × Fin 4))
    (acc : Equiv.Perm (Fin 4)) (x y : Fin 4) (hacc : acc x = y)
    (hfix : ∀ pair ∈ pairs, x ≠ pair.1 ∧ x ≠ pair.2) :
    (pairs.foldl (fun a pair => a * Equiv.swap pair.1 pair.2) acc) x = y := by
  induction pairs generalizing acc with
  | nil => simpa using hacc
  | cons pair ps ih =>
    have hx : Equiv.swap pair.1 pair.2 x = x :=
      Equiv.swap_apply_of_ne_of_ne
        (hfix pair (show pair ∈ pair :: ps from List.mem_cons_self)).1
        (hfix pair (show pair ∈ pair :: ps from List.mem_cons_self)).2
    have hacc' : (acc * Equiv.swap pair.1 pair.2) x = y := by
      simp [Equiv.Perm.mul_apply, hx, hacc]
    exact ih (acc * Equiv.swap pair.1 pair.2) hacc' fun q hq =>
      hfix q (List.mem_cons_of_mem pair hq)

private theorem reflectionPartnerPerm_fixed {P : Type*} [DecidableEq P] (prior : Fin 4 → P)
    (i : Fin 4) (h : ∀ j, ¬ priorTie prior i j) : reflectionPartnerPerm prior i = i := by
  refine foldl_swap_preserves_value (tieList prior) 1 i i rfl ?_
  intro pair hpair
  have hlt : pair.1 < pair.2 :=
    (mem_sourceUnorderedPairList_iff pair.1 pair.2).mp (tieList_source hpair)
  have heq : prior pair.1 = prior pair.2 := tie_prior_eq hpair
  refine ⟨?_, ?_⟩
  · intro hi
    exact h pair.2 ⟨by simpa [hi] using hlt.ne, by simpa [hi] using heq⟩
  · intro hi
    exact h pair.1 ⟨by simpa [hi] using hlt.ne.symm, by simpa [hi] using heq.symm⟩

private theorem reflectionPartnerPerm_of_tie {P : Type*} [DecidableEq P] (prior : Fin 4 → P)
    (classAtMostTwo : ∀ i j k, prior i = prior j → prior i = prior k →
      i = j ∨ i = k ∨ j = k)
    {i j : Fin 4} (hij : priorTie prior i j) : reflectionPartnerPerm prior i = j := by
  let pair := canonicalOrderedPair i j
  have hmem : pair ∈ tieList prior := by
    refine List.mem_filter_of_mem ?_ ?_
    · exact (mem_sourceUnorderedPairList_iff pair.1 pair.2).mpr (canonicalOrderedPair_lt hij.1)
    · have heq : prior pair.1 = prior pair.2 := by
        by_cases hlt : i < j
        · simp [pair, canonicalOrderedPair, hlt, hij.2]
        · simp [pair, canonicalOrderedPair, hlt, hij.2]
      simp [heq]
  obtain ⟨left, right, hsplit⟩ := mem_split hmem
  have hnodup : (tieList prior).Nodup := tieList_nodup prior
  have hleft : pair ∉ left := by
    intro hpair
    have hdis := (List.nodup_append.mp (by simpa [hsplit] using hnodup)).2.2
    exact hdis pair hpair pair (show pair ∈ pair :: right from List.mem_cons_self) rfl
  have hright : pair ∉ right := by
    have hcons := List.nodup_cons.mp (List.nodup_append.mp (by simpa [hsplit] using hnodup)).2.1
    exact hcons.1
  have honly : ∀ q ∈ tieList prior, i = q.1 ∨ i = q.2 ∨ j = q.1 ∨ j = q.2 → q = pair := by
    intro q hq htouch
    have hqlt : q.1 < q.2 := (mem_sourceUnorderedPairList_iff q.1 q.2).mp (tieList_source hq)
    have hqeq : prior q.1 = prior q.2 := tie_prior_eq hq
    have huni : ∀ k, priorTie prior i k → k = j := by
      intro k hk
      rcases classAtMostTwo i j k hij.2 hk.2 with h1 | h2 | h3
      · exact (hij.1 h1).elim
      · exact (hk.1 h2).elim
      · exact h3.symm
    have hunj : ∀ k, priorTie prior j k → k = i := by
      intro k hk
      rcases classAtMostTwo j i k hij.2.symm hk.2 with h1 | h2 | h3
      · exact (hij.1 h1.symm).elim
      · exact (hk.1 h2).elim
      · exact h3.symm
    have hset : (q.1 = i ∧ q.2 = j) ∨ (q.1 = j ∧ q.2 = i) := by
      rcases htouch with hi1 | hi2 | hj1 | hj2
      · exact Or.inl ⟨hi1.symm, huni q.2 ⟨by simpa [hi1] using hqlt.ne, by simpa [hi1] using hqeq⟩⟩
      · exact Or.inr ⟨huni q.1 ⟨by simpa [hi2] using hqlt.ne.symm, by simpa [hi2] using hqeq.symm⟩, hi2.symm⟩
      · exact Or.inr ⟨hj1.symm, hunj q.2 ⟨by simpa [hj1] using hqlt.ne, by simpa [hj1] using hqeq⟩⟩
      · exact Or.inl ⟨hunj q.1 ⟨by simpa [hj2] using hqlt.ne.symm, by simpa [hj2] using hqeq.symm⟩, hj2.symm⟩
    rcases hset with h | h
    · have hlt : i < j := by simpa [h] using hqlt
      have hqPair : q = (i, j) := Prod.ext h.1 h.2
      have hp : pair = (i, j) := by simp [pair, canonicalOrderedPair, hlt]
      exact hqPair.trans hp.symm
    · have hlt : j < i := by simpa [h] using hqlt
      have hnot : ¬ i < j := not_lt_of_gt hlt
      have hqPair : q = (j, i) := Prod.ext h.1 h.2
      have hp : pair = (j, i) := by simp [pair, canonicalOrderedPair, hnot]
      exact hqPair.trans hp.symm
  have havoid (q : Fin 4 × Fin 4) (hq : q ∈ left ∨ q ∈ right) :
      i ≠ q.1 ∧ i ≠ q.2 ∧ j ≠ q.1 ∧ j ≠ q.2 := by
    have hqmem : q ∈ tieList prior := by
      rw [hsplit]
      rcases hq with hql | hqr
      · exact List.mem_append_left _ hql
      · exact List.mem_append_right _ (List.mem_cons_of_mem pair hqr)
    have hnot : q ≠ pair := by
      intro heq
      rcases hq with hql | hqr
      · exact hleft (heq ▸ hql)
      · exact hright (heq ▸ hqr)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hnot (honly q hqmem (Or.inl h))
    · intro h
      exact hnot (honly q hqmem (Or.inr (Or.inl h)))
    · intro h
      exact hnot (honly q hqmem (Or.inr (Or.inr (Or.inl h))))
    · intro h
      exact hnot (honly q hqmem (Or.inr (Or.inr (Or.inr h))))
  have hswap : Equiv.swap pair.1 pair.2 i = j := by
    by_cases hlt : i < j
    · have hp : pair = (i, j) := by simp [pair, canonicalOrderedPair, hlt]
      simp [hp, Equiv.swap_apply_left]
    · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij.1)
      have hp : pair = (j, i) := by simp [pair, canonicalOrderedPair, hlt]
      simp [hp, Equiv.swap_apply_right]
  let accLeft := left.foldl (fun acc q => acc * Equiv.swap q.1 q.2) (1 : Equiv.Perm (Fin 4))
  have haccj : accLeft j = j :=
    foldl_swap_preserves_value left 1 j j rfl fun q hq => ⟨(havoid q (Or.inl hq)).2.2.1,
      (havoid q (Or.inl hq)).2.2.2⟩
  have hacc : (accLeft * Equiv.swap pair.1 pair.2) i = j := by
    simp [Equiv.Perm.mul_apply, hswap, haccj]
  have hfold : reflectionPartnerPerm prior =
      right.foldl (fun acc q => acc * Equiv.swap q.1 q.2)
        (accLeft * Equiv.swap pair.1 pair.2) := by
    simp [reflectionPartnerPerm, hsplit, accLeft, List.foldl_append, List.foldl_cons]
  rw [hfold]
  exact foldl_swap_preserves_value right (accLeft * Equiv.swap pair.1 pair.2) i j hacc
    fun q hq => ⟨(havoid q (Or.inr hq)).1, (havoid q (Or.inr hq)).2.1⟩

private theorem reflectionPartnerPerm_involutive {P : Type*} [DecidableEq P] (prior : Fin 4 → P)
    (classAtMostTwo : ∀ i j k, prior i = prior j → prior i = prior k →
      i = j ∨ i = k ∨ j = k) (i : Fin 4) :
    reflectionPartnerPerm prior (reflectionPartnerPerm prior i) = i := by
  by_cases h : ∃ j, priorTie prior i j
  · obtain ⟨j, hj⟩ := h
    rw [reflectionPartnerPerm_of_tie prior classAtMostTwo hj,
      reflectionPartnerPerm_of_tie prior classAtMostTwo ⟨Ne.symm hj.1, hj.2.symm⟩]
  · have hnot : ∀ j, ¬ priorTie prior i j := by simpa using h
    have hfix := reflectionPartnerPerm_fixed prior i hnot
    rw [hfix, hfix]

private theorem prior_reflectionPartner {P : Type*} [DecidableEq P] (prior : Fin 4 → P)
    (classAtMostTwo : ∀ i j k, prior i = prior j → prior i = prior k →
      i = j ∨ i = k ∨ j = k) (i : Fin 4) :
    prior (reflectionPartnerPerm prior i) = prior i := by
  by_cases h : ∃ j, priorTie prior i j
  · obtain ⟨j, hj⟩ := h
    rw [reflectionPartnerPerm_of_tie prior classAtMostTwo hj]
    exact hj.2.symm
  · have hnot : ∀ j, ¬ priorTie prior i j := by simpa using h
    rw [reflectionPartnerPerm_fixed prior i hnot]

/-- Original and reflected keys, with the two admitted finite hypotheses. -/
structure FourSlotReflection (P L : Type*) [LinearOrder P] [LinearOrder L] where
  prior : Fin 4 → P
  later : Fin 4 → L
  laterReflect : Fin 4 → L
  keyInjective : Function.Injective (slotKey prior later)
  reflectInjective : Function.Injective (slotKey prior laterReflect)
  classAtMostTwo : ∀ i j k, prior i = prior j → prior i = prior k →
    i = j ∨ i = k ∨ j = k
  tieReverses : ∀ i j, i ≠ j → prior i = prior j →
    (slotKey prior later i < slotKey prior later j ↔
      slotKey prior laterReflect j < slotKey prior laterReflect i)

private theorem reflect_lt_iff {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) (i j : Fin 4) :
    slotKey data.prior data.laterReflect i < slotKey data.prior data.laterReflect j ↔
      slotKey data.prior data.later (reflectionPartnerPerm data.prior i) <
        slotKey data.prior data.later (reflectionPartnerPerm data.prior j) := by
  by_cases hpri : data.prior i = data.prior j
  · by_cases hij : i = j
    · subst hij
      simp
    · have htie : priorTie data.prior i j := ⟨hij, hpri⟩
      rw [reflectionPartnerPerm_of_tie data.prior data.classAtMostTwo htie,
        reflectionPartnerPerm_of_tie data.prior data.classAtMostTwo ⟨Ne.symm hij, hpri.symm⟩]
      have hrev := data.tieReverses i j hij hpri
      have hneL : slotKey data.prior data.later i ≠ slotKey data.prior data.later j :=
        fun h => hij (data.keyInjective h)
      have hneR : slotKey data.prior data.laterReflect i ≠
          slotKey data.prior data.laterReflect j :=
        fun h => hij (data.reflectInjective h)
      constructor
      · intro hR
        have hnot : ¬ slotKey data.prior data.later i < slotKey data.prior data.later j := by
          intro hL
          exact lt_asymm hR (hrev.mp hL)
        exact (lt_or_gt_of_ne hneL).resolve_left hnot
      · intro hL
        have hnot : ¬ slotKey data.prior data.laterReflect j <
            slotKey data.prior data.laterReflect i := by
          intro hR
          exact lt_asymm hL (hrev.mpr hR)
        exact (lt_or_gt_of_ne hneR).resolve_right hnot
  · have hcross : slotKey data.prior data.laterReflect i < slotKey data.prior data.laterReflect j ↔
        data.prior i < data.prior j :=
      key_lt_iff_prior_lt data.prior data.laterReflect hpri
    have hpi := prior_reflectionPartner data.prior data.classAtMostTwo i
    have hpj := prior_reflectionPartner data.prior data.classAtMostTwo j
    have hdiff : data.prior (reflectionPartnerPerm data.prior i) ≠
        data.prior (reflectionPartnerPerm data.prior j) := by
      rw [hpi, hpj]
      exact hpri
    have hpartner :
        slotKey data.prior data.later (reflectionPartnerPerm data.prior i) <
            slotKey data.prior data.later (reflectionPartnerPerm data.prior j) ↔
          data.prior i < data.prior j := by
      rw [key_lt_iff_prior_lt data.prior data.later hdiff, hpi, hpj]
    exact hcross.trans hpartner.symm

private theorem greaterCount_comp {α : Type*} [LinearOrder α] (key : Fin 4 → α)
    (f : Equiv.Perm (Fin 4)) (i : Fin 4) :
    greaterCount (fun j => key (f j)) i = greaterCount key (f i) := by
  unfold greaterCount
  apply Finset.card_bij (fun j (_ : j ∈ Finset.univ.filter fun k => key (f i) < key (f k)) => f j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro a _ b _ heq
    exact f.injective heq
  · intro b hb
    refine ⟨f.symm b, ?_, f.apply_symm_apply b⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hb).2⟩

private theorem greaterCount_reflect {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) (i : Fin 4) :
    greaterCount (slotKey data.prior data.laterReflect) i =
      greaterCount (slotKey data.prior data.later) (reflectionPartnerPerm data.prior i) := by
  have hfilter : Finset.univ.filter
        (fun j => slotKey data.prior data.laterReflect i < slotKey data.prior data.laterReflect j) =
      Finset.univ.filter fun j =>
        slotKey data.prior data.later (reflectionPartnerPerm data.prior i) <
          slotKey data.prior data.later (reflectionPartnerPerm data.prior j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact reflect_lt_iff data i j
  rw [greaterCount, hfilter]
  simpa using greaterCount_comp (slotKey data.prior data.later)
    (reflectionPartnerPerm data.prior) i

private theorem posOf_reflect {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) (i : Fin 4) :
    posOf (slotKey data.prior data.laterReflect) i =
      posOf (slotKey data.prior data.later) (reflectionPartnerPerm data.prior i) := by
  apply Fin.ext
  simpa [posOf] using greaterCount_reflect data i

private theorem reflectionDescending_mul {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) :
    descendingOrder (slotKey data.prior data.laterReflect) data.reflectInjective =
      reflectionPartnerPerm data.prior *
        descendingOrder (slotKey data.prior data.later) data.keyInjective := by
  apply Equiv.ext
  intro p
  apply posOf_injective data.reflectInjective
  rw [posOf_descendingOrder (slotKey data.prior data.laterReflect) data.reflectInjective p,
    Equiv.Perm.mul_apply, posOf_reflect data (reflectionPartnerPerm data.prior
      (descendingOrder (slotKey data.prior data.later) data.keyInjective p)),
    reflectionPartnerPerm_involutive data.prior data.classAtMostTwo,
    posOf_descendingOrder (slotKey data.prior data.later) data.keyInjective p]

/-- Conjugate that carries the original descending order to the reflected one. -/
def reflectionPositionPerm {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) : Equiv.Perm (Fin 4) :=
  let descending := descendingOrder (slotKey data.prior data.later) data.keyInjective
  descending⁻¹ * reflectionPartnerPerm data.prior * descending

theorem reflectionPositionPerm_sign {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) :
    Equiv.Perm.sign (reflectionPositionPerm data) = (-1 : ℤˣ) ^ priorTieCount data.prior := by
  unfold reflectionPositionPerm
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, reflectionPartnerPerm_sign]
  rcases Int.units_eq_one_or
      (Equiv.Perm.sign (descendingOrder (slotKey data.prior data.later) data.keyInjective)) with
    hs | hs
  · simp [hs]
  · simp [hs, mul_comm]

theorem reflectionPositionPerm_handedness {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) :
    permHandedness (reflectionPositionPerm data) = (-1 : ℝ) ^ priorTieCount data.prior := by
  rw [permHandedness, reflectionPositionPerm_sign, coe_units_neg_one_pow]

/-- Reflected descending order is the original order followed by the tied-slot conjugate. -/
theorem reflectionDescending_eq {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) :
    descendingOrder (slotKey data.prior data.laterReflect) data.reflectInjective =
      descendingOrder (slotKey data.prior data.later) data.keyInjective *
        reflectionPositionPerm data := by
  rw [reflectionDescending_mul data]
  apply Equiv.ext
  intro p
  simp only [reflectionPositionPerm, Equiv.Perm.mul_apply]
  exact (Equiv.apply_symm_apply _ _).symm

/-- Any two strictly descending permutations differ by the tied-slot sign. -/
theorem descendingReflection_sign {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) (original reflected : Equiv.Perm (Fin 4))
    (horiginal : ∀ p q, p < q →
      slotKey data.prior data.later (original q) < slotKey data.prior data.later (original p))
    (hreflected : ∀ p q, p < q →
      slotKey data.prior data.laterReflect (reflected q) <
        slotKey data.prior data.laterReflect (reflected p)) :
    reflected = original * reflectionPositionPerm data ∧
      Equiv.Perm.sign (original⁻¹ * reflected) = (-1 : ℤˣ) ^ priorTieCount data.prior ∧
      permHandedness (original⁻¹ * reflected) = (-1 : ℝ) ^ priorTieCount data.prior := by
  have horiginalEq := descendingOrder_unique (slotKey data.prior data.later) data.keyInjective
    original horiginal
  have hreflectedEq := descendingOrder_unique (slotKey data.prior data.laterReflect)
    data.reflectInjective reflected hreflected
  refine ⟨?_, ?_, ?_⟩
  · rw [horiginalEq, hreflectedEq, reflectionDescending_eq]
  · rw [horiginalEq, hreflectedEq, reflectionDescending_eq, ← mul_assoc, inv_mul_cancel, one_mul]
    exact reflectionPositionPerm_sign data
  · rw [horiginalEq, hreflectedEq, reflectionDescending_eq, ← mul_assoc, inv_mul_cancel, one_mul]
    exact reflectionPositionPerm_handedness data

private def slotGeometry (vertexPoint : Fin 4 → CartesianPoint3) : TetrahedralGeometry where
  vertex i := (vertexPoint i).toRealPoint

private theorem slotGeometry_eq (vertexPoint : Fin 4 → CartesianPoint3) :
    slotGeometry vertexPoint =
      toRealTetrahedralGeometry (vertexPoint 0) (vertexPoint 1) (vertexPoint 2)
        (vertexPoint 3) := by
  apply TetrahedralGeometry.ext
  intro i
  fin_cases i <;> rfl

private theorem slotGeometry_reindex (vertexPoint : Fin 4 → CartesianPoint3)
    (ρ : Equiv.Perm (Fin 4)) :
    TetrahedralGeometry.reindex (slotGeometry vertexPoint) ρ =
      slotGeometry fun i => vertexPoint (ρ i) := rfl

/-- Reindexing four rational points multiplies the embedded oriented volume by the permutation sign. -/
theorem orientedVolume_slotPermutation (points : Fin 4 → CartesianPoint3)
    (order ρ : Equiv.Perm (Fin 4)) :
    (orientedVolume (points ((order * ρ) 0)) (points ((order * ρ) 1))
        (points ((order * ρ) 2)) (points ((order * ρ) 3)) : ℝ) =
      permHandedness ρ * (orientedVolume (points (order 0)) (points (order 1))
        (points (order 2)) (points (order 3)) : ℝ) := by
  have hreindex : slotGeometry (fun i => points ((order * ρ) i)) =
      TetrahedralGeometry.reindex (slotGeometry fun i => points (order i)) ρ := by
    rw [slotGeometry_reindex]
    congr 1
  have hreal := orientedVolume_reindex (slotGeometry fun i => points (order i)) ρ
  rw [← hreindex] at hreal
  rw [slotGeometry_eq, slotGeometry_eq, orientedVolume_toRealTetrahedralGeometry,
    orientedVolume_toRealTetrahedralGeometry] at hreal
  exact hreal

theorem orientedVolume_slotPermutation_even (points : Fin 4 → CartesianPoint3)
    (order ρ : Equiv.Perm (Fin 4)) (hρ : permHandedness ρ = 1) :
    orientedVolume (points ((order * ρ) 0)) (points ((order * ρ) 1))
        (points ((order * ρ) 2)) (points ((order * ρ) 3)) =
      orientedVolume (points (order 0)) (points (order 1)) (points (order 2))
        (points (order 3)) := by
  have hreal := orientedVolume_slotPermutation points order ρ
  rw [hρ, one_mul] at hreal
  exact Rat.cast_injective hreal

theorem orientedVolume_slotPermutation_odd (points : Fin 4 → CartesianPoint3)
    (order ρ : Equiv.Perm (Fin 4)) (hρ : permHandedness ρ = -1) :
    orientedVolume (points ((order * ρ) 0)) (points ((order * ρ) 1))
        (points ((order * ρ) 2)) (points ((order * ρ) 3)) =
      -orientedVolume (points (order 0)) (points (order 1)) (points (order 2))
        (points (order 3)) := by
  have hreal := orientedVolume_slotPermutation points order ρ
  rw [hρ] at hreal
  have hmul : (-1 : ℝ) * (orientedVolume (points (order 0)) (points (order 1))
      (points (order 2)) (points (order 3)) : ℝ) =
      - (orientedVolume (points (order 0)) (points (order 1)) (points (order 2))
        (points (order 3)) : ℝ) := neg_one_mul _
  rw [hmul] at hreal
  have hneg : ((-orientedVolume (points (order 0)) (points (order 1)) (points (order 2))
      (points (order 3)) : ℚ) : ℝ) =
      - (orientedVolume (points (order 0)) (points (order 1)) (points (order 2))
        (points (order 3)) : ℝ) := Rat.cast_neg _
  rw [← hneg] at hreal
  exact Rat.cast_injective hreal

private theorem ofFn_fin4 {α : Type*} (f : Fin 4 → α) :
    List.ofFn f = [f 0, f 1, f 2, f 3] := by
  refine List.ext_get (by simp) ?_
  intro n h1 h2
  have hn : n < 4 := by simpa using h1
  interval_cases n <;> simp

/-- Reflected descending points keep the descriptor when the tie count is even, and swap it when odd. -/
theorem rationalDescriptor_reflection {P L : Type*} [LinearOrder P] [LinearOrder L]
    (data : FourSlotReflection P L) (points : Fin 4 → CartesianPoint3)
    (original reflected : Equiv.Perm (Fin 4))
    (horiginal : ∀ p q, p < q →
      slotKey data.prior data.later (original q) < slotKey data.prior data.later (original p))
    (hreflected : ∀ p q, p < q →
      slotKey data.prior data.laterReflect (reflected q) <
        slotKey data.prior data.laterReflect (reflected p))
    {raw : RS}
    (hdesc : RationalTetrahedralDescriptor (List.ofFn fun i => points (original i)) raw) :
    RationalTetrahedralDescriptor (List.ofFn fun i => points (reflected i))
      (if Even (priorTieCount data.prior) then raw else RS.swap raw) := by
  obtain ⟨heq, -, hhand⟩ := descendingReflection_sign data original reflected horiginal hreflected
  have hvol := orientedVolume_slotPermutation points original (reflectionPositionPerm data)
  rw [← heq] at hvol
  rw [reflectionPositionPerm_handedness data] at hvol
  have horigList := ofFn_fin4 fun i => points (original i)
  have hreflList := ofFn_fin4 fun i => points (reflected i)
  rw [horigList] at hdesc
  obtain ⟨a, b, c, d, hpoints, hsign⟩ := hdesc
  injection hpoints with ha hrest
  injection hrest with hb hrest
  injection hrest with hc hrest
  injection hrest with hd _
  subst ha
  subst hb
  subst hc
  subst hd
  rw [hreflList]
  refine ⟨points (reflected 0), points (reflected 1), points (reflected 2), points (reflected 3),
    rfl, ?_⟩
  let vol := orientedVolume (points (original 0)) (points (original 1)) (points (original 2))
    (points (original 3))
  let volR := orientedVolume (points (reflected 0)) (points (reflected 1))
    (points (reflected 2)) (points (reflected 3))
  have hvol' : (volR : ℝ) = (-1 : ℝ) ^ priorTieCount data.prior * (vol : ℝ) := hvol
  rcases Nat.even_or_odd (priorTieCount data.prior) with heven | hodd
  · simp only [if_pos heven]
    rw [Even.neg_one_pow heven, one_mul] at hvol'
    have hrat : volR = vol := Rat.cast_injective hvol'
    cases raw with
    | R => simpa [hrat, vol, volR] using hsign
    | S => simpa [hrat, vol, volR] using hsign
  · simp only [if_neg (Nat.not_even_iff_odd.mpr hodd)]
    rw [Odd.neg_one_pow hodd, neg_one_mul] at hvol'
    have hnegcast : ((-vol : ℚ) : ℝ) = - (vol : ℝ) := Rat.cast_neg _
    rw [← hnegcast] at hvol'
    have hrat : volR = -vol := Rat.cast_injective hvol'
    cases raw with
    | R =>
        have hpos : 0 < volR := by
          rw [hrat]
          exact neg_pos.mpr hsign
        simpa [volR, RS.swap] using hpos
    | S =>
        have hneg : volR < 0 := by
          rw [hrat]
          exact neg_lt_zero.mpr hsign
        simpa [volR, RS.swap] using hneg

end

assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.priorTieCount_le_two
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.priorTieCount_completeRule5PairCount
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.crossPrior_comparison_unchanged
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.descendingOrder_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.descendingOrder_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.descendingOrder_perm_finRange
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.tiedSlots_adjacent
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.reflectionPartnerPerm_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.reflectionPartnerPerm_handedness
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.reflectionPositionPerm_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.reflectionPositionPerm_handedness
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.reflectionDescending_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.descendingReflection_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.orientedVolume_slotPermutation
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.orientedVolume_slotPermutation_even
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.orientedVolume_slotPermutation_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedFourSlotReflectionParity.rationalDescriptor_reflection

end TetraStereo.OneCenter.LocalizedFourSlotReflectionParity
