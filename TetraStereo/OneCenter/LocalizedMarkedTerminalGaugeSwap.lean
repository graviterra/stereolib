import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys
import TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exchanging two frame cursors under a comparator symmetry

If the key comparators under two marks are related by exchanging two frame cursors, then two
unique actual uncapped rankings are related by exchanging the two frame positions, the ranked atom
lists differ by exchanging the two atoms, and the geometric raw letters are complements. The
rankings are the actual insertion sorts; only root's pairwise-strictness law and the permutation
laws are used, never totality or a desired order.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap

open AuthoritativeCIPRule6ReferenceFamily AuthoritativeCIPRule6P92Enumeration
open LocalizedMarkedUncappedRankingLaws LocalizedMarkedTerminalGaugeKeys
open LocalizedMarkedOperationEvaluator
open LocalizedGenericMarkedRecalculation (Geometry readback? frameAtomsOf)
open CartesianPoint3

abbrev Cursor := CanonicalRerootCursor

/-! ## Strictly sorted permutations coincide -/

theorem sorted_unique {α : Type} (R : α → α → Prop) (asymm : ∀ a b, R a b → R b a → False) :
    ∀ l₁ l₂ : List α, l₁.Perm l₂ → l₁.Pairwise R → l₂.Pairwise R → l₁ = l₂
  | [], l₂, perm, _, _ => by
      have := List.Perm.nil_eq perm
      exact this
  | a :: l, l₂, perm, p₁, p₂ => by
      cases l₂ with
      | nil =>
          have := List.Perm.nil_eq perm.symm
          cases this
      | cons b l' =>
          by_cases same : a = b
          · subst same
            have tails := List.Perm.cons_inv perm
            rw [sorted_unique R asymm l l' tails (List.pairwise_cons.mp p₁).2
              (List.pairwise_cons.mp p₂).2]
          · exfalso
            have aMem : a ∈ b :: l' := perm.mem_iff.mp List.mem_cons_self
            have aIn : a ∈ l' := by
              rcases List.mem_cons.mp aMem with h | h
              · exact absurd h same
              · exact h
            have bMem : b ∈ a :: l := perm.symm.mem_iff.mp List.mem_cons_self
            have bIn : b ∈ l := by
              rcases List.mem_cons.mp bMem with h | h
              · exact absurd h.symm same
              · exact h
            exact asymm a b ((List.pairwise_cons.mp p₁).1 b bIn) ((List.pairwise_cons.mp p₂).1 a aIn)

/-! ## Exchanges -/

def swapCursor (u v c : Cursor) : Cursor := if c = u then v else if c = v then u else c

def swapIdx (i j p : Nat) : Nat := if p = i then j else if p = j then i else p

def swapAtom (t₁ t₂ a : Nat) : Nat := if a = t₁ then t₂ else if a = t₂ then t₁ else a

theorem swapCursor_left (u v : Cursor) : swapCursor u v u = v := by simp [swapCursor]

theorem swapCursor_right (u v : Cursor) (ne : u ≠ v) : swapCursor u v v = u := by
  simp [swapCursor, ne.symm]

theorem swapCursor_other (u v c : Cursor) (hu : c ≠ u) (hv : c ≠ v) : swapCursor u v c = c := by
  simp [swapCursor, hu, hv]

theorem swapCursor_involutive (u v c : Cursor) : swapCursor u v (swapCursor u v c) = c := by
  unfold swapCursor
  by_cases hu : c = u
  · subst hu
    rw [if_pos rfl]
    by_cases vu : v = c
    · rw [if_pos vu]
      exact vu
    · rw [if_neg vu, if_pos rfl]
  · by_cases hv : c = v
    · subst hv
      rw [if_neg hu, if_pos rfl, if_pos rfl]
    · rw [if_neg hu, if_neg hv, if_neg hu, if_neg hv]

theorem swapCursor_injective (u v : Cursor) : Function.Injective (swapCursor u v) := by
  intro a b h
  have := congrArg (swapCursor u v) h
  rwa [swapCursor_involutive, swapCursor_involutive] at this

/-- The exchange of two members of a duplicate-free list permutes it. -/
theorem map_swapCursor_perm (roots : List Cursor) (nodup : roots.Nodup) (u v : Cursor)
    (hu : u ∈ roots) (hv : v ∈ roots) : (roots.map (swapCursor u v)).Perm roots := by
  have image : ∀ c ∈ roots, swapCursor u v c ∈ roots := by
    intro c member
    by_cases hcu : c = u
    · subst hcu
      rw [swapCursor_left]
      exact hv
    · by_cases hcv : c = v
      · subst hcv
        by_cases uv : u = c
        · subst uv
          rw [swapCursor_left]
          exact hu
        · rw [swapCursor_right u c uv]
          exact hu
      · rw [swapCursor_other u v c hcu hcv]
        exact member
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact nodup.map (swapCursor_injective u v)
  · exact nodup
  · ext c
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨d, member, rfl⟩
      exact image d member
    · intro member
      exact ⟨swapCursor u v c, image c member, swapCursor_involutive u v c⟩

/-! ## Index facts on duplicate-free lists -/

theorem getElem?_inj_of_nodup {α : Type} : ∀ (l : List α), l.Nodup → ∀ (p q : Nat) (c : α),
    l[p]? = some c → l[q]? = some c → p = q
  | [], _, p, _, _, hp, _ => by simp at hp
  | a :: l, nodup, p, q, c, hp, hq => by
      cases p with
      | zero =>
          cases q with
          | zero => rfl
          | succ q =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
              simp only [List.getElem?_cons_succ] at hq
              subst hp
              exact absurd (List.mem_of_getElem? hq) (List.nodup_cons.mp nodup).1
      | succ p =>
          cases q with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
              simp only [List.getElem?_cons_succ] at hp
              subst hq
              exact absurd (List.mem_of_getElem? hp) (List.nodup_cons.mp nodup).1
          | succ q =>
              simp only [List.getElem?_cons_succ] at hp hq
              rw [getElem?_inj_of_nodup l (List.nodup_cons.mp nodup).2 p q c hp hq]

theorem mem_zipIdx_getElem? {α : Type} (l : List α) (e : α × Nat) (member : e ∈ l.zipIdx) :
    l[e.2]? = some e.1 :=
  List.mem_zipIdx_iff_getElem?.mp member

/-! ## Positions of two unique rankings under exchanged comparators -/

theorem tracked_cursors_sorted (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List Cursor) (mark : Nat) (tracked : List (Cursor × Nat) × Nat × Bool)
    (computed : sortIndexedOccurrencesThroughRule6Authoritative? mol state mark fuel roots.zipIdx =
      some tracked) (unique : tracked.2.2 = true) :
    (tracked.1.map Prod.fst).Pairwise (fun a b => cursorCompare mol state mark fuel a b = .gt) :=
  List.pairwise_map.mpr (sort_strict_of_unique mol state mark fuel roots.zipIdx tracked computed unique)

theorem tracked_cursors_perm (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List Cursor) (mark : Nat) (tracked : List (Cursor × Nat) × Nat × Bool)
    (computed : sortIndexedOccurrencesThroughRule6Authoritative? mol state mark fuel roots.zipIdx =
      some tracked) : (tracked.1.map Prod.fst).Perm roots := by
  have perm := (sortIndexedOccurrencesThroughRule6Authoritative?_perm mol state mark fuel
    roots.zipIdx tracked computed).map Prod.fst
  simpa using perm

theorem cursorCompare_asymm (mol : RawMolecule) (state : OccurrenceAuxState) (fuel mark : Nat)
    (a b : Cursor) (h₁ : cursorCompare mol state mark fuel a b = .gt)
    (h₂ : cursorCompare mol state mark fuel b a = .gt) : False := by
  have swap := Std.OrientedCmp.eq_swap (cmp := cursorCompare mol state mark fuel) (a := a) (b := b)
  rw [h₁, h₂] at swap
  cases swap

/-- The cursor sequence of the second unique ranking is the exchanged cursor sequence of the first. -/
theorem cursor_sequences_related (mol : RawMolecule) (state : OccurrenceAuxState) (m₁ m₂ fuel : Nat)
    (roots : List Cursor) (nodup : roots.Nodup) (u v : Cursor) (hu : u ∈ roots) (hv : v ∈ roots)
    (symmetry : ∀ a ∈ roots, ∀ b ∈ roots, cursorCompare mol state m₂ fuel a b =
      cursorCompare mol state m₁ fuel (swapCursor u v a) (swapCursor u v b))
    (tracked₁ tracked₂ : List (Cursor × Nat) × Nat × Bool)
    (computed₁ : sortIndexedOccurrencesThroughRule6Authoritative? mol state m₁ fuel roots.zipIdx =
      some tracked₁) (unique₁ : tracked₁.2.2 = true)
    (computed₂ : sortIndexedOccurrencesThroughRule6Authoritative? mol state m₂ fuel roots.zipIdx =
      some tracked₂) (unique₂ : tracked₂.2.2 = true) :
    tracked₁.1.map Prod.fst = (tracked₂.1.map Prod.fst).map (swapCursor u v) := by
  have perm₁ := tracked_cursors_perm mol state fuel roots m₁ tracked₁ computed₁
  have perm₂ := tracked_cursors_perm mol state fuel roots m₂ tracked₂ computed₂
  have sorted₁ := tracked_cursors_sorted mol state fuel roots m₁ tracked₁ computed₁ unique₁
  have sorted₂ := tracked_cursors_sorted mol state fuel roots m₂ tracked₂ computed₂ unique₂
  have sorted₂' : ((tracked₂.1.map Prod.fst).map (swapCursor u v)).Pairwise
      (fun a b => cursorCompare mol state m₁ fuel a b = .gt) := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ sorted₂
    intro a b aMem bMem h
    rw [← symmetry a (perm₂.mem_iff.mp aMem) b (perm₂.mem_iff.mp bMem)]
    exact h
  have perm₂' : ((tracked₂.1.map Prod.fst).map (swapCursor u v)).Perm roots :=
    (perm₂.map (swapCursor u v)).trans (map_swapCursor_perm roots nodup u v hu hv)
  exact sorted_unique _ (cursorCompare_asymm mol state fuel m₁) _ _
    (perm₁.trans perm₂'.symm) sorted₁ sorted₂'

/-- The positions of the second unique ranking are those of the first with `i` and `j` exchanged. -/
theorem positions_related (mol : RawMolecule) (state : OccurrenceAuxState) (m₁ m₂ fuel : Nat)
    (roots : List Cursor) (nodup : roots.Nodup) (u v : Cursor) (i j : Nat)
    (hu : roots[i]? = some u) (hv : roots[j]? = some v) (distinct : u ≠ v)
    (symmetry : ∀ a ∈ roots, ∀ b ∈ roots, cursorCompare mol state m₂ fuel a b =
      cursorCompare mol state m₁ fuel (swapCursor u v a) (swapCursor u v b))
    (tracked₁ tracked₂ : List (Cursor × Nat) × Nat × Bool)
    (computed₁ : sortIndexedOccurrencesThroughRule6Authoritative? mol state m₁ fuel roots.zipIdx =
      some tracked₁) (unique₁ : tracked₁.2.2 = true)
    (computed₂ : sortIndexedOccurrencesThroughRule6Authoritative? mol state m₂ fuel roots.zipIdx =
      some tracked₂) (unique₂ : tracked₂.2.2 = true) :
    tracked₂.1.map Prod.snd = (tracked₁.1.map Prod.snd).map (swapIdx i j) := by
  have uMem : u ∈ roots := List.mem_of_getElem? hu
  have vMem : v ∈ roots := List.mem_of_getElem? hv
  have cursors := cursor_sequences_related mol state m₁ m₂ fuel roots nodup u v uMem vMem
    symmetry tracked₁ tracked₂ computed₁ unique₁ computed₂ unique₂
  have perm₁ := sortIndexedOccurrencesThroughRule6Authoritative?_perm mol state m₁ fuel
    roots.zipIdx tracked₁ computed₁
  have perm₂ := sortIndexedOccurrencesThroughRule6Authoritative?_perm mol state m₂ fuel
    roots.zipIdx tracked₂ computed₂
  have len : tracked₂.1.length = tracked₁.1.length := by
    rw [perm₂.length_eq, perm₁.length_eq]
  apply List.ext_getElem
  · simp [len]
  intro k hk₂ hk₁
  simp only [List.getElem_map]
  have lenK₂ : k < tracked₂.1.length := by simpa using hk₂
  have lenK₁ : k < tracked₁.1.length := by simpa using hk₁
  have e₁Mem : tracked₁.1[k] ∈ roots.zipIdx := perm₁.mem_iff.mp (List.getElem_mem lenK₁)
  have e₂Mem : tracked₂.1[k] ∈ roots.zipIdx := perm₂.mem_iff.mp (List.getElem_mem lenK₂)
  have g₁ := mem_zipIdx_getElem? roots _ e₁Mem
  have g₂ := mem_zipIdx_getElem? roots _ e₂Mem
  have cursorK : (tracked₁.1[k]).1 = swapCursor u v (tracked₂.1[k]).1 := by
    have := congrArg (fun l => l[k]?) cursors
    simp only [List.getElem?_map, List.getElem?_eq_getElem lenK₁, List.getElem?_eq_getElem lenK₂,
      Option.map_some, Option.some.injEq] at this
    exact this
  by_cases c₂u : (tracked₂.1[k]).1 = u
  · rw [c₂u, swapCursor_left] at cursorK
    rw [c₂u] at g₂
    have p₂ : (tracked₂.1[k]).2 = i := getElem?_inj_of_nodup roots nodup _ _ u g₂ hu
    rw [cursorK] at g₁
    have p₁ : (tracked₁.1[k]).2 = j := getElem?_inj_of_nodup roots nodup _ _ v g₁ hv
    rw [p₁, p₂]
    by_cases ij : j = i
    · simp [swapIdx, ij]
    · simp [swapIdx, ij]
  · by_cases c₂v : (tracked₂.1[k]).1 = v
    · rw [c₂v, swapCursor_right u v distinct] at cursorK
      rw [c₂v] at g₂
      have p₂ : (tracked₂.1[k]).2 = j := getElem?_inj_of_nodup roots nodup _ _ v g₂ hv
      rw [cursorK] at g₁
      have p₁ : (tracked₁.1[k]).2 = i := getElem?_inj_of_nodup roots nodup _ _ u g₁ hu
      rw [p₁, p₂]
      simp [swapIdx]
    · rw [swapCursor_other u v _ c₂u c₂v] at cursorK
      rw [cursorK] at g₁
      have same : (tracked₁.1[k]).2 = (tracked₂.1[k]).2 :=
        getElem?_inj_of_nodup roots nodup _ _ _ g₁ g₂
      have notI : (tracked₂.1[k]).2 ≠ i := by
        intro h
        rw [h, hu] at g₂
        exact c₂u (Option.some.inj g₂).symm
      have notJ : (tracked₂.1[k]).2 ≠ j := by
        intro h
        rw [h, hv] at g₂
        exact c₂v (Option.some.inj g₂).symm
      rw [same]
      simp [swapIdx, notI, notJ]

/-! ## From positions to ranked atoms -/

theorem mapM_congr {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, agree => by
      simp only [List.mapM_cons]
      rw [agree a List.mem_cons_self, mapM_congr f g l fun x member => agree x (List.mem_cons_of_mem _ member)]

theorem mapM_option_map {α β γ : Type} (h : α → Option β) (s : β → γ) :
    ∀ l : List α, l.mapM (fun p => (h p).map s) = (l.mapM h).map (List.map s)
  | [] => rfl
  | a :: l => by
      simp only [List.mapM_cons, mapM_option_map h s l]
      cases h a <;> cases l.mapM h <;> rfl

theorem getElem?_swapIdx (atoms : List Nat) (nodup : atoms.Nodup) (t₁ t₂ : Nat) (i j : Nat)
    (hi : atoms[i]? = some t₁) (hj : atoms[j]? = some t₂) (ij : i ≠ j) (p : Nat)
    (bound : p < atoms.length) :
    atoms[swapIdx i j p]? = (atoms[p]?).map (swapAtom t₁ t₂) := by
  have ne : t₁ ≠ t₂ := by
    intro same
    rw [same] at hi
    exact ij (getElem?_inj_of_nodup atoms nodup i j t₂ hi hj)
  obtain ⟨a, ha⟩ : ∃ a, atoms[p]? = some a := ⟨atoms[p], List.getElem?_eq_getElem bound⟩
  rw [ha]
  by_cases pi : p = i
  · subst pi
    rw [hi] at ha
    have at₁ : a = t₁ := (Option.some.inj ha).symm
    subst at₁
    simp [swapIdx, swapAtom, hj]
  · by_cases pj : p = j
    · subst pj
      rw [hj] at ha
      have at₂ : a = t₂ := (Option.some.inj ha).symm
      subst at₂
      simp [swapIdx, pi, swapAtom, ne.symm, hi]
    · have aNe₁ : a ≠ t₁ := by
        intro same
        rw [same] at ha
        exact pi (getElem?_inj_of_nodup atoms nodup p i t₁ ha hi)
      have aNe₂ : a ≠ t₂ := by
        intro same
        rw [same] at ha
        exact pj (getElem?_inj_of_nodup atoms nodup p j t₂ ha hj)
      simp [swapIdx, pi, pj, ha, swapAtom, aNe₁, aNe₂]

theorem rankedAtoms_swap (atoms : List Nat) (nodup : atoms.Nodup) (t₁ t₂ i j : Nat)
    (hi : atoms[i]? = some t₁) (hj : atoms[j]? = some t₂) (ij : i ≠ j) (positions : List Nat)
    (inRange : ∀ p ∈ positions, p < atoms.length) :
    (positions.map (swapIdx i j)).mapM (fun p => atoms[p]?) =
      (positions.mapM (fun p => atoms[p]?)).map (List.map (swapAtom t₁ t₂)) := by
  rw [List.mapM_map, ← mapM_option_map]
  apply mapM_congr
  intro p member
  exact getElem?_swapIdx atoms nodup t₁ t₂ i j hi hj ij p (inRange p member)

/-! ## Facts about a successful `mapM` of frame lookups -/

theorem mapM_getElem?_forall₂ (atoms : List Nat) :
    ∀ (positions : List Nat) (L : List Nat), positions.mapM (fun p => atoms[p]?) = some L →
      List.Forall₂ (fun p a => atoms[p]? = some a) positions L
  | [], L, h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      exact .nil
  | p :: ps, L, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, ha, as, has, rfl⟩ := h
      exact .cons ha (mapM_getElem?_forall₂ atoms ps as has)

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | [], [], _, a, member => by simp at member
  | _ :: _, _ :: _, .cons h ht, a, member => by
      rcases List.mem_cons.mp member with rfl | rest
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨b, bMem, hb⟩ := forall₂_mem_left ht a rest
        exact ⟨b, List.mem_cons_of_mem _ bMem, hb⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | [], [], _, b, member => by simp at member
  | _ :: _, _ :: _, .cons h ht, b, member => by
      rcases List.mem_cons.mp member with rfl | rest
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨a, aMem, ha⟩ := forall₂_mem_right ht b rest
        exact ⟨a, List.mem_cons_of_mem _ aMem, ha⟩

theorem lookup_nodup (atoms : List Nat) (atomsNodup : atoms.Nodup) :
    ∀ {positions L : List Nat}, positions.Nodup →
      List.Forall₂ (fun p a => atoms[p]? = some a) positions L → L.Nodup
  | [], [], _, _ => List.nodup_nil
  | p :: ps, a :: as, nodup, .cons h ht => by
      obtain ⟨notMem, tailNodup⟩ := List.nodup_cons.mp nodup
      refine List.nodup_cons.mpr ⟨?_, lookup_nodup atoms atomsNodup tailNodup ht⟩
      intro aMem
      obtain ⟨q, qMem, hq⟩ := forall₂_mem_right ht a aMem
      exact notMem (getElem?_inj_of_nodup atoms atomsNodup q p a hq h ▸ qMem)

/-! ## Geometry: exchanging two of four priority-ordered atoms complements the letter -/

theorem volume_swap12 (a b c d : CartesianPoint3) :
    orientedVolume b a c d = - orientedVolume a b c d := by
  simp only [orientedVolume]; ring
theorem volume_swap13 (a b c d : CartesianPoint3) :
    orientedVolume c b a d = - orientedVolume a b c d := by
  simp only [orientedVolume]; ring
theorem volume_swap14 (a b c d : CartesianPoint3) :
    orientedVolume d b c a = - orientedVolume a b c d := by
  simp only [orientedVolume]; ring
theorem volume_swap23 (a b c d : CartesianPoint3) :
    orientedVolume a c b d = - orientedVolume a b c d := by
  simp only [orientedVolume]; ring
theorem volume_swap24 (a b c d : CartesianPoint3) :
    orientedVolume a d c b = - orientedVolume a b c d := by
  simp only [orientedVolume]; ring
theorem volume_swap34 (a b c d : CartesianPoint3) :
    orientedVolume a b d c = - orientedVolume a b c d := by
  simp only [orientedVolume]; ring

theorem descriptorOfOrientedVolume?_neg (v : ℚ) :
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? (-v) =
      (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? v).map RS.swap := by
  unfold CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
  rcases lt_trichotomy v 0 with neg | zero | pos
  · have negPos : 0 < -v := neg_pos.mpr neg
    have notNeg : ¬ (-v < 0) := not_lt.mpr negPos.le
    rw [if_neg notNeg, if_pos negPos, if_pos neg]
    rfl
  · subst zero
    simp
  · have negNeg : -v < 0 := neg_lt_zero.mpr pos
    have notNeg : ¬ (v < 0) := not_lt.mpr pos.le
    rw [if_pos negNeg, if_neg notNeg, if_pos pos]
    rfl

/-- Explicit four-point readback as nested lookups. -/
theorem readback4 (geom : Geometry) (a b c d : Nat) :
    readback? geom [a, b, c, d] =
      (geom a).bind fun pa => (geom b).bind fun pb => (geom c).bind fun pc => (geom d).bind fun pd =>
        CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? (orientedVolume pa pb pc pd) := by
  unfold readback?
  simp only [List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind]
  cases geom a <;> cases geom b <;> cases geom c <;> cases geom d <;> rfl

theorem readback_swap12 (geom : Geometry) (a b c d : Nat) :
    readback? geom [b, a, c, d] = (readback? geom [a, b, c, d]).map RS.swap := by
  rw [readback4, readback4]
  cases geom a <;> cases geom b <;> cases geom c <;> cases geom d <;>
    first
    | rfl
    | (dsimp only [Option.bind]
       rw [volume_swap12, descriptorOfOrientedVolume?_neg])

theorem readback_swap13 (geom : Geometry) (a b c d : Nat) :
    readback? geom [c, b, a, d] = (readback? geom [a, b, c, d]).map RS.swap := by
  rw [readback4, readback4]
  cases geom a <;> cases geom b <;> cases geom c <;> cases geom d <;>
    first
    | rfl
    | (dsimp only [Option.bind]
       rw [volume_swap13, descriptorOfOrientedVolume?_neg])

theorem readback_swap14 (geom : Geometry) (a b c d : Nat) :
    readback? geom [d, b, c, a] = (readback? geom [a, b, c, d]).map RS.swap := by
  rw [readback4, readback4]
  cases geom a <;> cases geom b <;> cases geom c <;> cases geom d <;>
    first
    | rfl
    | (dsimp only [Option.bind]
       rw [volume_swap14, descriptorOfOrientedVolume?_neg])

theorem readback_swap23 (geom : Geometry) (a b c d : Nat) :
    readback? geom [a, c, b, d] = (readback? geom [a, b, c, d]).map RS.swap := by
  rw [readback4, readback4]
  cases geom a <;> cases geom b <;> cases geom c <;> cases geom d <;>
    first
    | rfl
    | (dsimp only [Option.bind]
       rw [volume_swap23, descriptorOfOrientedVolume?_neg])

theorem readback_swap24 (geom : Geometry) (a b c d : Nat) :
    readback? geom [a, d, c, b] = (readback? geom [a, b, c, d]).map RS.swap := by
  rw [readback4, readback4]
  cases geom a <;> cases geom b <;> cases geom c <;> cases geom d <;>
    first
    | rfl
    | (dsimp only [Option.bind]
       rw [volume_swap24, descriptorOfOrientedVolume?_neg])

theorem readback_swap34 (geom : Geometry) (a b c d : Nat) :
    readback? geom [a, b, d, c] = (readback? geom [a, b, c, d]).map RS.swap := by
  rw [readback4, readback4]
  cases geom a <;> cases geom b <;> cases geom c <;> cases geom d <;>
    first
    | rfl
    | (dsimp only [Option.bind]
       rw [volume_swap34, descriptorOfOrientedVolume?_neg])

theorem map_swapAtom_eq (t₁ t₂ : Nat) (ne : t₁ ≠ t₂) (a b c d : Nat)
    (nodup : [a, b, c, d].Nodup) (m₁ : t₁ ∈ [a, b, c, d]) (m₂ : t₂ ∈ [a, b, c, d]) :
    ([a, b, c, d].map (swapAtom t₁ t₂) = [b, a, c, d]) ∨
    ([a, b, c, d].map (swapAtom t₁ t₂) = [c, b, a, d]) ∨
    ([a, b, c, d].map (swapAtom t₁ t₂) = [d, b, c, a]) ∨
    ([a, b, c, d].map (swapAtom t₁ t₂) = [a, c, b, d]) ∨
    ([a, b, c, d].map (swapAtom t₁ t₂) = [a, d, c, b]) ∨
    ([a, b, c, d].map (swapAtom t₁ t₂) = [a, b, d, c]) := by
  have ab : a ≠ b := fun h => by simp [h] at nodup
  have ac : a ≠ c := fun h => by simp [h] at nodup
  have ad : a ≠ d := fun h => by simp [h] at nodup
  have bc : b ≠ c := fun h => by simp [h] at nodup
  have bd : b ≠ d := fun h => by simp [h] at nodup
  have cd : c ≠ d := fun h => by simp [h] at nodup
  have ba : b ≠ a := fun h => ab h.symm
  have ca : c ≠ a := fun h => ac h.symm
  have da : d ≠ a := fun h => ad h.symm
  have cb : c ≠ b := fun h => bc h.symm
  have db : d ≠ b := fun h => bd h.symm
  have dc : d ≠ c := fun h => cd h.symm
  simp at m₁ m₂
  rcases m₁ with h₁ | h₁ | h₁ | h₁ <;> rcases m₂ with h₂ | h₂ | h₂ | h₂ <;> subst h₁ <;> subst h₂ <;>
    simp [swapAtom, ab, ac, ad, bc, bd, cd, ba, ca, da, cb, db, dc] at ne ⊢

/-- Exchanging two distinct atoms of a duplicate-free four-atom priority list complements the
geometric raw letter, for every geometry (both refuse together when a coordinate is missing). -/
theorem readback_swapAtom (geom : Geometry) (t₁ t₂ : Nat) (ne : t₁ ≠ t₂) (l : List Nat)
    (nodup : l.Nodup) (length : l.length = 4) (m₁ : t₁ ∈ l) (m₂ : t₂ ∈ l) :
    readback? geom (l.map (swapAtom t₁ t₂)) = (readback? geom l).map RS.swap := by
  match l, length with
  | [a, b, c, d], _ =>
      rcases map_swapAtom_eq t₁ t₂ ne a b c d nodup m₁ m₂ with h | h | h | h | h | h <;> rw [h]
      · exact readback_swap12 geom a b c d
      · exact readback_swap13 geom a b c d
      · exact readback_swap14 geom a b c d
      · exact readback_swap23 geom a b c d
      · exact readback_swap24 geom a b c d
      · exact readback_swap34 geom a b c d

/-! ## Two actual marked readings under exchanged comparators are complements -/

theorem marked_unfold (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (roots : List Cursor) (frame : occurrenceLigandFrame? mol node = some roots)
    (mark : Nat) (member : mark ∈ frameAtomsOf roots) :
    LocalizedMarkedUncappedOperations.marked? mol [] node mark =
      rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative? mol [] mark
        (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots := by
  have bound : (frameAtomsOf roots).idxOf mark < (frameAtomsOf roots).length :=
    List.idxOf_lt_length_iff.mpr member
  have lookup : (frameAtomsOf roots).getD ((frameAtomsOf roots).idxOf mark) 0 = mark := by
    rw [List.getD_eq_getElem?_getD]
    simp [List.getElem?_idxOf member]
  have notLe : ¬ (frameAtomsOf roots).length ≤ (frameAtomsOf roots).idxOf mark :=
    Nat.not_le_of_lt bound
  unfold LocalizedMarkedUncappedOperations.marked?
  rw [frame]
  show (if (frameAtomsOf roots).idxOf mark ≥ (frameAtomsOf roots).length then none else
      authoritativeOccurrenceRule6PositionRankingBackend mol [] (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots
        (frameAtomsOf roots) ((frameAtomsOf roots).idxOf mark)) = _
  rw [if_neg notLe]
  unfold authoritativeOccurrenceRule6PositionRankingBackend authoritativeOccurrenceRule6RankingBackend
  rw [lookup]

theorem frameAtoms_getElem? (roots : List Cursor) (p : Nat) :
    (frameAtomsOf roots)[p]? = (roots[p]?).map (·.node.atom) := by
  simp [frameAtomsOf, List.getElem?_map]

/-- If both own-twin readings succeed they are complements; refusal of either is handled by the
consensus separately. The marks are the two exchanged cursors' atoms. -/
theorem readings_complement (mol : RawMolecule) (geom : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (roots : List Cursor)
    (frame : occurrenceLigandFrame? mol node = some roots) (nodup : roots.Nodup)
    (atomsNodup : (frameAtomsOf roots).Nodup) (u v : Cursor) (i j : Nat)
    (hu : roots[i]? = some u) (hv : roots[j]? = some v) (distinct : u ≠ v)
    (symmetry : ∀ a ∈ roots, ∀ b ∈ roots,
      cursorCompare mol [] v.node.atom (LocalizedMarkedUncappedOperations.comparisonFuel mol) a b =
        cursorCompare mol [] u.node.atom (LocalizedMarkedUncappedOperations.comparisonFuel mol)
          (swapCursor u v a) (swapCursor u v b))
    (ℓ₁ ℓ₂ : RS)
    (read₁ : markedReading? mol (LocalizedMarkedUncappedEvaluator.operations mol) geom [] node
      u.node.atom = some ℓ₁)
    (read₂ : markedReading? mol (LocalizedMarkedUncappedEvaluator.operations mol) geom [] node
      v.node.atom = some ℓ₂) : ℓ₂ = ℓ₁.swap := by
  have uMem : u ∈ roots := List.mem_of_getElem? hu
  have vMem : v ∈ roots := List.mem_of_getElem? hv
  have uAtom : u.node.atom ∈ frameAtomsOf roots := List.mem_map.mpr ⟨u, uMem, rfl⟩
  have vAtom : v.node.atom ∈ frameAtomsOf roots := List.mem_map.mpr ⟨v, vMem, rfl⟩
  have frameAtoms : LocalizedGenericMarkedRecalculation.frameAtoms? mol node =
      some (frameAtomsOf roots) := by
    simp [LocalizedGenericMarkedRecalculation.frameAtoms?, frame]
  have hi : (frameAtomsOf roots)[i]? = some u.node.atom := by rw [frameAtoms_getElem?, hu]; rfl
  have hj : (frameAtomsOf roots)[j]? = some v.node.atom := by rw [frameAtoms_getElem?, hv]; rfl
  have ij : i ≠ j := by
    intro same
    rw [same, hv] at hu
    exact distinct (Option.some.inj hu).symm
  have atomNe : u.node.atom ≠ v.node.atom := by
    intro same
    rw [same] at hi
    exact ij (getElem?_inj_of_nodup _ atomsNodup i j _ hi hj)
  have four := AuthoritativeCIPRule6Scheduler.occurrenceLigandFrame?_result_length mol node roots
    frame
  have rootsLength : roots.length = (frameAtomsOf roots).length := by simp [frameAtomsOf]
  simp only [markedReading?, LocalizedMarkedUncappedEvaluator.operations, frameAtoms,
    Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at read₁ read₂
  rw [marked_unfold mol node roots frame u.node.atom uAtom] at read₁
  rw [marked_unfold mol node roots frame v.node.atom vAtom] at read₂
  obtain ⟨r₁, rank₁, L₁, ranked₁, letter₁⟩ := read₁
  obtain ⟨r₂, rank₂, L₂, ranked₂, letter₂⟩ := read₂
  have posPerm₁ := rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?_positions_perm
    mol [] u.node.atom _ roots r₁ rank₁
  simp only [rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq] at rank₁ rank₂
  obtain ⟨tracked₁, sorted₁, rfl⟩ := rank₁
  obtain ⟨tracked₂, sorted₂, rfl⟩ := rank₂
  simp only [LocalizedGenericMarkedRecalculation.rankedAtoms?] at ranked₁ ranked₂
  have unique₁ : tracked₁.2.2 = true := by
    by_contra h
    simp [h] at ranked₁
  have unique₂ : tracked₂.2.2 = true := by
    by_contra h
    simp [h] at ranked₂
  simp only [unique₁, unique₂, ↓reduceIte] at ranked₁ ranked₂
  simp only at posPerm₁
  have positions := positions_related mol [] u.node.atom v.node.atom
    (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots nodup u v i j hu hv distinct
    symmetry tracked₁ tracked₂ sorted₁ unique₁ sorted₂ unique₂
  have inRange : ∀ p ∈ tracked₁.1.map Prod.snd, p < (frameAtomsOf roots).length := by
    intro p member
    have := List.mem_range.mp (posPerm₁.mem_iff.mp member)
    simpa [frameAtomsOf] using this
  have swapped := rankedAtoms_swap (frameAtomsOf roots) atomsNodup u.node.atom v.node.atom i j hi
    hj ij (tracked₁.1.map Prod.snd) inRange
  rw [← positions, ranked₂, ranked₁] at swapped
  simp only [Option.map_some, Option.some.injEq] at swapped
  subst swapped
  have related := mapM_getElem?_forall₂ (frameAtomsOf roots) _ L₁ ranked₁
  have posNodup : (tracked₁.1.map Prod.snd).Nodup :=
    posPerm₁.nodup_iff.mpr List.nodup_range
  have L₁Nodup : L₁.Nodup := lookup_nodup _ atomsNodup posNodup related
  have L₁Length : L₁.length = 4 := by
    rw [← related.length_eq, posPerm₁.length_eq, List.length_range]
    exact four
  have iLt : i < roots.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp hu
    exact bound
  have jLt : j < roots.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp hv
    exact bound
  have iMem : i ∈ tracked₁.1.map Prod.snd := posPerm₁.mem_iff.mpr (List.mem_range.mpr iLt)
  have jMem : j ∈ tracked₁.1.map Prod.snd := posPerm₁.mem_iff.mpr (List.mem_range.mpr jLt)
  have t₁Mem : u.node.atom ∈ L₁ := by
    obtain ⟨a, aMem, ha⟩ := forall₂_mem_left related i iMem
    rw [hi] at ha
    rw [Option.some.inj ha]
    exact aMem
  have t₂Mem : v.node.atom ∈ L₁ := by
    obtain ⟨a, aMem, ha⟩ := forall₂_mem_left related j jMem
    rw [hj] at ha
    rw [Option.some.inj ha]
    exact aMem
  have complement := readback_swapAtom geom u.node.atom v.node.atom atomNe L₁ L₁Nodup L₁Length
    t₁Mem t₂Mem
  rw [letter₂, letter₁] at complement
  exact Option.some.inj complement

end TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap.sorted_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap.positions_related
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap.readback_swapAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap.readings_complement
