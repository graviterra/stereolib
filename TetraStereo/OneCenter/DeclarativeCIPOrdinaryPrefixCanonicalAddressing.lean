import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

open Certificate.CanonicalSphereKey (Key assemble sortDesc keyObservation slotOf WellShaped pad)
open RootedDigraph

/-!
# Ordinary-prefix canonical addressing

`OrdinaryKey` is the lexicographic pair of the constitutional vector and one stereochemical
vector.  That stereochemical vector stores five whole hierarchy keys, in order Rule 3, Rule 4a,
Rule 4b, Rule 4c, Rule 5.  It does not interleave the five rules at each node.  The projection

```
ordinaryKeyPrefix k key = toLex ((ofLex key).1, (ofLex key).2.take k)
```

is therefore weakly monotone for the full ordinary-key order, and the sorted-list argument of
`ordinaryKey_fst` extends from the constitutional half to any initial stereochemical segment.

This module constructs the dense prefix-sorted family, proves the projected key depends only on
stereochemical labels of index less than `k`, and reads those retained labels back from any
prefix-canonical addressing.  The resulting hierarchy judgment is the existing ordinary
`CanonicalOutcome`: admissibility stays the full ordinary family.

The observation lemma takes prefix canonicality as a hypothesis.  It does not prove that an
actual runtime addressing lies in the family.  In particular, prefix `3` retains Rule 3, Rule 4a
and Rule 4b (`stereoIndex` `0`, `1`, `2`).  Rule 5 has `stereoIndex` `4`, so prefix `3` does not
address it.  Membership of an actual original-arm addressing in
`OrdinaryPrefixCanonicalAddressing … 3` remains external integration.
-/

/-! ## List order used by the prefix projection -/

private theorem list_cons_lt_cons_iff {α : Type*} [LinearOrder α] {a b : α} {l m : List α} :
    a :: l < b :: m ↔ a < b ∨ a = b ∧ l < m := by
  constructor
  · intro h
    cases h with
    | cons h => exact Or.inr ⟨rfl, h⟩
    | rel h => exact Or.inl h
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

private theorem list_nil_lt_cons {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    ([] : List α) < a :: l := by
  exact List.Lex.nil

private theorem list_nil_le {α : Type*} [LinearOrder α] : ∀ l : List α, [] ≤ l
  | [] => le_rfl
  | a :: l => le_of_lt (list_nil_lt_cons a l)

private theorem not_cons_le_nil {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    ¬ a :: l ≤ ([] : List α) := by
  intro h
  rcases (le_iff_lt_or_eq).mp h with hlt | heq
  · cases hlt
  · cases heq

private theorem list_cons_le_cons_iff {α : Type*} [LinearOrder α] {a b : α} {l m : List α} :
    a :: l ≤ b :: m ↔ a < b ∨ a = b ∧ l ≤ m := by
  constructor
  · intro h
    rcases (le_iff_lt_or_eq).mp h with hlt | heq
    · rcases (list_cons_lt_cons_iff).mp hlt with hab | ⟨rfl, htail⟩
      · exact Or.inl hab
      · exact Or.inr ⟨rfl, le_of_lt htail⟩
    · have hpair : a = b ∧ l = m := by simpa using heq
      exact Or.inr ⟨hpair.1, le_of_eq hpair.2⟩
  · intro h
    rcases h with hab | ⟨rfl, hle⟩
    · exact le_of_lt ((list_cons_lt_cons_iff).mpr (Or.inl hab))
    · rcases (le_iff_lt_or_eq).mp hle with hlt | rfl
      · exact le_of_lt ((list_cons_lt_cons_iff).mpr (Or.inr ⟨rfl, hlt⟩))
      · exact le_rfl

private theorem list_take_le_take {α : Type*} [LinearOrder α] :
    ∀ (k : ℕ) (l m : List α), l ≤ m → l.take k ≤ m.take k
  | 0, _, _, _ => by
      simp only [List.take_zero]
      exact le_rfl
  | _ + 1, [], m, _ => by
      rw [List.take_nil]
      exact list_nil_le (m.take _)
  | _ + 1, a :: l, [], h => absurd h (not_cons_le_nil a l)
  | k + 1, a :: l, b :: m, h => by
      rw [List.take_succ_cons, List.take_succ_cons]
      rcases (list_cons_le_cons_iff).mp h with hlt | ⟨rfl, hle⟩
      · exact le_of_lt ((list_cons_lt_cons_iff).mpr (Or.inl hlt))
      · exact (list_cons_le_cons_iff).mpr (Or.inr ⟨rfl, list_take_le_take k l m hle⟩)

private theorem getD_take_of_lt {α : Type*} :
    ∀ (k i : ℕ) (l : List α) (d : α), i < k → (l.take k).getD i d = l.getD i d
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ + 1, _, [], _, _ => by
      rw [List.take_nil]
  | _ + 1, 0, _ :: _, _, _ => by
      simp only [List.take_succ_cons, List.getD_cons_zero]
  | k + 1, i + 1, _ :: tail, d, hi => by
      rw [List.take_succ_cons, List.getD_cons_succ, List.getD_cons_succ]
      exact getD_take_of_lt k i tail d (by omega)

/-! ## The prefix of an ordinary key -/

/-- Constitutional vector followed by the first `k` stereochemical components. -/
def ordinaryKeyPrefix (k : ℕ) (key : OrdinaryKey) : OrdinaryKey :=
  toLex ((ofLex key).1, (ofLex key).2.take k)

/-- The prefix projection is weakly monotone for the full ordinary-key order. -/
theorem ordinaryKeyPrefix_mono {k : ℕ} {x y : OrdinaryKey} (h : x ≤ y) :
    ordinaryKeyPrefix k x ≤ ordinaryKeyPrefix k y := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, hsnd⟩
  · exact Prod.Lex.le_iff.mpr (Or.inl hlt)
  · exact Prod.Lex.le_iff.mpr
      (Or.inr ⟨heq, list_take_le_take k _ _ hsnd⟩)

private theorem map_ordinaryKeyPrefix_sortDesc (k : ℕ) (keys : List OrdinaryKey) :
    (sortDesc keys).map (ordinaryKeyPrefix k) =
      sortDesc (keys.map (ordinaryKeyPrefix k)) := by
  have hdesc : ((sortDesc keys).map (ordinaryKeyPrefix k)).Pairwise (fun x y => y ≤ x) := by
    rw [List.pairwise_map]
    exact (Certificate.CanonicalSphereKey.sortDesc_pairwise keys).imp fun h =>
      ordinaryKeyPrefix_mono h
  have hperm : ((sortDesc keys).map (ordinaryKeyPrefix k)).Perm
      (keys.map (ordinaryKeyPrefix k)) :=
    (Certificate.CanonicalSphereKey.sortDesc_perm keys).map (ordinaryKeyPrefix k)
  exact (Certificate.CanonicalSphereKey.sortDesc_of_pairwise hdesc).symm.trans
    (Certificate.CanonicalSphereKey.sortDesc_eq_of_perm hperm)

private theorem map_stereoProjection_of_map_prefix {k : ℕ} {rule : StereochemicalRule}
    (hk : stereoIndex rule < k) {l m : List OrdinaryKey}
    (h : l.map (ordinaryKeyPrefix k) = m.map (ordinaryKeyPrefix k)) :
    l.map (fun key => (ofLex key).2.getD (stereoIndex rule) []) =
      m.map (fun key => (ofLex key).2.getD (stereoIndex rule) []) := by
  have hread (key : OrdinaryKey) :
      (ofLex key).2.getD (stereoIndex rule) [] =
        (ofLex (ordinaryKeyPrefix k key)).2.getD (stereoIndex rule) [] := by
    simp only [ordinaryKeyPrefix, ofLex_toLex]
    exact (getD_take_of_lt k (stereoIndex rule) (ofLex key).2 [] hk).symm
  calc
    l.map (fun key => (ofLex key).2.getD (stereoIndex rule) [])
        = (l.map (ordinaryKeyPrefix k)).map
            (fun key => (ofLex key).2.getD (stereoIndex rule) []) := by
          rw [List.map_map]
          refine List.map_congr_left fun key _ => ?_
          exact hread key
    _ = (m.map (ordinaryKeyPrefix k)).map
          (fun key => (ofLex key).2.getD (stereoIndex rule) []) := by
          rw [h]
    _ = m.map (fun key => (ofLex key).2.getD (stereoIndex rule) []) := by
          rw [List.map_map]
          refine List.map_congr_left fun key _ => ?_
          exact (hread key).symm

private theorem stereoVector_take_eq {k : ℕ}
    {l3 l4a l4b l4c l5 r3 r4a r4b r4c r5 : Key StereoLabel}
    (h3 : 0 < k → l3 = r3) (h4a : 1 < k → l4a = r4a) (h4b : 2 < k → l4b = r4b)
    (h4c : 3 < k → l4c = r4c) (h5 : 4 < k → l5 = r5) :
    ([l3, l4a, l4b, l4c, l5] : List (Key StereoLabel)).take k =
      ([r3, r4a, r4b, r4c, r5] : List (Key StereoLabel)).take k := by
  by_cases h0 : 0 < k
  · by_cases h1 : 1 < k
    · by_cases h2 : 2 < k
      · by_cases h3k : 3 < k
        · by_cases h4 : 4 < k
          · rw [h3 h0, h4a h1, h4b h2, h4c h3k, h5 h4]
          · have hk4 : k = 4 := by omega
            subst hk4
            simp only [List.take_succ_cons, List.take_zero, h3 h0, h4a h1, h4b h2,
              h4c (by decide : (3 : ℕ) < 4)]
        · have hk3 : k = 3 := by omega
          subst hk3
          simp only [List.take_succ_cons, List.take_zero, h3 (by decide), h4a (by decide),
            h4b (by decide)]
      · have hk2 : k = 2 := by omega
        subst hk2
        simp only [List.take_succ_cons, List.take_zero, h3 (by decide), h4a (by decide)]
    · have hk1 : k = 1 := by omega
      subst hk1
      simp only [List.take_succ_cons, List.take_zero, h3 (by decide)]
  · have hk0 : k = 0 := by omega
    subst hk0
    simp only [List.take_zero]

/-! ## Evidence masking for the discarded suffix -/

/-- Drop stereochemical fields of index at least `k`.  Fields of index less than `k` stay. -/
def maskObservation (k : ℕ) (observation : StereochemicalObservation) : StereochemicalObservation where
  rule3 := if 0 < k then observation.rule3 else none
  rule4a := if 1 < k then observation.rule4a else none
  rule4b := if 2 < k then observation.rule4b else none
  rule4c := if 3 < k then observation.rule4c else none
  rule5 := if 4 < k then observation.rule5 else none

/-- The same truncation at every node of one fixed graph. -/
def maskEvidence {Atom : Type u} {graph : RootedDigraph Atom} (k : ℕ)
    (evidence : StereochemicalEvidence graph) :
    StereochemicalEvidence graph :=
  fun node => maskObservation k (evidence node)

/-- A retained rule reads the same encoded label from the masked evidence. -/
theorem stereoLabel_mask_of_lt {Atom : Type u} {graph : RootedDigraph Atom}
    (evidence : StereochemicalEvidence graph)
    (k : ℕ) (rule : StereochemicalRule) (node : graph.Node) (hk : stereoIndex rule < k) :
    stereoLabel graph (maskEvidence k evidence) rule node =
      stereoLabel graph evidence rule node := by
  cases rule with
  | rule3DoubleBondGeometry =>
      have hk0 : 0 < k := by simpa [stereoIndex] using hk
      have hbind : (some (maskEvidence k evidence node)).bind (·.rule3) =
          (some (evidence node)).bind (·.rule3) := by
        rw [Option.bind_some, Option.bind_some]
        simp only [maskEvidence, maskObservation, if_pos hk0]
      simp only [stereoLabel, stereoValue, hbind]
  | rule4aStereogenicUnitKind =>
      have hk1 : 1 < k := by simpa [stereoIndex] using hk
      have hbind : (some (maskEvidence k evidence node)).bind (·.rule4a) =
          (some (evidence node)).bind (·.rule4a) := by
        rw [Option.bind_some, Option.bind_some]
        simp only [maskEvidence, maskObservation, if_pos hk1]
      simp only [stereoLabel, stereoValue, hbind]
  | rule4bLikeUnlikeDescriptorPairs =>
      have hk2 : 2 < k := by simpa [stereoIndex] using hk
      have hbind : (some (maskEvidence k evidence node)).bind (·.rule4b) =
          (some (evidence node)).bind (·.rule4b) := by
        rw [Option.bind_some, Option.bind_some]
        simp only [maskEvidence, maskObservation, if_pos hk2]
      simp only [stereoLabel, stereoValue, hbind]
  | rule4cPseudoasymmetricDescriptor =>
      have hk3 : 3 < k := by simpa [stereoIndex] using hk
      have hbind : (some (maskEvidence k evidence node)).bind (·.rule4c) =
          (some (evidence node)).bind (·.rule4c) := by
        rw [Option.bind_some, Option.bind_some]
        simp only [maskEvidence, maskObservation, if_pos hk3]
      simp only [stereoLabel, stereoValue, hbind]
  | rule5EnantiomorphicDescriptor =>
      have hk4 : 4 < k := by simpa [stereoIndex] using hk
      have hbind : (some (maskEvidence k evidence node)).bind (·.rule5) =
          (some (evidence node)).bind (·.rule5) := by
        rw [Option.bind_some, Option.bind_some]
        simp only [maskEvidence, maskObservation, if_pos hk4]
      simp only [stereoLabel, stereoValue, hbind]

section PrefixKey

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)

/-- The ordinary prefix key of one node, computed from the existing `ordinaryKey`. -/
def ordinaryPrefixKey (k W D : ℕ) (node : graph.Node) : OrdinaryKey :=
  ordinaryKeyPrefix k (ordinaryKey molecule graph evidence W D node)

/-- The stereochemical vector of every ordinary key has the five rule components. -/
theorem ordinaryPrefix_ordinaryKey_stereo_length (W D : ℕ) (node : graph.Node) :
    ((ofLex (ordinaryKey molecule graph evidence W D node)).2).length = 5 := by
  rw [ordinaryKey_eq, ofLex_toLex]
  rfl

/-- Prefix `0` is the constitutional vector key, by `ordinaryKey_fst`. -/
theorem ordinaryPrefixKey_zero (W D : ℕ) (node : graph.Node) :
    ordinaryPrefixKey molecule graph evidence 0 W D node =
      toLex (ruleKey molecule graph W D node, ([] : List (Key StereoLabel))) := by
  unfold ordinaryPrefixKey ordinaryKeyPrefix
  rw [List.take_zero, ordinaryKey_fst]

/-- Prefix `5` is the full ordinary key, because the stereochemical vector has length 5. -/
theorem ordinaryPrefixKey_five (W D : ℕ) (node : graph.Node) :
    ordinaryPrefixKey molecule graph evidence 5 W D node =
      ordinaryKey molecule graph evidence W D node := by
  unfold ordinaryPrefixKey ordinaryKeyPrefix
  rw [List.take_of_length_le
      (le_of_eq (ordinaryPrefix_ordinaryKey_stereo_length molecule graph evidence W D node)),
    Prod.mk.eta]
  rfl

private theorem toLex_nil_snd_le_iff {a b : List (Key ℤ)} :
    (toLex (a, ([] : List (Key StereoLabel))) : OrdinaryKey) ≤ toLex (b, []) ↔ a ≤ b := by
  rw [Prod.Lex.le_iff]
  constructor
  · rintro (hlt | ⟨heq, _⟩)
    · exact le_of_lt hlt
    · exact le_of_eq heq
  · intro hab
    rcases (le_iff_lt_or_eq).mp hab with hlt | rfl
    · exact Or.inl hlt
    · exact Or.inr ⟨rfl, le_rfl⟩

/-- **Prefix commutation.**  On one fixed graph, evidence that agrees at every node on every
stereochemical label of index less than `k` produces the same ordinary prefix key at every node.
Children stay on this graph, at the successor depth; the induction measure is
`graph.height + 1 - depth`.  The constitutional half is `ruleKey` by `ordinaryKey_fst`.  Each
retained stereochemical component is assembled from that rule's own head label and from the
corresponding component of the child prefix keys. -/
theorem ordinaryPrefixKey_eq_of_retainedStereoLabel (k W D : ℕ)
    {left right : StereochemicalEvidence graph}
    (hretained : ∀ node rule, stereoIndex rule < k →
      stereoLabel graph left rule node = stereoLabel graph right rule node) :
    ∀ node, ordinaryPrefixKey molecule graph left k W D node =
      ordinaryPrefixKey molecule graph right k W D node := by
  intro node
  refine node_induction graph (motive := fun node =>
      ordinaryPrefixKey molecule graph left k W D node =
        ordinaryPrefixKey molecule graph right k W D node) ?_ node
  intro node ih
  have hranked :
      (rankedOrdinaryKeys molecule graph left W D node).map (ordinaryKeyPrefix k) =
        (rankedOrdinaryKeys molecule graph right W D node).map (ordinaryKeyPrefix k) := by
    have hL := map_ordinaryKeyPrefix_sortDesc k
      ((graph.childList node).map (ordinaryKey molecule graph left W D))
    have hR := map_ordinaryKeyPrefix_sortDesc k
      ((graph.childList node).map (ordinaryKey molecule graph right W D))
    have hp :
        ((graph.childList node).map (ordinaryKey molecule graph left W D)).map
            (ordinaryKeyPrefix k) =
          ((graph.childList node).map (ordinaryKey molecule graph right W D)).map
            (ordinaryKeyPrefix k) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun child hmem => ?_
      exact ih child ((graph.mem_childList).1 hmem)
    simp only [rankedOrdinaryKeys]
    rw [hL, hR, hp]
  have hcomponent (rule : StereochemicalRule) (hk : stereoIndex rule < k) :
      stereoComponent graph left W D rule node (rankedOrdinaryKeys molecule graph left W D node) =
        stereoComponent graph right W D rule node
          (rankedOrdinaryKeys molecule graph right W D node) := by
    have hmap := map_stereoProjection_of_map_prefix hk hranked
    simp only [stereoComponent, hretained node rule hk, hmap]
  have htake : ((ofLex (ordinaryKey molecule graph left W D node)).2).take k =
      ((ofLex (ordinaryKey molecule graph right W D node)).2).take k := by
    rw [ordinaryKey_eq molecule graph left W D node, ordinaryKey_eq molecule graph right W D node,
      ofLex_toLex, ofLex_toLex]
    exact stereoVector_take_eq
      (fun hk => hcomponent .rule3DoubleBondGeometry (by simpa [stereoIndex] using hk))
      (fun hk => hcomponent .rule4aStereogenicUnitKind (by simpa [stereoIndex] using hk))
      (fun hk => hcomponent .rule4bLikeUnlikeDescriptorPairs (by simpa [stereoIndex] using hk))
      (fun hk => hcomponent .rule4cPseudoasymmetricDescriptor (by simpa [stereoIndex] using hk))
      (fun hk => hcomponent .rule5EnantiomorphicDescriptor (by simpa [stereoIndex] using hk))
  unfold ordinaryPrefixKey ordinaryKeyPrefix
  rw [ordinaryKey_fst molecule graph left W D node, ordinaryKey_fst molecule graph right W D node,
    htake]

/-- Masking every field of index at least `k` leaves the prefix key unchanged. -/
theorem ordinaryPrefixKey_mask (k W D : ℕ) (node : graph.Node) :
    ordinaryPrefixKey molecule graph (maskEvidence k evidence) k W D node =
      ordinaryPrefixKey molecule graph evidence k W D node :=
  ordinaryPrefixKey_eq_of_retainedStereoLabel molecule graph k W D
    (fun node rule hk => stereoLabel_mask_of_lt evidence k rule node hk) node

end PrefixKey

/-! ## The prefix-canonical family -/

section Family

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  {graph : RootedDigraph Atom} (evidence : StereochemicalEvidence graph)

/-- Dense addressings whose siblings descend in the ordinary prefix key of length `k`. -/
def OrdinaryPrefixCanonicalAddressing (k : ℕ) (addressing : graph.Addressing) : Prop :=
  Dense addressing ∧
    KeySorted (ordinaryPrefixKey molecule graph evidence k graph.width graph.height) addressing

/-- Every full ordinary-canonical addressing is prefix-canonical, by monotonicity of
`ordinaryKeyPrefix`. -/
theorem ordinaryCanonical_prefixCanonical {k : ℕ} {addressing : graph.Addressing}
    (h : OrdinaryCanonicalAddressing molecule evidence addressing) :
    OrdinaryPrefixCanonicalAddressing molecule evidence k addressing := by
  refine ⟨h.1, fun parent first second firstSlot secondSlot hfirst hsecond hlt => ?_⟩
  exact ordinaryKeyPrefix_mono
    (h.2 parent first second firstSlot secondSlot hfirst hsecond hlt)

/-- **Existence.**  `keyAddressing` builds a prefix-canonical addressing from any base addressing
of the same graph. -/
theorem exists_ordinaryPrefixCanonicalAddressing (k : ℕ) (base : graph.Addressing) :
    ∃ addressing : graph.Addressing,
      OrdinaryPrefixCanonicalAddressing molecule evidence k addressing :=
  ⟨keyAddressing base (ordinaryPrefixKey molecule graph evidence k graph.width graph.height),
    keyAddressing_dense_sorted base
      (ordinaryPrefixKey molecule graph evidence k graph.width graph.height)⟩

/-- Prefix length 0 is the accepted constitutional canonical family. -/
theorem ordinaryPrefixCanonical_zero_iff {addressing : graph.Addressing} :
    OrdinaryPrefixCanonicalAddressing molecule evidence 0 addressing ↔
      CanonicalAddressing molecule addressing := by
  constructor
  · rintro ⟨hdense, hsorted⟩
    refine ⟨hdense, fun parent first second firstSlot secondSlot hfirst hsecond hlt => ?_⟩
    have hkey := hsorted parent first second firstSlot secondSlot hfirst hsecond hlt
    rw [ordinaryPrefixKey_zero molecule graph evidence graph.width graph.height,
      ordinaryPrefixKey_zero molecule graph evidence graph.width graph.height] at hkey
    exact (toLex_nil_snd_le_iff).mp hkey
  · rintro ⟨hdense, hsorted⟩
    refine ⟨hdense, fun parent first second firstSlot secondSlot hfirst hsecond hlt => ?_⟩
    rw [ordinaryPrefixKey_zero molecule graph evidence graph.width graph.height,
      ordinaryPrefixKey_zero molecule graph evidence graph.width graph.height]
    exact (toLex_nil_snd_le_iff).mpr
      (hsorted parent first second firstSlot secondSlot hfirst hsecond hlt)

/-- Prefix length 5 is the full ordinary canonical family. -/
theorem ordinaryPrefixCanonical_five_iff {addressing : graph.Addressing} :
    OrdinaryPrefixCanonicalAddressing molecule evidence 5 addressing ↔
      OrdinaryCanonicalAddressing molecule evidence addressing := by
  constructor
  · rintro ⟨hdense, hsorted⟩
    refine ⟨hdense, fun parent first second firstSlot secondSlot hfirst hsecond hlt => ?_⟩
    have hkey := hsorted parent first second firstSlot secondSlot hfirst hsecond hlt
    rw [ordinaryPrefixKey_five molecule graph evidence graph.width graph.height,
      ordinaryPrefixKey_five molecule graph evidence graph.width graph.height] at hkey
    exact hkey
  · rintro ⟨hdense, hsorted⟩
    refine ⟨hdense, fun parent first second firstSlot secondSlot hfirst hsecond hlt => ?_⟩
    rw [ordinaryPrefixKey_five molecule graph evidence graph.width graph.height,
      ordinaryPrefixKey_five molecule graph evidence graph.width graph.height]
    exact hsorted parent first second firstSlot secondSlot hfirst hsecond hlt

private theorem rankedStereoProjection_eq_slotOrder (W D k : ℕ) {addressing : graph.Addressing}
    {parent : graph.Node} {count : ℕ} (hdense : DenseAt addressing parent count)
    (hsorted : KeySorted (ordinaryPrefixKey molecule graph evidence k W D) addressing)
    (rule : StereochemicalRule) (hk : stereoIndex rule < k) :
    (rankedOrdinaryKeys molecule graph evidence W D parent).map
        (fun key => (ofLex key).2.getD (stereoIndex rule) []) =
      ((slotList addressing parent count).map (ordinaryKey molecule graph evidence W D)).map
        (fun key => (ofLex key).2.getD (stereoIndex rule) []) := by
  have hslotPrefix :
      sortDesc ((graph.childList parent).map (ordinaryPrefixKey molecule graph evidence k W D)) =
        (slotList addressing parent count).map
          (ordinaryPrefixKey molecule graph evidence k W D) :=
    sortDesc_childKeys_eq_slotOrder (ordinaryPrefixKey molecule graph evidence k W D) hdense hsorted
  have hcanon :
      (sortDesc ((graph.childList parent).map (ordinaryKey molecule graph evidence W D))).map
          (ordinaryKeyPrefix k) =
        sortDesc ((graph.childList parent).map
          (ordinaryPrefixKey molecule graph evidence k W D)) := by
    rw [map_ordinaryKeyPrefix_sortDesc (k := k)]
    refine congrArg sortDesc ?_
    rw [List.map_map]
    refine List.map_congr_left fun _child _ => ?_
    rfl
  have hprefix :
      (rankedOrdinaryKeys molecule graph evidence W D parent).map (ordinaryKeyPrefix k) =
        ((slotList addressing parent count).map (ordinaryKey molecule graph evidence W D)).map
          (ordinaryKeyPrefix k) := by
    rw [rankedOrdinaryKeys, hcanon, hslotPrefix, List.map_map]
    refine List.map_congr_left fun _child _ => ?_
    rfl
  exact map_stereoProjection_of_map_prefix hk hprefix

/-- **Retained observation theorem.**  Dense prefix-key sortedness reads the full ordinary key's
component for every rule of index less than `k`.  The recursive step identifies only the prefix
projections of the canonically sorted child keys and of the slot-order child keys. -/
theorem stereoAddressValue_eq_prefixKeyObservation (W D k : ℕ) {addressing : graph.Addressing}
    (hdense : Dense addressing)
    (hsorted : KeySorted (ordinaryPrefixKey molecule graph evidence k W D) addressing)
    (rule : StereochemicalRule) (hk : stereoIndex rule < k) :
    ∀ (path : List ℕ) (node : graph.Node), (∀ slot ∈ path, slot < W) → path.length ≤ D →
      keyObservation ((ofLex (ordinaryKey molecule graph evidence W D node)).2.getD
          (stereoIndex rule) []) path.length (slotOf W path) =
        stereoAddressValue evidence addressing rule (addressing.address node ++ path)
  | [], node, _, _ => by
      rw [List.append_nil, stereoAddressValue_of_address, ordinaryKey_stereo_getD]
      simp [keyObservation, stereoComponent, assemble, slotOf]
  | slot :: path, node, hdigits, hlength => by
      have hs : slot < W := hdigits slot (by simp)
      have hpath : ∀ i ∈ path, i < W := fun i hi => hdigits i (by simp [hi])
      have hpl : path.length < D := by simp at hlength; omega
      have hbound := Certificate.CanonicalSphereKey.slotOf_lt hpath
      obtain ⟨count, hcount⟩ := hdense node
      have hproj := rankedStereoProjection_eq_slotOrder molecule evidence W D k hcount hsorted
        rule hk
      have hkeys : ∀ key ∈
          ((slotList addressing node count).map (ordinaryKey molecule graph evidence W D)).map
            (fun key => (ofLex key).2.getD (stereoIndex rule) []), WellShaped W D key := by
        intro key hkey
        obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
        obtain ⟨child, _, rfl⟩ := List.mem_map.1 hvector
        exact ordinaryKey_stereo_wellShaped molecule graph evidence W D rule child
      rw [ordinaryKey_stereo_getD]
      simp only [stereoComponent, hproj, keyObservation, assemble, List.length_cons, slotOf,
        List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range hpl, Option.map_some, Option.getD_some,
        Certificate.CanonicalSphereKey.getD_flatMap_range _ _ W
          (fun i _ => Certificate.CanonicalSphereKey.slotLevel_length hkeys hpl i) hs hbound]
      by_cases hocc : slot < count
      · obtain ⟨child, hchild, haddr⟩ := slotList_getD_of_lt hcount hocc
        have ih := stereoAddressValue_eq_prefixKeyObservation W D k hdense hsorted rule hk path
          child hpath (by omega)
        have hpos : addressing.address node ++ slot :: path =
            addressing.address child ++ path := by
          rw [haddr]; simp
        rw [hpos, ← ih]
        have hlenKey : path.length < ((ofLex (ordinaryKey molecule graph evidence W D child)).2.getD
            (stereoIndex rule) []).length := by
          rw [(ordinaryKey_stereo_wellShaped molecule graph evidence W D rule child).1]
          omega
        have hlenKey' : path.length <
            ((ofLex (ordinaryKey molecule graph evidence W D child)).2[stereoIndex rule]?.getD
              []).length := by
          simpa [List.getD_eq_getElem?_getD] using hlenKey
        simp [keyObservation, List.getD_eq_getElem?_getD, List.getElem?_map, hchild,
          List.getElem?_eq_getElem hlenKey']
      · have hnone : ((slotList addressing node count).map
            (ordinaryKey molecule graph evidence W D))[slot]? = none := by
          simp [slotList]
          omega
        have hunocc : ∀ found,
            addressing.address found ≠ addressing.address node ++ slot :: path := by
          intro found hfound
          obtain ⟨ancestor, hancestor⟩ := addressing.prefix_occupied found
            (addressing.address node ++ [slot]) path (by rw [hfound]; simp)
          exact hocc ((hcount slot).1 ⟨ancestor, hancestor⟩)
        rw [stereoAddressValue_of_unoccupied evidence addressing rule hunocc]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hnone, Option.map_none,
          Option.getD_none, List.getElem?_nil, pad, List.getElem?_replicate]
        split <;> rfl

/-- Retained rules agree at every address for any two prefix-canonical addressings. -/
theorem stereoAddressValue_prefixCanonical_eq {k : ℕ} {first second : graph.Addressing}
    (hfirst : OrdinaryPrefixCanonicalAddressing molecule evidence k first)
    (hsecond : OrdinaryPrefixCanonicalAddressing molecule evidence k second)
    (rule : StereochemicalRule) (hk : stereoIndex rule < k) (position : List ℕ) :
    stereoAddressValue evidence first rule position =
      stereoAddressValue evidence second rule position := by
  by_cases hin : (∀ slot ∈ position, slot < graph.width) ∧ position.length ≤ graph.height
  · have h₁ := stereoAddressValue_eq_prefixKeyObservation molecule evidence graph.width
      graph.height k hfirst.1 hfirst.2 rule hk position graph.root hin.1 hin.2
    have h₂ := stereoAddressValue_eq_prefixKeyObservation molecule evidence graph.width
      graph.height k hsecond.1 hsecond.2 rule hk position graph.root hin.1 hin.2
    rw [first.root_address, List.nil_append] at h₁
    rw [second.root_address, List.nil_append] at h₂
    rw [← h₁, ← h₂]
  · have hout : ∀ addressing : graph.Addressing, Dense addressing →
        ∀ node, addressing.address node ≠ position := by
      intro addressing hdense node hnode
      exact hin ⟨hnode ▸ address_slots_lt_width hdense node,
        hnode ▸ address_length_le_height addressing node⟩
    rw [stereoAddressValue_of_unoccupied evidence first rule (hout first hfirst.1),
      stereoAddressValue_of_unoccupied evidence second rule (hout second hsecond.1)]

/-- A prefix-canonical addressing and a full ordinary-canonical addressing agree on retained
rules.  Full ordinary canonicality supplies prefix canonicality; it is not assumed of the prefix
addressing. -/
theorem stereoAddressValue_prefix_eq_ordinaryCanonical {k : ℕ}
    {prefixAddressing ordinaryAddressing : graph.Addressing}
    (hprefix : OrdinaryPrefixCanonicalAddressing molecule evidence k prefixAddressing)
    (hordinary : OrdinaryCanonicalAddressing molecule evidence ordinaryAddressing)
    (rule : StereochemicalRule) (hk : stereoIndex rule < k) (position : List ℕ) :
    stereoAddressValue evidence prefixAddressing rule position =
      stereoAddressValue evidence ordinaryAddressing rule position :=
  stereoAddressValue_prefixCanonical_eq molecule evidence hprefix
    (ordinaryCanonical_prefixCanonical molecule evidence hordinary) rule hk position

end Family

/-! ## Retained hierarchy outcomes and the existing ordinary outcome -/

section OutcomeBridge

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)

/-- Retained-rule hierarchy outcomes agree for any two prefix-canonical addressings of each side.
Occupied and unoccupied addresses stay distinguished until `flattenBot` is applied by
`stereoValue_addressEvidence`. -/
theorem stereochemicalHierarchyOutcome_prefixCanonical_iff (rule : StereochemicalRule) {k : ℕ}
    (hk : stereoIndex rule < k) {left right : RootedDigraph Atom}
    {leftEvidence : StereochemicalEvidence left} {rightEvidence : StereochemicalEvidence right}
    {leftFirst leftSecond : left.Addressing} {rightFirst rightSecond : right.Addressing}
    (hleftFirst : OrdinaryPrefixCanonicalAddressing molecule leftEvidence k leftFirst)
    (hleftSecond : OrdinaryPrefixCanonicalAddressing molecule leftEvidence k leftSecond)
    (hrightFirst : OrdinaryPrefixCanonicalAddressing molecule rightEvidence k rightFirst)
    (hrightSecond : OrdinaryPrefixCanonicalAddressing molecule rightEvidence k rightSecond)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome rule left leftFirst leftEvidence right rightFirst
        rightEvidence outcome ↔
      StereochemicalHierarchyOutcome rule left leftSecond leftEvidence right rightSecond
        rightEvidence outcome := by
  apply FirstDifferenceOutcome.congr
  intro position outcome
  rw [stereochemicalOutcomeAt_iff, stereochemicalOutcomeAt_iff, stereoValue_addressEvidence,
    stereoValue_addressEvidence, stereoValue_addressEvidence, stereoValue_addressEvidence,
    stereoAddressValue_prefixCanonical_eq molecule leftEvidence hleftFirst hleftSecond rule hk
      position,
    stereoAddressValue_prefixCanonical_eq molecule rightEvidence hrightFirst hrightSecond rule hk
      position]

/-- The same agreement between prefix-canonical addressings and full ordinary-canonical
addressings. -/
theorem stereochemicalHierarchyOutcome_prefix_iff_ordinaryCanonical (rule : StereochemicalRule)
    {k : ℕ} (hk : stereoIndex rule < k) {left right : RootedDigraph Atom}
    {leftEvidence : StereochemicalEvidence left} {rightEvidence : StereochemicalEvidence right}
    {leftPrefix : left.Addressing} {rightPrefix : right.Addressing}
    {leftOrdinary : left.Addressing} {rightOrdinary : right.Addressing}
    (hleftPrefix : OrdinaryPrefixCanonicalAddressing molecule leftEvidence k leftPrefix)
    (hrightPrefix : OrdinaryPrefixCanonicalAddressing molecule rightEvidence k rightPrefix)
    (hleftOrdinary : OrdinaryCanonicalAddressing molecule leftEvidence leftOrdinary)
    (hrightOrdinary : OrdinaryCanonicalAddressing molecule rightEvidence rightOrdinary)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome rule left leftPrefix leftEvidence right rightPrefix
        rightEvidence outcome ↔
      StereochemicalHierarchyOutcome rule left leftOrdinary leftEvidence right rightOrdinary
        rightEvidence outcome :=
  stereochemicalHierarchyOutcome_prefixCanonical_iff molecule rule hk hleftPrefix
    (ordinaryCanonical_prefixCanonical molecule leftEvidence hleftOrdinary) hrightPrefix
    (ordinaryCanonical_prefixCanonical molecule rightEvidence hrightOrdinary) outcome

/-- **Fixed-graph bridge.**  For a retained rule, the existing ordinary canonical outcome on these
two graphs — existence of full ordinary-canonical addressings, and agreement of the hierarchy
judgment for every such pair — is the hierarchy judgment of the supplied prefix-canonical
addressings.  Full-family existence is `exists_ordinaryCanonicalAddressing` on the same graphs,
using the prefix addressings as bases.  The admissible family in the universal quantifier remains
`OrdinaryCanonicalAddressing`. -/
theorem ordinaryCanonicalOutcome_iff_prefixHierarchy (rule : StereochemicalRule) {k : ℕ}
    (hk : stereoIndex rule < k) {left right : RootedDigraph Atom}
    (leftEvidence : StereochemicalEvidence left) (rightEvidence : StereochemicalEvidence right)
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (hleft : OrdinaryPrefixCanonicalAddressing molecule leftEvidence k leftAddressing)
    (hright : OrdinaryPrefixCanonicalAddressing molecule rightEvidence k rightAddressing)
    (outcome : Ordering) :
    ((∃ addressing : left.Addressing,
        OrdinaryCanonicalAddressing molecule leftEvidence addressing) ∧
      (∃ addressing : right.Addressing,
        OrdinaryCanonicalAddressing molecule rightEvidence addressing) ∧
      ∀ leftFull : left.Addressing, ∀ rightFull : right.Addressing,
        OrdinaryCanonicalAddressing molecule leftEvidence leftFull →
          OrdinaryCanonicalAddressing molecule rightEvidence rightFull →
            StereochemicalHierarchyOutcome rule left leftFull leftEvidence right rightFull
              rightEvidence outcome) ↔
      StereochemicalHierarchyOutcome rule left leftAddressing leftEvidence right rightAddressing
        rightEvidence outcome := by
  constructor
  · intro hfamily
    rcases hfamily with ⟨⟨leftFull, hleftFull⟩, ⟨rightFull, hrightFull⟩, hall⟩
    exact (stereochemicalHierarchyOutcome_prefix_iff_ordinaryCanonical molecule rule hk hleft
      hright hleftFull hrightFull outcome).mpr (hall leftFull rightFull hleftFull hrightFull)
  · intro hprefix
    refine ⟨exists_ordinaryCanonicalAddressing molecule leftEvidence leftAddressing,
      exists_ordinaryCanonicalAddressing molecule rightEvidence rightAddressing, ?_⟩
    intro leftFull rightFull hleftFull hrightFull
    exact (stereochemicalHierarchyOutcome_prefix_iff_ordinaryCanonical molecule rule hk hleft
      hright hleftFull hrightFull outcome).mp hprefix

/-- The fixed-graph bridge is `CanonicalOutcome` of the ordinary canonical family. -/
theorem withOrdinaryCanonicalAddressing_canonicalOutcome_iff_prefixHierarchy
    {Unit : Type u} (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : StereochemicalRule) {k : ℕ}
    (hk : stereoIndex rule < k) {left right : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (hleft : OrdinaryPrefixCanonicalAddressing data.molecule
      (data.evidence descriptorMap unit left) k leftAddressing)
    (hright : OrdinaryPrefixCanonicalAddressing data.molecule
      (data.evidence descriptorMap unit right) k rightAddressing)
    (outcome : Ordering) :
    data.withOrdinaryCanonicalAddressing.CanonicalOutcome descriptorMap unit rule left right
        outcome ↔
      StereochemicalHierarchyOutcome rule left leftAddressing
        (data.evidence descriptorMap unit left) right rightAddressing
        (data.evidence descriptorMap unit right) outcome :=
  ordinaryCanonicalOutcome_iff_prefixHierarchy data.molecule rule hk
    (data.evidence descriptorMap unit left) (data.evidence descriptorMap unit right)
    leftAddressing rightAddressing hleft hright outcome

end OutcomeBridge

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyPrefix
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyPrefix_mono
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.maskObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.maskEvidence
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoLabel_mask_of_lt
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefixKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefix_ordinaryKey_stereo_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefixKey_zero
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefixKey_five
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefixKey_eq_of_retainedStereoLabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefixKey_mask
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.OrdinaryPrefixCanonicalAddressing
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryCanonical_prefixCanonical
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.exists_ordinaryPrefixCanonicalAddressing
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefixCanonical_zero_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefixCanonical_five_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoAddressValue_eq_prefixKeyObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoAddressValue_prefixCanonical_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoAddressValue_prefix_eq_ordinaryCanonical
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereochemicalHierarchyOutcome_prefixCanonical_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereochemicalHierarchyOutcome_prefix_iff_ordinaryCanonical
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryCanonicalOutcome_iff_prefixHierarchy
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.withOrdinaryCanonicalAddressing_canonicalOutcome_iff_prefixHierarchy
