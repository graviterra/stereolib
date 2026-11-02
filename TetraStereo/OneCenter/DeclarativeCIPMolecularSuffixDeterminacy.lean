import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalAddressing
import TetraStereo.Certificate.CanonicalSphereKey
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical
open Certificate.CanonicalSphereKey

universe u

/-!
# Same-graph molecular suffix determinacy

On one fixed rooted digraph, a supported whole-graph reference population and the absence of
pseudoasymmetric descriptor readings make the Rule 4c and Rule 5 node labels a function of the
Rule 4a and Rule 4b labels.  Prefix-3 equality of ordinary keys is therefore full ordinary-key
equality, and prefix-3 order is full ordinary-key order.

The argument builds an auxiliary dense addressing sorted by the full ordinary key
(`keyAddressing`).  That addressing is a mathematical device.  It is not a claim that any
particular evaluator addressing is already fully canonical.  The two nodes being compared stay on
the original graph, under one evidence assignment and one whole-graph reference population.
Layout bounds `W` and `D` stay arbitrary; `graph.width` and `graph.height` are the specialization
that covers every finite depth of that graph.

A present scalar zero and an absent field remain different `WithBot` values.  This module does not
identify `referencePopulation` with a physical selector.  That bridge is the population proof's
job; until it is accepted, no physical-only facade is stated.
-/

/-- The first three stereochemical components, keeping the constitutional vector intact.

This is the explicit prefix-3 projection `toLex ((ofLex key).1, (ofLex key).2.take 3)`. -/
def ordinaryPrefix3 (key : OrdinaryKey) : OrdinaryKey :=
  toLex ((ofLex key).1, (ofLex key).2.take 3)

/-- Encoded present scalar zero.  It is a real code, distinct from an absent field. -/
abbrev presentScalarZero : StereoCode :=
  encodeHierarchy id (singleEntry (0 : ℕ))

/-- **Absent field versus present scalar zero.**  The outer `WithBot` layer keeps them apart. -/
theorem presentScalarZero_ne_bot : (presentScalarZero : StereoLabel) ≠ ⊥ :=
  WithBot.coe_ne_bot _

/-- Lexicographic `take` preserves list order when both lists are long enough to supply the prefix. -/
private theorem take_le_take_of_le {α : Type _} [LinearOrder α] :
    ∀ (n : ℕ) {l m : List α}, n ≤ l.length → n ≤ m.length → l ≤ m → l.take n ≤ m.take n
  | 0, _, _, _, _, _ => by
      simp
  | n + 1, [], _, hl, _, _ => by
      exact absurd hl (Nat.not_succ_le_zero n)
  | n + 1, _ :: _, [], _, hm, _ => by
      exact absurd hm (Nat.not_succ_le_zero n)
  | n + 1, a :: l, b :: m, hl, hm, hle => by
      rw [List.take_cons (Nat.succ_pos n), List.take_cons (Nat.succ_pos n)]
      have hl' : n ≤ l.length :=
        Nat.le_of_succ_le_succ (by simpa [List.length_cons] using hl)
      have hm' : n ≤ m.length :=
        Nat.le_of_succ_le_succ (by simpa [List.length_cons] using hm)
      rcases (List.cons_le_cons_iff).1 hle with hlt | ⟨rfl, htail⟩
      · exact List.le_of_lt ((List.cons_lt_cons_iff).2 (Or.inl hlt))
      · exact (List.cons_le_cons_iff).2
          (Or.inr ⟨rfl, take_le_take_of_le n hl' hm' htail⟩)

/-- **Prefix projection is monotone** on ordinary keys whose stereochemical vector has length 5. -/
theorem ordinaryPrefix3_mono {a b : OrdinaryKey}
    (ha : (ofLex a).2.length = 5) (hb : (ofLex b).2.length = 5) (h : a ≤ b) :
    ordinaryPrefix3 a ≤ ordinaryPrefix3 b := by
  rw [Prod.Lex.le_iff] at h
  rw [Prod.Lex.le_iff]
  simp only [ordinaryPrefix3, ofLex_toLex] at h ⊢
  rcases h with hlt | ⟨heq, hsnd⟩
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, take_le_take_of_le 3 (by rw [ha]; omega) (by rw [hb]; omega) hsnd⟩

/-- Rule 4a and Rule 4b labels determine Rule 4c and Rule 5 labels, nodewise on one graph. -/
def SuffixLabelDetermined {Atom : Type u} {graph : RootedDigraph Atom}
    (evidence : StereochemicalEvidence graph) : Prop :=
  ∀ x y : graph.Node,
    stereoLabel graph evidence .rule4aStereogenicUnitKind x =
        stereoLabel graph evidence .rule4aStereogenicUnitKind y →
      stereoLabel graph evidence .rule4bLikeUnlikeDescriptorPairs x =
          stereoLabel graph evidence .rule4bLikeUnlikeDescriptorPairs y →
        stereoLabel graph evidence .rule4cPseudoasymmetricDescriptor x =
            stereoLabel graph evidence .rule4cPseudoasymmetricDescriptor y ∧
          stereoLabel graph evidence .rule5EnantiomorphicDescriptor x =
            stereoLabel graph evidence .rule5EnantiomorphicDescriptor y

private theorem getD_of_take_eq {α : Type _} {l m : List α} {n i : ℕ} {d : α}
    (h : l.take n = m.take n) (hi : i < n) : l.getD i d = m.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    ← List.getElem?_take_of_lt (l := l) hi, ← List.getElem?_take_of_lt (l := m) hi, h]

private theorem encodeReadings_singleton_injective {a b : ℕ}
    (h : encodeReadings [[a]] = encodeReadings [[b]]) : a = b := by
  simp only [encodeReadings, List.map_cons, List.map_nil] at h
  obtain ⟨hinner, _⟩ := List.cons_eq_cons.mp h
  obtain ⟨hentry, _⟩ := List.cons_eq_cons.mp hinner
  have hpair := congrArg ofLex hentry
  rw [ofLex_toLex, ofLex_toLex] at hpair
  exact congrArg Prod.snd hpair

/-! ## Generic lifting, for any evidence with the encoded node property -/

section Lifting

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
  (evidence : StereochemicalEvidence graph)

local instance : Fintype graph.Node := graph.nodeFintype

/-- The stereochemical vector of an ordinary key has the five rule components. -/
theorem ordinaryKey_stereo_length (W D : ℕ) (node : graph.Node) :
    ((ofLex (ordinaryKey molecule graph evidence W D node)).2).length = 5 := by
  rw [ordinaryKey_eq, ofLex_toLex]
  rfl

/-- **Auxiliary full addressing.**  Any base addressing determines a dense addressing sorted by the
full ordinary key.  The construction does not inspect an evaluator and does not assume that the
base addressing is canonical. -/
theorem auxiliaryKeyAddressing_dense_sorted (W D : ℕ) (base : graph.Addressing) :
    Dense (keyAddressing base (ordinaryKey molecule graph evidence W D)) ∧
      KeySorted (ordinaryKey molecule graph evidence W D)
        (keyAddressing base (ordinaryKey molecule graph evidence W D)) :=
  keyAddressing_dense_sorted base (ordinaryKey molecule graph evidence W D)

private theorem prefix3_constitutional_eq (W D : ℕ) {x y : graph.Node}
    (h : ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x) =
      ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y)) :
    (ofLex (ordinaryKey molecule graph evidence W D x)).1 =
      (ofLex (ordinaryKey molecule graph evidence W D y)).1 := by
  have hpair := congrArg ofLex h
  rw [ofLex_toLex, ofLex_toLex] at hpair
  exact congrArg Prod.fst hpair

private theorem prefix3_stereo_getD_eq (W D : ℕ) {x y : graph.Node}
    (h : ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x) =
      ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y))
    {i : ℕ} (hi : i < 3) :
    (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD i [] =
      (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD i [] := by
  have hpair := congrArg ofLex h
  rw [ofLex_toLex, ofLex_toLex] at hpair
  exact getD_of_take_eq (congrArg Prod.snd hpair) hi

private theorem pathObservation_eq_stereoAddress (W D : ℕ) {addressing : graph.Addressing}
    (hdense : Dense addressing)
    (hsorted : KeySorted (ordinaryKey molecule graph evidence W D) addressing)
    (rule : StereochemicalRule) (node : graph.Node) (path : List ℕ)
    (hdigits : ∀ slot ∈ path, slot < W) (hlen : path.length ≤ D) :
    pathObservationOf W D
        ((ofLex (ordinaryKey molecule graph evidence W D node)).2.getD (stereoIndex rule) [])
        path =
      stereoAddressValue evidence addressing rule (addressing.address node ++ path) := by
  unfold pathObservationOf
  rw [if_pos ⟨hdigits, hlen⟩]
  exact stereoAddressValue_eq_keyObservation molecule evidence W D hdense hsorted rule path node
    hdigits hlen

private theorem component_addressValue_eq (W D : ℕ) {addressing : graph.Addressing}
    (hdense : Dense addressing)
    (hsorted : KeySorted (ordinaryKey molecule graph evidence W D) addressing)
    (rule : StereochemicalRule) (x y : graph.Node) (path : List ℕ)
    (hdigits : ∀ slot ∈ path, slot < W) (hlen : path.length ≤ D)
    (hcomp : (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD (stereoIndex rule) [] =
      (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD (stereoIndex rule) []) :
    stereoAddressValue evidence addressing rule (addressing.address x ++ path) =
      stereoAddressValue evidence addressing rule (addressing.address y ++ path) := by
  have hx := pathObservation_eq_stereoAddress molecule graph evidence W D hdense hsorted rule x
    path hdigits hlen
  have hy := pathObservation_eq_stereoAddress molecule graph evidence W D hdense hsorted rule y
    path hdigits hlen
  rw [← hx, ← hy, hcomp]

private theorem stereoLabel_eq_at_relative (W D : ℕ) {addressing : graph.Addressing}
    (hdense : Dense addressing)
    (hsorted : KeySorted (ordinaryKey molecule graph evidence W D) addressing)
    (rule : StereochemicalRule) {x y nx ny : graph.Node} {path : List ℕ}
    (hcomp : (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD (stereoIndex rule) [] =
      (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD (stereoIndex rule) [])
    (hdigits : ∀ slot ∈ path, slot < W) (hlen : path.length ≤ D)
    (hnx : addressing.address nx = addressing.address x ++ path)
    (hny : addressing.address ny = addressing.address y ++ path) :
    stereoLabel graph evidence rule nx = stereoLabel graph evidence rule ny := by
  have hobs := component_addressValue_eq molecule graph evidence W D hdense hsorted rule x y path
    hdigits hlen hcomp
  rw [hnx.symm, stereoAddressValue_of_address evidence addressing rule nx, hny.symm,
    stereoAddressValue_of_address evidence addressing rule ny] at hobs
  exact WithBot.coe_injective hobs

private theorem suffix_component_eq (W D : ℕ) (base : graph.Addressing)
    (hdet : SuffixLabelDetermined graph evidence) {rule : StereochemicalRule}
    (hrule : rule = .rule4cPseudoasymmetricDescriptor ∨ rule = .rule5EnantiomorphicDescriptor)
    {x y : graph.Node}
    (hpref : ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x) =
      ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y)) :
    (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD (stereoIndex rule) [] =
      (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD (stereoIndex rule) [] := by
  let key := ordinaryKey molecule graph evidence W D
  let addressing := keyAddressing base key
  have hdense : Dense addressing :=
    (auxiliaryKeyAddressing_dense_sorted molecule graph evidence W D base).1
  have hsorted : KeySorted key addressing :=
    (auxiliaryKeyAddressing_dense_sorted molecule graph evidence W D base).2
  have h4a : (ofLex (key x)).2.getD (stereoIndex .rule4aStereogenicUnitKind) [] =
      (ofLex (key y)).2.getD (stereoIndex .rule4aStereogenicUnitKind) [] :=
    prefix3_stereo_getD_eq molecule graph evidence W D hpref
      (by simp [stereoIndex]; omega)
  have h4b : (ofLex (key x)).2.getD (stereoIndex .rule4bLikeUnlikeDescriptorPairs) [] =
      (ofLex (key y)).2.getD (stereoIndex .rule4bLikeUnlikeDescriptorPairs) [] :=
    prefix3_stereo_getD_eq molecule graph evidence W D hpref
      (by simp [stereoIndex]; omega)
  apply (key_eq_iff_pathObservation
      (ordinaryKey_stereo_wellShaped molecule graph evidence W D rule x)
      (ordinaryKey_stereo_wellShaped molecule graph evidence W D rule y)).2
  intro path
  by_cases hguard : (∀ digit ∈ path, digit < W) ∧ path.length ≤ D
  · have hdigits : ∀ digit ∈ path, digit < W := hguard.1
    have hlen : path.length ≤ D := hguard.2
    rw [pathObservation_eq_stereoAddress molecule graph evidence W D hdense hsorted rule x path
        hdigits hlen,
      pathObservation_eq_stereoAddress molecule graph evidence W D hdense hsorted rule y path
        hdigits hlen]
    have h4aAddr := component_addressValue_eq molecule graph evidence W D hdense hsorted
      .rule4aStereogenicUnitKind x y path hdigits hlen h4a
    have h4bAddr := component_addressValue_eq molecule graph evidence W D hdense hsorted
      .rule4bLikeUnlikeDescriptorPairs x y path hdigits hlen h4b
    by_cases hx : ∃ nx, addressing.address nx = addressing.address x ++ path
    · by_cases hy : ∃ ny, addressing.address ny = addressing.address y ++ path
      · obtain ⟨nx, hnx⟩ := hx
        obtain ⟨ny, hny⟩ := hy
        have hlab4a := stereoLabel_eq_at_relative molecule graph evidence W D hdense hsorted
          .rule4aStereogenicUnitKind h4a hdigits hlen hnx hny
        have hlab4b := stereoLabel_eq_at_relative molecule graph evidence W D hdense hsorted
          .rule4bLikeUnlikeDescriptorPairs h4b hdigits hlen hnx hny
        obtain ⟨h4c, h5⟩ := hdet nx ny hlab4a hlab4b
        have hleft : stereoAddressValue evidence addressing rule (addressing.address x ++ path) =
            (stereoLabel graph evidence rule nx : WithBot StereoLabel) := by
          rw [hnx.symm]
          exact stereoAddressValue_of_address evidence addressing rule nx
        have hright : stereoAddressValue evidence addressing rule (addressing.address y ++ path) =
            (stereoLabel graph evidence rule ny : WithBot StereoLabel) := by
          rw [hny.symm]
          exact stereoAddressValue_of_address evidence addressing rule ny
        rw [hleft, hright]
        rcases hrule with rfl | rfl
        · exact congrArg (fun z : StereoLabel => (z : WithBot StereoLabel)) h4c
        · exact congrArg (fun z : StereoLabel => (z : WithBot StereoLabel)) h5
      · obtain ⟨nx, hnx⟩ := hx
        have hunocc : ∀ node, addressing.address node ≠ addressing.address y ++ path := by
          intro node hnode
          exact hy ⟨node, hnode⟩
        rw [hnx.symm, stereoAddressValue_of_address evidence addressing
            .rule4aStereogenicUnitKind nx,
          stereoAddressValue_of_unoccupied evidence addressing
            .rule4aStereogenicUnitKind hunocc] at h4aAddr
        exact absurd h4aAddr (WithBot.coe_ne_bot _)
    · by_cases hy : ∃ ny, addressing.address ny = addressing.address y ++ path
      · obtain ⟨ny, hny⟩ := hy
        have hunocc : ∀ node, addressing.address node ≠ addressing.address x ++ path := by
          intro node hnode
          exact hx ⟨node, hnode⟩
        rw [stereoAddressValue_of_unoccupied evidence addressing
            .rule4aStereogenicUnitKind hunocc,
          hny.symm, stereoAddressValue_of_address evidence addressing
            .rule4aStereogenicUnitKind ny] at h4aAddr
        exact absurd h4aAddr.symm (WithBot.coe_ne_bot _)
      · have hunoccx : ∀ node, addressing.address node ≠ addressing.address x ++ path := by
          intro node hnode
          exact hx ⟨node, hnode⟩
        have hunoccy : ∀ node, addressing.address node ≠ addressing.address y ++ path := by
          intro node hnode
          exact hy ⟨node, hnode⟩
        rw [stereoAddressValue_of_unoccupied evidence addressing rule hunoccx,
          stereoAddressValue_of_unoccupied evidence addressing rule hunoccy]
  · unfold pathObservationOf
    rw [if_neg hguard, if_neg hguard]

private theorem stereo_getD_eq_of_prefix (W D : ℕ) (base : graph.Addressing)
    (hdet : SuffixLabelDetermined graph evidence) {x y : graph.Node}
    (hpref : ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x) =
      ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y))
    (i : ℕ) (hi : i < 5) :
    (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD i [] =
      (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD i [] := by
  have hsplit : i < 3 ∨ i = 3 ∨ i = 4 := by omega
  rcases hsplit with hlt | h3 | h4
  · exact prefix3_stereo_getD_eq molecule graph evidence W D hpref hlt
  · rw [h3]
    simpa [stereoIndex] using
      suffix_component_eq molecule graph evidence W D base hdet
        (rule := .rule4cPseudoasymmetricDescriptor) (Or.inl rfl) hpref
  · rw [h4]
    simpa [stereoIndex] using
      suffix_component_eq molecule graph evidence W D base hdet
        (rule := .rule5EnantiomorphicDescriptor) (Or.inr rfl) hpref

/-- **Prefix-3 equality is full ordinary-key equality** on one graph, for evidence whose encoded
node labels obey the Rule 4a/4b to Rule 4c/5 implication.  The proof reads both keys through the
auxiliary full-key addressing of `base`; `base` itself is not assumed canonical. -/
theorem ordinaryPrefix3_eq_iff (W D : ℕ) (base : graph.Addressing)
    (hdet : SuffixLabelDetermined graph evidence) (x y : graph.Node) :
    ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x) =
        ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y) ↔
      ordinaryKey molecule graph evidence W D x =
        ordinaryKey molecule graph evidence W D y := by
  constructor
  · intro hpref
    have hconst := prefix3_constitutional_eq molecule graph evidence W D hpref
    have hvec : (ofLex (ordinaryKey molecule graph evidence W D x)).2 =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2 := by
      apply List.ext_getElem
      · rw [ordinaryKey_stereo_length molecule graph evidence W D x,
          ordinaryKey_stereo_length molecule graph evidence W D y]
      · intro i hi hiy
        have hi5 : i < 5 := by
          rw [ordinaryKey_stereo_length molecule graph evidence W D x] at hi
          exact hi
        have hget := stereo_getD_eq_of_prefix molecule graph evidence W D base hdet hpref i hi5
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hiy] using hget
    have hpair : ofLex (ordinaryKey molecule graph evidence W D x) =
        ofLex (ordinaryKey molecule graph evidence W D y) :=
      Prod.ext hconst hvec
    simpa [toLex_ofLex] using congrArg toLex hpair
  · intro h
    rw [h]

/-- **Full order agrees with prefix-3 order.**  Monotonicity gives one direction.  The other
direction uses totality: a reversed full comparison would force a prefix tie, and prefix-3
injectivity turns that tie into a full tie. -/
theorem ordinaryPrefix3_le_iff (W D : ℕ) (base : graph.Addressing)
    (hdet : SuffixLabelDetermined graph evidence) (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x ≤ ordinaryKey molecule graph evidence W D y ↔
      ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x) ≤
        ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y) := by
  constructor
  · intro h
    exact ordinaryPrefix3_mono
      (ordinaryKey_stereo_length molecule graph evidence W D x)
      (ordinaryKey_stereo_length molecule graph evidence W D y) h
  · intro hpref
    by_contra hnot
    have hlt : ordinaryKey molecule graph evidence W D y <
        ordinaryKey molecule graph evidence W D x := (not_le).1 hnot
    have hback := ordinaryPrefix3_mono
      (ordinaryKey_stereo_length molecule graph evidence W D y)
      (ordinaryKey_stereo_length molecule graph evidence W D x) (le_of_lt hlt)
    have heqp := le_antisymm hpref hback
    have heqk := (ordinaryPrefix3_eq_iff molecule graph evidence W D base hdet x y).1 heqp
    exact lt_irrefl _ (heqk ▸ hlt)

/-- **Strict order agrees with prefix-3 strict order.** -/
theorem ordinaryPrefix3_lt_iff (W D : ℕ) (base : graph.Addressing)
    (hdet : SuffixLabelDetermined graph evidence) (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x < ordinaryKey molecule graph evidence W D y ↔
      ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x) <
        ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y) := by
  constructor
  · intro hlt
    have hle := (ordinaryPrefix3_le_iff molecule graph evidence W D base hdet x y).1 (le_of_lt hlt)
    have hne : ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x) ≠
        ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y) := by
      intro heq
      exact ne_of_lt hlt
        ((ordinaryPrefix3_eq_iff molecule graph evidence W D base hdet x y).1 heq)
    exact lt_of_le_of_ne hle hne
  · intro hlt
    have hle := (ordinaryPrefix3_le_iff molecule graph evidence W D base hdet x y).2 (le_of_lt hlt)
    have hne : ordinaryKey molecule graph evidence W D x ≠
        ordinaryKey molecule graph evidence W D y := by
      intro heq
      exact ne_of_lt hlt (congrArg ordinaryPrefix3 heq)
    exact lt_of_le_of_ne hle hne

/-- **Comparison agrees with prefix-3 comparison.** -/
theorem ordinaryPrefix3_compare_eq (W D : ℕ) (base : graph.Addressing)
    (hdet : SuffixLabelDetermined graph evidence) (x y : graph.Node) :
    compare (ordinaryKey molecule graph evidence W D x)
        (ordinaryKey molecule graph evidence W D y) =
      compare (ordinaryPrefix3 (ordinaryKey molecule graph evidence W D x))
        (ordinaryPrefix3 (ordinaryKey molecule graph evidence W D y)) := by
  rcases lt_trichotomy (ordinaryKey molecule graph evidence W D x)
      (ordinaryKey molecule graph evidence W D y) with hlt | heq | hgt
  · have hleft := compare_lt_iff_lt.2 hlt
    have hright := compare_lt_iff_lt.2
      ((ordinaryPrefix3_lt_iff molecule graph evidence W D base hdet x y).1 hlt)
    exact hleft.trans hright.symm
  · have hleft := compare_eq_iff_eq.2 heq
    have hright := compare_eq_iff_eq.2
      (congrArg ordinaryPrefix3 heq)
    exact hleft.trans hright.symm
  · have hleft := compare_gt_iff_gt.2 hgt
    have hright := compare_gt_iff_gt.2
      ((ordinaryPrefix3_lt_iff molecule graph evidence W D base hdet y x).1 hgt)
    exact hleft.trans hright.symm

/-- **Prefix-3 sibling order is full ordinary sibling order.** -/
theorem keySorted_of_ordinaryPrefix3 (W D : ℕ) (base : graph.Addressing)
    (hdet : SuffixLabelDetermined graph evidence) {addressing : graph.Addressing}
    (hsorted : KeySorted (fun node =>
      ordinaryPrefix3 (ordinaryKey molecule graph evidence W D node)) addressing) :
    KeySorted (ordinaryKey molecule graph evidence W D) addressing := by
  intro parent first second firstSlot secondSlot hfirst hsecond hlt
  exact (ordinaryPrefix3_le_iff molecule graph evidence W D base hdet second first).2
    (hsorted parent first second firstSlot secondSlot hfirst hsecond hlt)

/-- **Dense prefix-3 canonicality at the graph's own width and height is ordinary canonicality.** -/
theorem ordinaryCanonical_of_ordinaryPrefix3 (base : graph.Addressing)
    (hdet : SuffixLabelDetermined graph evidence) {addressing : graph.Addressing}
    (hdense : Dense addressing)
    (hsorted : KeySorted (fun node => ordinaryPrefix3
      (ordinaryKey molecule graph evidence graph.width graph.height node)) addressing) :
    OrdinaryCanonicalAddressing molecule evidence addressing := by
  refine ⟨hdense, ?_⟩
  exact keySorted_of_ordinaryPrefix3 molecule graph evidence graph.width graph.height base hdet
    hsorted

end Lifting

/-! ## Molecular evidence under no pseudo readings and a supported population -/

section Molecular

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance : Fintype graph.Node := graph.nodeFintype

private theorem ofSenses_priority_injective (reference observed₁ observed₂ : DescriptorSense)
    (h : (DescriptorPairKind.ofSenses reference observed₁).priority =
      (DescriptorPairKind.ofSenses reference observed₂).priority) :
    observed₁ = observed₂ := by
  cases reference <;> cases observed₁ <;> cases observed₂
  all_goals
    simp only [DescriptorPairKind.ofSenses, DescriptorPairKind.priority] at h
  all_goals
    first | rfl | cases h

private theorem stereoLabel_rule4a_lift (node : graph.Node) :
    stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule4aStereogenicUnitKind node =
      liftObservation (fun s : Rule4aSignature =>
        encodeHierarchy StereogenicUnitKind.priority s.layers)
        (rule4aObservation molecule descriptorMap unit graph node) := by
  unfold stereoLabel stereoValue molecularEvidence
  rfl

private theorem stereoLabel_rule4b_lift (node : graph.Node) :
    stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule4bLikeUnlikeDescriptorPairs node =
      liftObservation (fun s : Rule4bSignature => encodeReadings s.readings)
        (rule4bObservation molecule descriptorMap unit graph node) := by
  unfold stereoLabel stereoValue molecularEvidence
  rfl

private theorem stereoLabel_rule4c_lift (node : graph.Node) :
    stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule4cPseudoasymmetricDescriptor node =
      liftObservation (fun s : Rule4cSignature => encodeHierarchy id s.layers)
        (rule4cObservation molecule descriptorMap unit graph node) := by
  unfold stereoLabel stereoValue molecularEvidence
  rfl

private theorem stereoLabel_rule5_lift (node : graph.Node) :
    stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule5EnantiomorphicDescriptor node =
      liftObservation (fun s : Rule5Signature => encodeHierarchy id s.layers)
        (rule5Observation molecule descriptorMap unit graph node) := by
  unfold stereoLabel stereoValue molecularEvidence
  rfl

private theorem rule4a_eq_bot_iff (node : graph.Node) :
    stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule4aStereogenicUnitKind node = ⊥ ↔
      occurrenceReading molecule descriptorMap unit graph node = .unavailable := by
  rw [stereoLabel_rule4a_lift molecule descriptorMap unit graph node]
  cases hread : occurrenceReading molecule descriptorMap unit graph node with
  | unavailable =>
      rw [rule4aObservation, hread, liftObservation]
      exact Iff.rfl
  | outsideInventory =>
      rw [rule4aObservation, hread, liftObservation]
      exact iff_of_false (WithBot.coe_ne_bot _) (fun h => nomatch h)
  | unassigned =>
      rw [rule4aObservation, hread, liftObservation]
      exact iff_of_false (WithBot.coe_ne_bot _) (fun h => nomatch h)
  | descriptor value =>
      rw [rule4aObservation, hread, liftObservation]
      exact iff_of_false (WithBot.coe_ne_bot _) (fun h => nomatch h)

private theorem reading_unavailable_iff_of_rule4a {x y : graph.Node}
    (h4a : stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule4aStereogenicUnitKind x =
      stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule4aStereogenicUnitKind y) :
    (occurrenceReading molecule descriptorMap unit graph x = .unavailable) ↔
      (occurrenceReading molecule descriptorMap unit graph y = .unavailable) := by
  rw [← rule4a_eq_bot_iff molecule descriptorMap unit graph x,
    ← rule4a_eq_bot_iff molecule descriptorMap unit graph y, h4a]

private theorem stereoLabel_rule4c_of_noPseudo
    (noPseudo : ∀ (node : graph.Node) (value : Descriptor),
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value →
        value.pseudoSense = none)
    (node : graph.Node) :
    stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule4cPseudoasymmetricDescriptor node =
      (if occurrenceReading molecule descriptorMap unit graph node = .unavailable then ⊥
        else (presentScalarZero : StereoLabel)) := by
  rw [stereoLabel_rule4c_lift molecule descriptorMap unit graph node]
  cases hread : occurrenceReading molecule descriptorMap unit graph node with
  | unavailable =>
      rw [if_pos hread, rule4cObservation, hread, liftObservation]
  | outsideInventory =>
      rw [if_neg (fun h => nomatch h), rule4cObservation, hread, liftObservation]
      rfl
  | unassigned =>
      rw [if_neg (fun h => nomatch h), rule4cObservation, hread, liftObservation]
      rfl
  | descriptor value =>
      rw [if_neg (fun h => nomatch h), rule4cObservation, hread]
      have hpseudo : value.pseudoSense = none := noPseudo node value hread
      rw [hpseudo]
      unfold liftObservation senseValue presentScalarZero singleEntry encodeHierarchy encodeEntry
      rfl

private theorem not_Eligible_of_referencePopulation_empty
    (h : referencePopulation molecule descriptorMap unit graph = .empty) (node : graph.Node) :
    ¬ Eligible molecule descriptorMap unit graph node := by
  intro hnode
  rw [referencePopulation, if_neg (fun hnone => hnone ⟨node, hnode⟩)] at h
  by_cases huniq : ∃! n, NearestEligible molecule descriptorMap unit graph n
  · rw [dif_pos huniq] at h
    cases h
  · rw [dif_neg huniq] at h
    cases h

private theorem eligibleSense_eq_none_of_not {node : graph.Node}
    (h : ¬ Eligible molecule descriptorMap unit graph node) :
    eligibleSense molecule descriptorMap unit graph node = none := by
  cases helig : eligibleSense molecule descriptorMap unit graph node with
  | none => rfl
  | some sense =>
      exact False.elim (h (by simp [Eligible, helig]))

private theorem descriptor_of_eligibleSense_some {node : graph.Node} {sense : DescriptorSense}
    (h : eligibleSense molecule descriptorMap unit graph node = some sense) :
    ∃ value : Descriptor,
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value ∧
        value.chiralSense = some sense := by
  cases hread : occurrenceReading molecule descriptorMap unit graph node with
  | descriptor value =>
      refine ⟨value, rfl, ?_⟩
      simpa [eligibleSense, hread] using h
  | unavailable => simp [eligibleSense, hread] at h
  | outsideInventory => simp [eligibleSense, hread] at h
  | unassigned => simp [eligibleSense, hread] at h

private theorem stereoLabel_rule5_of_eligibleSense_none {node : graph.Node}
    (h : eligibleSense molecule descriptorMap unit graph node = none) :
    stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule5EnantiomorphicDescriptor node =
      (if occurrenceReading molecule descriptorMap unit graph node = .unavailable then ⊥
        else (presentScalarZero : StereoLabel)) := by
  rw [stereoLabel_rule5_lift molecule descriptorMap unit graph node]
  cases hread : occurrenceReading molecule descriptorMap unit graph node with
  | unavailable =>
      rw [if_pos hread, rule5Observation, hread, liftObservation]
  | outsideInventory =>
      rw [if_neg (fun hne => nomatch hne), rule5Observation, hread, liftObservation]
      rfl
  | unassigned =>
      rw [if_neg (fun hne => nomatch hne), rule5Observation, hread, liftObservation]
      rfl
  | descriptor value =>
      rw [if_neg (fun hne => nomatch hne), rule5Observation, hread]
      have hsense : value.chiralSense = none := by
        have hreadSense : eligibleSense molecule descriptorMap unit graph node =
            value.chiralSense := by
          simp [eligibleSense, hread]
        rw [hreadSense] at h
        cases hval : value.chiralSense with
        | none => rfl
        | some sense =>
            rw [hval] at h
            cases h
      rw [hsense]
      unfold liftObservation senseValue presentScalarZero singleEntry encodeHierarchy encodeEntry
      rfl

private theorem presenceLabel_eq {x y : graph.Node}
    (hpres : (occurrenceReading molecule descriptorMap unit graph x = .unavailable) ↔
      (occurrenceReading molecule descriptorMap unit graph y = .unavailable))
    {lx ly : StereoLabel}
    (hx : lx = (if occurrenceReading molecule descriptorMap unit graph x = .unavailable then ⊥
      else (presentScalarZero : StereoLabel)))
    (hy : ly = (if occurrenceReading molecule descriptorMap unit graph y = .unavailable then ⊥
      else (presentScalarZero : StereoLabel))) :
    lx = ly := by
  rw [hx, hy]
  by_cases hxu : occurrenceReading molecule descriptorMap unit graph x = .unavailable
  · rw [if_pos hxu, if_pos (hpres.mp hxu)]
  · have hyu : occurrenceReading molecule descriptorMap unit graph y ≠ .unavailable := by
      intro hyu
      exact hxu (hpres.mpr hyu)
    rw [if_neg hxu, if_neg hyu]

private theorem rule4b_label_of_unique {sense : DescriptorSense}
    (hpop : referencePopulation molecule descriptorMap unit graph = .unique sense)
    (node : graph.Node) :
    stereoLabel graph (molecularEvidence molecule descriptorMap unit graph)
        .rule4bLikeUnlikeDescriptorPairs node =
      match eligibleSense molecule descriptorMap unit graph node with
      | none => ⊥
      | some observed =>
          (encodeReadings [[(DescriptorPairKind.ofSenses sense observed).priority]] : StereoLabel) := by
  rw [stereoLabel_rule4b_lift molecule descriptorMap unit graph node, rule4bObservation, hpop]
  cases helig : eligibleSense molecule descriptorMap unit graph node with
  | none =>
      rw [helig, liftObservation]
  | some observed =>
      rw [helig, liftObservation]
      rfl

/-- A supported population is empty or a single nearest sense. -/
theorem referencePopulation_empty_or_unique_of_supported
    (supported : referencePopulation molecule descriptorMap unit graph ≠ .unsupported) :
    referencePopulation molecule descriptorMap unit graph = .empty ∨
      ∃ sense : DescriptorSense,
        referencePopulation molecule descriptorMap unit graph = .unique sense := by
  cases hpop : referencePopulation molecule descriptorMap unit graph with
  | empty => exact Or.inl hpop
  | unique sense => exact Or.inr ⟨sense, hpop⟩
  | unsupported => exact (supported hpop).elim

/-- **Encoded molecular node lemma.**  On one graph, with no pseudoasymmetric descriptor reading and
a supported whole-graph reference population, equal Rule 4a labels and equal Rule 4b labels give
equal Rule 4c labels and equal Rule 5 labels. -/
theorem molecularEvidence_suffixLabelDetermined
    (noPseudo : ∀ (node : graph.Node) (value : Descriptor),
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value →
        value.pseudoSense = none)
    (supported : referencePopulation molecule descriptorMap unit graph ≠ .unsupported) :
    SuffixLabelDetermined graph (molecularEvidence molecule descriptorMap unit graph) := by
  intro x y h4a h4b
  refine ⟨?_, ?_⟩
  · exact presenceLabel_eq molecule descriptorMap unit graph
      (reading_unavailable_iff_of_rule4a molecule descriptorMap unit graph h4a)
      (stereoLabel_rule4c_of_noPseudo molecule descriptorMap unit graph noPseudo x)
      (stereoLabel_rule4c_of_noPseudo molecule descriptorMap unit graph noPseudo y)
  · cases hpop : referencePopulation molecule descriptorMap unit graph with
    | unsupported => exact (supported hpop).elim
    | empty =>
        have hnone : ∀ node, eligibleSense molecule descriptorMap unit graph node = none :=
          fun node => eligibleSense_eq_none_of_not molecule descriptorMap unit graph
            (not_Eligible_of_referencePopulation_empty molecule descriptorMap unit graph hpop node)
        exact presenceLabel_eq molecule descriptorMap unit graph
          (reading_unavailable_iff_of_rule4a molecule descriptorMap unit graph h4a)
          (stereoLabel_rule5_of_eligibleSense_none molecule descriptorMap unit graph (hnone x))
          (stereoLabel_rule5_of_eligibleSense_none molecule descriptorMap unit graph (hnone y))
    | unique sense =>
        cases hxelig : eligibleSense molecule descriptorMap unit graph x with
        | some ox =>
            cases hyelig : eligibleSense molecule descriptorMap unit graph y with
            | some oy =>
                have hx4b := rule4b_label_of_unique molecule descriptorMap unit graph hpop x
                have hy4b := rule4b_label_of_unique molecule descriptorMap unit graph hpop y
                rw [hxelig] at hx4b
                rw [hyelig] at hy4b
                rw [hx4b, hy4b] at h4b
                have hsens : ox = oy :=
                  ofSenses_priority_injective sense ox oy
                    (encodeReadings_singleton_injective (WithBot.coe_injective h4b))
                subst hsens
                obtain ⟨vx, hxread, hxsense⟩ :=
                  descriptor_of_eligibleSense_some molecule descriptorMap unit graph hxelig
                obtain ⟨vy, hyread, hysense⟩ :=
                  descriptor_of_eligibleSense_some molecule descriptorMap unit graph hyelig
                rw [stereoLabel_rule5_lift molecule descriptorMap unit graph x,
                  stereoLabel_rule5_lift molecule descriptorMap unit graph y, rule5Observation,
                  rule5Observation, hxread, hyread, hxsense, hysense]
                rfl
            | none =>
                have hx4b := rule4b_label_of_unique molecule descriptorMap unit graph hpop x
                have hy4b := rule4b_label_of_unique molecule descriptorMap unit graph hpop y
                rw [hxelig, hyelig] at hx4b hy4b
                rw [hx4b, hy4b] at h4b
                exact absurd h4b (WithBot.coe_ne_bot _)
        | none =>
            cases hyelig : eligibleSense molecule descriptorMap unit graph y with
            | some oy =>
                have hx4b := rule4b_label_of_unique molecule descriptorMap unit graph hpop x
                have hy4b := rule4b_label_of_unique molecule descriptorMap unit graph hpop y
                rw [hxelig, hyelig] at hx4b hy4b
                rw [hx4b, hy4b] at h4b
                exact absurd h4b.symm (WithBot.coe_ne_bot _)
            | none =>
                exact presenceLabel_eq molecule descriptorMap unit graph
                  (reading_unavailable_iff_of_rule4a molecule descriptorMap unit graph h4a)
                  (stereoLabel_rule5_of_eligibleSense_none molecule descriptorMap unit graph hxelig)
                  (stereoLabel_rule5_of_eligibleSense_none molecule descriptorMap unit graph hyelig)

/-- **Molecular prefix-3 equality is full ordinary-key equality** under `noPseudo` and `supported`. -/
theorem molecular_ordinaryPrefix3_eq_iff
    (noPseudo : ∀ (node : graph.Node) (value : Descriptor),
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value →
        value.pseudoSense = none)
    (supported : referencePopulation molecule descriptorMap unit graph ≠ .unsupported)
    (W D : ℕ) (base : graph.Addressing) (x y : graph.Node) :
    ordinaryPrefix3 (ordinaryKey molecule graph
        (molecularEvidence molecule descriptorMap unit graph) W D x) =
      ordinaryPrefix3 (ordinaryKey molecule graph
        (molecularEvidence molecule descriptorMap unit graph) W D y) ↔
      ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D x =
        ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D y :=
  ordinaryPrefix3_eq_iff molecule graph (molecularEvidence molecule descriptorMap unit graph) W D
    base (molecularEvidence_suffixLabelDetermined molecule descriptorMap unit graph noPseudo
      supported) x y

/-- **Molecular full order agrees with prefix-3 order** under `noPseudo` and `supported`. -/
theorem molecular_ordinaryPrefix3_le_iff
    (noPseudo : ∀ (node : graph.Node) (value : Descriptor),
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value →
        value.pseudoSense = none)
    (supported : referencePopulation molecule descriptorMap unit graph ≠ .unsupported)
    (W D : ℕ) (base : graph.Addressing) (x y : graph.Node) :
    ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D x ≤
        ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D y ↔
      ordinaryPrefix3 (ordinaryKey molecule graph
          (molecularEvidence molecule descriptorMap unit graph) W D x) ≤
        ordinaryPrefix3 (ordinaryKey molecule graph
          (molecularEvidence molecule descriptorMap unit graph) W D y) :=
  ordinaryPrefix3_le_iff molecule graph (molecularEvidence molecule descriptorMap unit graph) W D
    base (molecularEvidence_suffixLabelDetermined molecule descriptorMap unit graph noPseudo
      supported) x y

/-- **Molecular strict order agrees with prefix-3 strict order** under `noPseudo` and `supported`. -/
theorem molecular_ordinaryPrefix3_lt_iff
    (noPseudo : ∀ (node : graph.Node) (value : Descriptor),
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value →
        value.pseudoSense = none)
    (supported : referencePopulation molecule descriptorMap unit graph ≠ .unsupported)
    (W D : ℕ) (base : graph.Addressing) (x y : graph.Node) :
    ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D x <
        ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D y ↔
      ordinaryPrefix3 (ordinaryKey molecule graph
          (molecularEvidence molecule descriptorMap unit graph) W D x) <
        ordinaryPrefix3 (ordinaryKey molecule graph
          (molecularEvidence molecule descriptorMap unit graph) W D y) :=
  ordinaryPrefix3_lt_iff molecule graph (molecularEvidence molecule descriptorMap unit graph) W D
    base (molecularEvidence_suffixLabelDetermined molecule descriptorMap unit graph noPseudo
      supported) x y

/-- **Molecular comparison agrees with prefix-3 comparison** under `noPseudo` and `supported`. -/
theorem molecular_ordinaryPrefix3_compare_eq
    (noPseudo : ∀ (node : graph.Node) (value : Descriptor),
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value →
        value.pseudoSense = none)
    (supported : referencePopulation molecule descriptorMap unit graph ≠ .unsupported)
    (W D : ℕ) (base : graph.Addressing) (x y : graph.Node) :
    compare (ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D x)
        (ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D y) =
      compare (ordinaryPrefix3 (ordinaryKey molecule graph
          (molecularEvidence molecule descriptorMap unit graph) W D x))
        (ordinaryPrefix3 (ordinaryKey molecule graph
          (molecularEvidence molecule descriptorMap unit graph) W D y)) :=
  ordinaryPrefix3_compare_eq molecule graph (molecularEvidence molecule descriptorMap unit graph)
    W D base (molecularEvidence_suffixLabelDetermined molecule descriptorMap unit graph noPseudo
      supported) x y

/-- **Molecular prefix-3 sibling order is full ordinary sibling order** under `noPseudo` and
`supported`. -/
theorem molecular_keySorted_of_ordinaryPrefix3
    (noPseudo : ∀ (node : graph.Node) (value : Descriptor),
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value →
        value.pseudoSense = none)
    (supported : referencePopulation molecule descriptorMap unit graph ≠ .unsupported)
    (W D : ℕ) (base : graph.Addressing) {addressing : graph.Addressing}
    (hsorted : KeySorted (fun node => ordinaryPrefix3 (ordinaryKey molecule graph
      (molecularEvidence molecule descriptorMap unit graph) W D node)) addressing) :
    KeySorted (ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D)
      addressing :=
  keySorted_of_ordinaryPrefix3 molecule graph (molecularEvidence molecule descriptorMap unit graph)
    W D base (molecularEvidence_suffixLabelDetermined molecule descriptorMap unit graph noPseudo
      supported) hsorted

/-- **Dense prefix-3 canonicality of molecular evidence is ordinary canonicality**, at this graph's
width and height, under `noPseudo` and `supported`.  `base` is only the seed of the auxiliary
addressing used to prove order agreement. -/
theorem molecular_ordinaryCanonical_of_ordinaryPrefix3
    (noPseudo : ∀ (node : graph.Node) (value : Descriptor),
      occurrenceReading molecule descriptorMap unit graph node = .descriptor value →
        value.pseudoSense = none)
    (supported : referencePopulation molecule descriptorMap unit graph ≠ .unsupported)
    (base : graph.Addressing) {addressing : graph.Addressing}
    (hdense : Dense addressing)
    (hsorted : KeySorted (fun node => ordinaryPrefix3 (ordinaryKey molecule graph
      (molecularEvidence molecule descriptorMap unit graph) graph.width graph.height node))
      addressing) :
    OrdinaryCanonicalAddressing molecule (molecularEvidence molecule descriptorMap unit graph)
      addressing :=
  ordinaryCanonical_of_ordinaryPrefix3 molecule graph
    (molecularEvidence molecule descriptorMap unit graph) base
    (molecularEvidence_suffixLabelDetermined molecule descriptorMap unit graph noPseudo supported)
    hdense hsorted

end Molecular

end

end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefix3
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.presentScalarZero
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.presentScalarZero_ne_bot
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefix3_mono
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.SuffixLabelDetermined
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_stereo_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.auxiliaryKeyAddressing_dense_sorted
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefix3_eq_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefix3_le_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefix3_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryPrefix3_compare_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.keySorted_of_ordinaryPrefix3
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryCanonical_of_ordinaryPrefix3
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referencePopulation_empty_or_unique_of_supported
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecularEvidence_suffixLabelDetermined
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecular_ordinaryPrefix3_eq_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecular_ordinaryPrefix3_le_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecular_ordinaryPrefix3_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecular_ordinaryPrefix3_compare_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecular_keySorted_of_ordinaryPrefix3
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecular_ordinaryCanonical_of_ordinaryPrefix3
