import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key
import TetraStereo.OneCenter.LocalizedRule5SwapAndSignal
import TetraStereo.OneCenter.LocalizedAutomaticComparisonRank
import TetraStereo.OneCenter.LocalizedTrackedSortSourcePairFidelity
import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedRule5SwapAndSignal





























































namespace CertifiedLocalizedCIPInput

/-! ## The actual compound comparator pulled back to four frame positions -/

/-- The actual complete compound Rules-4b/4c/5 comparator, pulled back along the frame key map.
`Ordering.byKey` is definitionally `cmp (keys i) (keys j)`; it is used so that the existing
`Std.TransCmp` instances for key pullbacks apply directly. -/
def compoundKeyComparison (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) :
    Fin 4 → Fin 4 → Ordering :=
  Ordering.byKey keys input.compareLocalizedRerootCompoundRule45Keys

/-- The pulled-back actual comparator is total and transitive.  This is the existing
`compareLocalizedRerootCompoundRule45Keys_transCmp`, transported along the key map. -/
theorem compoundKeyComparison_transCmp (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) :
    Std.TransCmp (compoundKeyComparison input keys) := by
  letI : Std.TransCmp input.compareLocalizedRerootCompoundRule45Keys :=
    input.compareLocalizedRerootCompoundRule45Keys_transCmp
  unfold compoundKeyComparison
  infer_instance

/-- Explicit separation obligation: distinct frame keys never tie under the complete actual
comparator.  This is strictly weaker than an injective rank: it says the actual comparator decides
every distinct pair, and it is the remaining physical separation fact. -/
def CompoundKeyOffDiagonalStrict (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) : Prop :=
  ∀ i j : Fin 4, i ≠ j → compoundKeyComparison input keys i j ≠ Ordering.eq

/-- Concrete rank: the number of frame keys strictly below `i` in the actual complete compound
order.  This is `comparisonRank` applied to `compoundKeyComparison`; no rank is supplied. -/
def compoundKeyRank (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) : Fin 4 → Nat :=
  comparisonRank (compoundKeyComparison input keys)

/-- Under off-diagonal separation the actual compound comparison is exactly the comparison of the
computed count-smaller-elements ranks. -/
theorem compoundKeyComparison_eq_compare_rank
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys) (i j : Fin 4) :
    compoundKeyComparison input keys i j =
      compare (compoundKeyRank input keys i) (compoundKeyRank input keys j) := by
  letI : Std.TransCmp (compoundKeyComparison input keys) :=
    compoundKeyComparison_transCmp input keys
  simpa [compoundKeyRank] using
    (comparisonRank_ordering (compoundKeyComparison input keys) separated i j)

/-- Off-diagonal separation makes the computed actual rank injective. -/
theorem compoundKeyRank_injective
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys) :
    Function.Injective (compoundKeyRank input keys) := by
  letI : Std.TransCmp (compoundKeyComparison input keys) :=
    compoundKeyComparison_transCmp input keys
  simpa [compoundKeyRank] using
    (comparisonRank_injective (compoundKeyComparison input keys) separated)

/-! ## The prior Rules-4b/4c tie classes -/

/-- Frame positions whose complete prior Rules-4b/4c keys tie under the actual prior comparator. -/
def priorKeyTie (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) (i j : Fin 4) : Prop :=
  input.compareLocalizedRerootCompoundRule4bcKeys (keys i).prior (keys j).prior =
    Ordering.eq

instance priorKeyTieDecidableRel (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) :
    DecidableRel (priorKeyTie input keys) :=
  fun i j => by
    unfold priorKeyTie
    infer_instance

/-- The constructed source enantiomorphic relation: distinct frame positions whose complete prior
Rules-4b/4c keys tie.  The prior tie is the actual comparator equality; the distinctness conjunct
is the usual irreflexive presentation of an unordered pair. -/
def compoundPriorTieRelation (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) (i j : Fin 4) : Prop :=
  i ≠ j ∧ priorKeyTie input keys i j

instance compoundPriorTieRelationDecidableRel (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) :
    DecidableRel (compoundPriorTieRelation input keys) :=
  fun i j => by
    unfold compoundPriorTieRelation priorKeyTie
    infer_instance

/-! ## Reading the lexicographic compound comparison -/

/-- A decisive prior comparison is decisive for the complete compound comparison.  This is the
first-component projection of the actual lexicographic definition. -/
theorem compoundKeyComparison_eq_prior_of_prior_ne
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) {i j : Fin 4}
    (h : input.compareLocalizedRerootCompoundRule4bcKeys
      (keys i).prior (keys j).prior ≠ Ordering.eq) :
    compoundKeyComparison input keys i j =
      input.compareLocalizedRerootCompoundRule4bcKeys (keys i).prior (keys j).prior := by
  have hdecisive : Ordering.byKey (fun key => key.prior)
      input.compareLocalizedRerootCompoundRule4bcKeys (keys i) (keys j) ≠ Ordering.eq := by
    simpa [Ordering.byKey] using h
  simpa [compoundKeyComparison, compareLocalizedRerootCompoundRule45Keys, Ordering.byKey] using
    (localizedCompareLex_eq_left_of_ne
      (cmp₁ := Ordering.byKey (fun key => key.prior)
        input.compareLocalizedRerootCompoundRule4bcKeys)
      (cmp₂ := Ordering.byKey (fun key => key.rule5Readings)
        (input.compareLocalizedRerootCompoundRule5Readings .R))
      (a := keys i) (b := keys j) hdecisive)

/-- Equality of the complete compound comparison forces a prior comparator tie. -/
theorem priorKeyTie_of_compoundKeyComparison_eq
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) {i j : Fin 4}
    (h : compoundKeyComparison input keys i j = Ordering.eq) :
    priorKeyTie input keys i j := by
  simp only [compoundKeyComparison, compareLocalizedRerootCompoundRule45Keys,
    Ordering.byKey] at h
  rw [compareLex_eq_eq] at h
  simpa [Ordering.byKey, priorKeyTie] using h.1

/-! ## Prior tie-class convexity in the complete order -/

/-- Prior tie classes are convex in the complete actual compound order: if `i` and `j` tie prior
to Rule 5 and `k` lies strictly between them in the complete order, then `k` ties with both.  The
proof is a direct case analysis on the prior comparator using only its transitivity and the
lexicographic definition; no convexity is supplied. -/
theorem priorKeyTie_of_compoundKeyComparison_between
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) {i j k : Fin 4}
    (htie : priorKeyTie input keys i j)
    (hik : compoundKeyComparison input keys i k = Ordering.lt)
    (hkj : compoundKeyComparison input keys k j = Ordering.lt) :
    priorKeyTie input keys i k ∧ priorKeyTie input keys k j := by
  haveI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
    input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
  have htie' : input.compareLocalizedRerootCompoundRule4bcKeys
      (keys i).prior (keys j).prior = Ordering.eq := htie
  constructor
  · by_contra hne
    have hne' : input.compareLocalizedRerootCompoundRule4bcKeys
        (keys i).prior (keys k).prior ≠ Ordering.eq := by
      simpa [priorKeyTie] using hne
    have hcmpIK : input.compareLocalizedRerootCompoundRule4bcKeys
        (keys i).prior (keys k).prior = Ordering.lt := by
      have h := hik
      rw [compoundKeyComparison_eq_prior_of_prior_ne input keys hne'] at h
      exact h
    have hlty : input.compareLocalizedRerootCompoundRule4bcKeys
        (keys i).prior (keys j).prior = Ordering.lt := by
      by_cases hkjEq : input.compareLocalizedRerootCompoundRule4bcKeys
          (keys k).prior (keys j).prior = Ordering.eq
      · exact Std.TransCmp.lt_of_lt_of_eq hcmpIK hkjEq
      · have hcmpKJ : input.compareLocalizedRerootCompoundRule4bcKeys
            (keys k).prior (keys j).prior = Ordering.lt := by
          have h := hkj
          rw [compoundKeyComparison_eq_prior_of_prior_ne input keys hkjEq] at h
          exact h
        exact Std.TransCmp.lt_trans hcmpIK hcmpKJ
    rw [htie'] at hlty
    cases hlty
  · by_contra hne
    have hne' : input.compareLocalizedRerootCompoundRule4bcKeys
        (keys k).prior (keys j).prior ≠ Ordering.eq := by
      simpa [priorKeyTie] using hne
    have hcmpKJ : input.compareLocalizedRerootCompoundRule4bcKeys
        (keys k).prior (keys j).prior = Ordering.lt := by
      have h := hkj
      rw [compoundKeyComparison_eq_prior_of_prior_ne input keys hne'] at h
      exact h
    have hlty : input.compareLocalizedRerootCompoundRule4bcKeys
        (keys i).prior (keys j).prior = Ordering.lt := by
      by_cases hikEq : input.compareLocalizedRerootCompoundRule4bcKeys
          (keys i).prior (keys k).prior = Ordering.eq
      · exact Std.TransCmp.lt_of_eq_of_lt hikEq hcmpKJ
      · have hcmpIK : input.compareLocalizedRerootCompoundRule4bcKeys
            (keys i).prior (keys k).prior = Ordering.lt := by
          have h := hik
          rw [compoundKeyComparison_eq_prior_of_prior_ne input keys hikEq] at h
          exact h
        exact Std.TransCmp.lt_trans hcmpIK hcmpKJ
    rw [htie'] at hlty
    cases hlty

/-- Explicit class-size obligation: among any three frame positions tied (prior to Rule 5) with a
common index, at most two of them are distinct.  This is the "each prior tie class has at most two
distinct frame indices" physical input. -/
def PriorTieClassAtMostTwo (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) : Prop :=
  ∀ i j k : Fin 4, priorKeyTie input keys i j → priorKeyTie input keys i k →
    j = k ∨ j = i ∨ k = i

/-- A rank-between witness in a distinct prior-tied pair contradicts the class-size premise. -/
theorem not_between_of_priorKeyTie
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys)
    (maxTwo : PriorTieClassAtMostTwo input keys) {i j k : Fin 4}
    (hne : i ≠ j) (htie : priorKeyTie input keys i j)
    (between :
      (compoundKeyRank input keys i < compoundKeyRank input keys k ∧
          compoundKeyRank input keys k < compoundKeyRank input keys j) ∨
        (compoundKeyRank input keys j < compoundKeyRank input keys k ∧
          compoundKeyRank input keys k < compoundKeyRank input keys i)) : False := by
  haveI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
    input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
  rcases between with ⟨hikRank, hkjRank⟩ | ⟨hjkRank, hkiRank⟩
  · have hik : compoundKeyComparison input keys i k = Ordering.lt := by
      rw [compoundKeyComparison_eq_compare_rank input keys separated i k]
      exact Nat.compare_eq_lt.mpr hikRank
    have hkj : compoundKeyComparison input keys k j = Ordering.lt := by
      rw [compoundKeyComparison_eq_compare_rank input keys separated k j]
      exact Nat.compare_eq_lt.mpr hkjRank
    obtain ⟨htieIK, _⟩ :=
      priorKeyTie_of_compoundKeyComparison_between input keys htie hik hkj
    rcases maxTwo i j k htie htieIK with h | h | h
    · rw [h] at hkjRank
      exact (lt_irrefl _) hkjRank
    · rw [h] at hne
      exact hne rfl
    · rw [h] at hikRank
      exact (lt_irrefl _) hikRank
  · have hjk : compoundKeyComparison input keys j k = Ordering.lt := by
      rw [compoundKeyComparison_eq_compare_rank input keys separated j k]
      exact Nat.compare_eq_lt.mpr hjkRank
    have hki : compoundKeyComparison input keys k i = Ordering.lt := by
      rw [compoundKeyComparison_eq_compare_rank input keys separated k i]
      exact Nat.compare_eq_lt.mpr hkiRank
    have htieJI : priorKeyTie input keys j i := by
      simpa [priorKeyTie] using
        (Std.OrientedCmp.eq_symm
          (cmp := input.compareLocalizedRerootCompoundRule4bcKeys)
          (a := (keys i).prior) (b := (keys j).prior)
          (by simpa [priorKeyTie] using htie))
    obtain ⟨htieJK, _⟩ :=
      priorKeyTie_of_compoundKeyComparison_between input keys htieJI hjk hki
    rcases maxTwo j i k htieJI htieJK with h | h | h
    · rw [h] at hkiRank
      exact (lt_irrefl _) hkiRank
    · rw [h] at hne
      exact hne rfl
    · rw [h] at hjkRank
      exact (lt_irrefl _) hjkRank

/-- The constructed rank and prior-tie relation satisfy the complete independent source structure.
Injectivity comes from actual-comparator separation; symmetry, irreflexivity and matching come from
the actual prior comparator and the class-size premise; mirror convexity is the lexicographic
prior-block convexity lemma combined with the class-size premise. -/
theorem compoundPriorTie_sourceStructure
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys)
    (maxTwo : PriorTieClassAtMostTwo input keys) :
    SourceEnantiomorphicPriorityStructure (compoundKeyRank input keys)
      (compoundPriorTieRelation input keys) := by
  haveI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
    input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
  refine
    { rank_injective := compoundKeyRank_injective input keys separated
      symmetric := ?_
      irreflexive := ?_
      matching := ?_
      convex := ?_ }
  · intro first second h
    exact ⟨Ne.symm h.1,
      Std.OrientedCmp.eq_symm
        (cmp := input.compareLocalizedRerootCompoundRule4bcKeys)
        (a := (keys first).prior) (b := (keys second).prior) h.2⟩
  · intro first h
    exact h.1 rfl
  · intro first second third h1 h2
    rcases maxTwo first second third h1.2 h2.2 with h | h | h
    · exact h
    · exact absurd h.symm h1.1
    · exact absurd h.symm h2.1
  · intro first second third h between
    exact not_between_of_priorKeyTie input keys separated maxTwo h.1 h.2 between

/-! ## The Rule-5 pseudo trace from the prior tie

The actual through-Rule-5 `pseudo` flag is characterized by
`LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff`:
it is true exactly when the prior comparator ties, the common-R reading comparison is strict, and
the common-S reading disagrees.  Under the explicit cross-addressed reading relation
`MirrorReadings`, the common-S comparison is the swap of the common-R comparison, so the flag is
exactly "prior tie and strict common-R comparison".  Off-diagonal separation then makes the
common-R comparison strict for every distinct frame pair, giving the per-pair trace agreement with
the constructed relation.  This is a proof, not a supplied count. -/

/-- Explicit physical cross-reading obligation: every distinct prior-tied frame pair has
cross-addressed common-R/common-S descriptor readings.  This is `MirrorReadings` restricted to the
pairs for which the `pseudo` flag can be true. -/
def PriorTieMirrorReadings (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) : Prop :=
  ∀ i j : Fin 4, i ≠ j → priorKeyTie input keys i j →
    MirrorReadings input (keys i).rule5Readings (keys j).rule5Readings

/-- The per-pair agreement of the actual through-Rule-5 `pseudo` flag with the constructed
distinct-prior-tie relation.  This is a `Prop`, not an assumed count: it is derived below from the
actual pseudo-signal law and the cross-reading premise. -/
def CompoundPseudoAgrees (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) : Prop :=
  ∀ i j : Fin 4,
    (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo =
      decide (compoundPriorTieRelation input keys i j)

/-- Distinct prior-tied frames have a strict common-R reading comparison: the complete compound
comparison equals the common-R comparison after the prior tie, and it is non-`eq` off the
diagonal. -/
theorem compoundThroughRule5_commonR_ne_of_priorTie
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys) {i j : Fin 4}
    (hne : i ≠ j) (htie : priorKeyTie input keys i j) :
    input.compareLocalizedRerootCompoundRule5Readings .R
      (keys i).rule5Readings (keys j).rule5Readings ≠ Ordering.eq := by
  have hfull : compoundKeyComparison input keys i j =
      input.compareLocalizedRerootCompoundRule5Readings .R
        (keys i).rule5Readings (keys j).rule5Readings := by
    have htied : Ordering.byKey (fun key => key.prior)
        input.compareLocalizedRerootCompoundRule4bcKeys (keys i) (keys j) = Ordering.eq := by
      simpa [Ordering.byKey] using htie
    simpa [compoundKeyComparison, compareLocalizedRerootCompoundRule45Keys, Ordering.byKey] using
      (localizedCompareLex_eq_right_of_eq
        (cmp₁ := Ordering.byKey (fun key => key.prior)
          input.compareLocalizedRerootCompoundRule4bcKeys)
        (cmp₂ := Ordering.byKey (fun key => key.rule5Readings)
          (input.compareLocalizedRerootCompoundRule5Readings .R))
        (a := keys i) (b := keys j) htied)
  rw [← hfull]
  exact separated i j hne

/-- Under the cross-reading premise, a distinct prior-tied pair receives `pseudo = true`. -/
theorem compoundThroughRule5_pseudo_eq_true_of_tie
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys) {i j : Fin 4}
    (hne : i ≠ j) (htie : priorKeyTie input keys i j)
    (mirror : MirrorReadings input (keys i).rule5Readings (keys j).rule5Readings) :
    (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo = true := by
  have hstrict := compoundThroughRule5_commonR_ne_of_priorTie input keys separated hne htie
  exact (compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff_of_mirror_of_prior_tie
    input (keys i) (keys j) mirror (by simpa [priorKeyTie] using htie)).mpr hstrict

/-- A non-prior-tied pair receives `pseudo = false`: the actual pseudo signal requires the prior
comparator to tie. -/
theorem compoundThroughRule5_pseudo_eq_false_of_not_tie
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) {i j : Fin 4}
    (h : ¬ priorKeyTie input keys i j) :
    (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo = false := by
  have hne : (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo ≠ true := by
    intro htrue
    have hspec := (compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff
      input (keys i) (keys j)).mp htrue
    exact h (by simpa [priorKeyTie] using hspec.1)
  cases hp : (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo with
  | false => rfl
  | true => exact absurd hp hne

/-- A diagonal pair receives `pseudo = false`: the prior comparator ties reflexively but the
common-R reading comparison is also reflexive, so the strictness requirement fails. -/
theorem compoundThroughRule5_pseudo_eq_false_of_eq
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) {i j : Fin 4}
    (h : i = j) :
    (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo = false := by
  have hne : (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo ≠ true := by
    intro htrue
    have hspec := (compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff
      input (keys i) (keys j)).mp htrue
    have hR : input.compareLocalizedRerootCompoundRule5Readings .R
        (keys i).rule5Readings (keys j).rule5Readings = Ordering.eq := by
      rw [h]
      letI : Std.TransCmp (input.compareLocalizedRerootCompoundRule5Readings .R) :=
        input.compareLocalizedRerootCompoundRule5Readings_transCmp .R
      exact Std.ReflCmp.compare_self
    exact hspec.2.1 hR
  cases hp : (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo with
  | false => rfl
  | true => exact absurd hp hne

/-- **Actual pseudo trace agreement.**  The actual through-Rule-5 `pseudo` flag is true exactly
for distinct frame positions whose actual prior Rules-4b/4c keys tie.  This is proved from the
actual signal law, the cross-reading premise, and actual off-diagonal separation; no comparison
count or desired classification is assumed. -/
theorem compoundThroughRule5_pseudo_eq_true_iff_priorTie
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys)
    (mirror : PriorTieMirrorReadings input keys) (i j : Fin 4) :
    (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo = true ↔
      compoundPriorTieRelation input keys i j := by
  constructor
  · intro hp
    have hspec := (compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff
      input (keys i) (keys j)).mp hp
    refine ⟨?_, by simpa [priorKeyTie] using hspec.1⟩
    intro hij
    have hR : input.compareLocalizedRerootCompoundRule5Readings .R
        (keys i).rule5Readings (keys j).rule5Readings = Ordering.eq := by
      rw [hij]
      letI : Std.TransCmp (input.compareLocalizedRerootCompoundRule5Readings .R) :=
        input.compareLocalizedRerootCompoundRule5Readings_transCmp .R
      exact Std.ReflCmp.compare_self
    exact hspec.2.1 hR
  · rintro ⟨hij, htie⟩
    exact compoundThroughRule5_pseudo_eq_true_of_tie input keys separated hij htie
      (mirror i j hij htie)

/-- The per-pair pseudo trace agreement follows from actual separation and the cross-reading
premise.  This is the `ComparatorAgreesWithSource` pseudo component; it is derived, not assumed. -/
theorem compoundPseudoAgrees_of_priorTieMirror
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys)
    (mirror : PriorTieMirrorReadings input keys) :
    CompoundPseudoAgrees input keys := by
  intro i j
  have hiff := compoundThroughRule5_pseudo_eq_true_iff_priorTie input keys separated mirror i j
  by_cases h : compoundPriorTieRelation input keys i j
  · rw [show decide (compoundPriorTieRelation input keys i j) = true from decide_eq_true h]
    exact hiff.mpr h
  · rw [show decide (compoundPriorTieRelation input keys i j) = false from decide_eq_false h]
    cases hp : (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)).pseudo with
    | false => rfl
    | true => exact absurd (hiff.mp hp) h

/-! ## Feeding the actual callback into the tracked sort -/

/-- The actual comparison callback used by the production four-ligand tracked sort: at positions
`i, j` it returns the actual compound through-Rule-5 comparison of the frame keys, converted to
the descriptor-hierarchy record by the production adapter
`localizedOccurrenceRule45ComparisonRecord` (which preserves `ordering` and `pseudo` and leaves
`decisiveRule?` at its default), exactly as `compareLocalizedOccurrenceThroughRule5At?` does. -/
def compoundActualCompareAt (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) (i j : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison :=
  some (localizedOccurrenceRule45ComparisonRecord
    (input.compareLocalizedRerootCompoundThroughRule5 (keys i) (keys j)))

/-- The actual callback agrees with the computed rank and the constructed prior-tie relation.
The ordering component is the actual comparator via `comparisonRank_ordering`; the pseudo
component is `CompoundPseudoAgrees`. -/
theorem compoundActualCompareAt_agrees
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys)
    (pseudoAgrees : CompoundPseudoAgrees input keys) :
    ComparatorAgreesWithSource (compoundActualCompareAt input keys)
      (compoundKeyRank input keys) (compoundPriorTieRelation input keys) := by
  intro i j
  have hord : (input.compareLocalizedRerootCompoundThroughRule5
      (keys i) (keys j)).ordering =
      compare (compoundKeyRank input keys i) (compoundKeyRank input keys j) := by
    rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
    simpa [compoundKeyComparison, Ordering.byKey] using
      compoundKeyComparison_eq_compare_rank input keys separated i j
  simp [trackedComparisonTrace, compoundActualCompareAt,
    localizedOccurrenceRule45ComparisonRecord, hord, pseudoAgrees i j]

/-- **Actual compound source-pair fidelity.**  For four actual compound Rules-4b/4c/5 keys, under
the explicit separation, prior-class-size, and cross-reading obligations, the actual production
four-ligand tracked sort run on the actual compound callback succeeds, sorts the four positions by
the computed count-smaller-elements rank, and its tracked pseudo-comparison count is exactly the
independent six-pair count of the constructed distinct-prior-tie relation.

No source rank, convexity field, sorted list, or comparison count is assumed: the rank and the
`SourceEnantiomorphicPriorityStructure` are constructed above from the actual comparator laws. -/
theorem sortFourLocalizedLigandsTracked_actualCompound_sourcePairFidelity
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys)
    (maxTwo : PriorTieClassAtMostTwo input keys)
    (mirror : PriorTieMirrorReadings input keys) :
    ∃ result,
      sortFourLocalizedLigandsTracked (compoundActualCompareAt input keys) = some result ∧
      result.highestFirst.Perm ([(0 : Fin 4), 1, 2, 3]) ∧
      SortedByRank (compoundKeyRank input keys) result.highestFirst.reverse ∧
      result.pseudoComparisons =
        sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) := by
  have agrees : ComparatorAgreesWithSource (compoundActualCompareAt input keys)
      (compoundKeyRank input keys) (compoundPriorTieRelation input keys) :=
    compoundActualCompareAt_agrees input keys separated
      (compoundPseudoAgrees_of_priorTieMirror input keys separated mirror)
  exact sortFourLocalizedLigandsTracked_sourcePairFidelity
    (compareAt := compoundActualCompareAt input keys)
    (rank := compoundKeyRank input keys)
    (enantiomorphic := compoundPriorTieRelation input keys) agrees
    (compoundPriorTie_sourceStructure input keys separated maxTwo)

/-- Classification corollary: any successful actual compound tracked sort classifies as the
lowercase pseudoasymmetric label exactly when the constructed prior-tie relation has one
enantiomorphic pair. -/
theorem sortFourLocalizedLigandsTracked_actualCompound_pseudoasymmetric_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : CompoundKeyOffDiagonalStrict input keys)
    (maxTwo : PriorTieClassAtMostTwo input keys)
    (mirror : PriorTieMirrorReadings input keys)
    (descriptor : RS) (result : TrackedLocalizedLigandOrder)
    (computed : sortFourLocalizedLigandsTracked (compoundActualCompareAt input keys) =
      some result) :
    classifyTetrahedralRSPseudo descriptor result.pseudoComparisons =
        .pseudoasymmetric (pseudoRSOfRS descriptor) ↔
      sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) = 1 := by
  have agrees : ComparatorAgreesWithSource (compoundActualCompareAt input keys)
      (compoundKeyRank input keys) (compoundPriorTieRelation input keys) :=
    compoundActualCompareAt_agrees input keys separated
      (compoundPseudoAgrees_of_priorTieMirror input keys separated mirror)
  rw [classifyTetrahedralRSPseudo_eq_pseudoasymmetric_iff,
    sortFourLocalizedLigandsTracked_pseudoComparisons_eq_sourcePairCount
      (compareAt := compoundActualCompareAt input keys)
      (rank := compoundKeyRank input keys)
      (enantiomorphic := compoundPriorTieRelation input keys) agrees
      (compoundPriorTie_sourceStructure input keys separated maxTwo) result computed]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the public exports -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundKeyComparison
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundKeyComparison_transCmp
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.CompoundKeyOffDiagonalStrict
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundKeyRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundKeyComparison_eq_compare_rank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundKeyRank_injective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.priorKeyTie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.priorKeyTieDecidableRel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundPriorTieRelation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundPriorTieRelationDecidableRel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundKeyComparison_eq_prior_of_prior_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.priorKeyTie_of_compoundKeyComparison_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.priorKeyTie_of_compoundKeyComparison_between
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.PriorTieClassAtMostTwo
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_between_of_priorKeyTie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundPriorTie_sourceStructure
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.PriorTieMirrorReadings
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.CompoundPseudoAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundThroughRule5_commonR_ne_of_priorTie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundThroughRule5_pseudo_eq_true_of_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundThroughRule5_pseudo_eq_false_of_not_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundThroughRule5_pseudo_eq_false_of_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundThroughRule5_pseudo_eq_true_iff_priorTie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundPseudoAgrees_of_priorTieMirror
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundActualCompareAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundActualCompareAt_agrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortFourLocalizedLigandsTracked_actualCompound_sourcePairFidelity
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortFourLocalizedLigandsTracked_actualCompound_pseudoasymmetric_iff
