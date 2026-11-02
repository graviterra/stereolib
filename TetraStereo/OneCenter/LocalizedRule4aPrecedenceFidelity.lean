import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcKey
import TetraStereo.OneCenter.LocalizedOccurrenceRule3Through5Descriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Rule-4a precedence fidelity in the localized compound comparison

Primary-source order.  P-92.5.1 states that chiral stereogenic units precede pseudoasymmetric
units and these precede nonstereogenic units; P-92.5.2.1 places the one-reference-over-two
criterion in Rule 4b.  Hanson (2018), Rule 4a, says the purpose of Rule 4a is to ensure that all
comparisons in Rule 4b and later are of the same general type, and that it guarantees the ranked
descriptor lists compared in Rule 4b are of equal length.  Both sources therefore require an
exhaustive Rule-4a comparison before the Rule-4b reference count is observed.

`LocalizedRerootCompoundRule4bcKey` already stores the complete Rule-4a key compiled by
`buildLocalizedRerootCumulativeRule45Key? .rule4a`, and the reference list, reference count, and
readings are all *derived* from that key.  The repaired comparator in
`LocalizedRerootCompoundRule4bcKey.lean` observes the stored Rule-4a key first.

This module records the exact data flow of the actual builder and lifts the precedence law from
bare keys to

* actual `buildLocalizedRerootCompoundRule4bcKey?` outputs (the compound builder image);
* the existing `compareLocalizedRerootCompoundRule45Keys` comparator;
* the existing Rule-3-through-5 comparator, after a Rule-3 tie;
* the descriptor-facing `compareLocalizedOccurrenceRule3Through5At` result;
* the actual four-ligand frame produced by `buildLocalizedOccurrenceRule3Through5KeyFrame?`.

No molecule-level descriptor change is claimed here.  The precedence statements are conditional
order-theoretic consequences of the source rule order; in particular no unreachable molecular
counterexample with a conflicting reference count is fabricated.  The 2018 four-ranking/highest
score Rule-4b process and the reference-dependent maximum/outcome sorting are untouched.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Data flow of the actual compound builder -/

/-- The actual builder derives the reference list from the *Rule-4a key's* ranked labels and the
reference count from that list; the stored Rule-4a key is therefore the source of the later
Rule-4b data, not an independent field. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_dataFlow
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    key.references =
        localizedRule4bReferencesFromRankedLabels key.rule4aKey.rankedLabels ∧
      key.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority key.references := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
      let alternatives := localizedRule4bcReferenceAlternatives references
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor alternatives with
      | none =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
          subst key
          exact ⟨by simp, rfl⟩

/-- The builder's reference data are derived from the exact Rule-4a key that the builder compiled
first, and that key carries the independent Rule-4a derivation. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_rule4a_dataFlow
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    key.references =
        localizedRule4bReferencesFromRankedLabels key.rule4aKey.rankedLabels ∧
      key.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority key.references ∧
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel cursor key.rule4aKey := by
  have flow := input.buildLocalizedRerootCompoundRule4bcKey?_dataFlow
    target view fuel cursor key computed
  exact ⟨flow.1, flow.2,
    (input.buildLocalizedRerootCompoundRule4bcKey?_sound
      target view fuel cursor key computed).1⟩

/-! ## Precedence on actual builder images -/

/-- On two actual `buildLocalizedRerootCompoundRule4bcKey?` outputs, a strict Rule-4a key
comparison determines the compound comparison before the later reference count is inspected, and
both images carry their derived reference data and independent Rule-4a derivations. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_rule4a_precedence_consequence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCompoundRule4bcKey)
    (leftComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel rightCursor = some rightKey)
    (rule4aDecisive : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey.rule4aKey rightKey.rule4aKey ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys leftKey rightKey =
        input.compareLocalizedRerootCumulativeRule45Keys
          leftKey.rule4aKey rightKey.rule4aKey ∧
      leftKey.references =
        localizedRule4bReferencesFromRankedLabels leftKey.rule4aKey.rankedLabels ∧
      rightKey.references =
        localizedRule4bReferencesFromRankedLabels rightKey.rule4aKey.rankedLabels ∧
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel leftCursor leftKey.rule4aKey ∧
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel rightCursor rightKey.rule4aKey := by
  have leftFlow := input.buildLocalizedRerootCompoundRule4bcKey?_rule4a_dataFlow
    target view fuel leftCursor leftKey leftComputed
  have rightFlow := input.buildLocalizedRerootCompoundRule4bcKey?_rule4a_dataFlow
    target view fuel rightCursor rightKey rightComputed
  exact ⟨
    input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      leftKey rightKey rule4aDecisive,
    leftFlow.1, rightFlow.1, leftFlow.2.2, rightFlow.2.2⟩

/-- On actual builder images, a strict Rule-4a decision still wins when the derived reference
counts disagree in the opposite direction. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_rule4a_strict_overrides_count
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCompoundRule4bcKey)
    (leftComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel rightCursor = some rightKey)
    (rule4aStrict : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey.rule4aKey rightKey.rule4aKey = Ordering.lt)
    (countDisagrees : compare leftKey.referenceCountPriority
      rightKey.referenceCountPriority = Ordering.gt) :
    input.compareLocalizedRerootCompoundRule4bcKeys leftKey rightKey = Ordering.lt ∧
      leftKey.references =
        localizedRule4bReferencesFromRankedLabels leftKey.rule4aKey.rankedLabels ∧
      rightKey.references =
        localizedRule4bReferencesFromRankedLabels rightKey.rule4aKey.rankedLabels := by
  have leftFlow := input.buildLocalizedRerootCompoundRule4bcKey?_dataFlow
    target view fuel leftCursor leftKey leftComputed
  have rightFlow := input.buildLocalizedRerootCompoundRule4bcKey?_dataFlow
    target view fuel rightCursor rightKey rightComputed
  exact ⟨
    (input.compareLocalizedRerootCompoundRule4bcKeys_rule4a_strict_overrides_later
      leftKey rightKey rule4aStrict countDisagrees).1,
    leftFlow.1, rightFlow.1⟩

/-- On actual builder images, after an exhaustive Rule-4a tie the derived reference count is the
first decisive Rule-4b gate, preserving the existing count ordering exactly. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_referenceCount_decides_after_rule4a_tie
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCompoundRule4bcKey)
    (leftComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel rightCursor = some rightKey)
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey.rule4aKey rightKey.rule4aKey = Ordering.eq)
    (decisive : compare leftKey.referenceCountPriority
      rightKey.referenceCountPriority ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys leftKey rightKey =
        compare leftKey.referenceCountPriority rightKey.referenceCountPriority ∧
      leftKey.references =
        localizedRule4bReferencesFromRankedLabels leftKey.rule4aKey.rankedLabels ∧
      rightKey.references =
        localizedRule4bReferencesFromRankedLabels rightKey.rule4aKey.rankedLabels := by
  have leftFlow := input.buildLocalizedRerootCompoundRule4bcKey?_dataFlow
    target view fuel leftCursor leftKey leftComputed
  have rightFlow := input.buildLocalizedRerootCompoundRule4bcKey?_dataFlow
    target view fuel rightCursor rightKey rightComputed
  exact ⟨
    input.compareLocalizedRerootCompoundRule4bcKeys_eq_referenceCount_of_ne
      leftKey rightKey rule4aTie decisive,
    leftFlow.1, rightFlow.1⟩

/-! ## Lift through the through-Rule-5 comparator -/

/-- A decisive compound Rules-4b/4c comparison determines the through-Rule-5 comparator before
any Rule-5 reading is consulted. -/
theorem compareLocalizedRerootCompoundRule45Keys_eq_prior_of_prior_ne
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (decisive : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundRule45Keys left right =
      input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior := by
  unfold compareLocalizedRerootCompoundRule45Keys
  generalize priorComparison : input.compareLocalizedRerootCompoundRule4bcKeys
    left.prior right.prior = outcome at decisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

/-- A strict Rule-4a decision wins in the through-Rule-5 comparator, independently of the derived
reference counts and of every Rule-5 reading. -/
theorem compareLocalizedRerootCompoundRule45Keys_rule4a_strict_overrides_later
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (rule4aStrict : input.compareLocalizedRerootCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey = Ordering.lt)
    (countDisagrees : compare left.prior.referenceCountPriority
      right.prior.referenceCountPriority = Ordering.gt) :
    input.compareLocalizedRerootCompoundRule45Keys left right = Ordering.lt := by
  have priorStrict : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.lt :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_rule4a_strict_overrides_later
      left.prior right.prior rule4aStrict countDisagrees).1
  rw [input.compareLocalizedRerootCompoundRule45Keys_eq_prior_of_prior_ne
    left right (by rw [priorStrict]; decide)]
  exact priorStrict

/-! ## Lift through the Rule-3-through-5 comparator -/

/-- Only an exhaustive Rule-3 tie exposes the compound Rules-4a--5 key comparison. -/
theorem compareLocalizedOccurrenceRule3Through5Keys_eq_rule45_of_rule3_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedOccurrenceRule3Through5Key)
    (rule3Tie : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      left.rule3 right.rule3 = Ordering.eq) :
    input.compareLocalizedOccurrenceRule3Through5Keys left right =
      input.compareLocalizedRerootCompoundRule45Keys left.rule45 right.rule45 := by
  simp [compareLocalizedOccurrenceRule3Through5Keys, compareLex,
    Ordering.byKey, rule3Tie]

/-- After a Rule-3 tie, a strict Rule-4a key comparison determines the full Rule-3-through-5
comparison before the reference count, the Rule-4b readings, and every later stage. -/
theorem compareLocalizedOccurrenceRule3Through5Keys_rule4a_precedence
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedOccurrenceRule3Through5Key)
    (rule3Tie : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      left.rule3 right.rule3 = Ordering.eq)
    (rule4aDecisive : input.compareLocalizedRerootCumulativeRule45Keys
      left.rule45.prior.rule4aKey right.rule45.prior.rule4aKey ≠ Ordering.eq) :
    input.compareLocalizedOccurrenceRule3Through5Keys left right =
      input.compareLocalizedRerootCumulativeRule45Keys
        left.rule45.prior.rule4aKey right.rule45.prior.rule4aKey := by
  have compoundDecisive : input.compareLocalizedRerootCompoundRule4bcKeys
      left.rule45.prior right.rule45.prior ≠ Ordering.eq := by
    rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      left.rule45.prior right.rule45.prior rule4aDecisive]
    exact rule4aDecisive
  rw [input.compareLocalizedOccurrenceRule3Through5Keys_eq_rule45_of_rule3_eq
    left right rule3Tie]
  rw [input.compareLocalizedRerootCompoundRule45Keys_eq_prior_of_prior_ne
    left.rule45 right.rule45 compoundDecisive]
  exact input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
    left.rule45.prior right.rule45.prior rule4aDecisive

/-- The descriptor-facing Rule-3-through-5 result inherits the precedence: after a Rule-3 tie its
ordering is exactly the strict Rule-4a key comparison, so the Rule-4/5 stage cannot reverse a
strict Rule-4a decision. -/
theorem compareLocalizedOccurrenceRule3Through5At_rule4a_precedence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (rule3Tie : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.eq)
    (rule4aDecisive : input.compareLocalizedRerootCumulativeRule45Keys
      (frame.keyAt left).rule45.prior.rule4aKey
      (frame.keyAt right).rule45.prior.rule4aKey ≠ Ordering.eq) :
    (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering =
      input.compareLocalizedRerootCumulativeRule45Keys
        (frame.keyAt left).rule45.prior.rule4aKey
        (frame.keyAt right).rule45.prior.rule4aKey := by
  rw [input.compareLocalizedOccurrenceRule3Through5At_ordering frame left right]
  exact input.compareLocalizedOccurrenceRule3Through5Keys_rule4a_precedence
    (frame.keyAt left) (frame.keyAt right) rule3Tie rule4aDecisive

/-- The actual four-ligand builder image carries the same precedence at every center pair: after a
Rule-3 tie, a strict Rule-4a key comparison determines the Rule-3-through-5 comparison, and the
frame satisfies the independent frame derivation. -/
theorem buildLocalizedOccurrenceRule3Through5KeyFrame?_rule4a_precedence_consequence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : input.buildLocalizedOccurrenceRule3Through5KeyFrame?
      target view base = some frame)
    (left right : Fin 4)
    (rule3Tie : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.eq)
    (rule4aDecisive : input.compareLocalizedRerootCumulativeRule45Keys
      (frame.keyAt left).rule45.prior.rule4aKey
      (frame.keyAt right).rule45.prior.rule4aKey ≠ Ordering.eq) :
    input.compareLocalizedOccurrenceRule3Through5Keys
        (frame.keyAt left) (frame.keyAt right) =
        input.compareLocalizedRerootCumulativeRule45Keys
          (frame.keyAt left).rule45.prior.rule4aKey
          (frame.keyAt right).rule45.prior.rule4aKey ∧
      input.DeclarativeLocalizedOccurrenceRule3Through5KeyFrame
        target view base frame := by
  exact ⟨
    input.compareLocalizedOccurrenceRule3Through5Keys_rule4a_precedence
      (frame.keyAt left) (frame.keyAt right) rule3Tie rule4aDecisive,
    input.buildLocalizedOccurrenceRule3Through5KeyFrame?_sound
      target view base frame computed⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
