import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.FullStateParentNoninterference
import TetraStereo.OneCenter.LocalizedOutwardWholeStateKeyAgreement
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Parametric compound Rules-4b/4c/5 keys over occurrence reroot cursors

`LocalizedParametricCumulativeLabels` separates label *reading* from *construction* for one
cumulative Rules-4a--5 hierarchy.  This module performs the same separation for the compound
layers: the complete no/one/two-reference Rules-4b/4c key and the through-Rule-5 key of
`LocalizedRerootCompoundRule4bcKey` / `LocalizedRerootCompoundRule45Key`.

`buildLocalizedRerootCompoundRule45KeyWithRead?` takes an arbitrary total callback

`read : cursor → Option LocalizedAuxiliaryLabel`

and otherwise performs exactly the production construction: it reuses the actual parametric
cumulative builder `buildLocalizedRerootCumulativeRule45KeyWithRead?`, the actual Rule-4b
reference selection `localizedRule4bReferencesFromRankedLabels`, the actual no/one/two-reference
alternatives `localizedRule4bcReferenceAlternatives`, the actual
`constitutionalRule4bReferenceCountPriority`, and the actual R/S Rule-5 reading stages
`localizedRule5StageFor`.  Nothing is guessed or collapsed: the two-reference Rule-4b case and the
both-R/S Rule-5 readings are retained exactly as in the production layers.

## Main results

* `buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel` — specializing the
  callback to the existing restricted dependency reader `localizedDependencyLabel target view`
  reproduces the existing `buildLocalizedRerootCompoundRule45Key?` *exactly*, for every fuel and
  cursor (through the matching specializations of the Rule-4bc reading lists and the Rule-5 reading
  lists).
* `exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice` — every path-valid cursor
  compiles the complete compound key at the proved budget `2 * (carrierFuel + 1)` for *every*
  label reader, using the GREEN arbitrary-label cumulative totality and finite reading-list
  recursion.  This is key *construction*, not an assumption.
* `buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable` — on an
  outward branch the whole-state reader `fun cursor => state cursor.occurrence` and the shipped
  restricted builder produce exactly equal full `Option` compound keys at every fuel, including
  the fail-closed `none` outcome.  The proof composes the GREEN cumulative whole-state equality at
  each of the Rule-4a/4b/4c/5 stages; no compound-key equality is assumed.
* `buildLocalizedRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey` and its through-Rule-5
  companion expose the actual Rule-4a projection `prior.rule4aKey` of a successful parametric
  compound build.  This is the projection the parent-versus-outward comparison short-circuits on:
  parent compound keys may differ in their reference selections, but
  `compareLocalizedRerootCompoundRule4bcKeys` inspects `rule4aKey` first.

## Scope

This module proves structural mathematics only: the compound builders are assembled from the same
pieces as the production builders with only the label source generalized.  It does not add a
solver, an evaluator or a production path, and it does not assert any equality of parent reference
selections or of old/new projected keys.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Parametric Rule-4b/4c reading -/

/-- Label-callback form of the one-reference Rule-4b/4c reading builder.  Both cumulative stages
are compiled through the arbitrary reader. -/
noncomputable def buildLocalizedRerootRule4bcReadingWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option RS → Option input.LocalizedRerootRule4bcReading
  | none => do
      let rule4bKey ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        .rule4a read fuel cursor
      let rule4cKey ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        .rule4cNoReference read fuel cursor
      some
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }
  | some reference => do
      let rule4bKey ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (.rule4b reference) read fuel cursor
      let rule4cKey ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (.rule4c reference) read fuel cursor
      some
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }

/-! ## Parametric Rule-4b/4c reading lists -/

/-- Label-callback form of the sequential no/one/two-reference reading-list compiler.  The
normative alternative order is untouched. -/
noncomputable def buildLocalizedRerootRule4bcReadingsWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (Option RS) → Option (List input.LocalizedRerootRule4bcReading)
  | [] => some []
  | reference :: references => do
      let reading ← input.buildLocalizedRerootRule4bcReadingWithRead?
        read fuel cursor reference
      let readings ← input.buildLocalizedRerootRule4bcReadingsWithRead?
        read fuel cursor references
      some (reading :: readings)

/-! ## Parametric compound Rules-4b/4c key -/

/-- Label-callback form of the complete compound Rules-4b/4c key.  The Rule-4a key is compiled
first, the P-92.5.2.1 reference selection is derived from its ranked labels exactly as in the
production builder, and the sequential readings are compiled under that selection. -/
noncomputable def buildLocalizedRerootCompoundRule4bcKeyWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule4bcKey := do
  let rule4aKey ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
    .rule4a read fuel cursor
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  let readings ← input.buildLocalizedRerootRule4bcReadingsWithRead?
    read fuel cursor alternatives
  some
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings }

/-! ## Parametric Rule-5 reading -/

/-- Label-callback form of one Rule-5 reading: the same prior Rule-4bc alternative with both
common-reference R/S cumulative hierarchies compiled through the arbitrary reader. -/
noncomputable def buildLocalizedRerootRule5ReadingWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    Option input.LocalizedRerootRule5Reading := do
  let commonR ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
    (localizedRule5StageFor prior.reference? .R) read fuel cursor
  let commonS ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
    (localizedRule5StageFor prior.reference? .S) read fuel cursor
  some { prior := prior, commonR := commonR, commonS := commonS }

/-! ## Parametric Rule-5 reading lists -/

/-- Label-callback form of the sequential Rule-5 reading-list compiler. -/
noncomputable def buildLocalizedRerootRule5ReadingsWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List input.LocalizedRerootRule4bcReading →
      Option (List input.LocalizedRerootRule5Reading)
  | [] => some []
  | prior :: priors => do
      let reading ← input.buildLocalizedRerootRule5ReadingWithRead?
        read fuel cursor prior
      let readings ← input.buildLocalizedRerootRule5ReadingsWithRead?
        read fuel cursor priors
      some (reading :: readings)

/-! ## Parametric complete through-Rule-5 key -/

/-- Label-callback form of the complete compound through-Rule-5 key. -/
noncomputable def buildLocalizedRerootCompoundRule45KeyWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key := do
  let prior ← input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
    read fuel cursor
  let readings ← input.buildLocalizedRerootRule5ReadingsWithRead?
    read fuel cursor prior.readings
  some { prior := prior, rule5Readings := readings }

/-! ## Exact recovery of the production compound builders -/

/-- Specializing the callback to the restricted dependency reader reproduces the existing
one-reference Rule-4b/4c reading builder exactly. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_eq_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (reference : Option RS),
      input.buildLocalizedRerootRule4bcReadingWithRead?
        (fun cursor => input.localizedDependencyLabel target view cursor)
        fuel cursor reference =
      input.buildLocalizedRerootRule4bcReading? target view fuel cursor reference := by
  intro fuel cursor reference
  cases reference with
  | none =>
      simp only [buildLocalizedRerootRule4bcReadingWithRead?,
        buildLocalizedRerootRule4bcReading?,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          .rule4a target view fuel cursor,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          .rule4cNoReference target view fuel cursor]
  | some reference =>
      simp only [buildLocalizedRerootRule4bcReadingWithRead?,
        buildLocalizedRerootRule4bcReading?,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          (.rule4b reference) target view fuel cursor,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          (.rule4c reference) target view fuel cursor]

/-- Specializing the callback reproduces the existing Rule-4b/4c reading-list compiler exactly. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_eq_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (references : List (Option RS)),
      input.buildLocalizedRerootRule4bcReadingsWithRead?
        (fun cursor => input.localizedDependencyLabel target view cursor)
        fuel cursor references =
      input.buildLocalizedRerootRule4bcReadings? target view fuel cursor references := by
  intro fuel cursor references
  induction references with
  | nil => rfl
  | cons reference references inductionHypothesis =>
      unfold buildLocalizedRerootRule4bcReadingsWithRead?
        buildLocalizedRerootRule4bcReadings?
      cases headComputed : input.buildLocalizedRerootRule4bcReadingWithRead?
          (fun cursor => input.localizedDependencyLabel target view cursor)
          fuel cursor reference with
      | none =>
          have restricted : input.buildLocalizedRerootRule4bcReading?
              target view fuel cursor reference = none := by
            rw [← input.buildLocalizedRerootRule4bcReadingWithRead?_eq_localizedDependencyLabel
              target view fuel cursor reference]
            exact headComputed
          simp [restricted]
      | some reading =>
          have restricted : input.buildLocalizedRerootRule4bcReading?
              target view fuel cursor reference = some reading := by
            rw [← input.buildLocalizedRerootRule4bcReadingWithRead?_eq_localizedDependencyLabel
              target view fuel cursor reference]
            exact headComputed
          simp [restricted]
          cases tailComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
              (fun cursor => input.localizedDependencyLabel target view cursor)
              fuel cursor references with
          | none =>
              have restricted : input.buildLocalizedRerootRule4bcReadings?
                  target view fuel cursor references = none := by
                rw [← inductionHypothesis]
                exact tailComputed
              simp [tailComputed, restricted]
          | some readings =>
              have restricted : input.buildLocalizedRerootRule4bcReadings?
                  target view fuel cursor references = some readings := by
                rw [← inductionHypothesis]
                exact tailComputed
              simp [tailComputed, restricted]

/-- Specializing the callback reproduces the existing compound Rules-4b/4c key builder exactly. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_eq_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor =
      input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor := by
  intro fuel cursor
  unfold buildLocalizedRerootCompoundRule4bcKeyWithRead?
    buildLocalizedRerootCompoundRule4bcKey?
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel cursor with
  | none =>
      have restricted : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target view fuel cursor = none := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          .rule4a target view fuel cursor]
        exact rule4aComputed
      simp [restricted]
  | some rule4aKey =>
      have restricted : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target view fuel cursor = some rule4aKey := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          .rule4a target view fuel cursor]
        exact rule4aComputed
      simp [restricted]
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
          (fun cursor => input.localizedDependencyLabel target view cursor)
          fuel cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none =>
          have restrictedReadings : input.buildLocalizedRerootRule4bcReadings?
              target view fuel cursor
              (localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) = none := by
            rw [← input.buildLocalizedRerootRule4bcReadingsWithRead?_eq_localizedDependencyLabel
              target view fuel cursor
              (localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))]
            exact readingsComputed
          simp [readingsComputed, restrictedReadings]
      | some readings =>
          have restrictedReadings : input.buildLocalizedRerootRule4bcReadings?
              target view fuel cursor
              (localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) = some readings := by
            rw [← input.buildLocalizedRerootRule4bcReadingsWithRead?_eq_localizedDependencyLabel
              target view fuel cursor
              (localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))]
            exact readingsComputed
          simp [readingsComputed, restrictedReadings]

/-- Specializing the callback reproduces the existing one-reading Rule-5 builder exactly. -/
theorem buildLocalizedRerootRule5ReadingWithRead?_eq_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (prior : input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule5ReadingWithRead?
        (fun cursor => input.localizedDependencyLabel target view cursor)
        fuel cursor prior =
      input.buildLocalizedRerootRule5Reading? target view fuel cursor prior := by
  intro fuel cursor prior
  unfold buildLocalizedRerootRule5ReadingWithRead?
    buildLocalizedRerootRule5Reading?
  cases commonRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor prior.reference? .R)
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor with
  | none =>
      have restricted : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .R) target view fuel cursor = none := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          (localizedRule5StageFor prior.reference? .R) target view fuel cursor]
        exact commonRComputed
      simp [restricted]
  | some commonR =>
      have restricted : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .R) target view fuel cursor = some commonR := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          (localizedRule5StageFor prior.reference? .R) target view fuel cursor]
        exact commonRComputed
      simp [restricted]
      cases commonSComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .S)
          (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor with
      | none =>
          have restricted : input.buildLocalizedRerootCumulativeRule45Key?
              (localizedRule5StageFor prior.reference? .S) target view fuel cursor = none := by
            rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
              (localizedRule5StageFor prior.reference? .S) target view fuel cursor]
            exact commonSComputed
          simp [commonSComputed, restricted]
      | some commonS =>
          have restricted : input.buildLocalizedRerootCumulativeRule45Key?
              (localizedRule5StageFor prior.reference? .S) target view fuel cursor = some commonS := by
            rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
              (localizedRule5StageFor prior.reference? .S) target view fuel cursor]
            exact commonSComputed
          simp [commonSComputed, restricted]

/-- Specializing the callback reproduces the existing Rule-5 reading-list compiler exactly. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_eq_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (priors : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule5ReadingsWithRead?
        (fun cursor => input.localizedDependencyLabel target view cursor)
        fuel cursor priors =
      input.buildLocalizedRerootRule5Readings? target view fuel cursor priors := by
  intro fuel cursor priors
  induction priors with
  | nil => rfl
  | cons prior priors inductionHypothesis =>
      unfold buildLocalizedRerootRule5ReadingsWithRead?
        buildLocalizedRerootRule5Readings?
      cases headComputed : input.buildLocalizedRerootRule5ReadingWithRead?
          (fun cursor => input.localizedDependencyLabel target view cursor)
          fuel cursor prior with
      | none =>
          have restricted : input.buildLocalizedRerootRule5Reading?
              target view fuel cursor prior = none := by
            rw [← input.buildLocalizedRerootRule5ReadingWithRead?_eq_localizedDependencyLabel
              target view fuel cursor prior]
            exact headComputed
          simp [restricted]
      | some reading =>
          have restricted : input.buildLocalizedRerootRule5Reading?
              target view fuel cursor prior = some reading := by
            rw [← input.buildLocalizedRerootRule5ReadingWithRead?_eq_localizedDependencyLabel
              target view fuel cursor prior]
            exact headComputed
          simp [restricted]
          cases tailComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
              (fun cursor => input.localizedDependencyLabel target view cursor)
              fuel cursor priors with
          | none =>
              have restricted : input.buildLocalizedRerootRule5Readings?
                  target view fuel cursor priors = none := by
                rw [← inductionHypothesis]
                exact tailComputed
              simp [tailComputed, restricted]
          | some readings =>
              have restricted : input.buildLocalizedRerootRule5Readings?
                  target view fuel cursor priors = some readings := by
                rw [← inductionHypothesis]
                exact tailComputed
              simp [tailComputed, restricted]

/-- Specializing the callback reproduces the existing complete through-Rule-5 compound key
builder exactly, for every fuel and cursor. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor =
      input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor := by
  intro fuel cursor
  unfold buildLocalizedRerootCompoundRule45KeyWithRead?
    buildLocalizedRerootCompoundRule45Key?
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor with
  | none =>
      have restricted : input.buildLocalizedRerootCompoundRule4bcKey?
          target view fuel cursor = none := by
        rw [← input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_eq_localizedDependencyLabel
          target view fuel cursor]
        exact priorComputed
      simp [restricted]
  | some prior =>
      have restricted : input.buildLocalizedRerootCompoundRule4bcKey?
          target view fuel cursor = some prior := by
        rw [← input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_eq_localizedDependencyLabel
          target view fuel cursor]
        exact priorComputed
      simp [restricted]
      cases readingsComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
          (fun cursor => input.localizedDependencyLabel target view cursor)
          fuel cursor prior.readings with
      | none =>
          have restrictedReadings : input.buildLocalizedRerootRule5Readings?
              target view fuel cursor prior.readings = none := by
            rw [← input.buildLocalizedRerootRule5ReadingsWithRead?_eq_localizedDependencyLabel
              target view fuel cursor prior.readings]
            exact readingsComputed
          simp [priorComputed, restricted, readingsComputed, restrictedReadings]
      | some readings =>
          have restrictedReadings : input.buildLocalizedRerootRule5Readings?
              target view fuel cursor prior.readings = some readings := by
            rw [← input.buildLocalizedRerootRule5ReadingsWithRead?_eq_localizedDependencyLabel
              target view fuel cursor prior.readings]
            exact readingsComputed
          simp [priorComputed, restricted, readingsComputed, restrictedReadings]

/-! ## Arbitrary-label compound totality at the proved budget -/

/-- Every one-reference Rule-4b/4c reading succeeds at the proved reroot bound for every label
reader. -/
theorem exists_buildLocalizedRerootRule4bcReadingWithRead?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (reference : Option RS) :
    ∃ reading, input.buildLocalizedRerootRule4bcReadingWithRead? read
      (2 * (carrierFuel + 1)) cursor reference = some reading := by
  cases reference with
  | none =>
      obtain ⟨rule4bKey, rule4bComputed⟩ :=
        WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
          input .rule4a read cursor valid
      obtain ⟨rule4cKey, rule4cComputed⟩ :=
        WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
          input .rule4cNoReference read cursor valid
      exact ⟨
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey },
        by simp [buildLocalizedRerootRule4bcReadingWithRead?,
          rule4bComputed, rule4cComputed]⟩
  | some reference =>
      obtain ⟨rule4bKey, rule4bComputed⟩ :=
        WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
          input (.rule4b reference) read cursor valid
      obtain ⟨rule4cKey, rule4cComputed⟩ :=
        WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
          input (.rule4c reference) read cursor valid
      exact ⟨
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey },
        by simp [buildLocalizedRerootRule4bcReadingWithRead?,
          rule4bComputed, rule4cComputed]⟩

/-- Every finite normative Rule-4b/4c alternative list succeeds at the proved bound for every
label reader. -/
theorem exists_buildLocalizedRerootRule4bcReadingsWithRead?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∀ references : List (Option RS),
      ∃ readings, input.buildLocalizedRerootRule4bcReadingsWithRead? read
        (2 * (carrierFuel + 1)) cursor references = some readings
  | [] => ⟨[], rfl⟩
  | reference :: references => by
      obtain ⟨reading, readingComputed⟩ :=
        input.exists_buildLocalizedRerootRule4bcReadingWithRead?_at_twice
          read cursor valid reference
      obtain ⟨readings, readingsComputed⟩ :=
        input.exists_buildLocalizedRerootRule4bcReadingsWithRead?_at_twice
          read cursor valid references
      exact ⟨reading :: readings,
        by simp [buildLocalizedRerootRule4bcReadingsWithRead?,
          readingComputed, readingsComputed]⟩

/-- The complete no/one/two-reference compound Rules-4b/4c key is total at the proved bound for
every label reader. -/
theorem exists_buildLocalizedRerootCompoundRule4bcKeyWithRead?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read
      (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨rule4aKey, rule4aComputed⟩ :=
    WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input .rule4a read cursor valid
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  obtain ⟨readings, readingsComputed⟩ :=
    input.exists_buildLocalizedRerootRule4bcReadingsWithRead?_at_twice
      read cursor valid alternatives
  exact ⟨
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings },
    by simp [buildLocalizedRerootCompoundRule4bcKeyWithRead?, rule4aComputed,
      references, alternatives, readingsComputed]⟩

/-- Both common-reference Rule-5 readings are total at the proved bound for every label reader. -/
theorem exists_buildLocalizedRerootRule5ReadingWithRead?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (prior : input.LocalizedRerootRule4bcReading) :
    ∃ reading, input.buildLocalizedRerootRule5ReadingWithRead? read
      (2 * (carrierFuel + 1)) cursor prior = some reading := by
  obtain ⟨commonR, commonRComputed⟩ :=
    WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input (localizedRule5StageFor prior.reference? .R) read cursor valid
  obtain ⟨commonS, commonSComputed⟩ :=
    WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input (localizedRule5StageFor prior.reference? .S) read cursor valid
  exact ⟨{ prior := prior, commonR := commonR, commonS := commonS },
    by simp [buildLocalizedRerootRule5ReadingWithRead?, commonRComputed, commonSComputed]⟩

/-- Every finite normative Rule-5 reading list is total at the proved bound for every label
reader. -/
theorem exists_buildLocalizedRerootRule5ReadingsWithRead?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∀ priors : List input.LocalizedRerootRule4bcReading,
      ∃ readings, input.buildLocalizedRerootRule5ReadingsWithRead? read
        (2 * (carrierFuel + 1)) cursor priors = some readings
  | [] => ⟨[], rfl⟩
  | prior :: priors => by
      obtain ⟨reading, readingComputed⟩ :=
        input.exists_buildLocalizedRerootRule5ReadingWithRead?_at_twice
          read cursor valid prior
      obtain ⟨readings, readingsComputed⟩ :=
        input.exists_buildLocalizedRerootRule5ReadingsWithRead?_at_twice
          read cursor valid priors
      exact ⟨reading :: readings,
        by simp [buildLocalizedRerootRule5ReadingsWithRead?,
          readingComputed, readingsComputed]⟩

/-- **Universal availability.**  The complete compound through-Rule-5 key compiles at the proved
budget `2 * (carrierFuel + 1)` for every path-valid cursor and every label reader.  Nothing about
the labels is assumed. -/
theorem exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCompoundRule45KeyWithRead? read
      (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨prior, priorComputed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule4bcKeyWithRead?_at_twice
      read cursor valid
  obtain ⟨readings, readingsComputed⟩ :=
    input.exists_buildLocalizedRerootRule5ReadingsWithRead?_at_twice
      read cursor valid prior.readings
  exact ⟨{ prior := prior, rule5Readings := readings }, by
    simp [buildLocalizedRerootCompoundRule45KeyWithRead?, priorComputed, readingsComputed]⟩

/-! ## Whole-state agreement on outward reroot branches -/

/-- On an outward branch the whole-state and shipped restricted one-reference Rule-4b/4c readings
are exactly equal, for every fuel and every reference alternative. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_wholeState_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ (fuel : Nat) (reference : Option RS),
      input.buildLocalizedRerootRule4bcReadingWithRead?
        (fun cursor => state cursor.occurrence) fuel child reference =
      input.buildLocalizedRerootRule4bcReading? target
        (input.localizedDependencyView state target) fuel child reference := by
  intro fuel reference
  cases reference with
  | none =>
      simp only [buildLocalizedRerootRule4bcReadingWithRead?,
        buildLocalizedRerootRule4bcReading?,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          .rule4a target state first child firstChild firstDeeper reachable fuel,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          .rule4cNoReference target state first child firstChild firstDeeper reachable fuel]
  | some reference =>
      simp only [buildLocalizedRerootRule4bcReadingWithRead?,
        buildLocalizedRerootRule4bcReading?,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          (.rule4b reference) target state first child firstChild firstDeeper reachable fuel,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          (.rule4c reference) target state first child firstChild firstDeeper reachable fuel]

/-- On an outward branch the whole-state and shipped restricted Rule-4b/4c reading lists are
exactly equal. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_wholeState_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ (fuel : Nat) (references : List (Option RS)),
      input.buildLocalizedRerootRule4bcReadingsWithRead?
        (fun cursor => state cursor.occurrence) fuel child references =
      input.buildLocalizedRerootRule4bcReadings? target
        (input.localizedDependencyView state target) fuel child references := by
  intro fuel references
  induction references with
  | nil => rfl
  | cons reference references inductionHypothesis =>
      unfold buildLocalizedRerootRule4bcReadingsWithRead?
        buildLocalizedRerootRule4bcReadings?
      cases headWhole : input.buildLocalizedRerootRule4bcReadingWithRead?
          (fun cursor => state cursor.occurrence) fuel child reference with
      | none =>
          have headShipped : input.buildLocalizedRerootRule4bcReading?
              target (input.localizedDependencyView state target) fuel child reference = none := by
            rw [← input.buildLocalizedRerootRule4bcReadingWithRead?_wholeState_eq_of_outward_reachable
              target state first child firstChild firstDeeper reachable fuel reference]
            exact headWhole
          simp [headShipped]
      | some reading =>
          have headShipped : input.buildLocalizedRerootRule4bcReading?
              target (input.localizedDependencyView state target) fuel child reference =
                some reading := by
            rw [← input.buildLocalizedRerootRule4bcReadingWithRead?_wholeState_eq_of_outward_reachable
              target state first child firstChild firstDeeper reachable fuel reference]
            exact headWhole
          simp [headShipped]
          cases tailWhole : input.buildLocalizedRerootRule4bcReadingsWithRead?
              (fun cursor => state cursor.occurrence) fuel child references with
          | none =>
              have tailShipped : input.buildLocalizedRerootRule4bcReadings?
                  target (input.localizedDependencyView state target) fuel child references = none := by
                rw [← inductionHypothesis]
                exact tailWhole
              simp [tailWhole, tailShipped]
          | some readings =>
              have tailShipped : input.buildLocalizedRerootRule4bcReadings?
                  target (input.localizedDependencyView state target) fuel child references =
                    some readings := by
                rw [← inductionHypothesis]
                exact tailWhole
              simp [tailWhole, tailShipped]

/-- On an outward branch the whole-state and shipped restricted compound Rules-4b/4c keys are
exactly equal, including the fail-closed `none` outcome. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_wholeState_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ fuel : Nat,
      input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
        (fun cursor => state cursor.occurrence) fuel child =
      input.buildLocalizedRerootCompoundRule4bcKey? target
        (input.localizedDependencyView state target) fuel child := by
  intro fuel
  unfold buildLocalizedRerootCompoundRule4bcKeyWithRead?
    buildLocalizedRerootCompoundRule4bcKey?
  cases rule4aWhole : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (fun cursor => state cursor.occurrence) fuel child with
  | none =>
      have rule4aShipped : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target (input.localizedDependencyView state target) fuel child = none := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          .rule4a target state first child firstChild firstDeeper reachable fuel]
        exact rule4aWhole
      simp [rule4aShipped]
  | some rule4aKey =>
      have rule4aShipped : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target (input.localizedDependencyView state target) fuel child =
            some rule4aKey := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          .rule4a target state first child firstChild firstDeeper reachable fuel]
        exact rule4aWhole
      simp [rule4aShipped]
      cases readingsWhole : input.buildLocalizedRerootRule4bcReadingsWithRead?
          (fun cursor => state cursor.occurrence) fuel child
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none =>
          have readingsShipped : input.buildLocalizedRerootRule4bcReadings?
              target (input.localizedDependencyView state target) fuel child
              (localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) = none := by
            rw [← input.buildLocalizedRerootRule4bcReadingsWithRead?_wholeState_eq_of_outward_reachable
              target state first child firstChild firstDeeper reachable fuel
              (localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))]
            exact readingsWhole
          simp [readingsWhole, readingsShipped]
      | some readings =>
          have readingsShipped : input.buildLocalizedRerootRule4bcReadings?
              target (input.localizedDependencyView state target) fuel child
              (localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) =
                some readings := by
            rw [← input.buildLocalizedRerootRule4bcReadingsWithRead?_wholeState_eq_of_outward_reachable
              target state first child firstChild firstDeeper reachable fuel
              (localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))]
            exact readingsWhole
          simp [readingsWhole, readingsShipped]

/-- On an outward branch the whole-state and shipped restricted one-reading Rule-5 results are
exactly equal. -/
theorem buildLocalizedRerootRule5ReadingWithRead?_wholeState_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ (fuel : Nat) (prior : input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule5ReadingWithRead?
        (fun cursor => state cursor.occurrence) fuel child prior =
      input.buildLocalizedRerootRule5Reading? target
        (input.localizedDependencyView state target) fuel child prior := by
  intro fuel prior
  unfold buildLocalizedRerootRule5ReadingWithRead?
    buildLocalizedRerootRule5Reading?
  cases commonRWhole : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor prior.reference? .R)
      (fun cursor => state cursor.occurrence) fuel child with
  | none =>
      have commonRShipped : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .R) target
            (input.localizedDependencyView state target) fuel child = none := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          (localizedRule5StageFor prior.reference? .R) target state first child firstChild
          firstDeeper reachable fuel]
        exact commonRWhole
      simp [commonRShipped]
  | some commonR =>
      have commonRShipped : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .R) target
            (input.localizedDependencyView state target) fuel child = some commonR := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          (localizedRule5StageFor prior.reference? .R) target state first child firstChild
          firstDeeper reachable fuel]
        exact commonRWhole
      simp [commonRShipped]
      cases commonSWhole : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .S)
          (fun cursor => state cursor.occurrence) fuel child with
      | none =>
          have commonSShipped : input.buildLocalizedRerootCumulativeRule45Key?
              (localizedRule5StageFor prior.reference? .S) target
                (input.localizedDependencyView state target) fuel child = none := by
            rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
              (localizedRule5StageFor prior.reference? .S) target state first child firstChild
              firstDeeper reachable fuel]
            exact commonSWhole
          simp [commonSWhole, commonSShipped]
      | some commonS =>
          have commonSShipped : input.buildLocalizedRerootCumulativeRule45Key?
              (localizedRule5StageFor prior.reference? .S) target
                (input.localizedDependencyView state target) fuel child = some commonS := by
            rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
              (localizedRule5StageFor prior.reference? .S) target state first child firstChild
              firstDeeper reachable fuel]
            exact commonSWhole
          simp [commonSWhole, commonSShipped]

/-- On an outward branch the whole-state and shipped restricted Rule-5 reading lists are exactly
equal. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_wholeState_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ (fuel : Nat) (priors : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule5ReadingsWithRead?
        (fun cursor => state cursor.occurrence) fuel child priors =
      input.buildLocalizedRerootRule5Readings? target
        (input.localizedDependencyView state target) fuel child priors := by
  intro fuel priors
  induction priors with
  | nil => rfl
  | cons prior priors inductionHypothesis =>
      unfold buildLocalizedRerootRule5ReadingsWithRead?
        buildLocalizedRerootRule5Readings?
      cases headWhole : input.buildLocalizedRerootRule5ReadingWithRead?
          (fun cursor => state cursor.occurrence) fuel child prior with
      | none =>
          have headShipped : input.buildLocalizedRerootRule5Reading?
              target (input.localizedDependencyView state target) fuel child prior = none := by
            rw [← input.buildLocalizedRerootRule5ReadingWithRead?_wholeState_eq_of_outward_reachable
              target state first child firstChild firstDeeper reachable fuel prior]
            exact headWhole
          simp [headShipped]
      | some reading =>
          have headShipped : input.buildLocalizedRerootRule5Reading?
              target (input.localizedDependencyView state target) fuel child prior =
                some reading := by
            rw [← input.buildLocalizedRerootRule5ReadingWithRead?_wholeState_eq_of_outward_reachable
              target state first child firstChild firstDeeper reachable fuel prior]
            exact headWhole
          simp [headShipped]
          cases tailWhole : input.buildLocalizedRerootRule5ReadingsWithRead?
              (fun cursor => state cursor.occurrence) fuel child priors with
          | none =>
              have tailShipped : input.buildLocalizedRerootRule5Readings?
                  target (input.localizedDependencyView state target) fuel child priors = none := by
                rw [← inductionHypothesis]
                exact tailWhole
              simp [tailWhole, tailShipped]
          | some readings =>
              have tailShipped : input.buildLocalizedRerootRule5Readings?
                  target (input.localizedDependencyView state target) fuel child priors =
                    some readings := by
                rw [← inductionHypothesis]
                exact tailWhole
              simp [tailWhole, tailShipped]

/-- **Whole-state compound agreement.**  On an outward branch the whole-state reader and the
shipped restricted builder produce exactly equal full `Option` complete through-Rule-5 compound
keys at every fuel, including the fail-closed `none` outcome. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ fuel : Nat,
      input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence) fuel child =
      input.buildLocalizedRerootCompoundRule45Key? target
        (input.localizedDependencyView state target) fuel child := by
  intro fuel
  unfold buildLocalizedRerootCompoundRule45KeyWithRead?
    buildLocalizedRerootCompoundRule45Key?
  cases priorWhole : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      (fun cursor => state cursor.occurrence) fuel child with
  | none =>
      have priorShipped : input.buildLocalizedRerootCompoundRule4bcKey?
          target (input.localizedDependencyView state target) fuel child = none := by
        rw [← input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_wholeState_eq_of_outward_reachable
          target state first child firstChild firstDeeper reachable fuel]
        exact priorWhole
      simp [priorShipped]
  | some prior =>
      have priorShipped : input.buildLocalizedRerootCompoundRule4bcKey?
          target (input.localizedDependencyView state target) fuel child = some prior := by
        rw [← input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_wholeState_eq_of_outward_reachable
          target state first child firstChild firstDeeper reachable fuel]
        exact priorWhole
      simp [priorShipped]
      cases readingsWhole : input.buildLocalizedRerootRule5ReadingsWithRead?
          (fun cursor => state cursor.occurrence) fuel child prior.readings with
      | none =>
          have readingsShipped : input.buildLocalizedRerootRule5Readings?
              target (input.localizedDependencyView state target) fuel child prior.readings = none := by
            rw [← input.buildLocalizedRerootRule5ReadingsWithRead?_wholeState_eq_of_outward_reachable
              target state first child firstChild firstDeeper reachable fuel prior.readings]
            exact readingsWhole
          simp [readingsShipped]
      | some readings =>
          have readingsShipped : input.buildLocalizedRerootRule5Readings?
              target (input.localizedDependencyView state target) fuel child prior.readings =
                some readings := by
            rw [← input.buildLocalizedRerootRule5ReadingsWithRead?_wholeState_eq_of_outward_reachable
              target state first child firstChild firstDeeper reachable fuel prior.readings]
            exact readingsWhole
          simp [readingsShipped]

/-- Successful whole-state and shipped compilations on an outward branch yield the *same*
complete compound key, not merely comparable projections. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child)
    (fuel : Nat)
    (wholeKey shippedKey : input.LocalizedRerootCompoundRule45Key)
    (wholeComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor => state cursor.occurrence) fuel child = some wholeKey)
    (shippedComputed : input.buildLocalizedRerootCompoundRule45Key? target
      (input.localizedDependencyView state target) fuel child = some shippedKey) :
    wholeKey = shippedKey := by
  have total := input.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
    target state first child firstChild firstDeeper reachable fuel
  rw [wholeComputed, shippedComputed] at total
  exact Option.some.inj total

/-! ## Rule-4a projection of a successful compound build -/

/-- A successful parametric compound Rules-4b/4c build is assembled from the Rule-4a cumulative
key it actually compiled: the projection `key.rule4aKey` is exactly the `.rule4a` cumulative
build.  This is the projection the parent-versus-outward comparison short-circuits on before any
reference count or reading is inspected. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel cursor =
      some key.rule4aKey := by
  unfold buildLocalizedRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      simp [rule4aComputed] at computed
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
          read fuel cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          rfl

/-- A successful parametric complete through-Rule-5 build carries the Rule-4a key it actually
compiled as `key.prior.rule4aKey`. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel cursor =
      some key.prior.rule4aKey := by
  unfold buildLocalizedRerootCompoundRule45KeyWithRead? at computed
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      simp [priorComputed] at computed
      cases readingsComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          exact input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
            read fuel cursor prior priorComputed

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the six parametric compound builders, their six exact
restricted-recovery theorems, the six arbitrary-label totality theorems at the proved budget, the
six whole-state agreement theorems and the whole-state key-equality corollary, and the two
Rule-4a projection exposures.  `assert_kernel_only` permits exactly `propext`, `Classical.choice`
and `Quot.sound`, and rejects `sorryAx`, project axioms and native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?_eq_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsWithRead?_eq_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_eq_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingWithRead?_eq_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsWithRead?_eq_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRerootRule4bcReadingWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRerootRule4bcReadingsWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRerootCompoundRule4bcKeyWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRerootRule5ReadingWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRerootRule5ReadingsWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
