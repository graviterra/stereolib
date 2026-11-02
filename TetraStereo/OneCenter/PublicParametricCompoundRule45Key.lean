import TetraStereo.OneCenter.PublicParametricCumulativeRule45Key
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule45
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Public parametric compound Rules-4b/4c/5 keys

`PublicParametricCumulativeRule45Key` separates *label reading* from *construction* for the
source-canonical cumulative Rules-4a--5 hierarchy: `buildAromaticCanonicalCumulativeRule45KeyWithRead?`
takes an arbitrary total callback

`read : cursor → Option AuxiliaryLabel`

and otherwise performs exactly the production construction of
`buildAromaticCanonicalCumulativeRule45Key?` on the public `AuthoritativeChemicalInput` source.

This module performs the same separation for the *compound* public layers of
`AuthoritativeSemanticMancudeOccurrenceCompoundRule4bc` /
`AuthoritativeSemanticMancudeOccurrenceCompoundRule45`.

`buildAromaticCanonicalRerootCompoundRule45KeyWithRead?` reuses the actual parametric cumulative
builder, the actual Rule-4b reference selection
`localizedRule4bReferencesFromRankedLabels`, the actual no/one/two-reference alternatives
`aromaticCanonicalRule4bcReferenceAlternatives`, the actual
`constitutionalRule4bReferenceCountPriority`, and the actual R/S Rule-5 reading stages
`aromaticCanonicalRule5StageFor`.  Nothing is guessed or collapsed: the two-reference Rule-4b case
and both `commonR`/`commonS` Rule-5 readings are retained exactly as in the production layers, and
every partial result keeps the production `Option` order and fail-closed `none` outcome.

## Main results

* `buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel` —
  specializing the callback to the existing source-canonical dependency reader
  `aromaticCanonicalDependencyLabel target view` reproduces the existing
  `buildAromaticCanonicalRerootCompoundRule45Key?` *exactly*, for every fuel and cursor, through
  the matching specializations of the Rule-4bc reading lists and the Rule-5 reading lists.
* `buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable` and
  `..._eq_of_readersAgreeOnReachable` — reader congruence on the actual executable reachable
  support: two arbitrary total readers that agree on every cursor reachable from `start` through
  the actual `aromaticCanonicalRerootEdge` (membership in `aromaticCanonicalRerootChildren`) build
  exactly equal full `Option` compound keys at every reachable cursor, including the fail-closed
  `none` outcome.
* `buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey` and its through-Rule-5
  companion expose the actual Rule-4a projection `key.prior.rule4aKey` of a successful parametric
  compound build; this is the projection a parent-versus-outward comparison inspects first.
* `compareAromaticCanonicalRerootCompoundRule45Keys_eq_prior_of_ne` and
  `..._eq_rule5_of_prior` record the short-circuit behavior of the shipped through-Rule-5
  comparator: a decisive prior Rules-4b/4c comparison is returned unchanged, and the Rule-5
  readings are consulted only after a complete prior tie.

## Scope

This module proves structural mathematics only: the compound builders are assembled from the same
pieces as the production builders with only the label source generalized.  It does not add a
solver, an evaluator or a production path, and it does not assert any equality of old/new projected
keys beyond the exact production specialization above.  No final descriptor-locality claim is made.
-/

/-! ## Parametric Rule-4b/4c reading -/

/-- Label-callback form of the one-reference Rule-4b/4c reading builder.  Both cumulative stages
are compiled through the arbitrary reader. -/
noncomputable def buildAromaticCanonicalRerootRule4bcReadingWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option RS → Option source.AromaticCanonicalRerootRule4bcReading
  | none => do
      let rule4bKey ← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        .rule4a read fuel cursor
      let rule4cKey ← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        .rule4cNoReference read fuel cursor
      some
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }
  | some reference => do
      let rule4bKey ← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        (.rule4b reference) read fuel cursor
      let rule4cKey ← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        (.rule4c reference) read fuel cursor
      some
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }

/-! ## Parametric Rule-4b/4c reading lists -/

/-- Label-callback form of the sequential no/one/two-reference reading-list compiler.  The
normative alternative order is untouched. -/
noncomputable def buildAromaticCanonicalRerootRule4bcReadingsWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    List (Option RS) →
      Option (List source.AromaticCanonicalRerootRule4bcReading)
  | [] => some []
  | reference :: references => do
      let reading ← source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
        read fuel cursor reference
      let readings ← source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read fuel cursor references
      some (reading :: readings)

/-! ## Parametric compound Rules-4b/4c key -/

/-- Label-callback form of the complete compound Rules-4b/4c key.  The Rule-4a key is compiled
first, the P-92.5.2.1 reference selection is derived from its ranked labels exactly as in the
production builder, and the sequential readings are compiled under that selection. -/
noncomputable def buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option source.AromaticCanonicalRerootCompoundRule4bcKey := do
  let rule4aKey ← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
    .rule4a read fuel cursor
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := aromaticCanonicalRule4bcReferenceAlternatives references
  let readings ← source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
    read fuel cursor alternatives
  some
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings }

/-! ## Parametric Rule-5 reading -/

/-- Label-callback form of one Rule-5 reading: the same prior Rule-4bc alternative with both
common-reference R/S cumulative hierarchies compiled through the arbitrary reader. -/
noncomputable def buildAromaticCanonicalRerootRule5ReadingWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading) :
    Option source.AromaticCanonicalRerootRule5Reading := do
  let commonR ← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
    (aromaticCanonicalRule5StageFor prior.reference? .R) read fuel cursor
  let commonS ← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
    (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor
  some { prior := prior, commonR := commonR, commonS := commonS }

/-! ## Parametric Rule-5 reading lists -/

/-- Label-callback form of the sequential Rule-5 reading-list compiler. -/
noncomputable def buildAromaticCanonicalRerootRule5ReadingsWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    List source.AromaticCanonicalRerootRule4bcReading →
      Option (List source.AromaticCanonicalRerootRule5Reading)
  | [] => some []
  | prior :: priors => do
      let reading ← source.buildAromaticCanonicalRerootRule5ReadingWithRead?
        read fuel cursor prior
      let readings ← source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        read fuel cursor priors
      some (reading :: readings)

/-! ## Parametric complete through-Rule-5 key -/

/-- Label-callback form of the complete compound through-Rule-5 key. -/
noncomputable def buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option source.AromaticCanonicalRerootCompoundRule45Key := do
  let prior ← source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
    read fuel cursor
  let readings ← source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
    read fuel cursor prior.readings
  some { prior := prior, rule5Readings := readings }

/-! ## Exact recovery of the production compound builders -/

/-- Specializing the callback to the source-canonical dependency reader reproduces the existing
one-reference Rule-4b/4c reading builder exactly. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_eq_aromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (reference : Option RS),
      source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        fuel cursor reference =
      source.buildAromaticCanonicalRerootRule4bcReading?
        target view fuel cursor reference := by
  intro fuel cursor reference
  cases reference with
  | none =>
      simp only [buildAromaticCanonicalRerootRule4bcReadingWithRead?,
        buildAromaticCanonicalRerootRule4bcReading?,
        source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          .rule4a target view fuel cursor,
        source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          .rule4cNoReference target view fuel cursor]
  | some reference =>
      simp only [buildAromaticCanonicalRerootRule4bcReadingWithRead?,
        buildAromaticCanonicalRerootRule4bcReading?,
        source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          (.rule4b reference) target view fuel cursor,
        source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          (.rule4c reference) target view fuel cursor]

/-- Specializing the callback reproduces the existing Rule-4b/4c reading-list compiler exactly. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_eq_aromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (references : List (Option RS)),
      source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        fuel cursor references =
      source.buildAromaticCanonicalRerootRule4bcReadings?
        target view fuel cursor references := by
  intro fuel cursor references
  induction references with
  | nil => rfl
  | cons reference references inductionHypothesis =>
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        buildAromaticCanonicalRerootRule4bcReadings?
      cases headComputed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
          fuel cursor reference with
      | none =>
          have restricted : source.buildAromaticCanonicalRerootRule4bcReading?
              target view fuel cursor reference = none := by
            rw [← source.buildAromaticCanonicalRerootRule4bcReadingWithRead?_eq_aromaticCanonicalDependencyLabel
              target view fuel cursor reference]
            exact headComputed
          simp [restricted]
      | some reading =>
          have restricted : source.buildAromaticCanonicalRerootRule4bcReading?
              target view fuel cursor reference = some reading := by
            rw [← source.buildAromaticCanonicalRerootRule4bcReadingWithRead?_eq_aromaticCanonicalDependencyLabel
              target view fuel cursor reference]
            exact headComputed
          simp [restricted]
          cases tailComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
              (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
              fuel cursor references with
          | none =>
              have restricted : source.buildAromaticCanonicalRerootRule4bcReadings?
                  target view fuel cursor references = none := by
                rw [← inductionHypothesis]
                exact tailComputed
              simp [tailComputed, restricted]
          | some readings =>
              have restricted : source.buildAromaticCanonicalRerootRule4bcReadings?
                  target view fuel cursor references = some readings := by
                rw [← inductionHypothesis]
                exact tailComputed
              simp [tailComputed, restricted]

/-- Specializing the callback reproduces the existing compound Rules-4b/4c key builder exactly. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_eq_aromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor) fuel cursor =
      source.buildAromaticCanonicalRerootCompoundRule4bcKey?
        target view fuel cursor := by
  intro fuel cursor
  unfold buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
    buildAromaticCanonicalRerootCompoundRule4bcKey?
  cases rule4aComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      fuel cursor with
  | none =>
      have restricted : source.buildAromaticCanonicalCumulativeRule45Key?
          .rule4a target view fuel cursor = none := by
        rw [← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          .rule4a target view fuel cursor]
        exact rule4aComputed
      simp [restricted]
  | some rule4aKey =>
      have restricted : source.buildAromaticCanonicalCumulativeRule45Key?
          .rule4a target view fuel cursor = some rule4aKey := by
        rw [← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          .rule4a target view fuel cursor]
        exact rule4aComputed
      simp [restricted]
      cases readingsComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
          (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
          fuel cursor
          (aromaticCanonicalRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none =>
          have restrictedReadings : source.buildAromaticCanonicalRerootRule4bcReadings?
              target view fuel cursor
              (aromaticCanonicalRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) = none := by
            rw [← source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_eq_aromaticCanonicalDependencyLabel
              target view fuel cursor
              (aromaticCanonicalRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))]
            exact readingsComputed
          simp [readingsComputed, restrictedReadings]
      | some readings =>
          have restrictedReadings : source.buildAromaticCanonicalRerootRule4bcReadings?
              target view fuel cursor
              (aromaticCanonicalRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) =
                some readings := by
            rw [← source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_eq_aromaticCanonicalDependencyLabel
              target view fuel cursor
              (aromaticCanonicalRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))]
            exact readingsComputed
          simp [readingsComputed, restrictedReadings]

/-- Specializing the callback reproduces the existing one-reading Rule-5 builder exactly. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_eq_aromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (prior : source.AromaticCanonicalRerootRule4bcReading),
      source.buildAromaticCanonicalRerootRule5ReadingWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        fuel cursor prior =
      source.buildAromaticCanonicalRerootRule5Reading?
        target view fuel cursor prior := by
  intro fuel cursor prior
  unfold buildAromaticCanonicalRerootRule5ReadingWithRead?
    buildAromaticCanonicalRerootRule5Reading?
  cases commonRComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      (aromaticCanonicalRule5StageFor prior.reference? .R)
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor) fuel cursor with
  | none =>
      have restricted : source.buildAromaticCanonicalCumulativeRule45Key?
          (aromaticCanonicalRule5StageFor prior.reference? .R) target view fuel cursor = none := by
        rw [← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          (aromaticCanonicalRule5StageFor prior.reference? .R) target view fuel cursor]
        exact commonRComputed
      simp [restricted]
  | some commonR =>
      have restricted : source.buildAromaticCanonicalCumulativeRule45Key?
          (aromaticCanonicalRule5StageFor prior.reference? .R) target view fuel cursor =
            some commonR := by
        rw [← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          (aromaticCanonicalRule5StageFor prior.reference? .R) target view fuel cursor]
        exact commonRComputed
      simp [restricted]
      cases commonSComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (aromaticCanonicalRule5StageFor prior.reference? .S)
          (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor) fuel cursor with
      | none =>
          have restricted : source.buildAromaticCanonicalCumulativeRule45Key?
              (aromaticCanonicalRule5StageFor prior.reference? .S) target view fuel cursor =
                none := by
            rw [← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
              (aromaticCanonicalRule5StageFor prior.reference? .S) target view fuel cursor]
            exact commonSComputed
          simp [commonSComputed, restricted]
      | some commonS =>
          have restricted : source.buildAromaticCanonicalCumulativeRule45Key?
              (aromaticCanonicalRule5StageFor prior.reference? .S) target view fuel cursor =
                some commonS := by
            rw [← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
              (aromaticCanonicalRule5StageFor prior.reference? .S) target view fuel cursor]
            exact commonSComputed
          simp [commonSComputed, restricted]

/-- Specializing the callback reproduces the existing Rule-5 reading-list compiler exactly. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_eq_aromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (priors : List source.AromaticCanonicalRerootRule4bcReading),
      source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        fuel cursor priors =
      source.buildAromaticCanonicalRerootRule5Readings?
        target view fuel cursor priors := by
  intro fuel cursor priors
  induction priors with
  | nil => rfl
  | cons prior priors inductionHypothesis =>
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead?
        buildAromaticCanonicalRerootRule5Readings?
      cases headComputed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
          (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
          fuel cursor prior with
      | none =>
          have restricted : source.buildAromaticCanonicalRerootRule5Reading?
              target view fuel cursor prior = none := by
            rw [← source.buildAromaticCanonicalRerootRule5ReadingWithRead?_eq_aromaticCanonicalDependencyLabel
              target view fuel cursor prior]
            exact headComputed
          simp [restricted]
      | some reading =>
          have restricted : source.buildAromaticCanonicalRerootRule5Reading?
              target view fuel cursor prior = some reading := by
            rw [← source.buildAromaticCanonicalRerootRule5ReadingWithRead?_eq_aromaticCanonicalDependencyLabel
              target view fuel cursor prior]
            exact headComputed
          simp [restricted]
          cases tailComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
              (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
              fuel cursor priors with
          | none =>
              have restricted : source.buildAromaticCanonicalRerootRule5Readings?
                  target view fuel cursor priors = none := by
                rw [← inductionHypothesis]
                exact tailComputed
              simp [tailComputed, restricted]
          | some readings =>
              have restricted : source.buildAromaticCanonicalRerootRule5Readings?
                  target view fuel cursor priors = some readings := by
                rw [← inductionHypothesis]
                exact tailComputed
              simp [tailComputed, restricted]

/-- **Unconditional production specialization.**  Specializing the callback to the existing
source-canonical dependency reader reproduces the existing complete through-Rule-5 compound key
builder exactly, for every fuel and cursor. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor) fuel cursor =
      source.buildAromaticCanonicalRerootCompoundRule45Key?
        target view fuel cursor := by
  intro fuel cursor
  unfold buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
    buildAromaticCanonicalRerootCompoundRule45Key?
  cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor) fuel cursor with
  | none =>
      have restricted : source.buildAromaticCanonicalRerootCompoundRule4bcKey?
          target view fuel cursor = none := by
        rw [← source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_eq_aromaticCanonicalDependencyLabel
          target view fuel cursor]
        exact priorComputed
      simp [restricted]
  | some prior =>
      have restricted : source.buildAromaticCanonicalRerootCompoundRule4bcKey?
          target view fuel cursor = some prior := by
        rw [← source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_eq_aromaticCanonicalDependencyLabel
          target view fuel cursor]
        exact priorComputed
      simp [restricted]
      cases readingsComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
          (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
          fuel cursor prior.readings with
      | none =>
          have restrictedReadings : source.buildAromaticCanonicalRerootRule5Readings?
              target view fuel cursor prior.readings = none := by
            rw [← source.buildAromaticCanonicalRerootRule5ReadingsWithRead?_eq_aromaticCanonicalDependencyLabel
              target view fuel cursor prior.readings]
            exact readingsComputed
          simp [priorComputed, restricted, readingsComputed, restrictedReadings]
      | some readings =>
          have restrictedReadings : source.buildAromaticCanonicalRerootRule5Readings?
              target view fuel cursor prior.readings = some readings := by
            rw [← source.buildAromaticCanonicalRerootRule5ReadingsWithRead?_eq_aromaticCanonicalDependencyLabel
              target view fuel cursor prior.readings]
            exact readingsComputed
          simp [priorComputed, restricted, readingsComputed, restrictedReadings]

/-! ## Reader congruence on the executable reachable support -/

/-- The honest read-support premise: two label readers agree on every cursor reachable from
`start` along the actual executable reroot edge `aromaticCanonicalRerootEdge`.  `start` itself is
reachable by reflexivity, so its label observation is included.  Arbitrary total readers and
arbitrary `Option` outcomes (including `none`) are allowed. -/
abbrev AromaticCanonicalRerootReadersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel) : Prop :=
  ∀ cursor : source.AromaticCanonicalRerootCursor carrierFuel,
    Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
    read1 cursor = read2 cursor

/-- Pointwise agreement of the two readers at one fixed fuel and cursor across *all* cumulative
stages.  This is exactly what every compound layer consumes. -/
abbrev AromaticCanonicalRerootCumulativeAgrees
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) : Prop :=
  ∀ stage : LocalizedCumulativeRule45Stage,
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read1 fuel cursor =
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read2 fuel cursor

/-! ## Compound-layer congruence from cumulative agreement -/

/-- One-reference Rule-4b/4c reading congruence. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (cumul : source.AromaticCanonicalRerootCumulativeAgrees read1 read2 fuel cursor) :
    ∀ reference : Option RS,
      source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
        read1 fuel cursor reference =
      source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
        read2 fuel cursor reference := by
  intro reference
  cases reference with
  | none =>
      simp only [buildAromaticCanonicalRerootRule4bcReadingWithRead?,
        cumul .rule4a, cumul .rule4cNoReference]
  | some reference =>
      simp only [buildAromaticCanonicalRerootRule4bcReadingWithRead?,
        cumul (.rule4b reference), cumul (.rule4c reference)]

/-- Rule-4b/4c reading-list congruence, by induction over the normative alternative list. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_congr_of_cumulativeAgrees
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (cumul : source.AromaticCanonicalRerootCumulativeAgrees read1 read2 fuel cursor) :
    ∀ references : List (Option RS),
      source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read1 fuel cursor references =
      source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read2 fuel cursor references := by
  intro references
  induction references with
  | nil => rfl
  | cons reference references inductionHypothesis =>
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead?
      cases headFirst : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read1 fuel cursor reference with
      | none =>
          have headSecond : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
              read2 fuel cursor reference = none := by
            rw [← source.buildAromaticCanonicalRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
              read1 read2 fuel cursor cumul reference]
            exact headFirst
          simp [headFirst, headSecond]
      | some reading =>
          have headSecond : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
              read2 fuel cursor reference = some reading := by
            rw [← source.buildAromaticCanonicalRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
              read1 read2 fuel cursor cumul reference]
            exact headFirst
          simp [headFirst, headSecond]
          rw [inductionHypothesis]

/-- Complete no/one/two-reference compound Rules-4b/4c key congruence.  The two readers produce
the *same* Rule-4a key, so the derived reference selection and normative alternatives are
syntactically identical on both sides. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (cumul : source.AromaticCanonicalRerootCumulativeAgrees read1 read2 fuel cursor) :
    source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? read1 fuel cursor =
    source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? read2 fuel cursor := by
  unfold buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
  cases rule4aFirst : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read1 fuel cursor with
  | none =>
      have rule4aSecond : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read2 fuel cursor = none := by
        rw [← cumul .rule4a]
        exact rule4aFirst
      simp [rule4aFirst, rule4aSecond]
  | some rule4aKey =>
      have rule4aSecond : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read2 fuel cursor = some rule4aKey := by
        rw [← cumul .rule4a]
        exact rule4aFirst
      simp [rule4aFirst, rule4aSecond]
      rw [source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_congr_of_cumulativeAgrees
        read1 read2 fuel cursor cumul
        (aromaticCanonicalRule4bcReferenceAlternatives
          (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))]

/-- One Rule-5 reading congruence: both common-reference R/S cumulative hierarchies are compared
through the cumulative agreement at the stages actually selected by
`aromaticCanonicalRule5StageFor`. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (cumul : source.AromaticCanonicalRerootCumulativeAgrees read1 read2 fuel cursor)
    (prior : source.AromaticCanonicalRerootRule4bcReading) :
    source.buildAromaticCanonicalRerootRule5ReadingWithRead? read1 fuel cursor prior =
    source.buildAromaticCanonicalRerootRule5ReadingWithRead? read2 fuel cursor prior := by
  unfold buildAromaticCanonicalRerootRule5ReadingWithRead?
  cases commonRFirst : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      (aromaticCanonicalRule5StageFor prior.reference? .R) read1 fuel cursor with
  | none =>
      have commonRSecond : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (aromaticCanonicalRule5StageFor prior.reference? .R) read2 fuel cursor = none := by
        rw [← cumul (aromaticCanonicalRule5StageFor prior.reference? .R)]
        exact commonRFirst
      simp [commonRFirst, commonRSecond]
  | some commonR =>
      have commonRSecond : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (aromaticCanonicalRule5StageFor prior.reference? .R) read2 fuel cursor =
            some commonR := by
        rw [← cumul (aromaticCanonicalRule5StageFor prior.reference? .R)]
        exact commonRFirst
      simp [commonRFirst, commonRSecond]
      cases commonSFirst : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (aromaticCanonicalRule5StageFor prior.reference? .S) read1 fuel cursor with
      | none =>
          have commonSSecond : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              (aromaticCanonicalRule5StageFor prior.reference? .S) read2 fuel cursor =
                none := by
            rw [← cumul (aromaticCanonicalRule5StageFor prior.reference? .S)]
            exact commonSFirst
          simp [commonSFirst, commonSSecond]
      | some commonS =>
          have commonSSecond : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              (aromaticCanonicalRule5StageFor prior.reference? .S) read2 fuel cursor =
                some commonS := by
            rw [← cumul (aromaticCanonicalRule5StageFor prior.reference? .S)]
            exact commonSFirst
          simp [commonSFirst, commonSSecond]

/-- Rule-5 reading-list congruence, by induction over the actual prior Rule-4b/4c readings. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_congr_of_cumulativeAgrees
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (cumul : source.AromaticCanonicalRerootCumulativeAgrees read1 read2 fuel cursor) :
    ∀ priors : List source.AromaticCanonicalRerootRule4bcReading,
      source.buildAromaticCanonicalRerootRule5ReadingsWithRead? read1 fuel cursor priors =
      source.buildAromaticCanonicalRerootRule5ReadingsWithRead? read2 fuel cursor priors := by
  intro priors
  induction priors with
  | nil => rfl
  | cons prior priors inductionHypothesis =>
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead?
      cases headFirst : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
          read1 fuel cursor prior with
      | none =>
          have headSecond : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
              read2 fuel cursor prior = none := by
            rw [← source.buildAromaticCanonicalRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
              read1 read2 fuel cursor cumul prior]
            exact headFirst
          simp [headFirst, headSecond]
      | some reading =>
          have headSecond : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
              read2 fuel cursor prior = some reading := by
            rw [← source.buildAromaticCanonicalRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
              read1 read2 fuel cursor cumul prior]
            exact headFirst
          simp [headFirst, headSecond]
          rw [inductionHypothesis]

/-- **Compound through-Rule-5 key congruence from cumulative agreement.** -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_congr_of_cumulativeAgrees
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (cumul : source.AromaticCanonicalRerootCumulativeAgrees read1 read2 fuel cursor) :
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read1 fuel cursor =
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read2 fuel cursor := by
  unfold buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
  cases priorFirst : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read1 fuel cursor with
  | none =>
      have priorSecond : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
          read2 fuel cursor = none := by
        rw [← source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
          read1 read2 fuel cursor cumul]
        exact priorFirst
      simp [priorFirst, priorSecond]
  | some prior =>
      have priorSecond : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
          read2 fuel cursor = some prior := by
        rw [← source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
          read1 read2 fuel cursor cumul]
        exact priorFirst
      simp [priorFirst, priorSecond]
      rw [source.buildAromaticCanonicalRerootRule5ReadingsWithRead?_congr_of_cumulativeAgrees
        read1 read2 fuel cursor cumul prior.readings]

/-! ## Instantiation at executable-reachable cursors -/

/-- The shipped generic cumulative congruence, restated as cumulative agreement at one reachable
cursor. -/
theorem aromaticCanonicalRerootCumulativeAgrees_of_readersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : source.AromaticCanonicalRerootReadersAgreeOnReachable read1 read2 start)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor)
    (fuel : Nat) :
    source.AromaticCanonicalRerootCumulativeAgrees read1 read2 fuel cursor :=
  fun stage =>
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr_of_reachable
      stage read1 read2 start agree fuel cursor reachable

/-- Read-support congruence for one Rule-4b/4c reading at every executable-reachable cursor. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_congr_of_readersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : source.AromaticCanonicalRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      ∀ reference : Option RS,
        source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read1 fuel cursor reference =
        source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read2 fuel cursor reference := by
  intro fuel cursor reachable reference
  exact source.buildAromaticCanonicalRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (source.aromaticCanonicalRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)
    reference

/-- Read-support congruence for the Rule-4b/4c reading list. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_congr_of_readersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : source.AromaticCanonicalRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      ∀ references : List (Option RS),
        source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
          read1 fuel cursor references =
        source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
          read2 fuel cursor references := by
  intro fuel cursor reachable references
  exact source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (source.aromaticCanonicalRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)
    references

/-- Read-support congruence for the compound Rules-4b/4c key, full `Option` including the
fail-closed outcome. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_congr_of_readersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : source.AromaticCanonicalRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? read1 fuel cursor =
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? read2 fuel cursor := by
  intro fuel cursor reachable
  exact source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (source.aromaticCanonicalRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)

/-- Read-support congruence for one Rule-5 reading. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_congr_of_readersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : source.AromaticCanonicalRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      ∀ prior : source.AromaticCanonicalRerootRule4bcReading,
        source.buildAromaticCanonicalRerootRule5ReadingWithRead? read1 fuel cursor prior =
        source.buildAromaticCanonicalRerootRule5ReadingWithRead? read2 fuel cursor prior := by
  intro fuel cursor reachable prior
  exact source.buildAromaticCanonicalRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (source.aromaticCanonicalRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)
    prior

/-- Read-support congruence for the Rule-5 reading list. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_congr_of_readersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : source.AromaticCanonicalRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      ∀ priors : List source.AromaticCanonicalRerootRule4bcReading,
        source.buildAromaticCanonicalRerootRule5ReadingsWithRead? read1 fuel cursor priors =
        source.buildAromaticCanonicalRerootRule5ReadingsWithRead? read2 fuel cursor priors := by
  intro fuel cursor reachable priors
  exact source.buildAromaticCanonicalRerootRule5ReadingsWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (source.aromaticCanonicalRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)
    priors

/-- **Main read-support theorem.**  If two arbitrary total label readers agree on every cursor
reachable from `start` through the actual executable reroot edge, then the complete parametric
compound through-Rule-5 builder returns exactly the same full `Option` key at every reachable
cursor and every fuel.  The equality is of the whole `Option`, so the fail-closed `none` outcome
is covered. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : source.AromaticCanonicalRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read1 fuel cursor =
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read2 fuel cursor := by
  intro fuel cursor reachable
  exact source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (source.aromaticCanonicalRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)

/-- **Endpoint form of the main theorem.**  At the starting cursor itself, reader agreement on
the executable-descendant set is enough for exact full `Option` equality of the complete compound
through-Rule-5 builds at every fuel. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read1 read2 : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : source.AromaticCanonicalRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ fuel : Nat,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read1 fuel start =
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read2 fuel start :=
  fun fuel =>
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable
      read1 read2 start agree fuel start Relation.ReflTransGen.refl

/-! ## Rule-4a projection of a successful compound build -/

/-- A successful parametric compound Rules-4b/4c build is assembled from the Rule-4a cumulative
key it actually compiled: the projection `key.rule4aKey` is exactly the `.rule4a` cumulative
build.  This is the projection the parent-versus-outward comparison short-circuits on before any
reference count or reading is inspected. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (computed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read fuel cursor =
      some key.rule4aKey := by
  unfold buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      simp [rule4aComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
          read fuel cursor
          (aromaticCanonicalRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          rfl

/-- A successful parametric complete through-Rule-5 build carries the Rule-4a key it actually
compiled as `key.prior.rule4aKey`. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? .rule4a read fuel cursor =
      some key.prior.rule4aKey := by
  unfold buildAromaticCanonicalRerootCompoundRule45KeyWithRead? at computed
  cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      simp [priorComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          exact source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
            read fuel cursor prior priorComputed

/-! ## Short-circuit behavior of the through-Rule-5 comparator -/

/-- A decisive prior Rules-4b/4c comparison is exactly the through-Rule-5 comparison; the Rule-5
readings are not consulted. -/
theorem compareAromaticCanonicalRerootCompoundRule45Keys_eq_prior_of_ne
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (decisive : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      left.prior right.prior ≠ Ordering.eq) :
    source.compareAromaticCanonicalRerootCompoundRule45Keys left right =
      source.compareAromaticCanonicalRerootCompoundRule4bcKeys left.prior right.prior := by
  unfold compareAromaticCanonicalRerootCompoundRule45Keys
  generalize priorComparison :
      source.compareAromaticCanonicalRerootCompoundRule4bcKeys
        left.prior right.prior = outcome at decisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

/-- After a complete prior Rules-4b/4c tie, the through-Rule-5 comparison is exactly the common-R
Rule-5 reading comparison. -/
theorem compareAromaticCanonicalRerootCompoundRule45Keys_eq_rule5_of_prior
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (priorTie : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq) :
    source.compareAromaticCanonicalRerootCompoundRule45Keys left right =
      source.compareAromaticCanonicalRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings := by
  simp [compareAromaticCanonicalRerootCompoundRule45Keys, compareLex,
    Ordering.byKey, priorTie]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the six parametric compound builders, their six exact production
specializations, the two read-agreement notions and every compound-layer read-support congruence,
the Rule-4a projection exposures, and the two comparator short-circuit lemmas.
`assert_kernel_only` permits exactly `propext`, `Classical.choice` and `Quot.sound`, and rejects
`sorryAx`, project axioms and native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_eq_aromaticCanonicalDependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_eq_aromaticCanonicalDependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_eq_aromaticCanonicalDependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_eq_aromaticCanonicalDependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_eq_aromaticCanonicalDependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalRerootReadersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalRerootCumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRerootCumulativeAgrees_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRerootCompoundRule45Keys_eq_prior_of_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRerootCompoundRule45Keys_eq_rule5_of_prior
