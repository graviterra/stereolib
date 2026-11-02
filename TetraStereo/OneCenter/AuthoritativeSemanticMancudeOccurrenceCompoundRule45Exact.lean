import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule45
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCumulativeRule45Exact

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact canonical source semantics for compound Rules 4b--5

The existing compound derivations deliberately allow every descending permutation of
comparator-equivalent children inherited from the broad cumulative-key soundness relation.  This
module instead lifts the canonical cumulative-key relation through reference selection, the
normative no/one/`[R,S]` Rule-4b/4c readings, and both common-reference Rule-5 readings.  The result
characterizes every exact `some` result and every `none` result of the compound builders.
-/

namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-- Canonical meaning of one exact Rule-4b/4c reading. -/
inductive CanonicalAromaticCanonicalRerootRule4bcReading
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option RS → source.AromaticCanonicalRerootRule4bcReading → Prop
  | noReference {rule4bKey rule4cKey}
      (rule4b : source.CanonicalAromaticCanonicalCumulativeRule45Key
        .rule4a target view fuel cursor rule4bKey)
      (rule4c : source.CanonicalAromaticCanonicalCumulativeRule45Key
        .rule4cNoReference target view fuel cursor rule4cKey) :
      CanonicalAromaticCanonicalRerootRule4bcReading source target view fuel cursor none
        { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey }
  | reference {reference rule4bKey rule4cKey}
      (rule4b : source.CanonicalAromaticCanonicalCumulativeRule45Key
        (.rule4b reference) target view fuel cursor rule4bKey)
      (rule4c : source.CanonicalAromaticCanonicalCumulativeRule45Key
        (.rule4c reference) target view fuel cursor rule4cKey) :
      CanonicalAromaticCanonicalRerootRule4bcReading source target view fuel cursor
        (some reference)
        { reference? := some reference, rule4bKey := rule4bKey, rule4cKey := rule4cKey }

/-- One-reading compilation is exactly the canonical two-key derivation. -/
theorem buildAromaticCanonicalRerootRule4bcReading?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS) (reading : source.AromaticCanonicalRerootRule4bcReading) :
    source.buildAromaticCanonicalRerootRule4bcReading?
        target view fuel cursor reference = some reading ↔
      source.CanonicalAromaticCanonicalRerootRule4bcReading
        target view fuel cursor reference reading := by
  cases reference with
  | none =>
      constructor
      · intro computed
        unfold buildAromaticCanonicalRerootRule4bcReading? at computed
        cases rule4bComputed : source.buildAromaticCanonicalCumulativeRule45Key?
            .rule4a target view fuel cursor with
        | none => simp [rule4bComputed] at computed
        | some rule4bKey =>
            cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45Key?
                .rule4cNoReference target view fuel cursor with
            | none => simp [rule4bComputed, rule4cComputed] at computed
            | some rule4cKey =>
                simp [rule4bComputed, rule4cComputed] at computed
                subst reading
                exact CanonicalAromaticCanonicalRerootRule4bcReading.noReference
                  ((source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                    .rule4a target view fuel cursor rule4bKey).mp rule4bComputed)
                  ((source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                    .rule4cNoReference target view fuel cursor rule4cKey).mp rule4cComputed)
      · intro derived
        cases derived with
        | noReference rule4b rule4c =>
            simp only [buildAromaticCanonicalRerootRule4bcReading?]
            rw [(source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
              .rule4a target view fuel cursor _).mpr rule4b]
            rw [(source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
              .rule4cNoReference target view fuel cursor _).mpr rule4c]
            rfl
  | some reference =>
      constructor
      · intro computed
        unfold buildAromaticCanonicalRerootRule4bcReading? at computed
        cases rule4bComputed : source.buildAromaticCanonicalCumulativeRule45Key?
            (.rule4b reference) target view fuel cursor with
        | none => simp [rule4bComputed] at computed
        | some rule4bKey =>
            cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45Key?
                (.rule4c reference) target view fuel cursor with
            | none => simp [rule4bComputed, rule4cComputed] at computed
            | some rule4cKey =>
                simp [rule4bComputed, rule4cComputed] at computed
                subst reading
                exact CanonicalAromaticCanonicalRerootRule4bcReading.reference
                  ((source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                    (.rule4b reference) target view fuel cursor rule4bKey).mp rule4bComputed)
                  ((source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                    (.rule4c reference) target view fuel cursor rule4cKey).mp rule4cComputed)
      · intro derived
        cases derived with
        | reference rule4b rule4c =>
            simp only [buildAromaticCanonicalRerootRule4bcReading?]
            rw [(source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
              (.rule4b reference) target view fuel cursor _).mpr rule4b]
            rw [(source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
              (.rule4c reference) target view fuel cursor _).mpr rule4c]
            rfl

/-- Canonical pointwise derivations in the exact normative alternative order. -/
inductive CanonicalAromaticCanonicalRerootRule4bcReadings
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    List (Option RS) → List source.AromaticCanonicalRerootRule4bcReading → Prop
  | nil : CanonicalAromaticCanonicalRerootRule4bcReadings
      source target view fuel cursor [] []
  | cons {reference references reading readings}
      (head : source.CanonicalAromaticCanonicalRerootRule4bcReading
        target view fuel cursor reference reading)
      (tail : source.CanonicalAromaticCanonicalRerootRule4bcReadings
        target view fuel cursor references readings) :
      CanonicalAromaticCanonicalRerootRule4bcReadings source target view fuel cursor
        (reference :: references) (reading :: readings)

/-- List compilation is exactly pointwise canonical compilation. -/
theorem buildAromaticCanonicalRerootRule4bcReadings?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ references readings,
      source.buildAromaticCanonicalRerootRule4bcReadings?
          target view fuel cursor references = some readings ↔
        source.CanonicalAromaticCanonicalRerootRule4bcReadings
          target view fuel cursor references readings
  | [], readings => by
      constructor
      · intro computed
        simp [buildAromaticCanonicalRerootRule4bcReadings?] at computed
        subst readings
        exact CanonicalAromaticCanonicalRerootRule4bcReadings.nil
      · intro derived
        cases derived
        rfl
  | reference :: references, readings => by
      constructor
      · intro computed
        unfold buildAromaticCanonicalRerootRule4bcReadings? at computed
        cases headComputed : source.buildAromaticCanonicalRerootRule4bcReading?
            target view fuel cursor reference with
        | none => simp [headComputed] at computed
        | some reading =>
            cases tailComputed : source.buildAromaticCanonicalRerootRule4bcReadings?
                target view fuel cursor references with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst readings
                exact CanonicalAromaticCanonicalRerootRule4bcReadings.cons
                  ((source.buildAromaticCanonicalRerootRule4bcReading?_eq_some_iff_canonical
                    target view fuel cursor reference reading).mp headComputed)
                  ((source.buildAromaticCanonicalRerootRule4bcReadings?_eq_some_iff_canonical
                    target view fuel cursor references tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            unfold buildAromaticCanonicalRerootRule4bcReadings?
            rw [(source.buildAromaticCanonicalRerootRule4bcReading?_eq_some_iff_canonical
              target view fuel cursor _ _).mpr head]
            rw [(source.buildAromaticCanonicalRerootRule4bcReadings?_eq_some_iff_canonical
              target view fuel cursor _ _).mpr tail]
            rfl

/-- Canonical meaning of the complete no/one/two-reference Rule-4b/4c key. -/
def CanonicalAromaticCanonicalRerootCompoundRule4bcKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey) : Prop :=
  source.CanonicalAromaticCanonicalCumulativeRule45Key
      .rule4a target view fuel cursor key.rule4aKey ∧
    DeclarativeLocalizedRule4bReferenceSelection
      key.rule4aKey.rankedLabels key.references ∧
    key.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority key.references ∧
    source.CanonicalAromaticCanonicalRerootRule4bcReadings target view fuel cursor
      (aromaticCanonicalRule4bcReferenceAlternatives key.references) key.readings

/-- The compound Rule-4b/4c builder has exactly the canonical independent meaning. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKey?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey) :
    source.buildAromaticCanonicalRerootCompoundRule4bcKey?
        target view fuel cursor = some key ↔
      source.CanonicalAromaticCanonicalRerootCompoundRule4bcKey
        target view fuel cursor key := by
  constructor
  · intro computed
    unfold buildAromaticCanonicalRerootCompoundRule4bcKey? at computed
    cases rule4aComputed : source.buildAromaticCanonicalCumulativeRule45Key?
        .rule4a target view fuel cursor with
    | none => simp [rule4aComputed] at computed
    | some rule4aKey =>
        let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
        let alternatives := aromaticCanonicalRule4bcReferenceAlternatives references
        cases readingsComputed : source.buildAromaticCanonicalRerootRule4bcReadings?
            target view fuel cursor alternatives with
        | none =>
            simp [rule4aComputed, references, alternatives, readingsComputed] at computed
        | some readings =>
            simp [rule4aComputed, references, alternatives, readingsComputed] at computed
            subst key
            exact ⟨
              (source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                .rule4a target view fuel cursor rule4aKey).mp rule4aComputed,
              (localizedRule4bReferencesFromRankedLabels_eq_iff
                rule4aKey.rankedLabels references).mp rfl,
              rfl,
              (source.buildAromaticCanonicalRerootRule4bcReadings?_eq_some_iff_canonical
                target view fuel cursor alternatives readings).mp readingsComputed⟩
  · intro derived
    rcases derived with ⟨rule4aDerived, referencesDerived, countEq, readingsDerived⟩
    have rule4aComputed :=
      (source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
        .rule4a target view fuel cursor key.rule4aKey).mpr rule4aDerived
    have referencesEq :=
      (localizedRule4bReferencesFromRankedLabels_eq_iff
        key.rule4aKey.rankedLabels key.references).mpr referencesDerived
    have readingsComputed :=
      (source.buildAromaticCanonicalRerootRule4bcReadings?_eq_some_iff_canonical
        target view fuel cursor
        (aromaticCanonicalRule4bcReferenceAlternatives key.references) key.readings).mpr
        readingsDerived
    have keyEq :
        ({ rule4aKey := key.rule4aKey
           references := key.references
           referenceCountPriority :=
             constitutionalRule4bReferenceCountPriority key.references
           readings := key.readings } : source.AromaticCanonicalRerootCompoundRule4bcKey) = key := by
      cases key
      simp_all
    simpa [buildAromaticCanonicalRerootCompoundRule4bcKey?, rule4aComputed,
      referencesEq, readingsComputed] using
      congrArg (fun value => (some value : Option source.AromaticCanonicalRerootCompoundRule4bcKey)) keyEq

/-- Failure of the compound Rule-4b/4c builder is exactly absence of a canonical result. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKey?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.buildAromaticCanonicalRerootCompoundRule4bcKey? target view fuel cursor = none ↔
      ¬ ∃ key, source.CanonicalAromaticCanonicalRerootCompoundRule4bcKey
        target view fuel cursor key := by
  constructor
  · intro computed ⟨key, derived⟩
    have successful :=
      (source.buildAromaticCanonicalRerootCompoundRule4bcKey?_eq_some_iff_canonical
        target view fuel cursor key).mpr derived
    rw [computed] at successful
    contradiction
  · intro absent
    cases computed : source.buildAromaticCanonicalRerootCompoundRule4bcKey?
        target view fuel cursor with
    | none => rfl
    | some key =>
        exact False.elim (absent ⟨key,
          (source.buildAromaticCanonicalRerootCompoundRule4bcKey?_eq_some_iff_canonical
            target view fuel cursor key).mp computed⟩)

/-- Canonical compound Rule-4b/4c semantics refines the broad chemical semantics. -/
theorem CanonicalAromaticCanonicalRerootCompoundRule4bcKey.sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (canonical : source.CanonicalAromaticCanonicalRerootCompoundRule4bcKey
      target view fuel cursor key) :
    source.DeclarativeAromaticCanonicalRerootCompoundRule4bcKey
      target view fuel cursor key :=
  source.buildAromaticCanonicalRerootCompoundRule4bcKey?_sound
    target view fuel cursor key
      ((source.buildAromaticCanonicalRerootCompoundRule4bcKey?_eq_some_iff_canonical
        target view fuel cursor key).mpr canonical)

/-! ## Rule 5 -/

/-- Canonical meaning of both common-reference Rule-5 readings. -/
def CanonicalAromaticCanonicalRerootRule5Reading
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading) : Prop :=
  reading.prior = prior ∧
    source.CanonicalAromaticCanonicalCumulativeRule45Key
      (aromaticCanonicalRule5StageFor prior.reference? .R)
      target view fuel cursor reading.commonR ∧
    source.CanonicalAromaticCanonicalCumulativeRule45Key
      (aromaticCanonicalRule5StageFor prior.reference? .S)
      target view fuel cursor reading.commonS

/-- One Rule-5 pair is exactly its two canonical cumulative-key readings. -/
theorem buildAromaticCanonicalRerootRule5Reading?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading) :
    source.buildAromaticCanonicalRerootRule5Reading?
        target view fuel cursor prior = some reading ↔
      source.CanonicalAromaticCanonicalRerootRule5Reading
        target view fuel cursor prior reading := by
  constructor
  · intro computed
    unfold buildAromaticCanonicalRerootRule5Reading? at computed
    cases commonRComputed : source.buildAromaticCanonicalCumulativeRule45Key?
        (aromaticCanonicalRule5StageFor prior.reference? .R)
        target view fuel cursor with
    | none => simp [commonRComputed] at computed
    | some commonR =>
        cases commonSComputed : source.buildAromaticCanonicalCumulativeRule45Key?
            (aromaticCanonicalRule5StageFor prior.reference? .S)
            target view fuel cursor with
        | none => simp [commonRComputed, commonSComputed] at computed
        | some commonS =>
            simp [commonRComputed, commonSComputed] at computed
            subst reading
            exact ⟨rfl,
              (source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                (aromaticCanonicalRule5StageFor prior.reference? .R)
                target view fuel cursor commonR).mp commonRComputed,
              (source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                (aromaticCanonicalRule5StageFor prior.reference? .S)
                target view fuel cursor commonS).mp commonSComputed⟩
  · rintro ⟨priorEq, commonRDerived, commonSDerived⟩
    have commonRComputed :=
      (source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
        (aromaticCanonicalRule5StageFor prior.reference? .R)
        target view fuel cursor reading.commonR).mpr commonRDerived
    have commonSComputed :=
      (source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
        (aromaticCanonicalRule5StageFor prior.reference? .S)
        target view fuel cursor reading.commonS).mpr commonSDerived
    have readingEq :
        ({ prior := prior
           commonR := reading.commonR
           commonS := reading.commonS } : source.AromaticCanonicalRerootRule5Reading) = reading := by
      cases reading
      simp_all
    simpa [buildAromaticCanonicalRerootRule5Reading?, commonRComputed, commonSComputed] using
      congrArg (fun value => (some value : Option source.AromaticCanonicalRerootRule5Reading)) readingEq

/-- Canonical pointwise Rule-5 derivations. -/
inductive CanonicalAromaticCanonicalRerootRule5Readings
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    List source.AromaticCanonicalRerootRule4bcReading →
      List source.AromaticCanonicalRerootRule5Reading → Prop
  | nil : CanonicalAromaticCanonicalRerootRule5Readings
      source target view fuel cursor [] []
  | cons {prior priors reading readings}
      (head : source.CanonicalAromaticCanonicalRerootRule5Reading
        target view fuel cursor prior reading)
      (tail : source.CanonicalAromaticCanonicalRerootRule5Readings
        target view fuel cursor priors readings) :
      CanonicalAromaticCanonicalRerootRule5Readings source target view fuel cursor
        (prior :: priors) (reading :: readings)

/-- The Rule-5 reading list builder is exactly pointwise canonical compilation. -/
theorem buildAromaticCanonicalRerootRule5Readings?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ priors readings,
      source.buildAromaticCanonicalRerootRule5Readings?
          target view fuel cursor priors = some readings ↔
        source.CanonicalAromaticCanonicalRerootRule5Readings
          target view fuel cursor priors readings
  | [], readings => by
      constructor
      · intro computed
        simp [buildAromaticCanonicalRerootRule5Readings?] at computed
        subst readings
        exact CanonicalAromaticCanonicalRerootRule5Readings.nil
      · intro derived
        cases derived
        rfl
  | prior :: priors, readings => by
      constructor
      · intro computed
        unfold buildAromaticCanonicalRerootRule5Readings? at computed
        cases headComputed : source.buildAromaticCanonicalRerootRule5Reading?
            target view fuel cursor prior with
        | none => simp [headComputed] at computed
        | some reading =>
            cases tailComputed : source.buildAromaticCanonicalRerootRule5Readings?
                target view fuel cursor priors with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst readings
                exact CanonicalAromaticCanonicalRerootRule5Readings.cons
                  ((source.buildAromaticCanonicalRerootRule5Reading?_eq_some_iff_canonical
                    target view fuel cursor prior reading).mp headComputed)
                  ((source.buildAromaticCanonicalRerootRule5Readings?_eq_some_iff_canonical
                    target view fuel cursor priors tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            unfold buildAromaticCanonicalRerootRule5Readings?
            rw [(source.buildAromaticCanonicalRerootRule5Reading?_eq_some_iff_canonical
              target view fuel cursor _ _).mpr head]
            rw [(source.buildAromaticCanonicalRerootRule5Readings?_eq_some_iff_canonical
              target view fuel cursor _ _).mpr tail]
            rfl

/-- Canonical meaning of the complete through-Rule-5 key. -/
def CanonicalAromaticCanonicalRerootCompoundRule45Key
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key) : Prop :=
  source.CanonicalAromaticCanonicalRerootCompoundRule4bcKey
      target view fuel cursor key.prior ∧
    source.CanonicalAromaticCanonicalRerootRule5Readings
      target view fuel cursor key.prior.readings key.rule5Readings

/-- The complete through-Rule-5 builder has exactly the canonical independent meaning. -/
theorem buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key) :
    source.buildAromaticCanonicalRerootCompoundRule45Key?
        target view fuel cursor = some key ↔
      source.CanonicalAromaticCanonicalRerootCompoundRule45Key
        target view fuel cursor key := by
  constructor
  · intro computed
    unfold buildAromaticCanonicalRerootCompoundRule45Key? at computed
    cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKey?
        target view fuel cursor with
    | none => simp [priorComputed] at computed
    | some prior =>
        cases readingsComputed : source.buildAromaticCanonicalRerootRule5Readings?
            target view fuel cursor prior.readings with
        | none => simp [priorComputed, readingsComputed] at computed
        | some readings =>
            simp [priorComputed, readingsComputed] at computed
            subst key
            exact ⟨
              (source.buildAromaticCanonicalRerootCompoundRule4bcKey?_eq_some_iff_canonical
                target view fuel cursor prior).mp priorComputed,
              (source.buildAromaticCanonicalRerootRule5Readings?_eq_some_iff_canonical
                target view fuel cursor prior.readings readings).mp readingsComputed⟩
  · rintro ⟨priorDerived, readingsDerived⟩
    have priorComputed :=
      (source.buildAromaticCanonicalRerootCompoundRule4bcKey?_eq_some_iff_canonical
        target view fuel cursor key.prior).mpr priorDerived
    have readingsComputed :=
      (source.buildAromaticCanonicalRerootRule5Readings?_eq_some_iff_canonical
        target view fuel cursor key.prior.readings key.rule5Readings).mpr readingsDerived
    simp [buildAromaticCanonicalRerootCompoundRule45Key?, priorComputed, readingsComputed]

/-- Failure of the complete through-Rule-5 builder is exactly absence of a canonical key. -/
theorem buildAromaticCanonicalRerootCompoundRule45Key?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel cursor = none ↔
      ¬ ∃ key, source.CanonicalAromaticCanonicalRerootCompoundRule45Key
        target view fuel cursor key := by
  constructor
  · intro computed ⟨key, derived⟩
    have successful :=
      (source.buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
        target view fuel cursor key).mpr derived
    rw [computed] at successful
    contradiction
  · intro absent
    cases computed : source.buildAromaticCanonicalRerootCompoundRule45Key?
        target view fuel cursor with
    | none => rfl
    | some key =>
        exact False.elim (absent ⟨key,
          (source.buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
            target view fuel cursor key).mp computed⟩)

/-- Canonical through-Rule-5 semantics refines the broad chemical semantics. -/
theorem CanonicalAromaticCanonicalRerootCompoundRule45Key.sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (canonical : source.CanonicalAromaticCanonicalRerootCompoundRule45Key
      target view fuel cursor key) :
    source.DeclarativeAromaticCanonicalRerootCompoundRule45Key
      target view fuel cursor key :=
  source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
    target view fuel cursor key
      ((source.buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
        target view fuel cursor key).mpr canonical)

end AuthoritativeChemicalInput

end TetraStereo.OneCenter
