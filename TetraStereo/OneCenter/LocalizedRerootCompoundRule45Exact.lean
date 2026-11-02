import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact canonical semantics for compound Rules 4b--5

The existing compound derivations deliberately admit every descending permutation of
comparator-equivalent children inherited from the broad cumulative-key soundness relation.  This
module instead lifts the canonical cumulative-key relation through reference selection, the
normative no/one/`[R,S]` Rule-4b/4c readings, and both common-reference Rule-5 readings.  The result
characterizes every exact `some` result and every `none` result of the compound builders.
-/

namespace CertifiedLocalizedCIPInput

/-- Canonical meaning of one exact Rule-4b/4c reading. -/
inductive CanonicalLocalizedRerootRule4bcReading
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option RS → input.LocalizedRerootRule4bcReading → Prop
  | noReference {rule4bKey rule4cKey}
      (rule4b : input.CanonicalLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel cursor rule4bKey)
      (rule4c : input.CanonicalLocalizedRerootCumulativeRule45Key
        .rule4cNoReference target view fuel cursor rule4cKey) :
      CanonicalLocalizedRerootRule4bcReading input target view fuel cursor none
        { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey }
  | reference {reference rule4bKey rule4cKey}
      (rule4b : input.CanonicalLocalizedRerootCumulativeRule45Key
        (.rule4b reference) target view fuel cursor rule4bKey)
      (rule4c : input.CanonicalLocalizedRerootCumulativeRule45Key
        (.rule4c reference) target view fuel cursor rule4cKey) :
      CanonicalLocalizedRerootRule4bcReading input target view fuel cursor
        (some reference)
        { reference? := some reference, rule4bKey := rule4bKey, rule4cKey := rule4cKey }

/-- One-reading compilation is exactly the canonical two-key derivation. -/
theorem buildLocalizedRerootRule4bcReading?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (reading : input.LocalizedRerootRule4bcReading) :
    input.buildLocalizedRerootRule4bcReading?
        target view fuel cursor reference = some reading ↔
      input.CanonicalLocalizedRerootRule4bcReading
        target view fuel cursor reference reading := by
  cases reference with
  | none =>
      constructor
      · intro computed
        unfold buildLocalizedRerootRule4bcReading? at computed
        cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45Key?
            .rule4a target view fuel cursor with
        | none => simp [rule4bComputed] at computed
        | some rule4bKey =>
            cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45Key?
                .rule4cNoReference target view fuel cursor with
            | none => simp [rule4bComputed, rule4cComputed] at computed
            | some rule4cKey =>
                simp [rule4bComputed, rule4cComputed] at computed
                subst reading
                exact CanonicalLocalizedRerootRule4bcReading.noReference
                  ((input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                    .rule4a target view fuel cursor rule4bKey).mp rule4bComputed)
                  ((input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                    .rule4cNoReference target view fuel cursor rule4cKey).mp rule4cComputed)
      · intro derived
        cases derived with
        | noReference rule4b rule4c =>
            simp only [buildLocalizedRerootRule4bcReading?]
            rw [(input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
              .rule4a target view fuel cursor _).mpr rule4b]
            rw [(input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
              .rule4cNoReference target view fuel cursor _).mpr rule4c]
            rfl
  | some reference =>
      constructor
      · intro computed
        unfold buildLocalizedRerootRule4bcReading? at computed
        cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45Key?
            (.rule4b reference) target view fuel cursor with
        | none => simp [rule4bComputed] at computed
        | some rule4bKey =>
            cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45Key?
                (.rule4c reference) target view fuel cursor with
            | none => simp [rule4bComputed, rule4cComputed] at computed
            | some rule4cKey =>
                simp [rule4bComputed, rule4cComputed] at computed
                subst reading
                exact CanonicalLocalizedRerootRule4bcReading.reference
                  ((input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                    (.rule4b reference) target view fuel cursor rule4bKey).mp rule4bComputed)
                  ((input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                    (.rule4c reference) target view fuel cursor rule4cKey).mp rule4cComputed)
      · intro derived
        cases derived with
        | reference rule4b rule4c =>
            simp only [buildLocalizedRerootRule4bcReading?]
            rw [(input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
              (.rule4b reference) target view fuel cursor _).mpr rule4b]
            rw [(input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
              (.rule4c reference) target view fuel cursor _).mpr rule4c]
            rfl

/-- Canonical pointwise derivations in the exact normative alternative order. -/
inductive CanonicalLocalizedRerootRule4bcReadings
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (Option RS) → List input.LocalizedRerootRule4bcReading → Prop
  | nil : CanonicalLocalizedRerootRule4bcReadings
      input target view fuel cursor [] []
  | cons {reference references reading readings}
      (head : input.CanonicalLocalizedRerootRule4bcReading
        target view fuel cursor reference reading)
      (tail : input.CanonicalLocalizedRerootRule4bcReadings
        target view fuel cursor references readings) :
      CanonicalLocalizedRerootRule4bcReadings input target view fuel cursor
        (reference :: references) (reading :: readings)

/-- List compilation is exactly pointwise canonical compilation. -/
theorem buildLocalizedRerootRule4bcReadings?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ references readings,
      input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor references = some readings ↔
        input.CanonicalLocalizedRerootRule4bcReadings
          target view fuel cursor references readings
  | [], readings => by
      constructor
      · intro computed
        simp [buildLocalizedRerootRule4bcReadings?] at computed
        subst readings
        exact CanonicalLocalizedRerootRule4bcReadings.nil
      · intro derived
        cases derived
        rfl
  | reference :: references, readings => by
      constructor
      · intro computed
        unfold buildLocalizedRerootRule4bcReadings? at computed
        cases headComputed : input.buildLocalizedRerootRule4bcReading?
            target view fuel cursor reference with
        | none => simp [headComputed] at computed
        | some reading =>
            cases tailComputed : input.buildLocalizedRerootRule4bcReadings?
                target view fuel cursor references with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst readings
                exact CanonicalLocalizedRerootRule4bcReadings.cons
                  ((input.buildLocalizedRerootRule4bcReading?_eq_some_iff_canonical
                    target view fuel cursor reference reading).mp headComputed)
                  ((input.buildLocalizedRerootRule4bcReadings?_eq_some_iff_canonical
                    target view fuel cursor references tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            unfold buildLocalizedRerootRule4bcReadings?
            rw [(input.buildLocalizedRerootRule4bcReading?_eq_some_iff_canonical
              target view fuel cursor _ _).mpr head]
            rw [(input.buildLocalizedRerootRule4bcReadings?_eq_some_iff_canonical
              target view fuel cursor _ _).mpr tail]
            rfl

/-- Canonical meaning of the complete no/one/two-reference Rule-4b/4c key. -/
def CanonicalLocalizedRerootCompoundRule4bcKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey) : Prop :=
  input.CanonicalLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor key.rule4aKey ∧
    DeclarativeLocalizedRule4bReferenceSelection
      key.rule4aKey.rankedLabels key.references ∧
    key.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority key.references ∧
    input.CanonicalLocalizedRerootRule4bcReadings target view fuel cursor
      (localizedRule4bcReferenceAlternatives key.references) key.readings

/-- The compound Rule-4b/4c builder has exactly the canonical independent meaning. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey) :
    input.buildLocalizedRerootCompoundRule4bcKey?
        target view fuel cursor = some key ↔
      input.CanonicalLocalizedRerootCompoundRule4bcKey
        target view fuel cursor key := by
  constructor
  · intro computed
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
            exact ⟨
              (input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                .rule4a target view fuel cursor rule4aKey).mp rule4aComputed,
              (localizedRule4bReferencesFromRankedLabels_eq_iff
                rule4aKey.rankedLabels references).mp rfl,
              rfl,
              (input.buildLocalizedRerootRule4bcReadings?_eq_some_iff_canonical
                target view fuel cursor alternatives readings).mp readingsComputed⟩
  · intro derived
    rcases derived with ⟨rule4aDerived, referencesDerived, countEq, readingsDerived⟩
    have rule4aComputed :=
      (input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
        .rule4a target view fuel cursor key.rule4aKey).mpr rule4aDerived
    have referencesEq :=
      (localizedRule4bReferencesFromRankedLabels_eq_iff
        key.rule4aKey.rankedLabels key.references).mpr referencesDerived
    have readingsComputed :=
      (input.buildLocalizedRerootRule4bcReadings?_eq_some_iff_canonical
        target view fuel cursor
        (localizedRule4bcReferenceAlternatives key.references) key.readings).mpr
        readingsDerived
    have keyEq :
        ({ rule4aKey := key.rule4aKey
           references := key.references
           referenceCountPriority :=
             constitutionalRule4bReferenceCountPriority key.references
           readings := key.readings } : input.LocalizedRerootCompoundRule4bcKey) = key := by
      cases key
      simp_all
    simpa [buildLocalizedRerootCompoundRule4bcKey?, rule4aComputed,
      referencesEq, readingsComputed] using
      congrArg (fun value => (some value : Option input.LocalizedRerootCompoundRule4bcKey)) keyEq

/-- Failure of the compound Rule-4b/4c builder is exactly absence of a canonical result. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor = none ↔
      ¬ ∃ key, input.CanonicalLocalizedRerootCompoundRule4bcKey
        target view fuel cursor key := by
  constructor
  · intro computed ⟨key, derived⟩
    have successful :=
      (input.buildLocalizedRerootCompoundRule4bcKey?_eq_some_iff_canonical
        target view fuel cursor key).mpr derived
    rw [computed] at successful
    contradiction
  · intro absent
    cases computed : input.buildLocalizedRerootCompoundRule4bcKey?
        target view fuel cursor with
    | none => rfl
    | some key =>
        exact False.elim (absent ⟨key,
          (input.buildLocalizedRerootCompoundRule4bcKey?_eq_some_iff_canonical
            target view fuel cursor key).mp computed⟩)

/-! ## Rule 5 -/

/-- Canonical meaning of both common-reference Rule-5 readings. -/
def CanonicalLocalizedRerootRule5Reading
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading) : Prop :=
  reading.prior = prior ∧
    input.CanonicalLocalizedRerootCumulativeRule45Key
      (localizedRule5StageFor prior.reference? .R)
      target view fuel cursor reading.commonR ∧
    input.CanonicalLocalizedRerootCumulativeRule45Key
      (localizedRule5StageFor prior.reference? .S)
      target view fuel cursor reading.commonS

/-- One Rule-5 pair is exactly its two canonical cumulative-key readings. -/
theorem buildLocalizedRerootRule5Reading?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading) :
    input.buildLocalizedRerootRule5Reading?
        target view fuel cursor prior = some reading ↔
      input.CanonicalLocalizedRerootRule5Reading
        target view fuel cursor prior reading := by
  constructor
  · intro computed
    unfold buildLocalizedRerootRule5Reading? at computed
    cases commonRComputed : input.buildLocalizedRerootCumulativeRule45Key?
        (localizedRule5StageFor prior.reference? .R)
        target view fuel cursor with
    | none => simp [commonRComputed] at computed
    | some commonR =>
        cases commonSComputed : input.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor prior.reference? .S)
            target view fuel cursor with
        | none => simp [commonRComputed, commonSComputed] at computed
        | some commonS =>
            simp [commonRComputed, commonSComputed] at computed
            subst reading
            exact ⟨rfl,
              (input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                (localizedRule5StageFor prior.reference? .R)
                target view fuel cursor commonR).mp commonRComputed,
              (input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                (localizedRule5StageFor prior.reference? .S)
                target view fuel cursor commonS).mp commonSComputed⟩
  · rintro ⟨priorEq, commonRDerived, commonSDerived⟩
    have commonRComputed :=
      (input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
        (localizedRule5StageFor prior.reference? .R)
        target view fuel cursor reading.commonR).mpr commonRDerived
    have commonSComputed :=
      (input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
        (localizedRule5StageFor prior.reference? .S)
        target view fuel cursor reading.commonS).mpr commonSDerived
    have readingEq :
        ({ prior := prior
           commonR := reading.commonR
           commonS := reading.commonS } : input.LocalizedRerootRule5Reading) = reading := by
      cases reading
      simp_all
    simpa [buildLocalizedRerootRule5Reading?, commonRComputed, commonSComputed] using
      congrArg (fun value => (some value : Option input.LocalizedRerootRule5Reading)) readingEq

/-- Canonical pointwise Rule-5 derivations. -/
inductive CanonicalLocalizedRerootRule5Readings
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List input.LocalizedRerootRule4bcReading →
      List input.LocalizedRerootRule5Reading → Prop
  | nil : CanonicalLocalizedRerootRule5Readings
      input target view fuel cursor [] []
  | cons {prior priors reading readings}
      (head : input.CanonicalLocalizedRerootRule5Reading
        target view fuel cursor prior reading)
      (tail : input.CanonicalLocalizedRerootRule5Readings
        target view fuel cursor priors readings) :
      CanonicalLocalizedRerootRule5Readings input target view fuel cursor
        (prior :: priors) (reading :: readings)

/-- The Rule-5 reading list builder is exactly pointwise canonical compilation. -/
theorem buildLocalizedRerootRule5Readings?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ priors readings,
      input.buildLocalizedRerootRule5Readings?
          target view fuel cursor priors = some readings ↔
        input.CanonicalLocalizedRerootRule5Readings
          target view fuel cursor priors readings
  | [], readings => by
      constructor
      · intro computed
        simp [buildLocalizedRerootRule5Readings?] at computed
        subst readings
        exact CanonicalLocalizedRerootRule5Readings.nil
      · intro derived
        cases derived
        rfl
  | prior :: priors, readings => by
      constructor
      · intro computed
        unfold buildLocalizedRerootRule5Readings? at computed
        cases headComputed : input.buildLocalizedRerootRule5Reading?
            target view fuel cursor prior with
        | none => simp [headComputed] at computed
        | some reading =>
            cases tailComputed : input.buildLocalizedRerootRule5Readings?
                target view fuel cursor priors with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst readings
                exact CanonicalLocalizedRerootRule5Readings.cons
                  ((input.buildLocalizedRerootRule5Reading?_eq_some_iff_canonical
                    target view fuel cursor prior reading).mp headComputed)
                  ((input.buildLocalizedRerootRule5Readings?_eq_some_iff_canonical
                    target view fuel cursor priors tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            unfold buildLocalizedRerootRule5Readings?
            rw [(input.buildLocalizedRerootRule5Reading?_eq_some_iff_canonical
              target view fuel cursor _ _).mpr head]
            rw [(input.buildLocalizedRerootRule5Readings?_eq_some_iff_canonical
              target view fuel cursor _ _).mpr tail]
            rfl

/-- Canonical meaning of the complete through-Rule-5 key. -/
def CanonicalLocalizedRerootCompoundRule45Key
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key) : Prop :=
  input.CanonicalLocalizedRerootCompoundRule4bcKey
      target view fuel cursor key.prior ∧
    input.CanonicalLocalizedRerootRule5Readings
      target view fuel cursor key.prior.readings key.rule5Readings

/-- The complete through-Rule-5 builder has exactly the canonical independent meaning. -/
theorem buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key) :
    input.buildLocalizedRerootCompoundRule45Key?
        target view fuel cursor = some key ↔
      input.CanonicalLocalizedRerootCompoundRule45Key
        target view fuel cursor key := by
  constructor
  · intro computed
    unfold buildLocalizedRerootCompoundRule45Key? at computed
    cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKey?
        target view fuel cursor with
    | none => simp [priorComputed] at computed
    | some prior =>
        cases readingsComputed : input.buildLocalizedRerootRule5Readings?
            target view fuel cursor prior.readings with
        | none => simp [priorComputed, readingsComputed] at computed
        | some readings =>
            simp [priorComputed, readingsComputed] at computed
            subst key
            exact ⟨
              (input.buildLocalizedRerootCompoundRule4bcKey?_eq_some_iff_canonical
                target view fuel cursor prior).mp priorComputed,
              (input.buildLocalizedRerootRule5Readings?_eq_some_iff_canonical
                target view fuel cursor prior.readings readings).mp readingsComputed⟩
  · rintro ⟨priorDerived, readingsDerived⟩
    have priorComputed :=
      (input.buildLocalizedRerootCompoundRule4bcKey?_eq_some_iff_canonical
        target view fuel cursor key.prior).mpr priorDerived
    have readingsComputed :=
      (input.buildLocalizedRerootRule5Readings?_eq_some_iff_canonical
        target view fuel cursor key.prior.readings key.rule5Readings).mpr readingsDerived
    simp [buildLocalizedRerootCompoundRule45Key?, priorComputed, readingsComputed]

/-- Failure of the complete through-Rule-5 builder is exactly absence of a canonical key. -/
theorem buildLocalizedRerootCompoundRule45Key?_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor = none ↔
      ¬ ∃ key, input.CanonicalLocalizedRerootCompoundRule45Key
        target view fuel cursor key := by
  constructor
  · intro computed ⟨key, derived⟩
    have successful :=
      (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
        target view fuel cursor key).mpr derived
    rw [computed] at successful
    contradiction
  · intro absent
    cases computed : input.buildLocalizedRerootCompoundRule45Key?
        target view fuel cursor with
    | none => rfl
    | some key =>
        exact False.elim (absent ⟨key,
          (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
            target view fuel cursor key).mp computed⟩)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
