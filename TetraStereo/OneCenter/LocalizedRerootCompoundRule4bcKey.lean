import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Exact

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-! ## Generic lexicographic composition facts

`compareLex` returns its first comparison unless that comparison is `Ordering.eq`.  These two
facts let subsequent layers of a nested compound comparison be analysed without unfolding the
whole definition at once.  They are purely order-theoretic; no chemical premise is used. -/

/-- A non-`eq` first comparison is decisive for a lexicographic composition. -/
theorem localizedCompareLex_eq_left_of_ne {α : Type*} {cmp₁ cmp₂ : α → α → Ordering}
    {a b : α} (decisive : cmp₁ a b ≠ Ordering.eq) :
    compareLex cmp₁ cmp₂ a b = cmp₁ a b := by
  unfold compareLex
  generalize comparison : cmp₁ a b = outcome at decisive ⊢
  cases outcome with
  | lt => rfl
  | eq => exact (decisive rfl).elim
  | gt => rfl

/-- An `eq` first comparison exposes exactly the second comparison. -/
theorem localizedCompareLex_eq_right_of_eq {α : Type*} {cmp₁ cmp₂ : α → α → Ordering}
    {a b : α} (tied : cmp₁ a b = Ordering.eq) :
    compareLex cmp₁ cmp₂ a b = cmp₂ a b := by
  unfold compareLex
  rw [tied]
  rfl

namespace CertifiedLocalizedCIPInput

/-!
# Compound Rules-4b/4c keys over occurrence reroot cursors

P-92.5.2.1 may select no Rule-4b reference, one reference, or sequentially both R and S.  This
module represents those alternatives without choosing one arbitrarily.  Each selected reference
has a complete Rule-4b key and a complete cumulative Rule-4c key.  The alternatives retain the
normative sequence `[R, S]`; they are not outcome-sorted.

Comparison follows the source rule order (P-92.5.1, P-92.5.2.1; Hanson 2018 Rule 4a):

1. the already compiled complete Rule-4a key, so that the class comparison of
   (P-92.5.1) is exhaustive before any Rule-4b data are inspected;
2. only after an exact Rule-4a tie, criterion (c)(i)'s reference count;
3. then the complete sequential Rule-4b like/unlike readings;
4. and only after every Rule-4b reading ties, the corresponding Rule-4c readings.

In particular the reference count is *not* permitted to override a strict Rule-4a decision.  The
actual builder `buildLocalizedRerootCompoundRule4bcKey?` compiles the Rule-4a key first and
derives the reference selection, the count, and the readings from it; the comparator now observes
that same key first.
-/

/-- One reference alternative.  `none` is the genuine no-uppercase-reference case; its Rule-4b
key is the Rule-4a hierarchy and its Rule-4c key uses the no-reference cumulative stage. -/
structure LocalizedRerootRule4bcReading
    (input : CertifiedLocalizedCIPInput) where
  reference? : Option RS
  rule4bKey : input.LocalizedRerootCumulativeRule45Key
  rule4cKey : input.LocalizedRerootCumulativeRule45Key

/-- Turn the P-92 reference list into the nonempty list of alternatives needed for Rule 4c. -/
def localizedRule4bcReferenceAlternatives : List RS → List (Option RS)
  | [] => [none]
  | references => references.map some

/-- Compile both cumulative stages for one exact reference alternative. -/
noncomputable def buildLocalizedRerootRule4bcReading?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option RS → Option input.LocalizedRerootRule4bcReading
  | none => do
      let rule4bKey ← input.buildLocalizedRerootCumulativeRule45Key?
        .rule4a target view fuel cursor
      let rule4cKey ← input.buildLocalizedRerootCumulativeRule45Key?
        .rule4cNoReference target view fuel cursor
      some
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }
  | some reference => do
      let rule4bKey ← input.buildLocalizedRerootCumulativeRule45Key?
        (.rule4b reference) target view fuel cursor
      let rule4cKey ← input.buildLocalizedRerootCumulativeRule45Key?
        (.rule4c reference) target view fuel cursor
      some
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }

/-- Rule-4b-only comparison used pointwise in the normative reference sequence. -/
def compareLocalizedRerootRule4bcReadingsByRule4b
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootRule4bcReading →
      input.LocalizedRerootRule4bcReading → Ordering :=
  Ordering.byKey (fun reading => reading.rule4bKey.descriptor)
    (OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority)

theorem compareLocalizedRerootRule4bcReadingsByRule4b_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedRerootRule4bcReadingsByRule4b := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedRerootRule4bcReadingsByRule4b
    compareLocalizedCumulativeRule45Priority
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- Complete compound key.  `references` is the exact P-92 selection and `readings` retains the
same normative no/one/`[R,S]` alternative order. -/
structure LocalizedRerootCompoundRule4bcKey
    (input : CertifiedLocalizedCIPInput) where
  rule4aKey : input.LocalizedRerootCumulativeRule45Key
  references : List RS
  referenceCountPriority : Nat
  readings : List input.LocalizedRerootRule4bcReading

noncomputable def buildLocalizedRerootRule4bcReadings?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (Option RS) → Option (List input.LocalizedRerootRule4bcReading)
  | [] => some []
  | reference :: references => do
      let reading ← input.buildLocalizedRerootRule4bcReading?
        target view fuel cursor reference
      let readings ← input.buildLocalizedRerootRule4bcReadings?
        target view fuel cursor references
      some (reading :: readings)

/-- General no/one/two-reference compiler. -/
noncomputable def buildLocalizedRerootCompoundRule4bcKey?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule4bcKey := do
  let rule4aKey ← input.buildLocalizedRerootCumulativeRule45Key?
    .rule4a target view fuel cursor
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  let readings ← input.buildLocalizedRerootRule4bcReadings?
    target view fuel cursor alternatives
  some
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings }

/-! ## Independent compound derivation -/

inductive DeclarativeLocalizedRerootRule4bcReading
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option RS → input.LocalizedRerootRule4bcReading → Prop
  | noReference {rule4bKey rule4cKey}
      (rule4b : input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel cursor rule4bKey)
      (rule4c : input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4cNoReference target view fuel cursor rule4cKey) :
      DeclarativeLocalizedRerootRule4bcReading input target view fuel cursor none
        { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey }
  | reference {reference rule4bKey rule4cKey}
      (rule4b : input.DeclarativeLocalizedRerootCumulativeRule45Key
        (.rule4b reference) target view fuel cursor rule4bKey)
      (rule4c : input.DeclarativeLocalizedRerootCumulativeRule45Key
        (.rule4c reference) target view fuel cursor rule4cKey) :
      DeclarativeLocalizedRerootRule4bcReading input target view fuel cursor
        (some reference)
        { reference? := some reference, rule4bKey := rule4bKey, rule4cKey := rule4cKey }

inductive DeclarativeLocalizedRerootRule4bcReadings
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (Option RS) → List input.LocalizedRerootRule4bcReading → Prop
  | nil : DeclarativeLocalizedRerootRule4bcReadings
      input target view fuel cursor [] []
  | cons {reference references reading readings}
      (head : input.DeclarativeLocalizedRerootRule4bcReading
        target view fuel cursor reference reading)
      (tail : input.DeclarativeLocalizedRerootRule4bcReadings
        target view fuel cursor references readings) :
      DeclarativeLocalizedRerootRule4bcReadings input target view fuel cursor
        (reference :: references) (reading :: readings)

theorem buildLocalizedRerootRule4bcReading?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReading?
      target view fuel cursor reference = some reading) :
    input.DeclarativeLocalizedRerootRule4bcReading
      target view fuel cursor reference reading := by
  cases reference with
  | none =>
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
              exact DeclarativeLocalizedRerootRule4bcReading.noReference
                (input.buildLocalizedRerootCumulativeRule45Key?_sound
                  .rule4a target view fuel cursor rule4bKey rule4bComputed)
                (input.buildLocalizedRerootCumulativeRule45Key?_sound
                  .rule4cNoReference target view fuel cursor rule4cKey rule4cComputed)
  | some reference =>
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
              exact DeclarativeLocalizedRerootRule4bcReading.reference
                (input.buildLocalizedRerootCumulativeRule45Key?_sound
                  (.rule4b reference) target view fuel cursor rule4bKey rule4bComputed)
                (input.buildLocalizedRerootCumulativeRule45Key?_sound
                  (.rule4c reference) target view fuel cursor rule4cKey rule4cComputed)

theorem buildLocalizedRerootRule4bcReadings?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ references readings,
      input.buildLocalizedRerootRule4bcReadings?
        target view fuel cursor references = some readings →
      input.DeclarativeLocalizedRerootRule4bcReadings
        target view fuel cursor references readings
  | [], readings, computed => by
      simp [buildLocalizedRerootRule4bcReadings?] at computed
      subst readings
      exact DeclarativeLocalizedRerootRule4bcReadings.nil
  | reference :: references, readings, computed => by
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
              exact DeclarativeLocalizedRerootRule4bcReadings.cons
                (input.buildLocalizedRerootRule4bcReading?_sound
                  target view fuel cursor reference reading headComputed)
                (input.buildLocalizedRerootRule4bcReadings?_sound
                  target view fuel cursor references tail tailComputed)

def DeclarativeLocalizedRerootCompoundRule4bcKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey) : Prop :=
  input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor key.rule4aKey ∧
    DeclarativeLocalizedRule4bReferenceSelection
      key.rule4aKey.rankedLabels key.references ∧
    key.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority key.references ∧
    input.DeclarativeLocalizedRerootRule4bcReadings target view fuel cursor
      (localizedRule4bcReferenceAlternatives key.references) key.readings

theorem buildLocalizedRerootCompoundRule4bcKey?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor key := by
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
            input.buildLocalizedRerootCumulativeRule45Key?_sound
              .rule4a target view fuel cursor rule4aKey rule4aComputed,
            (localizedRule4bReferencesFromRankedLabels_eq_iff
              rule4aKey.rankedLabels references).mp rfl,
            rfl,
            input.buildLocalizedRerootRule4bcReadings?_sound
              target view fuel cursor alternatives readings readingsComputed⟩

/-- Compare the canonical Rule-4b reading lists. -/
def compareLocalizedRerootCompoundRule4bReadings
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedRerootRule4bcReading →
      List input.LocalizedRerootRule4bcReading → Ordering :=
  List.compareLex input.compareLocalizedRerootRule4bcReadingsByRule4b

/-- Compare canonical cumulative Rule-4c readings, without re-sorting them by Rule 4c. -/
def compareLocalizedRerootCompoundRule4cReadings
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedRerootRule4bcReading →
      List input.LocalizedRerootRule4bcReading → Ordering :=
  List.compareLex
    (Ordering.byKey (fun reading => reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority))

/-- The compound sub-comparison used strictly after an exhaustive Rule-4a tie: criterion (c)(i)'s
reference count, then every Rule-4b reading, and only after their complete tie the corresponding
Rule-4c readings. -/
def compareLocalizedRerootCompoundRule4bcAfterRule4a
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey) : Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.referenceCountPriority) compare)
    (compareLex
      (Ordering.byKey (fun key => key.readings)
        input.compareLocalizedRerootCompoundRule4bReadings)
      (Ordering.byKey (fun key => key.readings)
        input.compareLocalizedRerootCompoundRule4cReadings))
    left right

/-- Normative compound comparison.  Rule 4a is exhausted first (P-92.5.1); only an exact Rule-4a
tie reaches criterion (c)(i)'s reference count, then the complete Rule-4b readings, and only a
complete Rule-4b tie reaches Rule 4c.  A strict Rule-4a decision therefore always wins,
independently of the later reference count. -/
def compareLocalizedRerootCompoundRule4bcKeys
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootCompoundRule4bcKey →
      input.LocalizedRerootCompoundRule4bcKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.rule4aKey)
      input.compareLocalizedRerootCumulativeRule45Keys)
    (compareLex
      (Ordering.byKey (fun key => key.referenceCountPriority) compare)
      (compareLex
        (Ordering.byKey (fun key => key.readings)
          input.compareLocalizedRerootCompoundRule4bReadings)
        (Ordering.byKey (fun key => key.readings)
          input.compareLocalizedRerootCompoundRule4cReadings)))

/-- A strict Rule-4a key comparison determines the compound comparison before
`referenceCountPriority` or any reading is inspected. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (decisive : input.compareLocalizedRerootCumulativeRule45Keys
      left.rule4aKey right.rule4aKey ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right =
      input.compareLocalizedRerootCumulativeRule45Keys
        left.rule4aKey right.rule4aKey := by
  unfold compareLocalizedRerootCompoundRule4bcKeys
  generalize rule4aComparison :
      input.compareLocalizedRerootCumulativeRule45Keys
        left.rule4aKey right.rule4aKey = outcome at decisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

/-- After an exact Rule-4a tie the compound comparison is exactly the reference-count/Rule-4b/
Rule-4c tail. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_eq_afterRule4a_of_tie
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      left.rule4aKey right.rule4aKey = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right =
      input.compareLocalizedRerootCompoundRule4bcAfterRule4a left right := by
  unfold compareLocalizedRerootCompoundRule4bcKeys
    compareLocalizedRerootCompoundRule4bcAfterRule4a
  simp [compareLex, Ordering.byKey, rule4aTie]

/-- After a Rule-4a tie, criterion (c)(i)'s reference count is the first decisive gate. -/
theorem compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_referenceCount_of_ne
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (decisive : compare left.referenceCountPriority right.referenceCountPriority ≠
      Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcAfterRule4a left right =
      compare left.referenceCountPriority right.referenceCountPriority := by
  unfold compareLocalizedRerootCompoundRule4bcAfterRule4a
  generalize countComparison :
      compare left.referenceCountPriority right.referenceCountPriority =
        outcome at decisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

/-- After a Rule-4a tie and an exact reference-count tie, the complete Rule-4b readings decide
before any Rule-4c reading is consulted. -/
theorem compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_rule4b_of_priorTie
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (countTie : compare left.referenceCountPriority right.referenceCountPriority =
      Ordering.eq)
    (rule4bDecisive : input.compareLocalizedRerootCompoundRule4bReadings
      left.readings right.readings ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcAfterRule4a left right =
      input.compareLocalizedRerootCompoundRule4bReadings
        left.readings right.readings := by
  unfold compareLocalizedRerootCompoundRule4bcAfterRule4a
  generalize rule4bComparison :
      input.compareLocalizedRerootCompoundRule4bReadings
        left.readings right.readings = outcome at rule4bDecisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

/-- Rule 4c is observed exactly after the Rule-4a, reference-count, and complete Rule-4b gates
tie. -/
theorem compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_rule4c_of_priorTies
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (countTie : compare left.referenceCountPriority right.referenceCountPriority =
      Ordering.eq)
    (rule4bTie : input.compareLocalizedRerootCompoundRule4bReadings
      left.readings right.readings = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcAfterRule4a left right =
      input.compareLocalizedRerootCompoundRule4cReadings
        left.readings right.readings := by
  simp [compareLocalizedRerootCompoundRule4bcAfterRule4a, compareLex,
    Ordering.byKey, countTie, rule4bTie]

/-- After an exact Rule-4a tie, criterion (c)(i)'s reference count is the first decisive gate.
This is the repaired form of the former count-first theorem: an explicit `rule4aTie` hypothesis is
required, because the count no longer precedes Rule 4a. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_eq_referenceCount_of_ne
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      left.rule4aKey right.rule4aKey = Ordering.eq)
    (decisive : compare left.referenceCountPriority right.referenceCountPriority ≠
      Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right =
      compare left.referenceCountPriority right.referenceCountPriority := by
  rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_afterRule4a_of_tie
    left right rule4aTie]
  exact input.compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_referenceCount_of_ne
    left right decisive

/-- Complete Rule-4b readings decide before any Rule-4c reading is consulted, after the prior
Rule-4a and reference-count ties. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_eq_rule4b_of_priorTie
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      left.rule4aKey right.rule4aKey = Ordering.eq)
    (countTie : compare left.referenceCountPriority right.referenceCountPriority =
      Ordering.eq)
    (rule4bDecisive : input.compareLocalizedRerootCompoundRule4bReadings
      left.readings right.readings ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right =
      input.compareLocalizedRerootCompoundRule4bReadings
        left.readings right.readings := by
  rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_afterRule4a_of_tie
    left right rule4aTie]
  exact input.compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_rule4b_of_priorTie
    left right countTie rule4bDecisive

/-- Rule 4c is observed exactly after the Rule-4a, reference-count, and complete Rule-4b gates
tie. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_eq_rule4c_of_priorTies
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      left.rule4aKey right.rule4aKey = Ordering.eq)
    (countTie : compare left.referenceCountPriority right.referenceCountPriority =
      Ordering.eq)
    (rule4bTie : input.compareLocalizedRerootCompoundRule4bReadings
      left.readings right.readings = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right =
      input.compareLocalizedRerootCompoundRule4cReadings
        left.readings right.readings := by
  rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_afterRule4a_of_tie
    left right rule4aTie]
  exact input.compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_rule4c_of_priorTies
    left right countTie rule4bTie

/-- The compound comparator is `eq` exactly when all four source-ordered gates tie. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right = Ordering.eq ↔
      input.compareLocalizedRerootCumulativeRule45Keys
          left.rule4aKey right.rule4aKey = Ordering.eq ∧
        (compare left.referenceCountPriority right.referenceCountPriority =
            Ordering.eq ∧
          (input.compareLocalizedRerootCompoundRule4bReadings
              left.readings right.readings = Ordering.eq ∧
            input.compareLocalizedRerootCompoundRule4cReadings
              left.readings right.readings = Ordering.eq)) := by
  unfold compareLocalizedRerootCompoundRule4bcKeys
  simp [compareLex_eq_eq, Ordering.byKey]

/-- A strict Rule-4a decision wins even when the later reference count points the other way.
This is an order-theoretic consequence of the source rule order; it does not by itself assert
that a molecule realising the conflicting later count exists. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_rule4a_strict_overrides_later
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (rule4aStrict : input.compareLocalizedRerootCumulativeRule45Keys
      left.rule4aKey right.rule4aKey = Ordering.lt)
    (countDisagrees : compare left.referenceCountPriority right.referenceCountPriority =
      Ordering.gt) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right = Ordering.lt ∧
      compare left.referenceCountPriority right.referenceCountPriority = Ordering.gt := by
  refine ⟨?_, countDisagrees⟩
  rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne left right
    (by rw [rule4aStrict]; decide)]
  exact rule4aStrict

/-- The complete compound comparator is oriented and transitive.  Transitivity is the ordinary
lexicographic composition of the lawful unary Rule-4a key comparator and the lawful unary
reference-count/reading comparators; chemical correctness is not assumed. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedRerootCompoundRule4bcKeys
    compareLocalizedRerootCompoundRule4bReadings
    compareLocalizedRerootCompoundRule4cReadings
    compareLocalizedRerootRule4bcReadingsByRule4b
    compareLocalizedCumulativeRule45Priority
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
