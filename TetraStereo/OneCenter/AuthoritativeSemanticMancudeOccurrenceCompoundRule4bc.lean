import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule45Key

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical compound Rules 4b and 4c

This module applies the normative Rule-4b reference selection to the independently derived,
source-canonical ranked-label hierarchy.  It then constructs every required no-reference, R, and
S reading in the prescribed order.  Neither a Kekule realization nor an aromatic bond placement
is an input to any definition in this module.
-/

open CertifiedLocalizedCIPInput

/-- The nonempty sequence of Rule-4c alternatives induced by the Rule-4b references. -/
def aromaticCanonicalRule4bcReferenceAlternatives : List RS → List (Option RS)
  | [] => [none]
  | references => references.map some

/-- One source-canonical Rule-4b/4c reference reading. -/
structure AromaticCanonicalRerootRule4bcReading
    (source : AuthoritativeChemicalInput) where
  reference? : Option RS
  rule4bKey : source.AromaticCanonicalCumulativeRule45Key
  rule4cKey : source.AromaticCanonicalCumulativeRule45Key

/-- Build both cumulative stages for exactly one reference alternative. -/
noncomputable def buildAromaticCanonicalRerootRule4bcReading?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option RS → Option source.AromaticCanonicalRerootRule4bcReading
  | none => do
      let rule4bKey ← source.buildAromaticCanonicalCumulativeRule45Key?
        .rule4a target view fuel cursor
      let rule4cKey ← source.buildAromaticCanonicalCumulativeRule45Key?
        .rule4cNoReference target view fuel cursor
      some { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey }
  | some reference => do
      let rule4bKey ← source.buildAromaticCanonicalCumulativeRule45Key?
        (.rule4b reference) target view fuel cursor
      let rule4cKey ← source.buildAromaticCanonicalCumulativeRule45Key?
        (.rule4c reference) target view fuel cursor
      some
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }

/-- Pointwise construction in the normative alternative order. -/
noncomputable def buildAromaticCanonicalRerootRule4bcReadings?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    List (Option RS) → Option (List source.AromaticCanonicalRerootRule4bcReading)
  | [] => some []
  | reference :: references => do
      let reading ← source.buildAromaticCanonicalRerootRule4bcReading?
        target view fuel cursor reference
      let readings ← source.buildAromaticCanonicalRerootRule4bcReadings?
        target view fuel cursor references
      some (reading :: readings)

/-- Complete source-canonical compound Rules-4b/4c key. -/
structure AromaticCanonicalRerootCompoundRule4bcKey
    (source : AuthoritativeChemicalInput) where
  rule4aKey : source.AromaticCanonicalCumulativeRule45Key
  references : List RS
  referenceCountPriority : Nat
  readings : List source.AromaticCanonicalRerootRule4bcReading

/-- Select the Rule-4b references from the exact ranked-label hierarchy, then compile every
normative Rule-4b/4c reading. -/
noncomputable def buildAromaticCanonicalRerootCompoundRule4bcKey?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option source.AromaticCanonicalRerootCompoundRule4bcKey := do
  let rule4aKey ← source.buildAromaticCanonicalCumulativeRule45Key?
    .rule4a target view fuel cursor
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := aromaticCanonicalRule4bcReferenceAlternatives references
  let readings ← source.buildAromaticCanonicalRerootRule4bcReadings?
    target view fuel cursor alternatives
  some
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings }

/-! ## Independent compound derivations -/

inductive DeclarativeAromaticCanonicalRerootRule4bcReading
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option RS → source.AromaticCanonicalRerootRule4bcReading → Prop
  | noReference {rule4bKey rule4cKey}
      (rule4b : source.DeclarativeAromaticCanonicalCumulativeRule45Key
        .rule4a target view fuel cursor rule4bKey)
      (rule4c : source.DeclarativeAromaticCanonicalCumulativeRule45Key
        .rule4cNoReference target view fuel cursor rule4cKey) :
      DeclarativeAromaticCanonicalRerootRule4bcReading
        source target view fuel cursor none
          { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey }
  | reference {reference rule4bKey rule4cKey}
      (rule4b : source.DeclarativeAromaticCanonicalCumulativeRule45Key
        (.rule4b reference) target view fuel cursor rule4bKey)
      (rule4c : source.DeclarativeAromaticCanonicalCumulativeRule45Key
        (.rule4c reference) target view fuel cursor rule4cKey) :
      DeclarativeAromaticCanonicalRerootRule4bcReading
        source target view fuel cursor (some reference)
          { reference? := some reference, rule4bKey := rule4bKey, rule4cKey := rule4cKey }

inductive DeclarativeAromaticCanonicalRerootRule4bcReadings
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    List (Option RS) → List source.AromaticCanonicalRerootRule4bcReading → Prop
  | nil : DeclarativeAromaticCanonicalRerootRule4bcReadings
      source target view fuel cursor [] []
  | cons {reference references reading readings}
      (head : source.DeclarativeAromaticCanonicalRerootRule4bcReading
        target view fuel cursor reference reading)
      (tail : source.DeclarativeAromaticCanonicalRerootRule4bcReadings
        target view fuel cursor references readings) :
      DeclarativeAromaticCanonicalRerootRule4bcReadings
        source target view fuel cursor
          (reference :: references) (reading :: readings)

theorem buildAromaticCanonicalRerootRule4bcReading?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS) (reading : source.AromaticCanonicalRerootRule4bcReading)
    (computed : source.buildAromaticCanonicalRerootRule4bcReading?
      target view fuel cursor reference = some reading) :
    source.DeclarativeAromaticCanonicalRerootRule4bcReading
      target view fuel cursor reference reading := by
  cases reference with
  | none =>
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
              exact DeclarativeAromaticCanonicalRerootRule4bcReading.noReference
                (source.buildAromaticCanonicalCumulativeRule45Key?_sound
                  .rule4a target view fuel cursor rule4bKey rule4bComputed)
                (source.buildAromaticCanonicalCumulativeRule45Key?_sound
                  .rule4cNoReference target view fuel cursor rule4cKey rule4cComputed)
  | some reference =>
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
              exact DeclarativeAromaticCanonicalRerootRule4bcReading.reference
                (source.buildAromaticCanonicalCumulativeRule45Key?_sound
                  (.rule4b reference) target view fuel cursor rule4bKey rule4bComputed)
                (source.buildAromaticCanonicalCumulativeRule45Key?_sound
                  (.rule4c reference) target view fuel cursor rule4cKey rule4cComputed)

theorem buildAromaticCanonicalRerootRule4bcReadings?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ references readings,
      source.buildAromaticCanonicalRerootRule4bcReadings?
        target view fuel cursor references = some readings →
      source.DeclarativeAromaticCanonicalRerootRule4bcReadings
        target view fuel cursor references readings
  | [], readings, computed => by
      simp [buildAromaticCanonicalRerootRule4bcReadings?] at computed
      subst readings
      exact DeclarativeAromaticCanonicalRerootRule4bcReadings.nil
  | reference :: references, readings, computed => by
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
              exact DeclarativeAromaticCanonicalRerootRule4bcReadings.cons
                (source.buildAromaticCanonicalRerootRule4bcReading?_sound
                  target view fuel cursor reference reading headComputed)
                (source.buildAromaticCanonicalRerootRule4bcReadings?_sound
                  target view fuel cursor references tail tailComputed)

/-- Independent meaning of a complete compound Rules-4b/4c key. -/
def DeclarativeAromaticCanonicalRerootCompoundRule4bcKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey) : Prop :=
  source.DeclarativeAromaticCanonicalCumulativeRule45Key
      .rule4a target view fuel cursor key.rule4aKey ∧
    DeclarativeLocalizedRule4bReferenceSelection
      key.rule4aKey.rankedLabels key.references ∧
    key.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority key.references ∧
    source.DeclarativeAromaticCanonicalRerootRule4bcReadings
      target view fuel cursor
        (aromaticCanonicalRule4bcReferenceAlternatives key.references) key.readings

theorem buildAromaticCanonicalRerootCompoundRule4bcKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (computed : source.buildAromaticCanonicalRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    source.DeclarativeAromaticCanonicalRerootCompoundRule4bcKey
      target view fuel cursor key := by
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
            source.buildAromaticCanonicalCumulativeRule45Key?_sound
              .rule4a target view fuel cursor rule4aKey rule4aComputed,
            (localizedRule4bReferencesFromRankedLabels_eq_iff
              rule4aKey.rankedLabels references).mp rfl,
            rfl,
            source.buildAromaticCanonicalRerootRule4bcReadings?_sound
              target view fuel cursor alternatives readings readingsComputed⟩

/-! ## Lawful compound comparison -/

def compareAromaticCanonicalRerootRule4bcReadingsByRule4b
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalRerootRule4bcReading →
      source.AromaticCanonicalRerootRule4bcReading → Ordering :=
  Ordering.byKey (fun reading => reading.rule4bKey.descriptor)
    (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)

def compareAromaticCanonicalRerootCompoundRule4bReadings
    (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalRerootRule4bcReading →
      List source.AromaticCanonicalRerootRule4bcReading → Ordering :=
  List.compareLex source.compareAromaticCanonicalRerootRule4bcReadingsByRule4b

def compareAromaticCanonicalRerootCompoundRule4cReadings
    (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalRerootRule4bcReading →
      List source.AromaticCanonicalRerootRule4bcReading → Ordering :=
  List.compareLex
    (Ordering.byKey (fun reading => reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))

/-- Reference-count priority, then all Rule-4b readings, then all Rule-4c readings. -/
def compareAromaticCanonicalRerootCompoundRule4bcKeys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalRerootCompoundRule4bcKey →
      source.AromaticCanonicalRerootCompoundRule4bcKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.referenceCountPriority) compare)
    (compareLex
      (Ordering.byKey (fun key => key.readings)
        source.compareAromaticCanonicalRerootCompoundRule4bReadings)
      (Ordering.byKey (fun key => key.readings)
        source.compareAromaticCanonicalRerootCompoundRule4cReadings))

theorem compareAromaticCanonicalRerootCompoundRule4bcKeys_eq_referenceCount_of_ne
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (decisive : compare left.referenceCountPriority right.referenceCountPriority ≠
      Ordering.eq) :
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys left right =
      compare left.referenceCountPriority right.referenceCountPriority := by
  unfold compareAromaticCanonicalRerootCompoundRule4bcKeys
  generalize countComparison :
      compare left.referenceCountPriority right.referenceCountPriority = outcome at decisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

theorem compareAromaticCanonicalRerootCompoundRule4bcKeys_eq_rule4b_of_priorTie
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (countTie : compare left.referenceCountPriority right.referenceCountPriority =
      Ordering.eq)
    (rule4bDecisive : source.compareAromaticCanonicalRerootCompoundRule4bReadings
      left.readings right.readings ≠ Ordering.eq) :
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys left right =
      source.compareAromaticCanonicalRerootCompoundRule4bReadings
        left.readings right.readings := by
  unfold compareAromaticCanonicalRerootCompoundRule4bcKeys
  generalize rule4bComparison :
      source.compareAromaticCanonicalRerootCompoundRule4bReadings
        left.readings right.readings = outcome at rule4bDecisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

theorem compareAromaticCanonicalRerootCompoundRule4bcKeys_eq_rule4c_of_priorTies
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (countTie : compare left.referenceCountPriority right.referenceCountPriority =
      Ordering.eq)
    (rule4bTie : source.compareAromaticCanonicalRerootCompoundRule4bReadings
      left.readings right.readings = Ordering.eq) :
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys left right =
      source.compareAromaticCanonicalRerootCompoundRule4cReadings
        left.readings right.readings := by
  simp [compareAromaticCanonicalRerootCompoundRule4bcKeys, compareLex,
    Ordering.byKey, countTie, rule4bTie]

theorem compareAromaticCanonicalRerootCompoundRule4bcKeys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalRerootCompoundRule4bcKeys := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareAromaticCanonicalRerootCompoundRule4bcKeys
    compareAromaticCanonicalRerootCompoundRule4bReadings
    compareAromaticCanonicalRerootCompoundRule4cReadings
    compareAromaticCanonicalRerootRule4bcReadingsByRule4b
    compareLocalizedCumulativeRule45Priority
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-! ## Reflection invariance through Rule 4c -/

private theorem list_compareLex_byKey_eq_of_map_eq
    {alpha beta : Type*} (project : alpha → beta) (compare : beta → beta → Ordering)
    (refl : ∀ value, compare value value = Ordering.eq) :
    ∀ left right : List alpha,
      left.map project = right.map project →
      List.compareLex (Ordering.byKey project compare) left right = Ordering.eq
  | [], [], _ => rfl
  | leftHead :: leftTail, rightHead :: rightTail, equal => by
      simp only [List.map_cons, List.cons.injEq] at equal
      simp [List.compareLex_cons_cons, Ordering.byKey, equal.1,
        refl, list_compareLex_byKey_eq_of_map_eq project compare refl
          leftTail rightTail equal.2]

private theorem compare_cumulative_descriptor_self
    (descriptor : List (List (OfficialSparseEntry (List Nat)))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      descriptor descriptor = Ordering.eq := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  letI : Std.TransCmp compareLocalizedCumulativeRule45Priority := by
    unfold compareLocalizedCumulativeRule45Priority
    infer_instance
  letI : Std.TransCmp
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority) := by
    unfold OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  exact Std.ReflCmp.compare_self

/-- Pointwise reflection relation for one authoritative Rule-4b/4c reading.  Selected uppercase
references are mirrored, while comparator-visible cumulative descriptors agree. -/
def AromaticCanonicalRule4bcReadingUppercaseReflection
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootRule4bcReading) : Prop :=
  right.reference? = left.reference?.map RS.swap ∧
    right.rule4bKey.descriptor = left.rule4bKey.descriptor ∧
    right.rule4cKey.descriptor = left.rule4cKey.descriptor

private theorem rule4b_descriptor_maps_eq_of_reflectedReadings
    (source : AuthoritativeChemicalInput) :
    ∀ {left right : List source.AromaticCanonicalRerootRule4bcReading},
      List.Forall₂ source.AromaticCanonicalRule4bcReadingUppercaseReflection left right →
      left.map (fun reading => reading.rule4bKey.descriptor) =
        right.map (fun reading => reading.rule4bKey.descriptor)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head tail => by
      simp [head.2.1, rule4b_descriptor_maps_eq_of_reflectedReadings source tail]

private theorem rule4c_descriptor_maps_eq_of_reflectedReadings
    (source : AuthoritativeChemicalInput) :
    ∀ {left right : List source.AromaticCanonicalRerootRule4bcReading},
      List.Forall₂ source.AromaticCanonicalRule4bcReadingUppercaseReflection left right →
      left.map (fun reading => reading.rule4cKey.descriptor) =
        right.map (fun reading => reading.rule4cKey.descriptor)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head tail => by
      simp [head.2.2, rule4c_descriptor_maps_eq_of_reflectedReadings source tail]

/-- Pointwise reflected readings tie under both pre-Rule-5 descriptor comparators. -/
theorem compareAromaticCanonicalRerootCompoundRule4bcReadings_eq_of_reflection
    (source : AuthoritativeChemicalInput)
    (left right : List source.AromaticCanonicalRerootRule4bcReading)
    (reflected : List.Forall₂
      source.AromaticCanonicalRule4bcReadingUppercaseReflection left right) :
    source.compareAromaticCanonicalRerootCompoundRule4bReadings left right = .eq ∧
      source.compareAromaticCanonicalRerootCompoundRule4cReadings left right = .eq := by
  constructor
  · unfold compareAromaticCanonicalRerootCompoundRule4bReadings
      compareAromaticCanonicalRerootRule4bcReadingsByRule4b
    exact list_compareLex_byKey_eq_of_map_eq
      (fun reading : source.AromaticCanonicalRerootRule4bcReading =>
        reading.rule4bKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
      compare_cumulative_descriptor_self left right
      (rule4b_descriptor_maps_eq_of_reflectedReadings source reflected)
  · unfold compareAromaticCanonicalRerootCompoundRule4cReadings
    exact list_compareLex_byKey_eq_of_map_eq
      (fun reading : source.AromaticCanonicalRerootRule4bcReading =>
        reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
      compare_cumulative_descriptor_self left right
      (rule4c_descriptor_maps_eq_of_reflectedReadings source reflected)

/-- The independently selected Rule-4b reference-count gate ties for reflected ranked labels. -/
theorem compareAromaticCanonicalRule4bReferenceCounts_eq_of_reflectedRankedLabels
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (leftExact : left.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels left.rule4aKey.rankedLabels))
    (rightExact : right.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels right.rule4aKey.rankedLabels))
    (rankedReflected : right.rule4aKey.rankedLabels =
      reflectUppercaseRankedLabels left.rule4aKey.rankedLabels) :
    compare left.referenceCountPriority right.referenceCountPriority = .eq := by
  rw [leftExact, rightExact, rankedReflected,
    constitutionalRule4bReferenceCountPriority_reflectUppercase]
  exact Std.ReflCmp.compare_self

/-- Reflected selector inputs and pointwise reflected readings force the complete compound
Rules-4b/4c prior key to tie. -/
theorem compareAromaticCanonicalRerootCompoundRule4bcKeys_eq_of_reflection
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (leftExact : left.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels left.rule4aKey.rankedLabels))
    (rightExact : right.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels right.rule4aKey.rankedLabels))
    (rankedReflected : right.rule4aKey.rankedLabels =
      reflectUppercaseRankedLabels left.rule4aKey.rankedLabels)
    (readingsReflected : List.Forall₂
      source.AromaticCanonicalRule4bcReadingUppercaseReflection
        left.readings right.readings) :
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys left right = .eq := by
  have countTie :=
    source.compareAromaticCanonicalRule4bReferenceCounts_eq_of_reflectedRankedLabels
      left right leftExact rightExact rankedReflected
  obtain ⟨rule4bTie, rule4cTie⟩ :=
    source.compareAromaticCanonicalRerootCompoundRule4bcReadings_eq_of_reflection
      left.readings right.readings readingsReflected
  rw [source.compareAromaticCanonicalRerootCompoundRule4bcKeys_eq_rule4c_of_priorTies
    left right countTie rule4bTie]
  exact rule4cTie

/-- The whole compound Rules-4b/4c construction is defined on the semantic source itself. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKey_source_fixed
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.buildAromaticCanonicalRerootCompoundRule4bcKey? target view fuel cursor =
      source.buildAromaticCanonicalRerootCompoundRule4bcKey? target view fuel cursor :=
  rfl

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
