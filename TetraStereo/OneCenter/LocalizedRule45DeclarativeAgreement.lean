import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableUnique

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Declarative agreement for the compound Rules-4a--5 comparison

Two independently derived compound Rules-4a--5 keys at the same reroot cursor need not be identical
records.  `declarative_cumulative_key_observable_unique` already shows that their cumulative stage
descriptors agree even when their hidden `labels`/`rankedLabels` payloads differ.  This module
carries that result up to the actual compound comparators.

The stages that the compound comparator reads are isolated first:

* the comparison-visible projection of the complete Rule-4a key: its addressed Rule-1a, Rule-1b and
  Rule-2 projections together with its cumulative Rule-4a descriptor,
* one Rule-4b/4c alternative at a fixed reference (its Rule-4b and Rule-4c descriptor readings),
* both common Rule-5 readings at a fixed prior reference,
* the numeric projection of a complete compound Rules-4b/4c key: the P-92.5.2.1(c)(i) reference
  count plus the Rule-4b/Rule-4c reading descriptors in their normative alternative order.

`compareLocalizedRerootCompoundRule4bcKeys` observes the complete comparison-visible Rule-4a key
*before* the reference-count gate, as P-92 Rule 4a requires, and then falls through to the
P-92.5.2.1(c)(i) reference count and the Rule-4b/Rule-4c reading descriptors.  It never inspects
any exact label payload.  The Rule-4a key matters in the tail only through the selected reference
list, which determines the reference-count priority and the alternative readings.  Equal reference
lists remain the single lower-layer premise for that tail:

`LocalizedRerootCompoundRule45ReferenceListAgreement`.

It is *not* implied by observable equality of the two Rule-4a derivations: the reference selection
reads the hierarchy-rank-addressed labels.  The separate `LocalizedRule4bReferenceAgreement`
development is to supply it.  Until then it is an explicit hypothesis here; nothing below assumes
the reference lists agree, and no exact-label or full-key equality is claimed.

The main results are:

* `compareLocalizedRerootCompoundRule4bcKeys_eq_compareObservable`, which identifies the actual
  compound Rules-4b/4c comparator with the observable comparator: Rule 4a first, then the reference
  count, then the Rule-4b and Rule-4c readings,
* `compareLocalizedRerootCompoundRule4bcKeys_congr_left/right`,
* `compareLocalizedRerootCompoundRule4bcKeys_congr_left/right_of_declarative`, which transport the
  Rule-4a observable and the tail together through the actual comparator,
* `compareLocalizedRerootCompoundRule5Readings_congr_left/right`,
* `compareLocalizedRerootCompoundThroughRule5_congr_left/right` and its bundled two-sided form,
  which preserve the complete comparison record (ordering, decisive-rule field of the occurrence
  wrapper, and pseudoasymmetric flag), and
* builder corollaries in which compiler soundness supplies one side.
-/

/-! ## Cumulative descriptor agreement at one stage

This is the only fact imported from the cumulative observable uniqueness development.  It is
restated as a descriptor projection so that the compound arguments below do not have to mention
`LocalizedCumulativeRule45Observable`. -/

/-- Any two declarative derivations of the same cumulative Rules-4a--5 stage at the same cursor have
the same addressed descriptor projection, whatever their hidden label payloads are. -/
theorem declarative_cumulative_key_descriptor_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor right) :
    left.descriptor = right.descriptor :=
  congrArg LocalizedCumulativeRule45Observable.descriptor
    (input.declarative_cumulative_key_observable_unique
      stage target view fuel cursor left right leftDerived rightDerived)

/-! ## One Rule-4b/4c alternative at a fixed reference -/

/-- Two independent derivations of the same reference alternative read the same Rule-4b descriptor,
the same Rule-4c descriptor, and carry the same reference.  The exact labels are not claimed. -/
theorem declarative_rule4bc_reading_observable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS)
    {left right : input.LocalizedRerootRule4bcReading}
    (leftDerived : input.DeclarativeLocalizedRerootRule4bcReading
      target view fuel cursor reference left)
    (rightDerived : input.DeclarativeLocalizedRerootRule4bcReading
      target view fuel cursor reference right) :
    left.rule4bKey.descriptor = right.rule4bKey.descriptor ∧
      left.rule4cKey.descriptor = right.rule4cKey.descriptor ∧
        left.reference? = right.reference? := by
  cases reference with
  | none =>
      cases leftDerived with
      | noReference leftRule4b leftRule4c =>
          cases rightDerived with
          | noReference rightRule4b rightRule4c =>
              exact
                ⟨input.declarative_cumulative_key_descriptor_eq
                    _ target view cursor leftRule4b rightRule4b,
                  input.declarative_cumulative_key_descriptor_eq
                    _ target view cursor leftRule4c rightRule4c,
                  rfl⟩
  | some chosen =>
      cases leftDerived with
      | reference leftRule4b leftRule4c =>
          cases rightDerived with
          | reference rightRule4b rightRule4c =>
              exact
                ⟨input.declarative_cumulative_key_descriptor_eq
                    _ target view cursor leftRule4b rightRule4b,
                  input.declarative_cumulative_key_descriptor_eq
                    _ target view cursor leftRule4c rightRule4c,
                  rfl⟩

/-- The pointwise Rule-4b comparison used inside the compound Rule-4b reading order depends only on
the Rule-4b descriptor. -/
theorem compareLocalizedRerootRule4bcReadingsByRule4b_congr_left
    (input : CertifiedLocalizedCIPInput)
    (left right other : input.LocalizedRerootRule4bcReading)
    (descriptors : left.rule4bKey.descriptor = right.rule4bKey.descriptor) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b left other =
      input.compareLocalizedRerootRule4bcReadingsByRule4b right other := by
  simp only [compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey, descriptors]

theorem compareLocalizedRerootRule4bcReadingsByRule4b_congr_right
    (input : CertifiedLocalizedCIPInput)
    (left right other : input.LocalizedRerootRule4bcReading)
    (descriptors : left.rule4bKey.descriptor = right.rule4bKey.descriptor) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b other left =
      input.compareLocalizedRerootRule4bcReadingsByRule4b other right := by
  simp only [compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey, descriptors]

/-! ## A canonical Rule-4b/4c alternative list -/

/-- Two declarative Rule-4b/4c alternative lists for the same normative alternative sequence
`alternatives` have the same Rule-4b descriptor sequence, the same Rule-4c descriptor sequence, and
the same reference sequence.  In particular they can be paired position by position. -/
theorem declarative_rule4bc_readings_observable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (alternatives : List (Option RS))
      (readingsLeft readingsRight : List input.LocalizedRerootRule4bcReading),
      input.DeclarativeLocalizedRerootRule4bcReadings
          target view fuel cursor alternatives readingsLeft →
        input.DeclarativeLocalizedRerootRule4bcReadings
            target view fuel cursor alternatives readingsRight →
          readingsLeft.map (fun reading => reading.rule4bKey.descriptor) =
              readingsRight.map (fun reading => reading.rule4bKey.descriptor) ∧
            readingsLeft.map (fun reading => reading.rule4cKey.descriptor) =
                readingsRight.map (fun reading => reading.rule4cKey.descriptor) ∧
              readingsLeft.map (fun reading => reading.reference?) =
                  readingsRight.map (fun reading => reading.reference?)
  | [], _, _, leftDerived, rightDerived => by
      cases leftDerived with
      | nil =>
          cases rightDerived with
          | nil => exact ⟨rfl, rfl, rfl⟩
  | reference :: references, _, _, leftDerived, rightDerived => by
      cases leftDerived with
      | cons head tail =>
          rename_i readingLeft readingsLeft
          cases rightDerived with
          | cons rightHead rightTail =>
              rename_i readingRight readingsRight
              obtain ⟨headRule4b, headRule4c, headReference⟩ :=
                input.declarative_rule4bc_reading_observable_eq
                  target view cursor reference head rightHead
              obtain ⟨tailRule4b, tailRule4c, tailReference⟩ :=
                declarative_rule4bc_readings_observable_eq input target view cursor
                  references readingsLeft readingsRight tail rightTail
              exact
                ⟨by rw [List.map_cons, List.map_cons, headRule4b, tailRule4b],
                  by rw [List.map_cons, List.map_cons, headRule4c, tailRule4c],
                  by rw [List.map_cons, List.map_cons, headReference, tailReference]⟩

/-! ## The observable projection of a compound Rules-4b/4c key

`compareLocalizedRerootCompoundRule4bcKeys` observes the comparison-visible Rule-4a key first,
exactly as `compareLocalizedRerootCumulativeRule45Keys` reads it: addressed Rule 1a, then Rule 1b,
then Rule 2, then the cumulative Rule-4a descriptor.  Only after that does it read the reference
count and the two reading descriptor sequences.  The fields `rule4aKey`, `references`, and every
exact label payload are absent from the structure; the Rule-4a key enters through the four recorded
projections, and the reference list enters through the count and the readings recorded here. -/

/-- Comparison-visible projection of a compound Rules-4b/4c key. -/
structure LocalizedRerootCompoundRule4bcComparisonObservable where
  /-- Addressed Rule-1a projection of the Rule-4a key. -/
  rule4aRule1a : List (List (OfficialSparseEntry ℕ))
  /-- Addressed Rule-1b projection of the Rule-4a key. -/
  rule4aRule1b : List (List (OfficialSparseEntry ℕ))
  /-- Addressed Rule-2 projection of the Rule-4a key. -/
  rule4aRule2 : List (List (OfficialSparseEntry ℕ))
  /-- Addressed cumulative Rule-4a descriptor projection. -/
  rule4aDescriptor : List (List (OfficialSparseEntry (List Nat)))
  /-- P-92.5.2.1(c)(i) reference-count priority. -/
  referenceCountPriority : Nat
  /-- Rule-4b descriptor readings in normative alternative order. -/
  rule4bDescriptors : List (List (List (OfficialSparseEntry (List Nat))))
  /-- Rule-4c descriptor readings in normative alternative order. -/
  rule4cDescriptors : List (List (List (OfficialSparseEntry (List Nat))))

/-- Forget a compound Rules-4b/4c key down to the projection the comparator reads. -/
def localizedRerootCompoundRule4bcComparisonObservable
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCompoundRule4bcKey) :
    LocalizedRerootCompoundRule4bcComparisonObservable where
  rule4aRule1a := key.rule4aKey.constitutional.rule1a
  rule4aRule1b := key.rule4aKey.constitutional.rule1b
  rule4aRule2 := key.rule4aKey.constitutional.rule2
  rule4aDescriptor := key.rule4aKey.descriptor
  referenceCountPriority := key.referenceCountPriority
  rule4bDescriptors := key.readings.map fun reading => reading.rule4bKey.descriptor
  rule4cDescriptors := key.readings.map fun reading => reading.rule4cKey.descriptor

/-- The projection comparator: the complete Rule-4a observable first (Rule 1a, Rule 1b, Rule 2,
then the cumulative Rule-4a descriptor), then the reference count, then the complete Rule-4b
readings, then the complete Rule-4c readings, exactly as the compound key comparator nests them. -/
def compareLocalizedRerootCompoundRule4bcComparisonObservable :
    LocalizedRerootCompoundRule4bcComparisonObservable →
      LocalizedRerootCompoundRule4bcComparisonObservable → Ordering :=
  compareLex
    (compareLex
      (compareLex
        (Ordering.byKey
          LocalizedRerootCompoundRule4bcComparisonObservable.rule4aRule1a
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
        (compareLex
          (Ordering.byKey
            LocalizedRerootCompoundRule4bcComparisonObservable.rule4aRule1b
            (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
          (Ordering.byKey
            LocalizedRerootCompoundRule4bcComparisonObservable.rule4aRule2
            (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))))
      (Ordering.byKey
        LocalizedRerootCompoundRule4bcComparisonObservable.rule4aDescriptor
        (OfficialRuleMajorKey.compareSparseLayers
          compareLocalizedCumulativeRule45Priority)))
    (compareLex
      (Ordering.byKey
        LocalizedRerootCompoundRule4bcComparisonObservable.referenceCountPriority compare)
      (compareLex
        (Ordering.byKey
          LocalizedRerootCompoundRule4bcComparisonObservable.rule4bDescriptors
          (List.compareLex
            (OfficialRuleMajorKey.compareSparseLayers
              compareLocalizedCumulativeRule45Priority)))
        (Ordering.byKey
          LocalizedRerootCompoundRule4bcComparisonObservable.rule4cDescriptors
          (List.compareLex
            (OfficialRuleMajorKey.compareSparseLayers
              compareLocalizedCumulativeRule45Priority)))))

/-- Comparing projected descriptor lists through `Ordering.byKey` is comparing the mapped lists. -/
private theorem listCompareLex_byKey_map {α β : Type*} (project : α → β)
    (compare : β → β → Ordering) :
    ∀ left right : List α,
      List.compareLex (Ordering.byKey project compare) left right =
        List.compareLex compare (left.map project) (right.map project) := by
  intro left
  induction left with
  | nil =>
      intro right
      cases right <;> rfl
  | cons leftHead leftTail inductionHypothesis =>
      intro right
      cases right with
      | nil => rfl
      | cons rightHead rightTail =>
          simp only [List.compareLex_cons_cons, List.map_cons, inductionHypothesis,
            Ordering.byKey]

/-- The same comparison with the key projection already beta-reduced. -/
private theorem listCompareLex_map_eq_compareLex {α β : Type*} (project : α → β)
    (compare : β → β → Ordering) :
    ∀ left right : List α,
      List.compareLex (fun a b => compare (project a) (project b)) left right =
        List.compareLex compare (left.map project) (right.map project) := by
  intro left
  induction left with
  | nil =>
      intro right
      cases right <;> rfl
  | cons leftHead leftTail inductionHypothesis =>
      intro right
      cases right with
      | nil => rfl
      | cons rightHead rightTail =>
          simp only [List.compareLex_cons_cons, List.map_cons, inductionHypothesis]

/-- The actual compound Rules-4b/4c comparator is the projection comparator.  It reads the
comparison-visible Rule-4a key first, then the reference count, then the two reading descriptor
sequences.  Nothing else in the key, in particular no exact label payload, is inspected. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_eq_compareObservable
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right =
      compareLocalizedRerootCompoundRule4bcComparisonObservable
        (input.localizedRerootCompoundRule4bcComparisonObservable left)
        (input.localizedRerootCompoundRule4bcComparisonObservable right) := by
  unfold compareLocalizedRerootCompoundRule4bcKeys
    compareLocalizedRerootCompoundRule4bcComparisonObservable
    localizedRerootCompoundRule4bcComparisonObservable
    compareLocalizedRerootCompoundRule4bReadings
    compareLocalizedRerootCompoundRule4cReadings
    compareLocalizedRerootRule4bcReadingsByRule4b
    compareLex Ordering.byKey
  dsimp only
  rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable
    left.rule4aKey right.rule4aKey]
  unfold compareLocalizedCumulativeRule45Observable
    localizedRerootCumulativeRule45Observable
    compareLex Ordering.byKey
  dsimp only
  simp only [listCompareLex_map_eq_compareLex]

/-- Equal projections make two compound Rules-4b/4c keys interchangeable on the left of the actual
comparator. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_congr_left
    (input : CertifiedLocalizedCIPInput)
    (left right other : input.LocalizedRerootCompoundRule4bcKey)
    (observable : input.localizedRerootCompoundRule4bcComparisonObservable left =
      input.localizedRerootCompoundRule4bcComparisonObservable right) :
    input.compareLocalizedRerootCompoundRule4bcKeys left other =
      input.compareLocalizedRerootCompoundRule4bcKeys right other := by
  rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_compareObservable left other,
    input.compareLocalizedRerootCompoundRule4bcKeys_eq_compareObservable right other, observable]

/-- Equal projections make two compound Rules-4b/4c keys interchangeable on the right of the actual
comparator. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_congr_right
    (input : CertifiedLocalizedCIPInput)
    (left right other : input.LocalizedRerootCompoundRule4bcKey)
    (observable : input.localizedRerootCompoundRule4bcComparisonObservable left =
      input.localizedRerootCompoundRule4bcComparisonObservable right) :
    input.compareLocalizedRerootCompoundRule4bcKeys other left =
      input.compareLocalizedRerootCompoundRule4bcKeys other right := by
  rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_compareObservable other left,
    input.compareLocalizedRerootCompoundRule4bcKeys_eq_compareObservable other right, observable]

/-! ## From declarative keys to projection agreement -/

/-- The reference-count priority and the reading fields read by the compound Rules-4b/4c comparator
agree for two declarative keys at the same cursor once their selected reference lists agree.  The
reference-list premise is the explicit lower-layer obligation.  The Rule-4a projection is not part
of this statement; it is supplied independently by
`declarative_compoundRule4bc_comparisonObservable_eq`. -/
theorem declarative_compoundRule4bc_observable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right)
    (referencesAgree : left.references = right.references) :
    left.referenceCountPriority = right.referenceCountPriority ∧
      left.readings.map (fun reading => reading.rule4bKey.descriptor) =
          right.readings.map (fun reading => reading.rule4bKey.descriptor) ∧
        left.readings.map (fun reading => reading.rule4cKey.descriptor) =
            right.readings.map (fun reading => reading.rule4cKey.descriptor) ∧
          left.readings.map (fun reading => reading.reference?) =
              right.readings.map (fun reading => reading.reference?) := by
  have alternativesAgree : localizedRule4bcReferenceAlternatives left.references =
      localizedRule4bcReferenceAlternatives right.references := by
    rw [referencesAgree]
  have rightReadings : input.DeclarativeLocalizedRerootRule4bcReadings
      target view fuel cursor
      (localizedRule4bcReferenceAlternatives left.references) right.readings := by
    have transported := rightDerived.2.2.2
    rw [← alternativesAgree] at transported
    exact transported
  obtain ⟨rule4bMaps, rule4cMaps, referenceMaps⟩ :=
    input.declarative_rule4bc_readings_observable_eq target view cursor
      (localizedRule4bcReferenceAlternatives left.references)
      left.readings right.readings leftDerived.2.2.2 rightReadings
  have countAgree : left.referenceCountPriority = right.referenceCountPriority := by
    rw [leftDerived.2.2.1, rightDerived.2.2.1, referencesAgree]
  exact ⟨countAgree, rule4bMaps, rule4cMaps, referenceMaps⟩

/-- Two declarative compound Rules-4b/4c keys at the same cursor have equal comparison projections
when their selected reference lists agree.  The Rule-4a component of the projection is derived from
`declarative_cumulative_key_observable_unique` at stage `.rule4a`, so the actual compound comparator
sees exactly the same Rule-4a key; no Rule-4a equality is assumed. -/
theorem declarative_compoundRule4bc_comparisonObservable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right)
    (referencesAgree : left.references = right.references) :
    input.localizedRerootCompoundRule4bcComparisonObservable left =
      input.localizedRerootCompoundRule4bcComparisonObservable right := by
  have rule4aObservable :=
    input.declarative_cumulative_key_observable_unique
      .rule4a target view fuel cursor left.rule4aKey right.rule4aKey
      leftDerived.1 rightDerived.1
  have rule1aAgree : left.rule4aKey.constitutional.rule1a =
      right.rule4aKey.constitutional.rule1a := by
    have observed := congrArg LocalizedCumulativeRule45Observable.rule1a rule4aObservable
    simpa only [localizedRerootCumulativeRule45Observable_rule1a] using observed
  have rule1bAgree : left.rule4aKey.constitutional.rule1b =
      right.rule4aKey.constitutional.rule1b := by
    have observed := congrArg LocalizedCumulativeRule45Observable.rule1b rule4aObservable
    simpa only [localizedRerootCumulativeRule45Observable_rule1b] using observed
  have rule2Agree : left.rule4aKey.constitutional.rule2 =
      right.rule4aKey.constitutional.rule2 := by
    have observed := congrArg LocalizedCumulativeRule45Observable.rule2 rule4aObservable
    simpa only [localizedRerootCumulativeRule45Observable_rule2] using observed
  have descriptorAgree : left.rule4aKey.descriptor = right.rule4aKey.descriptor := by
    have observed := congrArg LocalizedCumulativeRule45Observable.descriptor rule4aObservable
    simpa only [localizedRerootCumulativeRule45Observable_descriptor] using observed
  obtain ⟨countAgree, rule4bMaps, rule4cMaps, _⟩ :=
    input.declarative_compoundRule4bc_observable_eq target view cursor left right
      leftDerived rightDerived referencesAgree
  unfold localizedRerootCompoundRule4bcComparisonObservable
  rw [rule1aAgree, rule1bAgree, rule2Agree, descriptorAgree,
    countAgree, rule4bMaps, rule4cMaps]

/-- Declarative compound Rules-4b/4c keys at the same cursor are interchangeable on the left of the
actual compound comparator.  Because the projection now contains the Rule-4a observable, this
transport covers the repaired Rule-4a precedence gate as well as the reference-count and reading
gates. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_congr_left_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right)
    (referencesAgree : left.references = right.references) :
    input.compareLocalizedRerootCompoundRule4bcKeys left other =
      input.compareLocalizedRerootCompoundRule4bcKeys right other :=
  input.compareLocalizedRerootCompoundRule4bcKeys_congr_left left right other
    (input.declarative_compoundRule4bc_comparisonObservable_eq target view cursor
      left right leftDerived rightDerived referencesAgree)

/-- Declarative compound Rules-4b/4c keys at the same cursor are interchangeable on the right of
the actual compound comparator. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_congr_right_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right)
    (referencesAgree : left.references = right.references) :
    input.compareLocalizedRerootCompoundRule4bcKeys other left =
      input.compareLocalizedRerootCompoundRule4bcKeys other right :=
  input.compareLocalizedRerootCompoundRule4bcKeys_congr_right left right other
    (input.declarative_compoundRule4bc_comparisonObservable_eq target view cursor
      left right leftDerived rightDerived referencesAgree)

/-! ## One Rule-5 reading at a fixed prior -/

/-- Two independent derivations of the same successful Rule-5 reading read the same common-R and
common-S descriptors.  Both common readings are taken at the same prior reference. -/
theorem declarative_rule5_reading_descriptor_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    {left right : input.LocalizedRerootRule5Reading}
    (leftDerived : input.DeclarativeLocalizedRerootRule5Reading
      target view fuel cursor prior left)
    (rightDerived : input.DeclarativeLocalizedRerootRule5Reading
      target view fuel cursor prior right) :
    left.commonR.descriptor = right.commonR.descriptor ∧
      left.commonS.descriptor = right.commonS.descriptor :=
  ⟨input.declarative_cumulative_key_descriptor_eq
      _ target view cursor leftDerived.2.1 rightDerived.2.1,
    input.declarative_cumulative_key_descriptor_eq
      _ target view cursor leftDerived.2.2 rightDerived.2.2⟩

/-- Two declarative Rule-5 reading lists whose priors have the same reference sequence have equal
common-R and common-S descriptor sequences.  This is the stage-reading agreement used by
`compareLocalizedRerootCompoundRule5Readings`. -/
theorem declarative_rule5_readings_descriptor_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (priorsLeft priorsRight : List input.LocalizedRerootRule4bcReading)
      (readingsLeft readingsRight : List input.LocalizedRerootRule5Reading),
      priorsLeft.map (fun reading => reading.reference?) =
          priorsRight.map (fun reading => reading.reference?) →
        input.DeclarativeLocalizedRerootRule5Readings
            target view fuel cursor priorsLeft readingsLeft →
          input.DeclarativeLocalizedRerootRule5Readings
              target view fuel cursor priorsRight readingsRight →
            readingsLeft.map (fun reading => reading.commonR.descriptor) =
                readingsRight.map (fun reading => reading.commonR.descriptor) ∧
              readingsLeft.map (fun reading => reading.commonS.descriptor) =
                  readingsRight.map (fun reading => reading.commonS.descriptor)
  | [], [], _, _, _, leftDerived, rightDerived => by
      cases leftDerived with
      | nil =>
          cases rightDerived with
          | nil => exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, references, leftDerived, _ => by
      cases leftDerived with
      | nil => simp at references
  | _ :: _, [], _, _, references, _, _ => by
      simp at references
  | priorLeft :: priorsLeft, priorRight :: priorsRight, _, _, references,
      leftDerived, rightDerived => by
      cases leftDerived with
      | cons head tail =>
          rename_i readingLeft readingsLeft
          cases rightDerived with
          | cons rightHead rightTail =>
              rename_i readingRight readingsRight
              simp only [List.map_cons, List.cons.injEq] at references
              obtain ⟨headReference, tailReferences⟩ := references
              have rightCommonR :
                  input.DeclarativeLocalizedRerootCumulativeRule45Key
                    (localizedRule5StageFor priorLeft.reference? .R)
                    target view fuel cursor readingRight.commonR := by
                have transported := rightHead.2.1
                rw [← headReference] at transported
                exact transported
              have rightCommonS :
                  input.DeclarativeLocalizedRerootCumulativeRule45Key
                    (localizedRule5StageFor priorLeft.reference? .S)
                    target view fuel cursor readingRight.commonS := by
                have transported := rightHead.2.2
                rw [← headReference] at transported
                exact transported
              have headCommonR :=
                input.declarative_cumulative_key_descriptor_eq
                  _ target view cursor head.2.1 rightCommonR
              have headCommonS :=
                input.declarative_cumulative_key_descriptor_eq
                  _ target view cursor head.2.2 rightCommonS
              obtain ⟨tailCommonR, tailCommonS⟩ :=
                declarative_rule5_readings_descriptor_eq input target view cursor
                  priorsLeft priorsRight readingsLeft readingsRight
                  tailReferences tail rightTail
              exact
                ⟨by rw [List.map_cons, List.map_cons, headCommonR, tailCommonR],
                  by rw [List.map_cons, List.map_cons, headCommonS, tailCommonS]⟩

/-- The actual common-reference Rule-5 reading comparator is the descriptor-list comparator. -/
theorem compareLocalizedRerootCompoundRule5Readings_eq_compareMaps
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    (left right : List input.LocalizedRerootRule5Reading) :
    input.compareLocalizedRerootCompoundRule5Readings commonReference left right =
      List.compareLex
        (OfficialRuleMajorKey.compareSparseLayers
          compareLocalizedCumulativeRule45Priority)
        (left.map fun reading =>
          input.localizedRerootRule5Descriptor commonReference reading)
        (right.map fun reading =>
          input.localizedRerootRule5Descriptor commonReference reading) := by
  unfold compareLocalizedRerootCompoundRule5Readings
  exact listCompareLex_byKey_map _ _ _ _

/-- Equal common-reference descriptor sequences make Rule-5 reading lists interchangeable on the
left of `compareLocalizedRerootCompoundRule5Readings`. -/
theorem compareLocalizedRerootCompoundRule5Readings_congr_left
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    (left right other : List input.LocalizedRerootRule5Reading)
    (descriptors : left.map (fun reading =>
        input.localizedRerootRule5Descriptor commonReference reading) =
      right.map (fun reading =>
        input.localizedRerootRule5Descriptor commonReference reading)) :
    input.compareLocalizedRerootCompoundRule5Readings commonReference left other =
      input.compareLocalizedRerootCompoundRule5Readings commonReference right other := by
  rw [input.compareLocalizedRerootCompoundRule5Readings_eq_compareMaps,
    input.compareLocalizedRerootCompoundRule5Readings_eq_compareMaps, descriptors]

/-- Equal common-reference descriptor sequences make Rule-5 reading lists interchangeable on the
right of `compareLocalizedRerootCompoundRule5Readings`. -/
theorem compareLocalizedRerootCompoundRule5Readings_congr_right
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    (left right other : List input.LocalizedRerootRule5Reading)
    (descriptors : left.map (fun reading =>
        input.localizedRerootRule5Descriptor commonReference reading) =
      right.map (fun reading =>
        input.localizedRerootRule5Descriptor commonReference reading)) :
    input.compareLocalizedRerootCompoundRule5Readings commonReference other left =
      input.compareLocalizedRerootCompoundRule5Readings commonReference other right := by
  rw [input.compareLocalizedRerootCompoundRule5Readings_eq_compareMaps,
    input.compareLocalizedRerootCompoundRule5Readings_eq_compareMaps, descriptors]

/-! ## The complete compound Rules-4a--5 comparison

The through-Rule-5 record is a total function of the prior Rules-4b/4c comparison and the two
common-reference Rule-5 reading comparisons.  Transporting those three components transports the
whole record, including the `±2` pseudoasymmetric flag. -/

/-- The through-Rule-5 comparison record is determined by its three read comparisons. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_of_components
    (input : CertifiedLocalizedCIPInput)
    {left right otherLeft otherRight : input.LocalizedRerootCompoundRule45Key}
    (priorComparison :
      input.compareLocalizedRerootCompoundRule4bcKeys left.prior otherLeft.prior =
        input.compareLocalizedRerootCompoundRule4bcKeys right.prior otherRight.prior)
    (commonRComparison :
      input.compareLocalizedRerootCompoundRule5Readings
          .R left.rule5Readings otherLeft.rule5Readings =
        input.compareLocalizedRerootCompoundRule5Readings
          .R right.rule5Readings otherRight.rule5Readings)
    (commonSComparison :
      input.compareLocalizedRerootCompoundRule5Readings
          .S left.rule5Readings otherLeft.rule5Readings =
        input.compareLocalizedRerootCompoundRule5Readings
          .S right.rule5Readings otherRight.rule5Readings) :
    input.compareLocalizedRerootCompoundThroughRule5 left otherLeft =
      input.compareLocalizedRerootCompoundThroughRule5 right otherRight := by
  unfold compareLocalizedRerootCompoundThroughRule5
  dsimp only
  rw [priorComparison, commonRComparison, commonSComparison]

/-- Same-cursor declarative compound keys are interchangeable on the left of the through-Rule-5
comparison, preserving the complete comparison record. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_left
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (referencesAgree : left.prior.references = right.prior.references) :
    input.compareLocalizedRerootCompoundThroughRule5 left other =
      input.compareLocalizedRerootCompoundThroughRule5 right other := by
  have priorComparison :
      input.compareLocalizedRerootCompoundRule4bcKeys left.prior other.prior =
        input.compareLocalizedRerootCompoundRule4bcKeys right.prior other.prior :=
    input.compareLocalizedRerootCompoundRule4bcKeys_congr_left_of_declarative
      target view cursor left.prior right.prior other.prior
      leftDerived.1 rightDerived.1 referencesAgree
  obtain ⟨_, _, _, priorReferenceMaps⟩ :=
    input.declarative_compoundRule4bc_observable_eq target view cursor left.prior right.prior
      leftDerived.1 rightDerived.1 referencesAgree
  obtain ⟨commonRMaps, commonSMaps⟩ :=
    input.declarative_rule5_readings_descriptor_eq target view cursor
      left.prior.readings right.prior.readings left.rule5Readings right.rule5Readings
      priorReferenceMaps leftDerived.2 rightDerived.2
  have commonRComparison :
      input.compareLocalizedRerootCompoundRule5Readings
          .R left.rule5Readings other.rule5Readings =
        input.compareLocalizedRerootCompoundRule5Readings
          .R right.rule5Readings other.rule5Readings :=
    input.compareLocalizedRerootCompoundRule5Readings_congr_left .R
      left.rule5Readings right.rule5Readings other.rule5Readings
      (by
        show left.rule5Readings.map (fun reading => reading.commonR.descriptor) =
          right.rule5Readings.map (fun reading => reading.commonR.descriptor)
        exact commonRMaps)
  have commonSComparison :
      input.compareLocalizedRerootCompoundRule5Readings
          .S left.rule5Readings other.rule5Readings =
        input.compareLocalizedRerootCompoundRule5Readings
          .S right.rule5Readings other.rule5Readings :=
    input.compareLocalizedRerootCompoundRule5Readings_congr_left .S
      left.rule5Readings right.rule5Readings other.rule5Readings
      (by
        show left.rule5Readings.map (fun reading => reading.commonS.descriptor) =
          right.rule5Readings.map (fun reading => reading.commonS.descriptor)
        exact commonSMaps)
  exact input.compareLocalizedRerootCompoundThroughRule5_congr_of_components
    priorComparison commonRComparison commonSComparison

/-- Same-cursor declarative compound keys are interchangeable on the right of the through-Rule-5
comparison, preserving the complete comparison record. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_right
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (referencesAgree : left.prior.references = right.prior.references) :
    input.compareLocalizedRerootCompoundThroughRule5 other left =
      input.compareLocalizedRerootCompoundThroughRule5 other right := by
  have priorComparison :
      input.compareLocalizedRerootCompoundRule4bcKeys other.prior left.prior =
        input.compareLocalizedRerootCompoundRule4bcKeys other.prior right.prior :=
    input.compareLocalizedRerootCompoundRule4bcKeys_congr_right_of_declarative
      target view cursor left.prior right.prior other.prior
      leftDerived.1 rightDerived.1 referencesAgree
  obtain ⟨_, _, _, priorReferenceMaps⟩ :=
    input.declarative_compoundRule4bc_observable_eq target view cursor left.prior right.prior
      leftDerived.1 rightDerived.1 referencesAgree
  obtain ⟨commonRMaps, commonSMaps⟩ :=
    input.declarative_rule5_readings_descriptor_eq target view cursor
      left.prior.readings right.prior.readings left.rule5Readings right.rule5Readings
      priorReferenceMaps leftDerived.2 rightDerived.2
  have commonRComparison :
      input.compareLocalizedRerootCompoundRule5Readings
          .R other.rule5Readings left.rule5Readings =
        input.compareLocalizedRerootCompoundRule5Readings
          .R other.rule5Readings right.rule5Readings :=
    input.compareLocalizedRerootCompoundRule5Readings_congr_right .R
      left.rule5Readings right.rule5Readings other.rule5Readings
      (by
        show left.rule5Readings.map (fun reading => reading.commonR.descriptor) =
          right.rule5Readings.map (fun reading => reading.commonR.descriptor)
        exact commonRMaps)
  have commonSComparison :
      input.compareLocalizedRerootCompoundRule5Readings
          .S other.rule5Readings left.rule5Readings =
        input.compareLocalizedRerootCompoundRule5Readings
          .S other.rule5Readings right.rule5Readings :=
    input.compareLocalizedRerootCompoundRule5Readings_congr_right .S
      left.rule5Readings right.rule5Readings other.rule5Readings
      (by
        show left.rule5Readings.map (fun reading => reading.commonS.descriptor) =
          right.rule5Readings.map (fun reading => reading.commonS.descriptor)
        exact commonSMaps)
  exact input.compareLocalizedRerootCompoundThroughRule5_congr_of_components
    priorComparison commonRComparison commonSComparison

/-- Same-cursor declarative compound keys are interchangeable on both sides of the through-Rule-5
comparison.  This is the two-sided form used by an occurrence-level comparator that holds one key
fixed and substitutes the other. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (referencesAgree : left.prior.references = right.prior.references) :
    input.compareLocalizedRerootCompoundThroughRule5 left other =
        input.compareLocalizedRerootCompoundThroughRule5 right other ∧
      input.compareLocalizedRerootCompoundThroughRule5 other left =
        input.compareLocalizedRerootCompoundThroughRule5 other right :=
  ⟨input.compareLocalizedRerootCompoundThroughRule5_congr_left target view cursor
      left right other leftDerived rightDerived referencesAgree,
    input.compareLocalizedRerootCompoundThroughRule5_congr_right target view cursor
      left right other leftDerived rightDerived referencesAgree⟩

/-! ## Record components

`ConstitutionalRule5Comparison` carries `ordering` and `pseudo`.  The occurrence wrapper
`localizedOccurrenceRule45ComparisonRecord` lifts it to `ConstitutionalDescriptorHierarchyComparison`,
whose `decisiveRule?` field is `none` on this fallthrough path.  All three components are preserved
because the whole record is. -/

/-- The through-Rule-5 record is unchanged on the left substitution. -/
theorem compareLocalizedRerootCompoundThroughRule5_ordering_eq_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (referencesAgree : left.prior.references = right.prior.references) :
    (input.compareLocalizedRerootCompoundThroughRule5 left other).ordering =
      (input.compareLocalizedRerootCompoundThroughRule5 right other).ordering := by
  rw [input.compareLocalizedRerootCompoundThroughRule5_congr_left target view cursor
    left right other leftDerived rightDerived referencesAgree]

/-- The pseudoasymmetric flag is unchanged on the left substitution. -/
theorem compareLocalizedRerootCompoundThroughRule5_pseudo_eq_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (referencesAgree : left.prior.references = right.prior.references) :
    (input.compareLocalizedRerootCompoundThroughRule5 left other).pseudo =
      (input.compareLocalizedRerootCompoundThroughRule5 right other).pseudo := by
  rw [input.compareLocalizedRerootCompoundThroughRule5_congr_left target view cursor
    left right other leftDerived rightDerived referencesAgree]

/-- The occurrence comparison record, including its decisive-rule field, is unchanged on the left
substitution. -/
theorem compareLocalizedOccurrenceRule45ComparisonRecord_congr_left
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (referencesAgree : left.prior.references = right.prior.references) :
    localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 left other) =
      localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 right other) := by
  rw [input.compareLocalizedRerootCompoundThroughRule5_congr_left target view cursor
    left right other leftDerived rightDerived referencesAgree]

/-- The decisive-rule field of the occurrence comparison record is unchanged on the left
substitution. -/
theorem compareLocalizedOccurrenceRule45ComparisonRecord_decisiveRule?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (referencesAgree : left.prior.references = right.prior.references) :
    (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 left other)).decisiveRule? =
      (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 right other)).decisiveRule? := by
  rw [input.compareLocalizedOccurrenceRule45ComparisonRecord_congr_left target view cursor
    left right other leftDerived rightDerived referencesAgree]

/-- The pseudoasymmetric field of the occurrence comparison record is unchanged on the left
substitution. -/
theorem compareLocalizedOccurrenceRule45ComparisonRecord_pseudo_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (referencesAgree : left.prior.references = right.prior.references) :
    (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 left other)).pseudo =
      (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 right other)).pseudo := by
  rw [input.compareLocalizedOccurrenceRule45ComparisonRecord_congr_left target view cursor
    left right other leftDerived rightDerived referencesAgree]

/-! ## The explicit lower-layer reference premise

Equal reference lists are not derivable from observable equality: the P-92.5.2.1 selection reads
hierarchy-rank-addressed labels.  The premise below is stated in the exact form the separate
reference-agreement development is expected to produce. -/

/-- Lower-layer premise: two independent Rule-4a derivations at the same cursor select the same
P-92.5.2.1 Rule-4b reference list. -/
def LocalizedRerootCompoundRule45ReferenceListAgreement
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key) : Prop :=
  localizedRule4bReferencesFromRankedLabels left.prior.rule4aKey.rankedLabels =
    localizedRule4bReferencesFromRankedLabels right.prior.rule4aKey.rankedLabels

/-- With declarative key meanings, reference-list agreement makes the recorded `references` fields
equal.  No exact-label equality is involved: only the selector outcome is used. -/
theorem references_eq_of_referenceListAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (agreement : LocalizedRerootCompoundRule45ReferenceListAgreement input left right) :
    left.prior.references = right.prior.references := by
  have leftSelector : localizedRule4bReferencesFromRankedLabels
      left.prior.rule4aKey.rankedLabels = left.prior.references :=
    (localizedRule4bReferencesFromRankedLabels_eq_iff _ _).mpr leftDerived.1.2.1
  have rightSelector : localizedRule4bReferencesFromRankedLabels
      right.prior.rule4aKey.rankedLabels = right.prior.references :=
    (localizedRule4bReferencesFromRankedLabels_eq_iff _ _).mpr rightDerived.1.2.1
  rw [← leftSelector, ← rightSelector]
  exact agreement

/-- Two-sided interchangeability from the explicit reference-list premise.  Until
`LocalizedRule4bReferenceAgreement` is available, this is the honest conditional form of the
compound agreement theorem. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_of_referenceListAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right)
    (agreement : LocalizedRerootCompoundRule45ReferenceListAgreement input left right) :
    input.compareLocalizedRerootCompoundThroughRule5 left other =
        input.compareLocalizedRerootCompoundThroughRule5 right other ∧
      input.compareLocalizedRerootCompoundThroughRule5 other left =
        input.compareLocalizedRerootCompoundThroughRule5 other right :=
  input.compareLocalizedRerootCompoundThroughRule5_congr_of_declarative
    target view cursor left right other leftDerived rightDerived
    (input.references_eq_of_referenceListAgreement target view cursor
      left right leftDerived rightDerived agreement)

/-! ## Builder corollaries

Compiler soundness supplies the declarative meaning of the compiled side; the independent side
remains a declarative derivation. -/

/-- Comparison against a successfully compiled compound key agrees with comparison against any
independent derivation at the same cursor, given the lower-layer reference-list premise. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_of_compiled
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (compiled derived other : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel cursor = some compiled)
    (derivedMeaning : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor derived)
    (agreement : LocalizedRerootCompoundRule45ReferenceListAgreement
      input compiled derived) :
    input.compareLocalizedRerootCompoundThroughRule5 compiled other =
        input.compareLocalizedRerootCompoundThroughRule5 derived other ∧
      input.compareLocalizedRerootCompoundThroughRule5 other compiled =
        input.compareLocalizedRerootCompoundThroughRule5 other derived :=
  input.compareLocalizedRerootCompoundThroughRule5_congr_of_referenceListAgreement
    target view cursor compiled derived other
    (input.buildLocalizedRerootCompoundRule45Key?_sound
      target view fuel cursor compiled computed)
    derivedMeaning agreement

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
