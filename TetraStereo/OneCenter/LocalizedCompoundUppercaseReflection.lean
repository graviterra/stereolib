import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.OneCenter.LocalizedCumulativeUppercaseReflection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Uppercase reader-swap reflection of the actual compound Rule-4a--5 builders

`LocalizedParametricCompoundRule45Key` exposes the production compound builders with the label
reader generalized to an arbitrary total callback
`read : cursor → Option LocalizedAuxiliaryLabel`.  This module studies those *actual* builders
under the simultaneous reflection

* `read ↦ compoundUppercaseRead input read`, where only uppercase `.chiral` descriptors are swapped
  and lowercase `.pseudoasymmetric` observations are fixed, and
* every selected uppercase reference `r ↦ RS.swap r` (Rule-4b/4c references and both Rule-5
  common-reference channels).

All statements are same-cursor value statements: the cursor, the child reader and every structural
decision are the production ones; only label values and reference values are reflected.  No
physical mirror operation on molecules, cursors or occurrences is introduced or claimed.

## Main results

* `compoundUppercaseRead` — the reflected label callback.
* `buildLocalizedRerootRule4bcReadingWithRead?_compoundUppercase_reflect` — the one-reference
  Rule-4b/4c reading builder reflects at every fuel and cursor, with `none` preserved.
* `buildLocalizedRerootRule4bcReadingsWithRead?_compoundUppercase_reverse` — the normative
  alternative list reflects to the **reverse** of the entrywise reflected successful readings.
  This is the exact statement: the two-reference P-92 alternative list is canonical `[R,S]`, so
  after reference swap it is again `[R,S]` and the reading order is reversed, not naively mapped.
* `buildLocalizedRerootCompoundRule4bcKeyWithRead?_compoundUppercase_reflect` — the complete
  no/one/two-reference compound Rules-4b/4c builder reflects, with the canonical field
  `references = reflectSelectedRule4bReferences` and the reversed reading list.
* `buildLocalizedRerootRule5ReadingWithRead?_compoundUppercase_reflect` — one Rule-5 reading
  reflects, exchanging the two common channels: reflected `commonR` is the image of the original
  `commonS`, and reflected `commonS` is the image of the original `commonR`.
* `buildLocalizedRerootRule5ReadingsWithRead?_compoundUppercase_reverse` and
  `buildLocalizedRerootCompoundRule45KeyWithRead?_compoundUppercase_reflect` — the Rule-5 reading
  list and the complete compound through-Rule-5 builder reflect at every fuel and cursor.
* `localizedRerootRule5Descriptor_compoundUppercase` — the Rule-5 descriptor probe flips together
  with the common-reference swap.
* `compareLocalizedRerootCompoundRule{4b,4c,5}Readings_compoundUppercase_reverse` — the actual
  compound reading comparators of the reflected lists are the comparators of the reversed original
  lists (with the Rule-5 probe flipped).
* `compareLocalizedRerootCompoundRule{4b,4c,5}Readings_compoundUppercase_of_length_le_one` and
  `compareLocalizedRerootCompoundRule4bcKeys_compoundUppercase_of_length_le_one` — the no- and
  one-reference core: when a reading list has at most one entry, reversal is the identity, so the
  comparator is literally invariant.

## Dependency note

The cumulative sibling `LocalizedCumulativeUppercaseReflection` owns the cumulative stage/key
reflection, the actual cumulative comparator reflection, the actual cumulative insert/sort
reflection, and the headline fuel induction
`buildLocalizedRerootCumulativeRule45KeyWithRead?_reflectUppercase`.  Every compound proof below
consumes that sibling theorem directly; the local private bridge
`buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling` is only a named re-export of
the sibling headline (definitional callback equality), not a second induction.  No cumulative
construction or merge fact is re-proved here.

## Scope

This is mechanical actual-builder reflection.  It does not claim that a physical branch label is
faithful under molecular mirroring, and it does not claim observable separation.  The canonical
two-reference case is handled by reversing the reading order, never by a naive pointwise map-swap
equality over all lists.
-/

namespace CertifiedLocalizedCIPInput

/-! ## The reflected label callback -/

/-- Compose an arbitrary label reader with uppercase reflection.  Only `.chiral` descriptors are
swapped; `.pseudoasymmetric` observations are fixed. -/
def compoundUppercaseRead
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option LocalizedAuxiliaryLabel :=
  reflectUppercaseOptionalLabel (read cursor)

/-- The uppercase reference swap is an involution. -/
private theorem compoundUppercaseSwapSwap (reference : RS) :
    RS.swap (RS.swap reference) = reference := by
  cases reference <;> rfl

/-- Pointwise agreement of two `Option`-valued functions with a post-composition lifts through
`List.mapM` to post-composition of the whole result list. -/
private theorem compoundUppercaseListMapMPointwiseMap {α β : Type*}
    (first second : α → Option β) (transform : β → β)
    (agrees : ∀ value, first value = (second value).map transform) :
    ∀ values : List α,
      values.mapM first = (values.mapM second).map (List.map transform)
  | [] => rfl
  | value :: values => by
      rw [List.mapM_cons, List.mapM_cons, agrees value,
        compoundUppercaseListMapMPointwiseMap first second transform agrees values]
      cases valueComputed : second value with
      | none => simp [valueComputed]
      | some result =>
          cases valuesComputed : values.mapM second <;>
            simp [valueComputed, valuesComputed]

/-! ## Cumulative-builder bridge

The cumulative recursion is owned by the sibling module `LocalizedCumulativeUppercaseReflection`,
whose headline `buildLocalizedRerootCumulativeRule45KeyWithRead?_reflectUppercase` has exactly
this statement (its reflected callback is `fun cursor => reflectUppercaseOptionalLabel (read
cursor)`, definitionally `compoundUppercaseRead input read`).  The bridge below is therefore the
sibling theorem itself, not a second induction. -/

private theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (reflectLocalizedCumulativeRule45Stage stage)
          (compoundUppercaseRead input read) fuel cursor =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor).map
          (reflectLocalizedRerootCumulativeRule45Key input) := by
  exact input.buildLocalizedRerootCumulativeRule45KeyWithRead?_reflectUppercase stage read

/-! ## Zero-, one- and two-reference alternative shapes -/

/-- The actual Rule-4b selector can return only `[]`, one reference, or the canonical tied pair
`[R,S]`. -/
theorem localizedRule4bReferencesFromRankedLabels_shape
    (layers : List (List
      (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    localizedRule4bReferencesFromRankedLabels layers = [] ∨
      (∃ reference,
        localizedRule4bReferencesFromRankedLabels layers = [reference]) ∨
      localizedRule4bReferencesFromRankedLabels layers = [RS.R, RS.S] := by
  unfold localizedRule4bReferencesFromRankedLabels localizedRule4bReferencesFromPopulation
  dsimp only
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl ⟨RS.R, rfl⟩)
    · split
      · exact Or.inr (Or.inl ⟨RS.S, rfl⟩)
      · exact Or.inr (Or.inr rfl)

/-- For the three selector shapes, reflecting the selected reference list and then taking the
actual sequential alternatives is the reverse of the entrywise swapped alternatives.  In the tied
case both sides are the canonical `[some R, some S]`: the list of alternatives is *fixed*, so the
order in which the two readings were compiled is what reverses. -/
theorem localizedRule4bcReferenceAlternatives_reflectSelected_shape
    (references : List RS)
    (shape : references = [] ∨
      (∃ reference, references = [reference]) ∨
      references = [RS.R, RS.S]) :
    localizedRule4bcReferenceAlternatives
        (reflectSelectedRule4bReferences references) =
      ((localizedRule4bcReferenceAlternatives references).map
        (Option.map RS.swap)).reverse := by
  rcases shape with empty | ⟨reference, single⟩ | tied
  · rw [empty]; rfl
  · rw [single]; rfl
  · rw [tied]; rfl

/-- The reference-count priority is invariant on the three selector shapes, because the tied list
`[R,S]` reflects to itself and a unique reference stays unique. -/
theorem constitutionalRule4bReferenceCountPriority_reflectSelected_shape
    (references : List RS)
    (shape : references = [] ∨
      (∃ reference, references = [reference]) ∨
      references = [RS.R, RS.S]) :
    constitutionalRule4bReferenceCountPriority
        (reflectSelectedRule4bReferences references) =
      constitutionalRule4bReferenceCountPriority references := by
  rcases shape with empty | ⟨reference, single⟩ | tied
  · rw [empty]; rfl
  · rw [single]; rfl
  · rw [tied]; rfl

/-! ## Reflected compound keys and readings -/

/-- Reflected one-reference Rule-4b/4c reading: the selected alternative is swapped and both
cumulative keys are reflected. -/
def compoundUppercaseRule4bcReading
    (input : CertifiedLocalizedCIPInput)
    (reading : input.LocalizedRerootRule4bcReading) :
    input.LocalizedRerootRule4bcReading where
  reference? := reading.reference?.map RS.swap
  rule4bKey := reflectLocalizedRerootCumulativeRule45Key input reading.rule4bKey
  rule4cKey := reflectLocalizedRerootCumulativeRule45Key input reading.rule4cKey

/-- Reflected complete no/one/two-reference compound Rules-4b/4c key.  The reference selection is
the canonical reflected selection, the count priority is fixed, and the reading list is reversed
because the canonical alternative order `[some R, some S]` does not move under reference swap. -/
def compoundUppercaseCompoundRule4bcKey
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCompoundRule4bcKey) :
    input.LocalizedRerootCompoundRule4bcKey where
  rule4aKey := reflectLocalizedRerootCumulativeRule45Key input key.rule4aKey
  references := reflectSelectedRule4bReferences key.references
  referenceCountPriority := key.referenceCountPriority
  readings := (key.readings.map (compoundUppercaseRule4bcReading input)).reverse

/-- Reflected Rule-5 reading: the prior alternative is reflected and the two common-reference
channels are exchanged before reflection. -/
def compoundUppercaseRule5Reading
    (input : CertifiedLocalizedCIPInput)
    (reading : input.LocalizedRerootRule5Reading) :
    input.LocalizedRerootRule5Reading where
  prior := compoundUppercaseRule4bcReading input reading.prior
  commonR := reflectLocalizedRerootCumulativeRule45Key input reading.commonS
  commonS := reflectLocalizedRerootCumulativeRule45Key input reading.commonR

/-- Reflected complete compound through-Rule-5 key.  The Rule-5 reading list is reversed for the
same canonical-ordering reason as the Rule-4b/4c reading list. -/
def compoundUppercaseCompoundRule45Key
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCompoundRule45Key) :
    input.LocalizedRerootCompoundRule45Key where
  prior := compoundUppercaseCompoundRule4bcKey input key.prior
  rule5Readings :=
    (key.rule5Readings.map (compoundUppercaseRule5Reading input)).reverse

/-! ## Generic `mapM` facts -/

/-- `List.mapM` of the reverse list is the reverse of the `List.mapM` result. -/
private theorem compoundUppercaseListMapMReverse {α β : Type*}
    (step : α → Option β) :
    ∀ values : List α,
      values.reverse.mapM step = Option.map List.reverse (values.mapM step)
  | [] => rfl
  | value :: values => by
      rw [List.reverse_cons, List.mapM_append, List.mapM_cons,
        compoundUppercaseListMapMReverse step values]
      cases valueComputed : step value with
      | none =>
          cases valuesComputed : values.mapM step <;>
            simp [valueComputed, valuesComputed]
      | some result =>
          cases valuesComputed : values.mapM step <;>
            simp [valueComputed, valuesComputed]

/-- The combined reversal/swap rule for a sequential reading list.  If compiling a swapped
alternative with the reflected step is the mapped compilation of the original alternative, then
compiling the reversed swapped alternatives is the reversed mapped compilation. -/
private theorem compoundUppercaseListMapMReverseSwapMap {α β : Type*}
    (step' step : α → Option β) (transform : β → β) (swap : α → α)
    (agrees : ∀ value, step' (swap value) = (step value).map transform) :
    ∀ values : List α,
      ((values.map swap).reverse).mapM step' =
        Option.map
          (fun results => (results.map transform).reverse)
          (values.mapM step)
  | values => by
      rw [compoundUppercaseListMapMReverse step' (values.map swap),
        List.mapM_map,
        compoundUppercaseListMapMPointwiseMap (step' ∘ swap) step transform
          (fun value => agrees value) values,
        Option.map_map]
      rfl

/-- The sequential Rule-4b/4c reading-list compiler is `List.mapM` of the one-reading compiler. -/
private theorem buildLocalizedRerootRule4bcReadingsWithRead?_eq_mapM
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (alternatives : List (Option RS)) :
    input.buildLocalizedRerootRule4bcReadingsWithRead? read fuel cursor alternatives =
      alternatives.mapM
        (fun alternative =>
          input.buildLocalizedRerootRule4bcReadingWithRead? read fuel cursor alternative) := by
  induction alternatives with
  | nil => rfl
  | cons alternative alternatives inductionHypothesis =>
      unfold buildLocalizedRerootRule4bcReadingsWithRead?
      rw [inductionHypothesis]
      simp [List.mapM_cons]

/-- The sequential Rule-5 reading-list compiler is `List.mapM` of the one-reading compiler. -/
private theorem buildLocalizedRerootRule5ReadingsWithRead?_eq_mapM
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (priors : List input.LocalizedRerootRule4bcReading) :
    input.buildLocalizedRerootRule5ReadingsWithRead? read fuel cursor priors =
      priors.mapM
        (fun prior =>
          input.buildLocalizedRerootRule5ReadingWithRead? read fuel cursor prior) := by
  induction priors with
  | nil => rfl
  | cons prior priors inductionHypothesis =>
      unfold buildLocalizedRerootRule5ReadingsWithRead?
      rw [inductionHypothesis]
      simp [List.mapM_cons]

/-! ## Actual one-reading Rule-4b/4c reflection -/

/-- The actual one-reference Rule-4b/4c reading builder reflects at every fuel and cursor.  The
none, unique-R and unique-S alternatives are all covered; a failed compilation stays `none`. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_compoundUppercase_reflect
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) :
    input.buildLocalizedRerootRule4bcReadingWithRead?
        (compoundUppercaseRead input read) fuel cursor
        (reference.map RS.swap) =
      (input.buildLocalizedRerootRule4bcReadingWithRead? read fuel cursor reference).map
        (compoundUppercaseRule4bcReading input) := by
  cases reference with
  | none =>
      change input.buildLocalizedRerootRule4bcReadingWithRead?
          (compoundUppercaseRead input read) fuel cursor none =
        (input.buildLocalizedRerootRule4bcReadingWithRead? read fuel cursor none).map
          (compoundUppercaseRule4bcReading input)
      unfold buildLocalizedRerootRule4bcReadingWithRead?
      dsimp only
      have rule4bBridge :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
              (compoundUppercaseRead input read) fuel cursor =
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
              read fuel cursor).map
              (reflectLocalizedRerootCumulativeRule45Key input) := by
        simpa only [reflectLocalizedCumulativeRule45Stage] using
          buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling
            input .rule4a read fuel cursor
      have rule4cBridge :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4cNoReference
              (compoundUppercaseRead input read) fuel cursor =
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4cNoReference
              read fuel cursor).map
              (reflectLocalizedRerootCumulativeRule45Key input) := by
        simpa only [reflectLocalizedCumulativeRule45Stage] using
          buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling
            input .rule4cNoReference read fuel cursor
      rw [rule4bBridge, rule4cBridge]
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor with
      | none => simp [rule4bComputed]
      | some rule4bKey =>
          simp only [rule4bComputed, Option.map_some, Option.bind_some]
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4cComputed]
          | some rule4cKey => simp [compoundUppercaseRule4bcReading]
  | some reference =>
      change input.buildLocalizedRerootRule4bcReadingWithRead?
          (compoundUppercaseRead input read) fuel cursor
          (some (RS.swap reference)) =
        (input.buildLocalizedRerootRule4bcReadingWithRead? read fuel cursor
          (some reference)).map
          (compoundUppercaseRule4bcReading input)
      unfold buildLocalizedRerootRule4bcReadingWithRead?
      dsimp only
      have rule4bBridge :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b (RS.swap reference))
              (compoundUppercaseRead input read) fuel cursor =
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b reference)
              read fuel cursor).map
              (reflectLocalizedRerootCumulativeRule45Key input) := by
        simpa only [reflectLocalizedCumulativeRule45Stage] using
          buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling
            input (.rule4b reference) read fuel cursor
      have rule4cBridge :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4c (RS.swap reference))
              (compoundUppercaseRead input read) fuel cursor =
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4c reference)
              read fuel cursor).map
              (reflectLocalizedRerootCumulativeRule45Key input) := by
        simpa only [reflectLocalizedCumulativeRule45Stage] using
          buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling
            input (.rule4c reference) read fuel cursor
      rw [rule4bBridge, rule4cBridge]
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor with
      | none => simp [rule4bComputed]
      | some rule4bKey =>
          simp only [rule4bComputed, Option.map_some, Option.bind_some]
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4cComputed]
          | some rule4cKey => simp [compoundUppercaseRule4bcReading]

/-! ## Actual reading-list reflection: the canonical two-reference reversal -/

/-- The actual sequential reading-list builder reflects the reversed swapped alternatives into the
reverse of the entrywise reflected successful readings.  This is the exact two-reference statement:
`[some R, some S]` is swapped to `[some S, some R]` and then compiled in reverse order, which
returns the reversed reflected reading list, not a naively mapped one. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_compoundUppercase_reverse
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (alternatives : List (Option RS)),
      input.buildLocalizedRerootRule4bcReadingsWithRead?
          (compoundUppercaseRead input read) fuel cursor
          ((alternatives.map (Option.map RS.swap)).reverse) =
        Option.map
          (fun readings => (readings.map (compoundUppercaseRule4bcReading input)).reverse)
          (input.buildLocalizedRerootRule4bcReadingsWithRead?
            read fuel cursor alternatives) := by
  intro fuel cursor alternatives
  rw [buildLocalizedRerootRule4bcReadingsWithRead?_eq_mapM,
    buildLocalizedRerootRule4bcReadingsWithRead?_eq_mapM]
  exact compoundUppercaseListMapMReverseSwapMap
    (fun alternative =>
      input.buildLocalizedRerootRule4bcReadingWithRead?
        (compoundUppercaseRead input read) fuel cursor alternative)
    (fun alternative =>
      input.buildLocalizedRerootRule4bcReadingWithRead? read fuel cursor alternative)
    (compoundUppercaseRule4bcReading input) (Option.map RS.swap)
    (fun alternative =>
      buildLocalizedRerootRule4bcReadingWithRead?_compoundUppercase_reflect
        input read fuel cursor alternative)
    alternatives

/-! ## Actual compound Rules-4b/4c key reflection -/

/-- The actual complete no/one/two-reference compound Rules-4b/4c builder reflects at every fuel
and cursor.  The Rule-4a cumulative key is reflected by the cumulative sibling API; the P-92
reference selection is reflected canonically; the tied `[R,S]` alternative list is fixed and the
reading list is reversed. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_compoundUppercase_reflect
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
          (compoundUppercaseRead input read) fuel cursor =
        (input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read fuel cursor).map
          (compoundUppercaseCompoundRule4bcKey input) := by
  intro fuel cursor
  unfold buildLocalizedRerootCompoundRule4bcKeyWithRead?
  dsimp only
  have rule4aBridge :
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (compoundUppercaseRead input read) fuel cursor =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          read fuel cursor).map
          (reflectLocalizedRerootCumulativeRule45Key input) := by
    simpa only [reflectLocalizedCumulativeRule45Stage] using
      buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling
        input .rule4a read fuel cursor
  rw [rule4aBridge]
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed]
  | some rule4aKey =>
      simp [rule4aComputed]
      have selectionReflection :
          localizedRule4bReferencesFromRankedLabels
              (reflectUppercaseRankedLabels rule4aKey.rankedLabels) =
            reflectSelectedRule4bReferences
              (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels) := by
        simpa only [reflectLocalizedRerootCumulativeRule45Key]
          using localizedRule4bReferencesFromRankedLabels_reflectUppercase rule4aKey.rankedLabels
      have shape :
          localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels = [] ∨
            (∃ reference,
              localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels =
                [reference]) ∨
            localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels =
              [RS.R, RS.S] :=
        localizedRule4bReferencesFromRankedLabels_shape rule4aKey.rankedLabels
      have alternativesReflection :
          localizedRule4bcReferenceAlternatives
              (reflectSelectedRule4bReferences
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) =
            ((localizedRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels
                  rule4aKey.rankedLabels)).map (Option.map RS.swap)).reverse :=
        localizedRule4bcReferenceAlternatives_reflectSelected_shape _ shape
      have countReflection :
          constitutionalRule4bReferenceCountPriority
              (reflectSelectedRule4bReferences
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) =
            constitutionalRule4bReferenceCountPriority
              (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels) :=
        constitutionalRule4bReferenceCountPriority_reflectSelected_shape _ shape
      rw [selectionReflection]
      rw [alternativesReflection]
      rw [buildLocalizedRerootRule4bcReadingsWithRead?_compoundUppercase_reverse]
      cases readingsComputed :
          input.buildLocalizedRerootRule4bcReadingsWithRead?
            read fuel cursor
            (localizedRule4bcReferenceAlternatives
              (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [readingsComputed]
      | some readings =>
          simp only [readingsComputed, Option.map_some, Option.some.injEq]
          dsimp only [compoundUppercaseCompoundRule4bcKey]
          simp [countReflection]

/-! ## Actual Rule-5 reflection: the common channels exchange -/

/-- For a fixed prior alternative, the reflected common-R stage is the reflection of the original
common-S stage. -/
private theorem localizedRule5StageFor_compoundUppercase_R
    (rule4bReference : Option RS) :
    localizedRule5StageFor (rule4bReference.map RS.swap) .R =
      reflectLocalizedCumulativeRule45Stage
        (localizedRule5StageFor rule4bReference .S) := by
  cases rule4bReference <;> rfl

/-- For a fixed prior alternative, the reflected common-S stage is the reflection of the original
common-R stage. -/
private theorem localizedRule5StageFor_compoundUppercase_S
    (rule4bReference : Option RS) :
    localizedRule5StageFor (rule4bReference.map RS.swap) .S =
      reflectLocalizedCumulativeRule45Stage
        (localizedRule5StageFor rule4bReference .R) := by
  cases rule4bReference <;> rfl

/-- The actual one-reading Rule-5 builder reflects at every fuel and cursor, exchanging the two
common-reference channels. -/
theorem buildLocalizedRerootRule5ReadingWithRead?_compoundUppercase_reflect
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    input.buildLocalizedRerootRule5ReadingWithRead?
        (compoundUppercaseRead input read) fuel cursor
        (compoundUppercaseRule4bcReading input prior) =
      (input.buildLocalizedRerootRule5ReadingWithRead? read fuel cursor prior).map
        (compoundUppercaseRule5Reading input) := by
  unfold buildLocalizedRerootRule5ReadingWithRead?
  dsimp only [compoundUppercaseRule4bcReading]
  rw [localizedRule5StageFor_compoundUppercase_R prior.reference?,
    localizedRule5StageFor_compoundUppercase_S prior.reference?]
  rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling
        input (localizedRule5StageFor prior.reference? .S) read fuel cursor,
      buildLocalizedRerootCumulativeRule45KeyWithRead?_of_sibling
        input (localizedRule5StageFor prior.reference? .R) read fuel cursor]
  cases commonRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor prior.reference? .R) read fuel cursor with
  | none =>
      cases commonSComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .S) read fuel cursor <;>
        simp [commonRComputed, commonSComputed]
  | some commonR =>
      cases commonSComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .S) read fuel cursor with
      | none => simp [commonRComputed, commonSComputed]
      | some commonS =>
          simp [compoundUppercaseRule5Reading, compoundUppercaseRule4bcReading]

/-- The actual sequential Rule-5 reading-list builder reflects the reversed entrywise-reflected
priors into the reverse of the entrywise reflected successful readings. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_compoundUppercase_reverse
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (priors : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule5ReadingsWithRead?
          (compoundUppercaseRead input read) fuel cursor
          (priors.map (compoundUppercaseRule4bcReading input)).reverse =
        Option.map
          (fun readings => (readings.map (compoundUppercaseRule5Reading input)).reverse)
          (input.buildLocalizedRerootRule5ReadingsWithRead? read fuel cursor priors) := by
  intro fuel cursor priors
  rw [buildLocalizedRerootRule5ReadingsWithRead?_eq_mapM,
    buildLocalizedRerootRule5ReadingsWithRead?_eq_mapM]
  exact compoundUppercaseListMapMReverseSwapMap
    (fun prior =>
      input.buildLocalizedRerootRule5ReadingWithRead?
        (compoundUppercaseRead input read) fuel cursor prior)
    (fun prior =>
      input.buildLocalizedRerootRule5ReadingWithRead? read fuel cursor prior)
    (compoundUppercaseRule5Reading input) (compoundUppercaseRule4bcReading input)
    (fun prior =>
      buildLocalizedRerootRule5ReadingWithRead?_compoundUppercase_reflect
        input read fuel cursor prior)
    priors

/-- The actual complete compound through-Rule-5 builder reflects at every fuel and cursor. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_compoundUppercase_reflect
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCompoundRule45KeyWithRead?
          (compoundUppercaseRead input read) fuel cursor =
        (input.buildLocalizedRerootCompoundRule45KeyWithRead? read fuel cursor).map
          (compoundUppercaseCompoundRule45Key input) := by
  intro fuel cursor
  unfold buildLocalizedRerootCompoundRule45KeyWithRead?
  rw [buildLocalizedRerootCompoundRule4bcKeyWithRead?_compoundUppercase_reflect
        input read fuel cursor]
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed]
  | some prior =>
      simp [priorComputed]
      dsimp only [compoundUppercaseCompoundRule4bcKey]
      rw [buildLocalizedRerootRule5ReadingsWithRead?_compoundUppercase_reverse
            input read fuel cursor prior.readings]
      cases readingsComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [readingsComputed]
      | some readings =>
          simp only [readingsComputed, Option.map_some, Option.some.injEq]
          dsimp only [compoundUppercaseCompoundRule45Key]
          rfl

/-! ## Comparison observables -/

/-- The Rule-5 descriptor probe flips together with the common-reference swap: probing the
reflected reading at the swapped reference returns exactly the reflection of the original probe
(the reflected cumulative key fixes its descriptor projection). -/
theorem localizedRerootRule5Descriptor_compoundUppercase
    (input : CertifiedLocalizedCIPInput)
    (commonReference : RS) (reading : input.LocalizedRerootRule5Reading) :
    input.localizedRerootRule5Descriptor (RS.swap commonReference)
        (compoundUppercaseRule5Reading input reading) =
      input.localizedRerootRule5Descriptor commonReference reading := by
  cases commonReference <;> rfl

/-- A `compareLex` map lemma that permits different comparison functions on the two sides. -/
private theorem compoundUppercaseCompareLexMapRel {α : Type*}
    (compare' compare : α → α → Ordering) (transform : α → α)
    (respects : ∀ left right,
      compare' (transform left) (transform right) = compare left right) :
    ∀ (left right : List α),
      List.compareLex compare' (left.map transform) (right.map transform) =
        List.compareLex compare left right
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | left :: lefts, right :: rights => by
      rw [List.map_cons, List.map_cons, List.compareLex_cons_cons,
        List.compareLex_cons_cons, respects left right,
        compoundUppercaseCompareLexMapRel compare' compare transform respects lefts rights]

/-- The actual Rule-4b reading comparator of two reflected readings agrees pointwise with the
original reading comparator. -/
private theorem compareLocalizedRerootRule4bcReadingsByRule4b_compoundUppercase
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b
        (compoundUppercaseRule4bcReading input left)
        (compoundUppercaseRule4bcReading input right) =
      input.compareLocalizedRerootRule4bcReadingsByRule4b left right := by
  unfold compareLocalizedRerootRule4bcReadingsByRule4b
  rfl

/-- The actual Rule-4c reading comparator agrees pointwise on two reflected readings. -/
private theorem compareLocalizedRerootCompoundRule4cReadingsBy_compoundUppercase
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule4bcReading) :
    Ordering.byKey (fun reading => reading.rule4cKey.descriptor)
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
        (compoundUppercaseRule4bcReading input left)
        (compoundUppercaseRule4bcReading input right) =
      Ordering.byKey (fun reading => reading.rule4cKey.descriptor)
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
        left right := by
  rfl

/-- The actual Rule-5 reading comparator, probed at the swapped reference on two reflected
readings, agrees pointwise with the original comparator probed at the original reference. -/
private theorem compareLocalizedRerootRule5ReadingsBy_compoundUppercase
    (input : CertifiedLocalizedCIPInput)
    (commonReference : RS)
    (left right : input.LocalizedRerootRule5Reading) :
    Ordering.byKey
        (input.localizedRerootRule5Descriptor (RS.swap commonReference))
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
        (compoundUppercaseRule5Reading input left)
        (compoundUppercaseRule5Reading input right) =
      Ordering.byKey (input.localizedRerootRule5Descriptor commonReference)
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
        left right := by
  cases commonReference <;> rfl

/-- The actual Rule-4b reading-list comparator of the reflected lists equals the comparator of the
reversed original lists. -/
theorem compareLocalizedRerootCompoundRule4bReadings_compoundUppercase_reverse
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootCompoundRule4bReadings
        ((left.map (compoundUppercaseRule4bcReading input)).reverse)
        ((right.map (compoundUppercaseRule4bcReading input)).reverse) =
      input.compareLocalizedRerootCompoundRule4bReadings left.reverse right.reverse := by
  unfold compareLocalizedRerootCompoundRule4bReadings
  rw [← List.map_reverse, ← List.map_reverse]
  exact compoundUppercaseCompareLexMapRel
    input.compareLocalizedRerootRule4bcReadingsByRule4b
    input.compareLocalizedRerootRule4bcReadingsByRule4b
    (compoundUppercaseRule4bcReading input)
    (fun a b =>
      compareLocalizedRerootRule4bcReadingsByRule4b_compoundUppercase input a b)
    left.reverse right.reverse

/-- The actual Rule-4c reading-list comparator of the reflected lists equals the comparator of the
reversed original lists. -/
theorem compareLocalizedRerootCompoundRule4cReadings_compoundUppercase_reverse
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootCompoundRule4cReadings
        ((left.map (compoundUppercaseRule4bcReading input)).reverse)
        ((right.map (compoundUppercaseRule4bcReading input)).reverse) =
      input.compareLocalizedRerootCompoundRule4cReadings left.reverse right.reverse := by
  unfold compareLocalizedRerootCompoundRule4cReadings
  rw [← List.map_reverse, ← List.map_reverse]
  exact compoundUppercaseCompareLexMapRel
    (Ordering.byKey (fun reading => reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
    (Ordering.byKey (fun reading => reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
    (compoundUppercaseRule4bcReading input)
    (fun a b =>
      compareLocalizedRerootCompoundRule4cReadingsBy_compoundUppercase input a b)
    left.reverse right.reverse

/-- Reversal is the identity on a list of length at most one. -/
private theorem compoundUppercaseListReverseEqSelf {α : Type*} {values : List α}
    (short : values.length ≤ 1) : values.reverse = values := by
  cases values with
  | nil => rfl
  | cons value values =>
      cases values with
      | nil => rfl
      | cons next rest => simp at short

/-- No/one-reference Rule-4b reading comparison: a reading list of length at most one is unchanged
by reversal, so the actual comparator is literally invariant under reflection. -/
theorem compareLocalizedRerootCompoundRule4bReadings_compoundUppercase_of_length_le_one
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRule4bcReading)
    (leftShort : left.length ≤ 1) (rightShort : right.length ≤ 1) :
    input.compareLocalizedRerootCompoundRule4bReadings
        ((left.map (compoundUppercaseRule4bcReading input)).reverse)
        ((right.map (compoundUppercaseRule4bcReading input)).reverse) =
      input.compareLocalizedRerootCompoundRule4bReadings left right := by
  rw [compareLocalizedRerootCompoundRule4bReadings_compoundUppercase_reverse,
    compoundUppercaseListReverseEqSelf leftShort,
    compoundUppercaseListReverseEqSelf rightShort]

/-- No/one-reference Rule-4c reading comparison: literal comparator invariance. -/
theorem compareLocalizedRerootCompoundRule4cReadings_compoundUppercase_of_length_le_one
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRule4bcReading)
    (leftShort : left.length ≤ 1) (rightShort : right.length ≤ 1) :
    input.compareLocalizedRerootCompoundRule4cReadings
        ((left.map (compoundUppercaseRule4bcReading input)).reverse)
        ((right.map (compoundUppercaseRule4bcReading input)).reverse) =
      input.compareLocalizedRerootCompoundRule4cReadings left right := by
  rw [compareLocalizedRerootCompoundRule4cReadings_compoundUppercase_reverse,
    compoundUppercaseListReverseEqSelf leftShort,
    compoundUppercaseListReverseEqSelf rightShort]

/-- The actual Rule-5 reading-list comparator of the reflected lists, probed at the swapped
common reference, equals the comparator of the reversed original lists at the original reference.
This is the precise probe-flip statement; it is not literal comparator invariance. -/
theorem compareLocalizedRerootCompoundRule5Readings_compoundUppercase_reverse
    (input : CertifiedLocalizedCIPInput)
    (commonReference : RS)
    (left right : List input.LocalizedRerootRule5Reading) :
    input.compareLocalizedRerootCompoundRule5Readings (RS.swap commonReference)
        ((left.map (compoundUppercaseRule5Reading input)).reverse)
        ((right.map (compoundUppercaseRule5Reading input)).reverse) =
      input.compareLocalizedRerootCompoundRule5Readings commonReference
        left.reverse right.reverse := by
  unfold compareLocalizedRerootCompoundRule5Readings
  rw [← List.map_reverse, ← List.map_reverse]
  exact compoundUppercaseCompareLexMapRel
    (Ordering.byKey (input.localizedRerootRule5Descriptor (RS.swap commonReference))
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
    (Ordering.byKey (input.localizedRerootRule5Descriptor commonReference)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
    (compoundUppercaseRule5Reading input)
    (fun a b =>
      compareLocalizedRerootRule5ReadingsBy_compoundUppercase input commonReference a b)
    left.reverse right.reverse

/-- No/one-reading Rule-5 comparison: reversal is the identity, so the reflected comparator at the
swapped reference equals the original comparator at the original reference. -/
theorem compareLocalizedRerootCompoundRule5Readings_compoundUppercase_of_length_le_one
    (input : CertifiedLocalizedCIPInput)
    (commonReference : RS)
    (left right : List input.LocalizedRerootRule5Reading)
    (leftShort : left.length ≤ 1) (rightShort : right.length ≤ 1) :
    input.compareLocalizedRerootCompoundRule5Readings (RS.swap commonReference)
        ((left.map (compoundUppercaseRule5Reading input)).reverse)
        ((right.map (compoundUppercaseRule5Reading input)).reverse) =
      input.compareLocalizedRerootCompoundRule5Readings commonReference left right := by
  rw [compareLocalizedRerootCompoundRule5Readings_compoundUppercase_reverse,
    compoundUppercaseListReverseEqSelf leftShort,
    compoundUppercaseListReverseEqSelf rightShort]

/-- No/one-reference complete compound Rules-4b/4c key comparison invariance.  When both reading
lists have at most one entry, the reflected key comparator is literally the original comparator:
the Rule-4a cumulative comparison is reflected by the sibling API, the count priority is fixed, and
the reversed reading lists are unchanged. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_compoundUppercase_of_length_le_one
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftShort : left.readings.length ≤ 1) (rightShort : right.readings.length ≤ 1) :
    input.compareLocalizedRerootCompoundRule4bcKeys
        (compoundUppercaseCompoundRule4bcKey input left)
        (compoundUppercaseCompoundRule4bcKey input right) =
      input.compareLocalizedRerootCompoundRule4bcKeys left right := by
  unfold compareLocalizedRerootCompoundRule4bcKeys
  simp only [compoundUppercaseCompoundRule4bcKey, compareLex, Ordering.byKey]
  rw [compareLocalizedRerootCumulativeRule45Keys_reflect,
    compareLocalizedRerootCompoundRule4bReadings_compoundUppercase_of_length_le_one input
      left.readings right.readings leftShort rightShort,
    compareLocalizedRerootCompoundRule4cReadings_compoundUppercase_of_length_le_one input
      left.readings right.readings leftShort rightShort]

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundUppercaseRead
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bReferencesFromRankedLabels_shape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bcReferenceAlternatives_reflectSelected_shape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutionalRule4bReferenceCountPriority_reflectSelected_shape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundUppercaseRule4bcReading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundUppercaseCompoundRule4bcKey
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundUppercaseRule5Reading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundUppercaseCompoundRule45Key
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?_compoundUppercase_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsWithRead?_compoundUppercase_reverse
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_compoundUppercase_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingWithRead?_compoundUppercase_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsWithRead?_compoundUppercase_reverse
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_compoundUppercase_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRule5Descriptor_compoundUppercase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bReadings_compoundUppercase_reverse
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4cReadings_compoundUppercase_reverse
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bReadings_compoundUppercase_of_length_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4cReadings_compoundUppercase_of_length_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule5Readings_compoundUppercase_reverse
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule5Readings_compoundUppercase_of_length_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys_compoundUppercase_of_length_le_one

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
