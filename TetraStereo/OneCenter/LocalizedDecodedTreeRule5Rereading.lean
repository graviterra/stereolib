import TetraStereo.OneCenter.LocalizedRule5SwapAndSignal
import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedSparseAddressReconstruction
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.OneCenter.LocalizedCompoundRankConvexity
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.OneCenter.LocalizedCumulativeCursorTransport
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedRule5SwapAndSignal




































/-! ## Generic list helper -/

/-- Every nonempty list is a cons. -/
theorem list_exists_cons_of_ne_nil {α : Type*} {list : List α} (nonempty : list ≠ []) :
    ∃ head tail, list = head :: tail := by
  cases list with
  | nil => exact absurd rfl nonempty
  | cons head tail => exact ⟨head, tail, rfl⟩

/-! ## Decomposing the full actual compound Rule-5 comparator tie -/

/-- A full actual compound through-Rule-5 comparator tie is exactly the compound Rules-4b/4c tie
and the common-`R` Rule-5 reading-list tie.  No stage, reference or label is assumed. -/
theorem compareLocalizedRerootCompoundRule45Keys_eq_prior_and_readings
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (tie : input.compareLocalizedRerootCompoundRule45Keys left right = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = Ordering.eq ∧
      input.compareLocalizedRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings = Ordering.eq := by
  have decomposed := tie
  simp only [compareLocalizedRerootCompoundRule45Keys, compareLex, Ordering.byKey,
    Ordering.then_eq_eq] at decomposed
  exact ⟨decomposed.1, decomposed.2⟩

/-! ## Scalar injectivity of the actual cumulative priority vector -/

/-- **Four-case injectivity of the actual cumulative priority vector.**  For a fixed common Rule-5
reference and *any* pair of own Rule-4b references (`none` or `some`), equality of the actual
Rule-4a--5 priority vectors forces equality of the sparse labels.  The two mixed cases are
impossible because the `rule5NoRule4bReference` vector has length three while the `rule5` vector
has length four.  No sparsity hypothesis on the labels is used. -/
theorem localizedRule5StageFor_priority_injective
    (ownLeft ownRight : Option RS) (commonReference : RS)
    (left right : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority
        (localizedRule5StageFor ownLeft commonReference) left =
      localizedCumulativeRule45Priority
        (localizedRule5StageFor ownRight commonReference) right) :
    left = right := by
  cases ownLeft with
  | none =>
      cases ownRight with
      | none =>
          exact localizedCumulativeRule45Priority_rule5NoRule4bReference_injective
            commonReference left right same
      | some _ =>
          exact absurd same (by
            intro hypothesis
            have lengthEq := congrArg List.length hypothesis
            simp [localizedRule5StageFor, localizedCumulativeRule45Priority] at lengthEq)
  | some leftReference =>
      cases ownRight with
      | none =>
          exact absurd same (by
            intro hypothesis
            have lengthEq := congrArg List.length hypothesis
            simp [localizedRule5StageFor, localizedCumulativeRule45Priority] at lengthEq)
      | some rightReference =>
          exact localizedCumulativeRule45Priority_rule5_commonReference_injective
            leftReference rightReference commonReference left right same

/-! ## Paired head readings of a tied reading list -/

/-- The paired head readings of a tied nonempty common-reference reading list carry equal
common-reference descriptors.  This is the actual data-domain content of a full compound tie: the
comparator inspects the readings in canonical order, and the first comparison it makes is the
comparison of the two head descriptors by the injective actual Rule-4a--5 priority comparator. -/
theorem compareLocalizedRerootCompoundRule5Readings_cons_cons_eq
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    (headLeft headRight : input.LocalizedRerootRule5Reading)
    (tailLeft tailRight : List input.LocalizedRerootRule5Reading)
    (same : input.compareLocalizedRerootCompoundRule5Readings commonReference
      (headLeft :: tailLeft) (headRight :: tailRight) = Ordering.eq) :
    input.localizedRerootRule5Descriptor commonReference headLeft =
      input.localizedRerootRule5Descriptor commonReference headRight :=
  (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp
    (by
      have headTie := same
      simp only [compareLocalizedRerootCompoundRule5Readings, List.compareLex_cons_cons,
        Ordering.byKey, Ordering.then_eq_eq] at headTie
      exact headTie.1)

/-- **Actual data extraction from a full compound Rule-5 tie.**  A full actual compound comparator
tie of two keys with nonempty Rule-5 reading lists yields, at the actual data level: the complete
compound Rules-4b/4c prior tie, the paired head readings, and equality of their common-`R`
descriptors.  Nothing about labels, trees or physical cuts is assumed. -/
theorem compareLocalizedRerootCompoundRule45Keys_eq_head_descriptor
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (tie : input.compareLocalizedRerootCompoundRule45Keys left right = Ordering.eq)
    (leftNonempty : left.rule5Readings ≠ [])
    (rightNonempty : right.rule5Readings ≠ []) :
    ∃ headLeft tailLeft headRight tailRight,
      left.rule5Readings = headLeft :: tailLeft ∧
      right.rule5Readings = headRight :: tailRight ∧
      input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = Ordering.eq ∧
      input.localizedRerootRule5Descriptor .R headLeft =
        input.localizedRerootRule5Descriptor .R headRight := by
  obtain ⟨priorTie, readingsTie⟩ :=
    compareLocalizedRerootCompoundRule45Keys_eq_prior_and_readings input left right tie
  obtain ⟨headLeft, tailLeft, leftEq⟩ := list_exists_cons_of_ne_nil leftNonempty
  obtain ⟨headRight, tailRight, rightEq⟩ := list_exists_cons_of_ne_nil rightNonempty
  have readingsTieCons : input.compareLocalizedRerootCompoundRule5Readings .R
      (headLeft :: tailLeft) (headRight :: tailRight) = Ordering.eq := by
    simpa only [Ordering.byKey, leftEq, rightEq] using readingsTie
  exact ⟨headLeft, tailLeft, headRight, tailRight, leftEq, rightEq, priorTie,
    compareLocalizedRerootCompoundRule5Readings_cons_cons_eq input .R
      headLeft headRight tailLeft tailRight readingsTieCons⟩

/-! ## Assembling a full comparator tie from componentwise data -/

/-- The actual sparse-layer comparison of two readings with equal common-reference descriptors is a
tie.  This is the step that turns descriptor equality into the actual comparator outcome, using the
injectivity of the actual Rule-4a--5 priority comparator. -/
theorem compareSparseLayers_descriptor_eq
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    {left right : input.LocalizedRerootRule5Reading}
    (descriptorEq : input.localizedRerootRule5Descriptor commonReference left =
      input.localizedRerootRule5Descriptor commonReference right) :
    Ordering.byKey (input.localizedRerootRule5Descriptor commonReference)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
      left right = Ordering.eq := by
  simp only [Ordering.byKey, descriptorEq]
  exact CompilerProjectionFidelity.compareSparseLayers_self
    compareLocalizedCumulativeRule45Priority
    (fun value => compareLocalizedCumulativeRule45Priority_self value) _

/-- If two canonical reading lists have equal common-reference descriptors index by index, then the
actual reading-list comparator ties.  This is the converse of the cons decomposition. -/
theorem compareLocalizedRerootCompoundRule5Readings_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    {left right : List input.LocalizedRerootRule5Reading}
    (related : List.Forall₂ (fun a b =>
      input.localizedRerootRule5Descriptor commonReference a =
        input.localizedRerootRule5Descriptor commonReference b) left right) :
    input.compareLocalizedRerootCompoundRule5Readings commonReference left right =
      Ordering.eq := by
  have unfolded : ∀ {left right : List input.LocalizedRerootRule5Reading},
      List.Forall₂ (fun a b =>
        input.localizedRerootRule5Descriptor commonReference a =
          input.localizedRerootRule5Descriptor commonReference b) left right →
        List.compareLex
          (Ordering.byKey (input.localizedRerootRule5Descriptor commonReference)
            (OfficialRuleMajorKey.compareSparseLayers
              compareLocalizedCumulativeRule45Priority)) left right = Ordering.eq := by
    intro left right h
    induction h with
    | nil => rfl
    | cons head tail tailHypothesis =>
        rw [List.compareLex_cons_cons,
          compareSparseLayers_descriptor_eq input commonReference head, tailHypothesis]
        rfl
  exact unfolded related

/-- A full actual compound Rule-5 comparator tie follows from the compound Rules-4b/4c prior tie
together with the common-`R` Rule-5 reading-list tie.  This is the exact converse of
`compareLocalizedRerootCompoundRule45Keys_eq_prior_and_readings`. -/
theorem compareLocalizedRerootCompoundRule45Keys_eq_of_prior_tie
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq)
    (readingsTie : input.compareLocalizedRerootCompoundRule5Readings .R
      left.rule5Readings right.rule5Readings = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule45Keys left right = Ordering.eq := by
  have unfolded : compareLex
      (Ordering.byKey (fun key => key.prior)
        input.compareLocalizedRerootCompoundRule4bcKeys)
      (Ordering.byKey (fun key => key.rule5Readings)
        (input.compareLocalizedRerootCompoundRule5Readings .R)) left right = Ordering.eq := by
    unfold compareLex
    rw [Ordering.then_eq_eq]
    exact ⟨by simpa only [Ordering.byKey] using priorTie,
      by simpa only [Ordering.byKey] using readingsTie⟩
  exact unfolded

/-! ## Singleton readings and the explicit cross-addressed relation -/

/-- The list-level cross-addressed relation on a singleton pair is exactly the pair-level
relation.  This is the bridge needed to state the per-pair `PriorTieMirrorReadings` shape of
`LocalizedCompoundRankConvexity` for singleton reading lists. -/
theorem mirrorReadings_singleton_iff
    {input : CertifiedLocalizedCIPInput}
    {left right : input.LocalizedRerootRule5Reading} :
    MirrorReadings input [left] [right] ↔ MirrorReading input left right := by
  constructor
  · intro related
    cases related with
    | cons headRelated _ => exact headRelated
  · intro related
    exact List.Forall₂.cons related List.Forall₂.nil

/-- Under the explicit cross-addressed relation, a tie of the actual common-`R` reading comparison
forces the actual common-`S` reading comparison to tie as well.  This is the SAME/CROSSED reading
law at the comparator level: the mirrored pair of readings cannot be distinguished by the second
common reference once it is invisible to the first. -/
theorem compareLocalizedRerootCompoundRule5Readings_S_eq_of_R_eq_of_mirror
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRule5Reading)
    (mirror : MirrorReadings input left right)
    (tieR : input.compareLocalizedRerootCompoundRule5Readings .R left right =
      Ordering.eq) :
    input.compareLocalizedRerootCompoundRule5Readings .S left right = Ordering.eq := by
  rw [compareLocalizedRerootCompoundRule5Readings_S_eq_swap_of_mirror input left right mirror,
    tieR]
  rfl

/-! ## Actual builder extraction for a single own Rule-4b reference

The compound builders thread one and the same recursion budget `fuel` through every cumulative
sub-build.  The lemmas below expose those actual sub-builds from the actual compound build
successes; they extract data, they never assume a desired equality. -/

/-- The cumulative stage at which one Rule-4b/4c alternative compiles its Rule-4b key. -/
def localizedRule4bOwnStage : Option RS → LocalizedCumulativeRule45Stage
  | none => .rule4a
  | some reference => .rule4b reference

/-- A successful per-reference Rule-4b/4c reading records the reference it was compiled for. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_reference
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    reading.reference? = reference := by
  cases reference with
  | none =>
      unfold buildLocalizedRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              rfl
  | some reference =>
      unfold buildLocalizedRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              rfl

/-- A successful per-reference reading exposes its Rule-4b key as a successful actual cumulative
build at the reference's own stage, at the same fuel. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey_built
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule4bOwnStage reference) read fuel cursor = some reading.rule4bKey := by
  cases reference with
  | none =>
      unfold buildLocalizedRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              exact rule4bComputed
  | some reference =>
      unfold buildLocalizedRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              exact rule4bComputed

/-- Every member of a successful per-reference reading-list build comes from one successful
per-reference reading build at an alternative of the same list. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_member
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (alternatives : List (Option RS))
      (readings : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule4bcReadingsWithRead?
        read fuel cursor alternatives = some readings →
      ∀ reading, reading ∈ readings →
        ∃ reference, reference ∈ alternatives ∧
          input.buildLocalizedRerootRule4bcReadingWithRead?
            read fuel cursor reference = some reading
  | [], readings, computed => by
      simp [buildLocalizedRerootRule4bcReadingsWithRead?] at computed
      subst readings
      intro reading mem
      simp at mem
  | reference :: alternatives, readings, computed => by
      unfold buildLocalizedRerootRule4bcReadingsWithRead? at computed
      cases headComputed : input.buildLocalizedRerootRule4bcReadingWithRead?
          read fuel cursor reference with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
              read fuel cursor alternatives with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              intro reading mem
              rcases List.mem_cons.mp mem with rfl | tailMem
              · exact ⟨reference, by simp, headComputed⟩
              · obtain ⟨sourceReference, sourceMem, sourceComputed⟩ :=
                  buildLocalizedRerootRule4bcReadingsWithRead?_member input read fuel cursor
                    alternatives tail tailComputed reading tailMem
                exact ⟨sourceReference, List.mem_cons_of_mem reference sourceMem, sourceComputed⟩

/-- A successful reading-list build over a single alternative is a single reading of that
alternative. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (readings : List input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadingsWithRead?
      read fuel cursor [reference] = some readings) :
    ∃ reading, readings = [reading] ∧
      input.buildLocalizedRerootRule4bcReadingWithRead?
        read fuel cursor reference = some reading := by
  unfold buildLocalizedRerootRule4bcReadingsWithRead? at computed
  cases headComputed : input.buildLocalizedRerootRule4bcReadingWithRead?
      read fuel cursor reference with
  | none => simp [headComputed] at computed
  | some head =>
      have tailComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
          read fuel cursor ([] : List (Option RS)) = some [] := rfl
      have readingsEq : readings = head :: [] := by
        simpa [headComputed, tailComputed] using computed.symm
      rw [readingsEq]
      exact ⟨head, rfl, rfl⟩

/-- A successful compound Rules-4b/4c key build exposes its actual Rule-4a build and its actual
reading-list build at the same fuel. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        .rule4a read fuel cursor = some key.rule4aKey ∧
      input.buildLocalizedRerootRule4bcReadingsWithRead? read fuel cursor
        (localizedRule4bcReferenceAlternatives key.references) = some key.readings := by
  unfold buildLocalizedRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
          read fuel cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [rule4aComputed, readingsComputed] at computed
      | some readings =>
          have keyEq : key =
              { rule4aKey := rule4aKey
                references :=
                  localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
                referenceCountPriority :=
                  constitutionalRule4bReferenceCountPriority
                    (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)
                readings := readings } := by
            simpa [rule4aComputed, readingsComputed] using computed.symm
          rw [keyEq]
          exact ⟨rfl, readingsComputed⟩

/-- A successful Rule-5 reading build exposes the prior alternative and both actual
common-reference builds, at the same fuel. -/
theorem buildLocalizedRerootRule5ReadingWithRead?_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5ReadingWithRead?
      read fuel cursor prior = some reading) :
    reading.prior = prior ∧
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (localizedRule5StageFor prior.reference? .R) read fuel cursor = some reading.commonR ∧
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (localizedRule5StageFor prior.reference? .S) read fuel cursor = some reading.commonS := by
  unfold buildLocalizedRerootRule5ReadingWithRead? at computed
  cases commonRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor prior.reference? .R) read fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      cases commonSComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .S) read fuel cursor with
      | none => simp [commonRComputed, commonSComputed] at computed
      | some commonS =>
          have readingEq : reading =
              { prior := prior, commonR := commonR, commonS := commonS } := by
            simpa [commonRComputed, commonSComputed] using computed.symm
          rw [readingEq]
          exact ⟨rfl, rfl, rfl⟩

/-- A successful reading-list build over a single prior alternative is a single Rule-5 reading of
that alternative. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (readings : List input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5ReadingsWithRead?
      read fuel cursor [prior] = some readings) :
    ∃ reading, readings = [reading] ∧
      input.buildLocalizedRerootRule5ReadingWithRead?
        read fuel cursor prior = some reading := by
  unfold buildLocalizedRerootRule5ReadingsWithRead? at computed
  cases headComputed : input.buildLocalizedRerootRule5ReadingWithRead?
      read fuel cursor prior with
  | none => simp [headComputed] at computed
  | some head =>
      have tailComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
          read fuel cursor ([] : List input.LocalizedRerootRule4bcReading) = some [] := rfl
      have readingsEq : readings = head :: [] := by
        simpa [headComputed, tailComputed] using computed.symm
      rw [readingsEq]
      exact ⟨head, rfl, rfl⟩

/-- A successful compound through-Rule-5 key build exposes its actual compound Rules-4b/4c build
and its actual Rule-5 reading-list build, at the same fuel. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
        read fuel cursor = some key.prior ∧
      input.buildLocalizedRerootRule5ReadingsWithRead? read fuel cursor
        key.prior.readings = some key.rule5Readings := by
  unfold buildLocalizedRerootCompoundRule45KeyWithRead? at computed
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      cases readingsComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [priorComputed, readingsComputed] at computed
      | some readings =>
          have keyEq : key = { prior := prior, rule5Readings := readings } := by
            simpa [priorComputed, readingsComputed] using computed.symm
          rw [keyEq]
          exact ⟨rfl, readingsComputed⟩

/-- Reading-list comparison ties are index-wise: a tie of two single-reading lists is the
comparison tie of the two readings. -/
theorem compareLocalizedRerootCompoundRule4bReadings_singleton_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootCompoundRule4bReadings [left] [right] = Ordering.eq ↔
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.rule4bKey.descriptor right.rule4bKey.descriptor = Ordering.eq := by
  simp only [compareLocalizedRerootCompoundRule4bReadings, List.compareLex_cons_cons,
    compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey, Ordering.then_eq_eq,
    List.compareLex_nil_nil, and_true]

/-- **Actual singleton-own-reference data extraction.**  From two actual successful compound
through-Rule-5 builds at one common fuel, each selecting exactly one own Rule-4b reference, plus
the actual prior Rules-4b/4c comparator tie, all the actual sub-builds and both common-reference
builds of the two Rule-5 readings are exposed at that same fuel.  Nothing here assumes a reading
equality, a tree correspondence or a nearest-reference relation. -/
theorem actual_singleton_prior_tie_builds
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (fuel : Nat)
    (leftReference rightReference : RS)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel rightCursor = some rightKey)
    (leftReferences : leftKey.prior.references = [leftReference])
    (rightReferences : rightKey.prior.references = [rightReference])
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.eq) :
    ∃ (leftPriorReading rightPriorReading : input.LocalizedRerootRule4bcReading)
      (leftReading rightReading : input.LocalizedRerootRule5Reading),
      leftKey.prior.readings = [leftPriorReading] ∧
        rightKey.prior.readings = [rightPriorReading] ∧
          leftKey.rule5Readings = [leftReading] ∧
            rightKey.rule5Readings = [rightReading] ∧
              input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  (.rule4b leftReference) read fuel leftCursor =
                some leftPriorReading.rule4bKey ∧
              input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  (.rule4b rightReference) read fuel rightCursor =
                some rightPriorReading.rule4bKey ∧
              input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  (localizedRule5StageFor (some leftReference) .R) read fuel leftCursor =
                some leftReading.commonR ∧
              input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  (localizedRule5StageFor (some rightReference) .R) read fuel rightCursor =
                some rightReading.commonR ∧
              input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  (localizedRule5StageFor (some leftReference) .S) read fuel leftCursor =
                some leftReading.commonS ∧
              input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  (localizedRule5StageFor (some rightReference) .S) read fuel rightCursor =
                some rightReading.commonS ∧
              OfficialRuleMajorKey.compareSparseLayers
                  compareLocalizedCumulativeRule45Priority
                  leftPriorReading.rule4bKey.descriptor
                  rightPriorReading.rule4bKey.descriptor = Ordering.eq := by
  obtain ⟨priorLeftComputed, readingsLeftComputed⟩ :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_components input read fuel leftCursor
      leftKey leftComputed
  obtain ⟨priorRightComputed, readingsRightComputed⟩ :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_components input read fuel rightCursor
      rightKey rightComputed
  obtain ⟨_, rule4bReadingsLeftComputed⟩ :=
    buildLocalizedRerootCompoundRule4bcKeyWithRead?_components input read fuel leftCursor
      leftKey.prior priorLeftComputed
  obtain ⟨_, rule4bReadingsRightComputed⟩ :=
    buildLocalizedRerootCompoundRule4bcKeyWithRead?_components input read fuel rightCursor
      rightKey.prior priorRightComputed
  rw [leftReferences] at rule4bReadingsLeftComputed
  rw [rightReferences] at rule4bReadingsRightComputed
  obtain ⟨leftPriorReading, leftReadingsEq, leftPriorReadingComputed⟩ :=
    buildLocalizedRerootRule4bcReadingsWithRead?_singleton input read fuel leftCursor
      (some leftReference) leftKey.prior.readings rule4bReadingsLeftComputed
  obtain ⟨rightPriorReading, rightReadingsEq, rightPriorReadingComputed⟩ :=
    buildLocalizedRerootRule4bcReadingsWithRead?_singleton input read fuel rightCursor
      (some rightReference) rightKey.prior.readings rule4bReadingsRightComputed
  have leftReferenceEq : leftPriorReading.reference? = some leftReference :=
    buildLocalizedRerootRule4bcReadingWithRead?_reference input read fuel leftCursor
      (some leftReference) leftPriorReading leftPriorReadingComputed
  have rightReferenceEq : rightPriorReading.reference? = some rightReference :=
    buildLocalizedRerootRule4bcReadingWithRead?_reference input read fuel rightCursor
      (some rightReference) rightPriorReading rightPriorReadingComputed
  have leftRule4bBuilt :=
    buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey_built input read fuel leftCursor
      (some leftReference) leftPriorReading leftPriorReadingComputed
  have rightRule4bBuilt :=
    buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey_built input read fuel rightCursor
      (some rightReference) rightPriorReading rightPriorReadingComputed
  rw [leftReadingsEq] at readingsLeftComputed
  rw [rightReadingsEq] at readingsRightComputed
  obtain ⟨leftReading, leftRule5Eq, leftRule5ReadingComputed⟩ :=
    buildLocalizedRerootRule5ReadingsWithRead?_singleton input read fuel leftCursor
      leftPriorReading leftKey.rule5Readings readingsLeftComputed
  obtain ⟨rightReading, rightRule5Eq, rightRule5ReadingComputed⟩ :=
    buildLocalizedRerootRule5ReadingsWithRead?_singleton input read fuel rightCursor
      rightPriorReading rightKey.rule5Readings readingsRightComputed
  obtain ⟨-, leftCommonRBuilt, leftCommonSBuilt⟩ :=
    buildLocalizedRerootRule5ReadingWithRead?_components input read fuel leftCursor
      leftPriorReading leftReading leftRule5ReadingComputed
  obtain ⟨-, rightCommonRBuilt, rightCommonSBuilt⟩ :=
    buildLocalizedRerootRule5ReadingWithRead?_components input read fuel rightCursor
      rightPriorReading rightReading rightRule5ReadingComputed
  rw [leftReferenceEq] at leftCommonRBuilt leftCommonSBuilt
  rw [rightReferenceEq] at rightCommonRBuilt rightCommonSBuilt
  obtain ⟨-, -, rule4bTie, -⟩ :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      leftKey.prior rightKey.prior).mp priorTie
  have rule4bTieSingle : input.compareLocalizedRerootCompoundRule4bReadings
      [leftPriorReading] [rightPriorReading] = Ordering.eq := by
    simpa only [leftReadingsEq, rightReadingsEq] using rule4bTie
  have descriptorTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority
      leftPriorReading.rule4bKey.descriptor rightPriorReading.rule4bKey.descriptor =
        Ordering.eq :=
    (compareLocalizedRerootCompoundRule4bReadings_singleton_eq input
      leftPriorReading rightPriorReading).mp rule4bTieSingle
  exact ⟨leftPriorReading, rightPriorReading, leftReading, rightReading,
    leftReadingsEq, rightReadingsEq, leftRule5Eq, rightRule5Eq,
    leftRule4bBuilt, rightRule4bBuilt, leftCommonRBuilt, rightCommonRBuilt,
    leftCommonSBuilt, rightCommonSBuilt, descriptorTie⟩



























section TreeRereading

open LocalizedCumulativeDecoratedTree

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ### Element steps of the two structural clauses -/



theorem positionSource_officialNodeAtomLabel_eq
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) :
    input.moleculeGraph.officialNodeAtomLabel (positionSource p).occurrence.1.node =
      toLex (input.moleculeGraph.atomZ (positionAtom singleBonded acyclic p),
        input.moleculeGraph.atomMass (positionAtom singleBonded acyclic p)) :=
  officialNodeAtomLabel_eq_of_observed (positionAtom_spec singleBonded acyclic p)
    (input.carrierOccurrence_provenance_real singleBonded acyclic (positionSource p).occurrence)

/-- A realised decorated tree stores the actual node's Rule-1b original-root distance. -/
theorem rule1bDistance_eq_stored
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    tree.rule1bDistance = tree.source.occurrence.1.node.rule1bRootDistance := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize => rfl

/-- The erased child list of a decorated tree is the tree's own child list mapped through the
erasure. -/
theorem shape_children_eq_map
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (shape tree).children = tree.children.map shape := by
  cases tree with
  | mk source atomicNumber rule1bDistance isotopeMass label children =>
      rw [table_shape_mk, table_shapeList_eq_map]




def ShapePositionCursorRelation
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    (x y : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ p : Position tL, positionSource p = x ∧ positionSource (shapePositionEquiv hshape p) = y

/-! ### List plumbing for the actual child frame -/

/-- Positional `Forall₂` from a length match and slotwise relatedness. -/
theorem forall₂_of_length_eq_of_getElem?
    {α β : Type*} {relation : α → β → Prop} :
    ∀ {left : List α} {right : List β}, left.length = right.length →
      (∀ (slot : Nat) (leftValue : α), left[slot]? = some leftValue →
        ∀ (rightValue : β), right[slot]? = some rightValue →
          relation leftValue rightValue) →
      List.Forall₂ relation left right
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, lengthEq, _ => by exact absurd lengthEq (by simp)
  | _ :: _, [], lengthEq, _ => by exact absurd lengthEq (by simp)
  | leftHead :: leftTail, rightHead :: rightTail, lengthEq, step =>
      List.Forall₂.cons
        (step 0 leftHead (by simp) rightHead (by simp))
        (forall₂_of_length_eq_of_getElem? (by simpa using lengthEq)
          (fun slot leftValue leftLookup rightValue rightLookup =>
            step (slot + 1) leftValue (by simpa using leftLookup)
              rightValue (by simpa using rightLookup)))

/-- Transport a positional `Forall₂` of decorated children through the actual cursor sources on
both sides. -/
theorem forall₂_map_source_of_forall₂
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {hshape : shape tL = shape tR} :
    ∀ {left right : List (LocalizedCumulativeDecoratedTree input carrierFuel)},
      List.Forall₂ (fun leftChild rightChild =>
        ShapePositionCursorRelation hshape leftChild.source rightChild.source) left right →
      List.Forall₂ (ShapePositionCursorRelation hshape)
        (left.map (fun child => child.source)) (right.map (fun child => child.source))
  | _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, List.Forall₂.cons head tail =>
      List.Forall₂.cons head (forall₂_map_source_of_forall₂ tail)

/-- Reorder the left list along a permutation of the right list while preserving a `Forall₂`
relation.  This is the list plumbing the actual child clause needs: the two evaluated child frames
are only permutations of the sorted child sources. -/
theorem forall₂_exists_perm_of_perm_right
    {α : Type*} {relation : α → α → Prop} :
    ∀ {right right' : List α}, right.Perm right' → ∀ {left : List α},
      List.Forall₂ relation left right →
        ∃ left', left'.Perm left ∧ List.Forall₂ relation left' right'
  | _, _, .nil, _, related => by
      cases related
      exact ⟨[], List.Perm.refl _, List.Forall₂.nil⟩
  | _, _, .cons _ permutation, _, List.Forall₂.cons head tail => by
      obtain ⟨tail', tail'Perm, tail'Related⟩ :=
        forall₂_exists_perm_of_perm_right permutation tail
      exact ⟨_ :: tail', List.Perm.cons _ tail'Perm,
        List.Forall₂.cons head tail'Related⟩
  | _, _, .swap _ _ _, _,
      List.Forall₂.cons head (List.Forall₂.cons secondHead restRelated) =>
      ⟨_, List.Perm.swap _ _ _,
        List.Forall₂.cons secondHead (List.Forall₂.cons head restRelated)⟩
  | _, _, .trans firstPermutation secondPermutation, _, related => by
      obtain ⟨middle, middlePerm, middleRelated⟩ :=
        forall₂_exists_perm_of_perm_right firstPermutation related
      obtain ⟨final, finalPerm, finalRelated⟩ :=
        forall₂_exists_perm_of_perm_right secondPermutation middleRelated
      exact ⟨final, finalPerm.trans middlePerm, finalRelated⟩

/-! ### The structural clauses of the cursor relation -/




theorem shapePositionCursorRelation_atomLabel
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y) :
    input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node := by
  obtain ⟨p, rfl, rfl⟩ := related
  rw [positionSource_officialNodeAtomLabel_eq singleBonded acyclic p,
      positionSource_officialNodeAtomLabel_eq singleBonded acyclic
        (shapePositionEquiv hshape p),
      shapePositionEquiv_positionAtom_atomZ_eq hshape realizesL realizesR p,
      shapePositionEquiv_positionAtom_atomMass_eq hshape realizesL realizesR p]




theorem shapePositionCursorRelation_rootDistance
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y) :
    x.occurrence.1.node.rule1bRootDistance = y.occurrence.1.node.rule1bRootDistance := by
  obtain ⟨p, rfl, rfl⟩ := related
  have leftStored : (positionNode p).rule1bDistance =
      (positionSource p).occurrence.1.node.rule1bRootDistance :=
    rule1bDistance_eq_stored (read := readL)
      (realizes_of_subtree realizesL (positionNode_spec p))
  have rightStored : (positionNode (shapePositionEquiv hshape p)).rule1bDistance =
      (positionSource (shapePositionEquiv hshape p)).occurrence.1.node.rule1bRootDistance :=
    rule1bDistance_eq_stored (read := readR)
      (realizes_of_subtree realizesR (positionNode_spec (shapePositionEquiv hshape p)))
  rw [← leftStored, ← rightStored]
  exact (shapePositionEquiv_positionNode_rule1bDistance_eq hshape p).symm

/-- **Actual child-frame clause.**  Related cursors have child frames that are permutations of one
another along `ShapePositionCursorRelation`.  The sorted child at one slot of a position node and
the sorted child at the same slot of the corresponding node are related by the position at that
slot, so the sorted child source lists are pointwise related; the two actual evaluated child frames
are permutations of those sorted lists, and the permutation plumbing above reorders one side. -/
theorem shapePositionCursorRelation_children
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y) :
    ∃ frame,
      (input.executableLocalizedRerootChildren x).Perm frame ∧
        List.Forall₂ (ShapePositionCursorRelation hshape) frame
          (input.executableLocalizedRerootChildren y) := by
  obtain ⟨p, rfl, rfl⟩ := related
  have lengthEq : (positionNode p).children.length =
      (positionNode (shapePositionEquiv hshape p)).children.length :=
    (shapePositionEquiv_positionNode_children_length_eq hshape p).symm
  have sortedRelated : List.Forall₂
      (fun leftChild rightChild : LocalizedCumulativeDecoratedTree input carrierFuel =>
        ShapePositionCursorRelation hshape leftChild.source rightChild.source)
      (positionNode p).children
      (positionNode (shapePositionEquiv hshape p)).children :=
    forall₂_of_length_eq_of_getElem? lengthEq
      (fun slot leftChild leftLookup rightChild rightLookup => by
        obtain ⟨leftBound, leftGet⟩ := List.getElem?_eq_some_iff.mp leftLookup
        obtain ⟨rightBound, rightGet⟩ := List.getElem?_eq_some_iff.mp rightLookup
        refine ⟨positionChild p slot leftBound, ?_, ?_⟩
        · have nodeEq := positionNode_positionChild p slot leftBound
          have sourceStep : (positionNode (positionChild p slot leftBound)).source =
              ((positionNode p).children[slot]'leftBound).source :=
            congrArg (fun node => node.source) nodeEq
          have hit : ((positionNode p).children[slot]'leftBound).source = leftChild.source :=
            congrArg (fun node => node.source) leftGet
          simpa only [positionSource] using sourceStep.trans hit
        · have posEq : shapePositionEquiv hshape (positionChild p slot leftBound) =
              positionChild (shapePositionEquiv hshape p) slot rightBound :=
            position_ext (by simp only [positionChild_val, shapePositionEquiv_val])
          have nodeEq : positionNode
                (shapePositionEquiv hshape (positionChild p slot leftBound)) =
              ((positionNode (shapePositionEquiv hshape p)).children[slot]'rightBound) := by
            rw [posEq, positionNode_positionChild (shapePositionEquiv hshape p) slot rightBound]
          have hit : (((positionNode (shapePositionEquiv hshape p)).children[slot]'rightBound)).source =
              rightChild.source :=
            congrArg (fun node => node.source) rightGet
          calc positionSource (shapePositionEquiv hshape (positionChild p slot leftBound))
              = (positionNode
                  (shapePositionEquiv hshape (positionChild p slot leftBound))).source := rfl
            _ = (((positionNode (shapePositionEquiv hshape p)).children[slot]'rightBound)).source :=
                congrArg (fun node => node.source) nodeEq
            _ = rightChild.source := hit)
  have mapped : List.Forall₂ (ShapePositionCursorRelation hshape)
      ((positionNode p).children.map (fun child => child.source))
      ((positionNode (shapePositionEquiv hshape p)).children.map (fun child => child.source)) :=
    forall₂_map_source_of_forall₂ sortedRelated
  obtain ⟨leftPerm, _⟩ :=
    exists_sourcePerm_executable (read := readL)
      (realizes_of_subtree realizesL (positionNode_spec p))
  obtain ⟨rightPerm, _⟩ :=
    exists_sourcePerm_executable (read := readR)
      (realizes_of_subtree realizesR (positionNode_spec (shapePositionEquiv hshape p)))
  obtain ⟨frame, framePerm, frameRelated⟩ :=
    forall₂_exists_perm_of_perm_right rightPerm mapped
  exact ⟨frame, leftPerm.symm.trans framePerm.symm, frameRelated⟩

/-! ### The actual cumulative transport along the correspondence -/

/-- **Actual cumulative observable transport along the equal-shape position correspondence.**  For
two realised trees of equal shape, one shared reader and one stage, two actual cumulative builds at
the same fuel have the same comparison-visible observable whenever the reader returns
priority-equal labels at related cursors.  The three structural clauses are discharged above; the
priority clause is the only reader input, and it is exactly what a label-table correspondence
supplies.  Build success is not assumed. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (realizesL : LocalizedCumulativeTreeRealizes input read tL)
    (realizesR : LocalizedCumulativeTreeRealizes input read tR)
    (stage : LocalizedCumulativeRule45Stage)
    (priorityRelated : ∀ x y, ShapePositionCursorRelation hshape x y →
      localizedCumulativeRule45Priority stage (read x) =
        localizedCumulativeRule45Priority stage (read y)) :
    ∀ (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel},
      ShapePositionCursorRelation hshape x y →
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel x).map
          (input.localizedRerootCumulativeRule45Observable) =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel y).map
          (input.localizedRerootCumulativeRule45Observable) :=
  input.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related
    stage stage read read (ShapePositionCursorRelation hshape)
    (fun x y related =>
      shapePositionCursorRelation_atomLabel singleBonded acyclic hshape
        realizesL realizesR related)
    (fun x y related =>
      shapePositionCursorRelation_rootDistance hshape realizesL realizesR related)
    (fun x y related =>
      shapePositionCursorRelation_children hshape realizesL realizesR related)
    priorityRelated

/-- **SAME-reader form.**  When the two actual readers agree at related cursors, the priority
clause is automatic and the actual cumulative observables coincide at the same stage and fuel. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor_sameReader
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (realizesL : LocalizedCumulativeTreeRealizes input read tL)
    (realizesR : LocalizedCumulativeTreeRealizes input read tR)
    (readerEq : ∀ x y, ShapePositionCursorRelation hshape x y → read y = read x)
    (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel},
      ShapePositionCursorRelation hshape x y →
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel x).map
          (input.localizedRerootCumulativeRule45Observable) =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel y).map
          (input.localizedRerootCumulativeRule45Observable) :=
  buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor
    singleBonded acyclic hshape read realizesL realizesR stage
    (fun x y related => by rw [readerEq x y related])






theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor_reflectUppercase
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (readerReflect : ∀ x y, ShapePositionCursorRelation hshape x y →
      readR y = reflectUppercaseOptionalLabel (readL x))
    (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel},
      ShapePositionCursorRelation hshape x y →
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage readL fuel x).map
          (input.localizedRerootCumulativeRule45Observable) =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (reflectLocalizedCumulativeRule45Stage stage) readR fuel y).map
          (input.localizedRerootCumulativeRule45Observable) :=
  input.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related_reflectUppercase
    stage readL readR (ShapePositionCursorRelation hshape)
    (fun x y related =>
      shapePositionCursorRelation_atomLabel singleBonded acyclic hshape
        realizesL realizesR related)
    (fun x y related =>
      shapePositionCursorRelation_rootDistance hshape realizesL realizesR related)
    (fun x y related =>
      shapePositionCursorRelation_children hshape realizesL realizesR related)
    readerReflect

/-! ### Comparison-visible descriptor equality from actual builds -/

/-- The descriptor component of the comparison-visible observable of a cumulative key. -/
theorem localizedRerootCumulativeRule45Observable_descriptor
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.localizedRerootCumulativeRule45Observable key).descriptor = key.descriptor := rfl

/-- Two actual successful cumulative builds of related cursors have equal comparison-visible
descriptors.  This is the descriptor projection of the actual observable transport. -/
theorem descriptor_eq_of_shapePositionCursor_builds
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (realizesL : LocalizedCumulativeTreeRealizes input read tL)
    (realizesR : LocalizedCumulativeTreeRealizes input read tR)
    (stage : LocalizedCumulativeRule45Stage)
    (priorityRelated : ∀ x y, ShapePositionCursorRelation hshape x y →
      localizedCumulativeRule45Priority stage (read x) =
        localizedCumulativeRule45Priority stage (read y))
    (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage read fuel x = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage read fuel y = some rightKey) :
    leftKey.descriptor = rightKey.descriptor := by
  have transported :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor
      singleBonded acyclic hshape read realizesL realizesR stage priorityRelated fuel related
  simp only [leftBuilt, rightBuilt, Option.map_some] at transported
  exact congrArg (fun observable => observable.descriptor) (Option.some.inj transported)

/-- **SAME-reader descriptor equality of two actual builds.** -/
theorem descriptor_eq_of_shapePositionCursor_sameReader_builds
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (realizesL : LocalizedCumulativeTreeRealizes input read tL)
    (realizesR : LocalizedCumulativeTreeRealizes input read tR)
    (readerEq : ∀ x y, ShapePositionCursorRelation hshape x y → read y = read x)
    (stage : LocalizedCumulativeRule45Stage)
    (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage read fuel x = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage read fuel y = some rightKey) :
    leftKey.descriptor = rightKey.descriptor :=
  descriptor_eq_of_shapePositionCursor_builds singleBonded acyclic hshape read
    realizesL realizesR stage (fun x y related => by rw [readerEq x y related])
    fuel related leftBuilt rightBuilt

/-- **CROSSED-reference descriptor equality of two actual builds.**  The left key is built at
`stage` with the left reader and the right key at the uppercase reflection of `stage` with the
right reader; the conclusion is the comparison-visible descriptor equality that the mirror reading
requires. -/
theorem descriptor_eq_of_shapePositionCursor_reflectUppercase_builds
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (readerReflect : ∀ x y, ShapePositionCursorRelation hshape x y →
      readR y = reflectUppercaseOptionalLabel (readL x))
    (stage : LocalizedCumulativeRule45Stage)
    (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage readL fuel x = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (reflectLocalizedCumulativeRule45Stage stage) readR fuel y = some rightKey) :
    leftKey.descriptor = rightKey.descriptor := by
  have transported :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor_reflectUppercase
      singleBonded acyclic hshape realizesL realizesR readerReflect stage fuel related
  simp only [leftBuilt, rightBuilt, Option.map_some] at transported
  exact congrArg (fun observable => observable.descriptor) (Option.some.inj transported)

/-! ### Rule-5 stage bookkeeping for the crossed case -/

/-- The uppercase reflection of a Rule-5 stage is the Rule-5 stage of the swapped own Rule-4b
reference under the swapped common reference. -/
theorem reflectLocalizedRule5StageFor (own : Option RS) (common : RS) :
    reflectLocalizedCumulativeRule45Stage (localizedRule5StageFor own common) =
      localizedRule5StageFor (own.map RS.swap) (RS.swap common) := by
  cases own with
  | none => rfl
  | some reference => rfl

/-- On the two-valued `RS` reference type, distinct references are swaps of one another.  This is
the case split that turns the actual strict off-diagonal reference comparison of a prior tie into
the swapped-reference hypothesis of the crossed reading. -/
theorem eq_swap_of_ne {left right : RS} (different : left ≠ right) :
    right = RS.swap left := by
  cases left <;> cases right <;> simp_all [RS.swap]

/-- **Actual crossed Rule-5 common-reading descriptor equality.**  If the right own Rule-4b
reference is the swap of the left one, then the left common-`R` build and the right common-`S`
build of the paired Rule-5 readings have equal comparison-visible descriptors, given the reflected
reader correspondence at related cursors.  This is the per-pair `PriorTieMirrorReadings` component
in the crossed case. -/
theorem rule5_commonReading_descriptor_eq_of_shapePosition_crossed
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (readerReflect : ∀ x y, ShapePositionCursorRelation hshape x y →
      readR y = reflectUppercaseOptionalLabel (readL x))
    (reference rightReference : RS)
    (swapped : rightReference = RS.swap reference)
    (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor (some reference) .R) readL fuel x = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor (some rightReference) .S) readR fuel y = some rightKey) :
    leftKey.descriptor = rightKey.descriptor := by
  have stageEq : reflectLocalizedCumulativeRule45Stage
        (localizedRule5StageFor (some reference) .R) =
      localizedRule5StageFor (some rightReference) .S := by
    rw [reflectLocalizedRule5StageFor, swapped]
    -- `RS.swap .R` is definitionally `.S`: only the raw reference is left to identify
    rfl
  exact descriptor_eq_of_shapePositionCursor_reflectUppercase_builds singleBonded acyclic hshape
    realizesL realizesR readerReflect (localizedRule5StageFor (some reference) .R)
    fuel related leftBuilt (by rw [stageEq]; exact rightBuilt)

end TreeRereading

















section ActualSingletonRereading

open LocalizedCumulativeDecoratedTree

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- The reader value stored at a realised decorated node is the actual reader's value at that
node's actual source cursor. -/
theorem label_eq_read_source
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    tree.label = read tree.source := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize => rfl






theorem read_source_eq_of_shapePositionCursor
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input read tL)
    (realizesR : LocalizedCumulativeTreeRealizes input read tR)
    (f : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
    (labels : ∀ p : Position tL,
      (positionNode (shapePositionEquiv hshape p)).label = f (positionNode p).label)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y) :
    read y = f (read x) := by
  obtain ⟨p, rfl, rfl⟩ := related
  show read (positionNode (shapePositionEquiv hshape p)).source =
    f (read (positionNode p).source)
  rw [← label_eq_read_source
        (realizes_of_subtree realizesR (positionNode_spec (shapePositionEquiv hshape p))),
      ← label_eq_read_source (realizes_of_subtree realizesL (positionNode_spec p))]
  exact labels p

/-- The two actual tree sources are related cursors: the root position is the witness. -/
theorem shapePositionCursorRelation_sources
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    (sourceL : tL.source = leftCursor)
    (sourceR : tR.source = rightCursor) :
    ShapePositionCursorRelation hshape leftCursor rightCursor := by
  refine ⟨rootPosition tL, ?_, ?_⟩
  · rw [positionSource_rootPosition]
    exact sourceL
  · rw [shapePositionEquiv_rootPosition, positionSource_rootPosition]
    exact sourceR

/-- **CROSSED common-reading descriptor equality, general common references.**  The left build uses
the left own reference and the left common reference, the right build uses the swapped own reference
and the swapped common reference; the descriptors agree.  The specialization to `.R`/`.S` is the
first component of `MirrorReading`, the specialization to `.S`/`.R` is the second. -/
theorem rule5_commonReading_descriptor_eq_of_shapePosition_crossed_common
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tL tR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape tL = shape tR)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL tL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR tR)
    (readerReflect : ∀ x y, ShapePositionCursorRelation hshape x y →
      readR y = reflectUppercaseOptionalLabel (readL x))
    (ownLeft ownRight commonLeft commonRight : RS)
    (swappedOwn : ownRight = RS.swap ownLeft)
    (swappedCommon : commonRight = RS.swap commonLeft)
    (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel}
    (related : ShapePositionCursorRelation hshape x y)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor (some ownLeft) commonLeft) readL fuel x = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor (some ownRight) commonRight) readR fuel y = some rightKey) :
    leftKey.descriptor = rightKey.descriptor := by
  have stageEq : reflectLocalizedCumulativeRule45Stage
        (localizedRule5StageFor (some ownLeft) commonLeft) =
      localizedRule5StageFor (some ownRight) commonRight := by
    rw [reflectLocalizedRule5StageFor]
    simp only [Option.map_some]
    rw [← swappedOwn, ← swappedCommon]
  exact descriptor_eq_of_shapePositionCursor_reflectUppercase_builds singleBonded acyclic hshape
    realizesL realizesR readerReflect (localizedRule5StageFor (some ownLeft) commonLeft)
    fuel related leftBuilt (by rw [stageEq]; exact rightBuilt)

/-- **Actual singleton prior tie gives the per-pair mirror reading.**  Two actual successful
compound through-Rule-5 builds, each selecting exactly one own Rule-4b reference, whose actual
compound Rules-4b/4c priors tie, and whose two own references are distinct, have singleton Rule-5
reading lists satisfying the cross-addressed `MirrorReading` relation.  The distinctness is exactly
what makes the two own references swaps of one another on the two-valued `RS` type, so the right
common-`R`/`S` reads are the uppercase reflections of the left ones; the two cross-descriptor
equalities then follow from the actual observable transport along the realised equal-shape tree
correspondence. -/
theorem actual_singleton_prior_tie_mirrorReading
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (fuel : Nat) (leftReference rightReference : RS)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel rightCursor = some rightKey)
    (leftReferences : leftKey.prior.references = [leftReference])
    (rightReferences : rightKey.prior.references = [rightReference])
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.eq)
    (different : leftReference ≠ rightReference) :
    ∃ leftReading rightReading : input.LocalizedRerootRule5Reading,
      leftKey.rule5Readings = [leftReading] ∧
        rightKey.rule5Readings = [rightReading] ∧
          MirrorReading input leftReading rightReading := by
  obtain ⟨leftPriorReading, rightPriorReading, leftReading, rightReading,
    leftReadingsEq, rightReadingsEq, leftRule5Eq, rightRule5Eq,
    leftRule4bBuilt, rightRule4bBuilt, leftCommonRBuilt, rightCommonRBuilt,
    leftCommonSBuilt, rightCommonSBuilt, descriptorTie⟩ :=
    actual_singleton_prior_tie_builds input read leftCursor rightCursor fuel
      leftReference rightReference leftKey rightKey leftComputed rightComputed
      leftReferences rightReferences priorTie
  have leftRule4aBuilt :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey input read fuel
      leftCursor leftKey leftComputed
  have rightRule4aBuilt :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey input read fuel
      rightCursor rightKey rightComputed
  obtain ⟨rule4aTie, -, -, -⟩ :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      leftKey.prior rightKey.prior).mp priorTie
  obtain ⟨tL, tR, tLSource, tRSource, realizesL, realizesR, hshape, -, pathLabels⟩ :=
    actual_rule4b_key_tie_labelTableTransport input read readerSparse
      leftCursor rightCursor fuel fuel fuel fuel leftReference rightReference
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey
      leftPriorReading.rule4bKey rightPriorReading.rule4bKey
      leftRule4aBuilt rightRule4aBuilt leftRule4bBuilt rightRule4bBuilt
      rule4aTie descriptorTie
  have flagEq : referenceMirror leftReference rightReference = true :=
    referenceMirror_eq_true_iff.mpr different
  have labelsReflect : ∀ p : Position tL,
      (positionNode (shapePositionEquiv hshape p)).label =
        reflectUppercaseOptionalLabel (positionNode p).label := by
    intro p
    have rightLookup : compatibilitySubtreeAt? tR p.val =
        some (positionNode (shapePositionEquiv hshape p)) := by
      have spec := positionNode_spec (shapePositionEquiv hshape p)
      simpa [shapePositionEquiv_val] using spec
    have h := pathLabels p.val (positionNode p)
      (positionNode (shapePositionEquiv hshape p)) (positionNode_spec p) rightLookup
    rw [flagEq, labelMirror_true] at h
    exact h
  have readerReflect : ∀ x y, ShapePositionCursorRelation hshape x y →
      read y = reflectUppercaseOptionalLabel (read x) :=
    fun x y related =>
      read_source_eq_of_shapePositionCursor hshape realizesL realizesR
        reflectUppercaseOptionalLabel labelsReflect related
  have related : ShapePositionCursorRelation hshape leftCursor rightCursor :=
    shapePositionCursorRelation_sources hshape tLSource tRSource
  have swapped : rightReference = RS.swap leftReference := eq_swap_of_ne different
  have first : leftReading.commonR.descriptor = rightReading.commonS.descriptor :=
    rule5_commonReading_descriptor_eq_of_shapePosition_crossed singleBonded acyclic hshape
      realizesL realizesR readerReflect leftReference rightReference swapped fuel related
      leftCommonRBuilt rightCommonSBuilt
  have second : leftReading.commonS.descriptor = rightReading.commonR.descriptor :=
    rule5_commonReading_descriptor_eq_of_shapePosition_crossed_common singleBonded acyclic
      hshape realizesL realizesR readerReflect leftReference rightReference .S .R swapped rfl
      fuel related leftCommonSBuilt rightCommonRBuilt
  exact ⟨leftReading, rightReading, leftRule5Eq, rightRule5Eq, first, second⟩

/-- **List-level form of the singleton mirror reading.**  The same data give the actual
cross-addressed relation on the two actual Rule-5 reading lists, i.e. the per-pair shape consumed
by `PriorTieMirrorReadings`. -/
theorem actual_singleton_prior_tie_mirrorReadings
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (fuel : Nat) (leftReference rightReference : RS)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel rightCursor = some rightKey)
    (leftReferences : leftKey.prior.references = [leftReference])
    (rightReferences : rightKey.prior.references = [rightReference])
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.eq)
    (different : leftReference ≠ rightReference) :
    MirrorReadings input leftKey.rule5Readings rightKey.rule5Readings := by
  obtain ⟨leftReading, rightReading, leftEq, rightEq, mirror⟩ :=
    actual_singleton_prior_tie_mirrorReading input singleBonded acyclic read readerSparse
      leftCursor rightCursor fuel leftReference rightReference leftKey rightKey
      leftComputed rightComputed leftReferences rightReferences priorTie different
  rw [leftEq, rightEq]
  exact mirrorReadings_singleton_iff.mpr mirror






theorem actual_singleton_prior_tie_compound_eq_of_sameReference
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (fuel : Nat) (leftReference rightReference : RS)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel rightCursor = some rightKey)
    (leftReferences : leftKey.prior.references = [leftReference])
    (rightReferences : rightKey.prior.references = [rightReference])
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.eq)
    (sameReference : leftReference = rightReference) :
    input.compareLocalizedRerootCompoundRule45Keys leftKey rightKey = Ordering.eq := by
  cases sameReference
  obtain ⟨leftPriorReading, rightPriorReading, leftReading, rightReading,
    leftReadingsEq, rightReadingsEq, leftRule5Eq, rightRule5Eq,
    leftRule4bBuilt, rightRule4bBuilt, leftCommonRBuilt, rightCommonRBuilt,
    leftCommonSBuilt, rightCommonSBuilt, descriptorTie⟩ :=
    actual_singleton_prior_tie_builds input read leftCursor rightCursor fuel
      leftReference leftReference leftKey rightKey leftComputed rightComputed
      leftReferences rightReferences priorTie
  have leftRule4aBuilt :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey input read fuel
      leftCursor leftKey leftComputed
  have rightRule4aBuilt :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey input read fuel
      rightCursor rightKey rightComputed
  obtain ⟨rule4aTie, -, -, -⟩ :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      leftKey.prior rightKey.prior).mp priorTie
  obtain ⟨tL, tR, tLSource, tRSource, realizesL, realizesR, hshape, -, pathLabels⟩ :=
    actual_rule4b_key_tie_labelTableTransport input read readerSparse
      leftCursor rightCursor fuel fuel fuel fuel leftReference leftReference
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey
      leftPriorReading.rule4bKey rightPriorReading.rule4bKey
      leftRule4aBuilt rightRule4aBuilt leftRule4bBuilt rightRule4bBuilt
      rule4aTie descriptorTie
  have readerEq : ∀ x y, ShapePositionCursorRelation hshape x y → read y = read x := by
    have labelsRaw : ∀ p : Position tL,
        (positionNode (shapePositionEquiv hshape p)).label =
          labelMirror (referenceMirror leftReference leftReference) (positionNode p).label := by
      intro p
      have rightLookup : compatibilitySubtreeAt? tR p.val =
          some (positionNode (shapePositionEquiv hshape p)) := by
        have spec := positionNode_spec (shapePositionEquiv hshape p)
        simpa [shapePositionEquiv_val] using spec
      exact pathLabels p.val (positionNode p)
        (positionNode (shapePositionEquiv hshape p)) (positionNode_spec p) rightLookup
    intro x y related
    have h := read_source_eq_of_shapePositionCursor hshape realizesL realizesR
      (labelMirror (referenceMirror leftReference leftReference)) labelsRaw related
    simpa [referenceMirror, labelMirror] using h
  have related : ShapePositionCursorRelation hshape leftCursor rightCursor :=
    shapePositionCursorRelation_sources hshape tLSource tRSource
  have commonREq : leftReading.commonR.descriptor = rightReading.commonR.descriptor :=
    descriptor_eq_of_shapePositionCursor_sameReader_builds singleBonded acyclic hshape read
      realizesL realizesR readerEq (localizedRule5StageFor (some leftReference) .R)
      fuel related leftCommonRBuilt rightCommonRBuilt
  have readingsTie : input.compareLocalizedRerootCompoundRule5Readings .R
      leftKey.rule5Readings rightKey.rule5Readings = Ordering.eq := by
    rw [leftRule5Eq, rightRule5Eq]
    exact compareLocalizedRerootCompoundRule5Readings_eq_of_forall₂ input .R
      (List.Forall₂.cons (by simpa [localizedRerootRule5Descriptor] using commonREq)
        List.Forall₂.nil)
  exact compareLocalizedRerootCompoundRule45Keys_eq_of_prior_tie input leftKey rightKey
    priorTie readingsTie

/-- **Under actual off-diagonal strictness, a prior-tied pair cannot share its own Rule-4b
reference.**  A shared reference would give the complete compound comparator tie by the previous
theorem, contradicting off-diagonal strictness. -/
theorem actual_singleton_prior_tie_references_ne_of_offDiagonalStrict
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (fuel : Nat) (leftReference rightReference : RS)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel rightCursor = some rightKey)
    (leftReferences : leftKey.prior.references = [leftReference])
    (rightReferences : rightKey.prior.references = [rightReference])
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.eq)
    (offDiagonal : input.compareLocalizedRerootCompoundRule45Keys leftKey rightKey ≠
      Ordering.eq) :
    leftReference ≠ rightReference := by
  intro sameReference
  exact offDiagonal
    (actual_singleton_prior_tie_compound_eq_of_sameReference input singleBonded acyclic read
      readerSparse leftCursor rightCursor fuel leftReference rightReference leftKey rightKey
      leftComputed rightComputed leftReferences rightReferences priorTie sameReference)

/-- **The actual prior tie class has at most two members.**  Each distinct prior-tied pair has
distinct own Rule-4b references (previous theorem), and `RS` has only the two values `R` and `S`.
Three pairwise distinct indices tied with a common index would therefore carry three pairwise
distinct reference values, which is impossible. -/
theorem actual_priorTieClassAtMostTwo
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (cursors : Fin 4 → input.LocalizedRerootCursor carrierFuel)
    (fuel : Nat) (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ i, input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel (cursors i) = some (keys i))
    (referenceOf : Fin 4 → RS)
    (references : ∀ i, (keys i).prior.references = [referenceOf i])
    (separated : CompoundKeyOffDiagonalStrict input keys) :
    PriorTieClassAtMostTwo input keys := by
  have referencesNe : ∀ i j, i ≠ j → priorKeyTie input keys i j →
      referenceOf i ≠ referenceOf j := by
    intro i j different tied
    exact actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input
      singleBonded acyclic read readerSparse (cursors i) (cursors j) fuel
      (referenceOf i) (referenceOf j) (keys i) (keys j) (built i) (built j)
      (references i) (references j) tied (separated i j different)
  intro i j k hij hik
  by_contra h
  push_neg at h
  obtain ⟨hjkNe, hjiNe, hkiNe⟩ := h
  have hjiTie : priorKeyTie input keys j i := by
    haveI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
      input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
    exact Std.OrientedCmp.eq_symm (cmp := input.compareLocalizedRerootCompoundRule4bcKeys)
      (a := (keys i).prior) (b := (keys j).prior) hij
  have hjkTie : priorKeyTie input keys j k := by
    haveI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
      input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
    exact Std.TransCmp.eq_trans hjiTie hik
  have ijNe : referenceOf i ≠ referenceOf j :=
    referencesNe i j (Ne.symm hjiNe) hij
  have ikNe : referenceOf i ≠ referenceOf k :=
    referencesNe i k (Ne.symm hkiNe) hik
  have jkNe : referenceOf j ≠ referenceOf k :=
    referencesNe j k hjkNe hjkTie
  have sameJK : referenceOf j = referenceOf k := by
    cases hI : referenceOf i <;> cases hJ : referenceOf j <;>
      cases hK : referenceOf k <;> simp_all
  exact jkNe sameJK

/-- **Actual per-pair `PriorTieMirrorReadings`.**  Every distinct prior-tied pair of the actual
compound key family has cross-addressed common-`R`/common-`S` readings.  The pair's own references
are distinct by off-diagonal strictness, so the singleton readings of the pair satisfy the crossed
`MirrorReading` relation of the actual tree rereading. -/
theorem actual_priorTieMirrorReadings
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (cursors : Fin 4 → input.LocalizedRerootCursor carrierFuel)
    (fuel : Nat) (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ i, input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel (cursors i) = some (keys i))
    (referenceOf : Fin 4 → RS)
    (references : ∀ i, (keys i).prior.references = [referenceOf i])
    (separated : CompoundKeyOffDiagonalStrict input keys) :
    PriorTieMirrorReadings input keys := by
  intro i j different tied
  have referencesNe : referenceOf i ≠ referenceOf j :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input
      singleBonded acyclic read readerSparse (cursors i) (cursors j) fuel
      (referenceOf i) (referenceOf j) (keys i) (keys j) (built i) (built j)
      (references i) (references j) tied (separated i j different)
  obtain ⟨leftReading, rightReading, leftEq, rightEq, mirror⟩ :=
    actual_singleton_prior_tie_mirrorReading input singleBonded acyclic read readerSparse
      (cursors i) (cursors j) fuel (referenceOf i) (referenceOf j) (keys i) (keys j)
      (built i) (built j) (references i) (references j) tied referencesNe
  rw [leftEq, rightEq]
  exact mirrorReadings_singleton_iff.mpr mirror

end ActualSingletonRereading

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.list_exists_cons_of_ne_nil
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundRule45Keys_eq_prior_and_readings
assert_kernel_only TetraStereo.OneCenter.localizedRule5StageFor_priority_injective
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundRule5Readings_cons_cons_eq
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundRule45Keys_eq_head_descriptor
assert_kernel_only TetraStereo.OneCenter.compareSparseLayers_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundRule5Readings_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundRule45Keys_eq_of_prior_tie
assert_kernel_only TetraStereo.OneCenter.mirrorReadings_singleton_iff
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundRule5Readings_S_eq_of_R_eq_of_mirror
assert_kernel_only TetraStereo.OneCenter.localizedRule4bOwnStage
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule4bcReadingWithRead?_reference
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey_built
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule4bcReadingsWithRead?_member
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule4bcReadingsWithRead?_singleton
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule4bcKeyWithRead?_components
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule5ReadingWithRead?_components
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule5ReadingsWithRead?_singleton
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule45KeyWithRead?_components
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundRule4bReadings_singleton_eq
assert_kernel_only TetraStereo.OneCenter.actual_singleton_prior_tie_builds
assert_kernel_only TetraStereo.OneCenter.positionSource_officialNodeAtomLabel_eq
assert_kernel_only TetraStereo.OneCenter.rule1bDistance_eq_stored
assert_kernel_only TetraStereo.OneCenter.shape_children_eq_map
assert_kernel_only TetraStereo.OneCenter.forall₂_of_length_eq_of_getElem?
assert_kernel_only TetraStereo.OneCenter.forall₂_map_source_of_forall₂
assert_kernel_only TetraStereo.OneCenter.forall₂_exists_perm_of_perm_right
assert_kernel_only TetraStereo.OneCenter.ShapePositionCursorRelation
assert_kernel_only TetraStereo.OneCenter.shapePositionCursorRelation_atomLabel
assert_kernel_only TetraStereo.OneCenter.shapePositionCursorRelation_rootDistance
assert_kernel_only TetraStereo.OneCenter.shapePositionCursorRelation_children
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor_sameReader
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_shapePositionCursor_reflectUppercase
assert_kernel_only TetraStereo.OneCenter.localizedRerootCumulativeRule45Observable_descriptor
assert_kernel_only TetraStereo.OneCenter.descriptor_eq_of_shapePositionCursor_builds
assert_kernel_only TetraStereo.OneCenter.descriptor_eq_of_shapePositionCursor_sameReader_builds
assert_kernel_only TetraStereo.OneCenter.descriptor_eq_of_shapePositionCursor_reflectUppercase_builds
assert_kernel_only TetraStereo.OneCenter.reflectLocalizedRule5StageFor
assert_kernel_only TetraStereo.OneCenter.eq_swap_of_ne
assert_kernel_only TetraStereo.OneCenter.rule5_commonReading_descriptor_eq_of_shapePosition_crossed
assert_kernel_only TetraStereo.OneCenter.label_eq_read_source
assert_kernel_only TetraStereo.OneCenter.read_source_eq_of_shapePositionCursor
assert_kernel_only TetraStereo.OneCenter.shapePositionCursorRelation_sources
assert_kernel_only TetraStereo.OneCenter.rule5_commonReading_descriptor_eq_of_shapePosition_crossed_common
assert_kernel_only TetraStereo.OneCenter.actual_singleton_prior_tie_mirrorReading
assert_kernel_only TetraStereo.OneCenter.actual_singleton_prior_tie_mirrorReadings
assert_kernel_only TetraStereo.OneCenter.actual_singleton_prior_tie_compound_eq_of_sameReference
assert_kernel_only TetraStereo.OneCenter.actual_singleton_prior_tie_references_ne_of_offDiagonalStrict
assert_kernel_only TetraStereo.OneCenter.actual_priorTieClassAtMostTwo
assert_kernel_only TetraStereo.OneCenter.actual_priorTieMirrorReadings
