import TetraStereo.OneCenter.LocalizedPhysicalBranchKeyTransport
import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.OneCenter.LocalizedRule5SwapAndSignal
import TetraStereo.OneCenter.LocalizedConstitutionallyRigidFrameNormalization

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


































namespace TetraStereo.OneCenter

open RootedTetrahedralBranchSymmetry

namespace CertifiedLocalizedCIPInput

/-! ## The mirror map on the at-most-one own Rule-4b reference -/

/-- The reference map induced by physical mirror transport on an optional own Rule-4b reference.
Proper transport fixes it, mirror transport swaps `R` and `S`. -/
def localizedOwnReferenceMirror : Bool → Option RS → Option RS
  | false, own => own
  | true, own => own.map RS.swap

@[simp] theorem localizedOwnReferenceMirror_false (own : Option RS) :
    localizedOwnReferenceMirror false own = own := rfl

@[simp] theorem localizedOwnReferenceMirror_true (own : Option RS) :
    localizedOwnReferenceMirror true own = own.map RS.swap := rfl

/-- The cumulative stage at which one Rule-4b alternative compiles its Rule-4b key. -/
def localizedRule4bOwnStageOf : Option RS → LocalizedCumulativeRule45Stage
  | none => .rule4a
  | some reference => .rule4b reference

/-- The cumulative stage at which one Rule-4b/4c alternative compiles its Rule-4c key. -/
def localizedRule4cOwnStage : Option RS → LocalizedCumulativeRule45Stage
  | none => .rule4cNoReference
  | some reference => .rule4c reference

/-! ## The explicit reference-selection shape -/

/-- **The honest initial reference-selection shape.**  Either both sides select no own Rule-4b
reference at all, or the left selects exactly one reference and the right selects the physically
corresponding reference: the same one under proper transport, its swap under mirror transport.

This is a statement about the actual `references` field selected from the actual Rule-4a ranked
labels.  It is not a claim about labels, ranks or comparator outcomes. -/
def LocalizedPhysicalCompoundSelectorShape
    (left right : List RS) (mirror : Bool) : Prop :=
  (left = [] ∧ right = []) ∨
    ∃ reference : RS,
      left = [reference] ∧ right = [if mirror then RS.swap reference else reference]

/-- The selector shape exposes a single actual alternative on each side, related by the physical
mirror map. -/
theorem localizedPhysicalCompoundSelectorShape_alternatives
    {left right : List RS} {mirror : Bool}
    (shape : LocalizedPhysicalCompoundSelectorShape left right mirror) :
    ∃ leftOwn rightOwn : Option RS,
      localizedRule4bcReferenceAlternatives left = [leftOwn] ∧
        localizedRule4bcReferenceAlternatives right = [rightOwn] ∧
          rightOwn = localizedOwnReferenceMirror mirror leftOwn := by
  rcases shape with ⟨rfl, rfl⟩ | ⟨reference, rfl, rfl⟩
  · refine ⟨none, none, rfl, rfl, ?_⟩
    cases mirror <;> rfl
  · refine ⟨some reference,
      some (if mirror then RS.swap reference else reference), ?_, ?_, ?_⟩
    · simp [localizedRule4bcReferenceAlternatives]
    · simp [localizedRule4bcReferenceAlternatives]
    · cases mirror <;> rfl

/-- The selector shape preserves the actual reference-count priority. -/
theorem localizedPhysicalCompoundSelectorShape_referenceCountPriority
    {left right : List RS} {mirror : Bool}
    (shape : LocalizedPhysicalCompoundSelectorShape left right mirror) :
    constitutionalRule4bReferenceCountPriority left =
      constitutionalRule4bReferenceCountPriority right := by
  rcases shape with ⟨rfl, rfl⟩ | ⟨reference, rfl, rfl⟩
  · rfl
  · cases mirror <;> rfl

/-! ## Stage bookkeeping under the physical mirror map

All three identities are purely symbolic: they record that the uppercase reflection of an own
Rule-4b/4c stage, or of a Rule-5 common-reference stage, is the same stage re-indexed by the mirror
map on the own reference and (for Rule 5) by the swap of the common reference. -/

/-- The reflected own Rule-4b stage is the own Rule-4b stage of the mirrored reference. -/
theorem localizedRule4bOwnStage_mirror (mirror : Bool) (own : Option RS) :
    (if mirror then
        reflectLocalizedCumulativeRule45Stage (localizedRule4bOwnStageOf own)
      else localizedRule4bOwnStageOf own) =
    localizedRule4bOwnStageOf (localizedOwnReferenceMirror mirror own) := by
  cases mirror with
  | false => rfl
  | true => cases own <;> rfl

/-- The reflected own Rule-4c stage is the own Rule-4c stage of the mirrored reference. -/
theorem localizedRule4cOwnStage_mirror (mirror : Bool) (own : Option RS) :
    (if mirror then
        reflectLocalizedCumulativeRule45Stage (localizedRule4cOwnStage own)
      else localizedRule4cOwnStage own) =
    localizedRule4cOwnStage (localizedOwnReferenceMirror mirror own) := by
  cases mirror with
  | false => rfl
  | true => cases own <;> rfl

/-- The uppercase reflection of a Rule-5 stage is the Rule-5 stage of the swapped own Rule-4b
reference under the swapped common reference. -/
theorem reflectLocalizedRule5StageFor_swap (own : Option RS) (common : RS) :
    reflectLocalizedCumulativeRule45Stage (localizedRule5StageFor own common) =
      localizedRule5StageFor (own.map RS.swap) (RS.swap common) := by
  cases own with
  | none => rfl
  | some reference => rfl

/-- The reflected Rule-5 stage is the Rule-5 stage of the mirrored own reference under the mirrored
common reference. -/
theorem localizedRule5StageFor_mirror (mirror : Bool) (own : Option RS) (common : RS) :
    (if mirror then
        reflectLocalizedCumulativeRule45Stage (localizedRule5StageFor own common)
      else localizedRule5StageFor own common) =
    localizedRule5StageFor (localizedOwnReferenceMirror mirror own)
      (if mirror then RS.swap common else common) := by
  cases mirror with
  | false => rfl
  | true => exact reflectLocalizedRule5StageFor_swap own common

/-! ## Decomposition of the actual executable compound builders

All statements below are inversions of the *actual* executable `Option` builders.  They expose the
sub-computations that the success value was assembled from; no desired sub-key is supplied. -/

/-- A successful per-reference Rule-4b/4c reading exposes the reference it was compiled for and both
of its actual cumulative sub-builds, at that reference's own stages and at the same fuel. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    reading.reference? = reference ∧
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule4bOwnStageOf reference) read fuel cursor = some reading.rule4bKey ∧
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule4cOwnStage reference) read fuel cursor = some reading.rule4cKey := by
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
              exact ⟨rfl, rule4bComputed, rule4cComputed⟩
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
              exact ⟨rfl, rule4bComputed, rule4cComputed⟩

/-- A successful singleton alternative list exposes exactly one reading built at that alternative. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (alternative : Option RS)
    (readings : List input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadingsWithRead?
      read fuel cursor [alternative] = some readings) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      readings = [reading] ∧
        input.buildLocalizedRerootRule4bcReadingWithRead?
          read fuel cursor alternative = some reading := by
  cases headComputed : input.buildLocalizedRerootRule4bcReadingWithRead?
      read fuel cursor alternative with
  | none => simp [buildLocalizedRerootRule4bcReadingsWithRead?, headComputed] at computed
  | some reading =>
      simp [buildLocalizedRerootRule4bcReadingsWithRead?, headComputed] at computed
      refine ⟨reading, ?_, ?_⟩
      · simpa [eq_comm] using computed.symm
      · rfl

/-- A successful compound Rules-4b/4c build exposes its actual Rule-4a sub-build, its exact
reference selection, the exact reference-count priority, and its complete reading list. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        .rule4a read fuel cursor = some key.rule4aKey ∧
      key.references =
        localizedRule4bReferencesFromRankedLabels key.rule4aKey.rankedLabels ∧
        key.referenceCountPriority =
          constitutionalRule4bReferenceCountPriority key.references ∧
          input.buildLocalizedRerootRule4bcReadingsWithRead? read fuel cursor
              (localizedRule4bcReferenceAlternatives key.references) =
            some key.readings := by
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
          have keyEq : key = {
              rule4aKey := rule4aKey
              references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
              referenceCountPriority :=
                constitutionalRule4bReferenceCountPriority
                  (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)
              readings := readings } := by
            simpa [rule4aComputed, readingsComputed] using computed.symm
          subst key
          refine ⟨?_, ?_, ?_, ?_⟩
          · rfl
          · rfl
          · rfl
          · first | rfl | exact readingsComputed

/-- A successful singleton prior list exposes exactly one Rule-5 reading built from that prior. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (readings : List input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5ReadingsWithRead?
      read fuel cursor [prior] = some readings) :
    ∃ reading : input.LocalizedRerootRule5Reading,
      readings = [reading] ∧
        input.buildLocalizedRerootRule5ReadingWithRead?
          read fuel cursor prior = some reading := by
  cases headComputed : input.buildLocalizedRerootRule5ReadingWithRead?
      read fuel cursor prior with
  | none => simp [buildLocalizedRerootRule5ReadingsWithRead?, headComputed] at computed
  | some reading =>
      simp [buildLocalizedRerootRule5ReadingsWithRead?, headComputed] at computed
      refine ⟨reading, ?_, ?_⟩
      · simpa [eq_comm] using computed.symm
      · rfl

/-- A successful Rule-5 reading exposes its prior alternative and both actual common-reference
sub-builds, at the Rule-5 stages fixed by that prior's own reference. -/
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
          (localizedRule5StageFor prior.reference? .R) read fuel cursor =
        some reading.commonR ∧
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?
            (localizedRule5StageFor prior.reference? .S) read fuel cursor =
          some reading.commonS := by
  unfold buildLocalizedRerootRule5ReadingWithRead? at computed
  cases commonRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor prior.reference? .R) read fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      cases commonSComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .S) read fuel cursor with
      | none => simp [commonRComputed, commonSComputed] at computed
      | some commonS =>
          simp [commonRComputed, commonSComputed] at computed
          subst reading
          exact ⟨rfl, rfl, rfl⟩

/-- A successful through-Rule-5 compound build exposes its actual prior Rules-4b/4c sub-build and
its complete Rule-5 reading list at the same fuel. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read fuel cursor =
        some key.prior ∧
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
          subst key
          refine ⟨?_, ?_⟩
          · rfl
          · first | rfl | exact readingsComputed

/-! ## Singleton reading-list comparisons

The canonical reading lists have exactly one element in the selector shapes considered here, so the
list comparator reduces to the addressed descriptor comparator of that single element. -/

/-- The actual Rule-4b reading-list comparison of two singleton reading lists is the addressed
descriptor comparison of their Rule-4b keys. -/
theorem compareLocalizedRerootCompoundRule4bReadings_singleton_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootCompoundRule4bReadings [left] [right] = Ordering.eq ↔
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.rule4bKey.descriptor right.rule4bKey.descriptor = Ordering.eq := by
  simp only [compareLocalizedRerootCompoundRule4bReadings, List.compareLex_cons_cons,
    compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey, Ordering.then_eq_eq,
    List.compareLex_nil_nil, and_true]

/-- The actual Rule-4c reading-list comparison of two singleton reading lists is the addressed
descriptor comparison of their Rule-4c keys. -/
theorem compareLocalizedRerootCompoundRule4cReadings_singleton_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootCompoundRule4cReadings [left] [right] = Ordering.eq ↔
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.rule4cKey.descriptor right.rule4cKey.descriptor = Ordering.eq := by
  simp only [compareLocalizedRerootCompoundRule4cReadings, List.compareLex_cons_cons,
    Ordering.byKey, Ordering.then_eq_eq, List.compareLex_nil_nil, and_true]

/-! ## Comparison-visible projection of actual cumulative builds -/

/-- Two actual successful *production* cumulative builds at related cursors whose comparison-visible
observables are transported have equal comparison-visible observables. -/
theorem localizedRerootCumulativeRule45Observable_eq_of_transported_builds
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    {leftStage rightStage : LocalizedCumulativeRule45Stage}
    (transported :
      (input.buildLocalizedRerootCumulativeRule45Key? leftStage target view fuel
          leftCursor).map input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key? rightStage target view fuel
          rightCursor).map input.localizedRerootCumulativeRule45Observable)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45Key?
      leftStage target view fuel leftCursor = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45Key?
      rightStage target view fuel rightCursor = some rightKey) :
    input.localizedRerootCumulativeRule45Observable leftKey =
      input.localizedRerootCumulativeRule45Observable rightKey := by
  rw [leftBuilt, rightBuilt] at transported
  simp only [Option.map_some] at transported
  exact Option.some.inj transported

/-- Same conclusion for actual *reader-parametric* builds: the production builds they denote are
the actual `localizedDependencyLabel` builds at the same fuel. -/
theorem localizedRerootCumulativeRule45Observable_eq_of_transported_withRead_builds
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    {leftStage rightStage : LocalizedCumulativeRule45Stage}
    (transported :
      (input.buildLocalizedRerootCumulativeRule45Key? leftStage target view fuel
          leftCursor).map input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key? rightStage target view fuel
          rightCursor).map input.localizedRerootCumulativeRule45Observable)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      leftStage (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        leftCursor = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      rightStage (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        rightCursor = some rightKey) :
    input.localizedRerootCumulativeRule45Observable leftKey =
      input.localizedRerootCumulativeRule45Observable rightKey := by
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    leftStage target view fuel leftCursor] at transported
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    rightStage target view fuel rightCursor] at transported
  rw [leftBuilt, rightBuilt] at transported
  simp only [Option.map_some] at transported
  exact Option.some.inj transported

/-- Descriptor component of the preceding observable equality. -/
theorem descriptor_eq_of_transported_withRead_builds
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    {leftStage rightStage : LocalizedCumulativeRule45Stage}
    (transported :
      (input.buildLocalizedRerootCumulativeRule45Key? leftStage target view fuel
          leftCursor).map input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key? rightStage target view fuel
          rightCursor).map input.localizedRerootCumulativeRule45Observable)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      leftStage (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        leftCursor = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      rightStage (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        rightCursor = some rightKey) :
    leftKey.descriptor = rightKey.descriptor := by
  have observableEq :=
    input.localizedRerootCumulativeRule45Observable_eq_of_transported_withRead_builds
      target view transported leftBuilt rightBuilt
  exact congrArg (fun observed => observed.descriptor) observableEq

/-! ## Transported descriptor equalities at the own and common reference stages -/

/-- Own-reference stage transport: a mirrored own reference turns the transported stage equality
into the exact descriptor equality of the two Rule-4b (or Rule-4c) sub-builds. -/
theorem descriptor_eq_of_transported_ownStage
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    (mirror : Bool)
    (transported : ∀ stage : LocalizedCumulativeRule45Stage,
      (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel leftCursor).map
          input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key?
          (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
          target view fuel rightCursor).map
          input.localizedRerootCumulativeRule45Observable)
    (stageOf : Option RS → LocalizedCumulativeRule45Stage)
    (stageOfMirror : ∀ own : Option RS,
      (if mirror then reflectLocalizedCumulativeRule45Stage (stageOf own) else stageOf own) =
        stageOf (localizedOwnReferenceMirror mirror own))
    {leftOwn rightOwn : Option RS}
    (ownEq : rightOwn = localizedOwnReferenceMirror mirror leftOwn)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (stageOf leftOwn) (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        leftCursor = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (stageOf rightOwn) (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        rightCursor = some rightKey) :
    leftKey.descriptor = rightKey.descriptor := by
  have transportedHere := transported (stageOf leftOwn)
  rw [stageOfMirror leftOwn, ← ownEq] at transportedHere
  exact input.descriptor_eq_of_transported_withRead_builds
    target view transportedHere leftBuilt rightBuilt

/-- Crossed common-reference transport: a mirrored own reference and a swapped common reference turn
the transported stage equality into the exact crossed descriptor equality. -/
theorem descriptor_eq_of_transported_commonStage_crossed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    (transported : ∀ stage : LocalizedCumulativeRule45Stage,
      (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel leftCursor).map
          input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key?
          (reflectLocalizedCumulativeRule45Stage stage)
          target view fuel rightCursor).map
          input.localizedRerootCumulativeRule45Observable)
    {leftOwn rightOwn : Option RS}
    (ownEq : rightOwn = leftOwn.map RS.swap)
    {commonLeft commonRight : RS}
    (commonEq : commonRight = RS.swap commonLeft)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor leftOwn commonLeft)
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        leftCursor = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor rightOwn commonRight)
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        rightCursor = some rightKey) :
    leftKey.descriptor = rightKey.descriptor := by
  have transportedHere := transported (localizedRule5StageFor leftOwn commonLeft)
  rw [reflectLocalizedRule5StageFor_swap, ← ownEq, ← commonEq] at transportedHere
  exact input.descriptor_eq_of_transported_withRead_builds
    target view transportedHere leftBuilt rightBuilt

/-- The proper common-reference case: both sides compile the same stage. -/
theorem descriptor_eq_of_transported_commonStage_same
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    (transported : ∀ stage : LocalizedCumulativeRule45Stage,
      (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel leftCursor).map
          input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key? stage
          target view fuel rightCursor).map
          input.localizedRerootCumulativeRule45Observable)
    {own : Option RS} {common : RS}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor own common)
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        leftCursor = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor own common)
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        rightCursor = some rightKey) :
    leftKey.descriptor = rightKey.descriptor :=
  input.descriptor_eq_of_transported_withRead_builds target view
    (transported (localizedRule5StageFor own common)) leftBuilt rightBuilt

/-- Common-reference transport at an arbitrary left common reference: the right side compiles the
physically corresponding stage, whose common reference is the swap exactly in the mirror case.  The
own-reference relation is supplied as an equation on the actual references; the stage identity is
discharged locally. -/
theorem descriptor_eq_of_transported_commonStage
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    (mirror : Bool)
    (transported : ∀ stage : LocalizedCumulativeRule45Stage,
      (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel leftCursor).map
          input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key?
          (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
          target view fuel rightCursor).map
          input.localizedRerootCumulativeRule45Observable)
    {leftOwn rightOwn : Option RS}
    (ownEq : rightOwn = localizedOwnReferenceMirror mirror leftOwn)
    (commonLeft : RS)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor leftOwn commonLeft)
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        leftCursor = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor rightOwn
        (if mirror then RS.swap commonLeft else commonLeft))
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel
        rightCursor = some rightKey) :
    leftKey.descriptor = rightKey.descriptor := by
  have transportedHere := transported (localizedRule5StageFor leftOwn commonLeft)
  rw [localizedRule5StageFor_mirror, ← ownEq] at transportedHere
  exact input.descriptor_eq_of_transported_withRead_builds
    target view transportedHere leftBuilt rightBuilt

/-! ## The relation returned for the actual singleton common readings -/

/-- The common-reference reading relation exposed by physical transport: same-channel descriptor
equality under proper transport, crossed (`R` with `S`) descriptor equality under mirror transport. -/
def LocalizedCompoundCommonReadingRelation
    (input : CertifiedLocalizedCIPInput) (mirror : Bool)
    (left right : input.LocalizedRerootRule5Reading) : Prop :=
  if mirror then LocalizedRule5SwapAndSignal.MirrorReading input left right
  else
    left.commonR.descriptor = right.commonR.descriptor ∧
      left.commonS.descriptor = right.commonS.descriptor







theorem localizedCompoundPriorTie_and_commonReading_of_transported
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    (mirror : Bool)
    (transported : ∀ stage : LocalizedCumulativeRule45Stage,
      (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel leftCursor).map
          input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key?
          (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
          target view fuel rightCursor).map
          input.localizedRerootCumulativeRule45Observable)
    {leftKey rightKey : input.LocalizedRerootCompoundRule45Key}
    (leftBuilt : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel leftCursor =
        some leftKey)
    (rightBuilt : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel rightCursor =
        some rightKey)
    (shape : LocalizedPhysicalCompoundSelectorShape
      leftKey.prior.references rightKey.prior.references mirror) :
    ∃ (leftPriorReading rightPriorReading : input.LocalizedRerootRule4bcReading)
      (leftReading rightReading : input.LocalizedRerootRule5Reading),
      leftKey.prior.readings = [leftPriorReading] ∧
        rightKey.prior.readings = [rightPriorReading] ∧
          leftKey.rule5Readings = [leftReading] ∧
            rightKey.rule5Readings = [rightReading] ∧
              leftReading.prior = leftPriorReading ∧
                rightReading.prior = rightPriorReading ∧
                  input.compareLocalizedRerootCompoundRule4bcKeys
                    leftKey.prior rightKey.prior = Ordering.eq ∧
                    LocalizedCompoundCommonReadingRelation input mirror leftReading rightReading := by
  classical
  -- Decompose both actual through-Rule-5 builds.
  obtain ⟨leftPriorBuilt, leftRule5Built⟩ :=
    input.buildLocalizedRerootCompoundRule45KeyWithRead?_components
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel leftCursor leftKey leftBuilt
  obtain ⟨rightPriorBuilt, rightRule5Built⟩ :=
    input.buildLocalizedRerootCompoundRule45KeyWithRead?_components
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel rightCursor rightKey rightBuilt
  -- Decompose both actual Rules-4b/4c builds.
  obtain ⟨leftRule4aBuilt, leftReferences, leftCount, leftReadingsBuilt⟩ :=
    input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_components
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel leftCursor leftKey.prior leftPriorBuilt
  obtain ⟨rightRule4aBuilt, rightReferences, rightCount, rightReadingsBuilt⟩ :=
    input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_components
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel rightCursor rightKey.prior rightPriorBuilt
  -- The shape gives one alternative per side, related by the mirror map.
  obtain ⟨leftOwn, rightOwn, leftAlternatives, rightAlternatives, rightOwnEq⟩ :=
    localizedPhysicalCompoundSelectorShape_alternatives shape
  rw [leftAlternatives] at leftReadingsBuilt
  rw [rightAlternatives] at rightReadingsBuilt
  -- Extract the unique actual prior reading on each side.
  obtain ⟨leftPriorReading, leftReadingsEq, leftPriorReadingBuilt⟩ :=
    input.buildLocalizedRerootRule4bcReadingsWithRead?_singleton
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel leftCursor leftOwn leftKey.prior.readings leftReadingsBuilt
  obtain ⟨rightPriorReading, rightReadingsEq, rightPriorReadingBuilt⟩ :=
    input.buildLocalizedRerootRule4bcReadingsWithRead?_singleton
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel rightCursor rightOwn rightKey.prior.readings rightReadingsBuilt
  -- Expose the actual own-reference cumulative sub-builds.
  obtain ⟨leftReferenceEq, left4bBuilt, left4cBuilt⟩ :=
    input.buildLocalizedRerootRule4bcReadingWithRead?_components
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel leftCursor leftOwn leftPriorReading leftPriorReadingBuilt
  obtain ⟨rightReferenceEq, right4bBuilt, right4cBuilt⟩ :=
    input.buildLocalizedRerootRule4bcReadingWithRead?_components
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel rightCursor rightOwn rightPriorReading rightPriorReadingBuilt
  -- Extract the unique actual Rule-5 reading on each side.
  rw [leftReadingsEq] at leftRule5Built
  rw [rightReadingsEq] at rightRule5Built
  obtain ⟨leftReading, leftRule5Eq, leftReadingBuilt⟩ :=
    input.buildLocalizedRerootRule5ReadingsWithRead?_singleton
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel leftCursor leftPriorReading leftKey.rule5Readings leftRule5Built
  obtain ⟨rightReading, rightRule5Eq, rightReadingBuilt⟩ :=
    input.buildLocalizedRerootRule5ReadingsWithRead?_singleton
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel rightCursor rightPriorReading rightKey.rule5Readings rightRule5Built
  -- Expose both actual common-reference sub-builds.
  obtain ⟨leftReadingPriorEq, leftCommonRBuilt, leftCommonSBuilt⟩ :=
    input.buildLocalizedRerootRule5ReadingWithRead?_components
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel leftCursor leftPriorReading leftReading leftReadingBuilt
  obtain ⟨rightReadingPriorEq, rightCommonRBuilt, rightCommonSBuilt⟩ :=
    input.buildLocalizedRerootRule5ReadingWithRead?_components
      (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel rightCursor rightPriorReading rightReading rightReadingBuilt
  have referenceOwnEq : rightPriorReading.reference? =
      localizedOwnReferenceMirror mirror leftPriorReading.reference? := by
    rw [rightReferenceEq, rightOwnEq, ← leftReferenceEq]
  -- Rule 4a gate: transported observable equality.
  have transported4a :
      (input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel
          leftCursor).map input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel
          rightCursor).map input.localizedRerootCumulativeRule45Observable := by
    have h := transported .rule4a
    rw [show (if mirror then
          reflectLocalizedCumulativeRule45Stage .rule4a else .rule4a) = .rule4a from by
        cases mirror <;> rfl] at h
    exact h
  have rule4aObservable :=
    input.localizedRerootCumulativeRule45Observable_eq_of_transported_withRead_builds
      target view transported4a leftRule4aBuilt rightRule4aBuilt
  have rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey = Ordering.eq :=
    (input.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey).mpr rule4aObservable
  -- Own Rule-4b gate: descriptor equality.
  have rule4bDescriptor : leftPriorReading.rule4bKey.descriptor =
      rightPriorReading.rule4bKey.descriptor :=
    input.descriptor_eq_of_transported_ownStage target view mirror transported
      localizedRule4bOwnStageOf (localizedRule4bOwnStage_mirror mirror)
      rightOwnEq left4bBuilt right4bBuilt
  -- Own Rule-4c gate: descriptor equality.
  have rule4cDescriptor : leftPriorReading.rule4cKey.descriptor =
      rightPriorReading.rule4cKey.descriptor :=
    input.descriptor_eq_of_transported_ownStage target view mirror transported
      localizedRule4cOwnStage (localizedRule4cOwnStage_mirror mirror)
      rightOwnEq left4cBuilt right4cBuilt
  -- Rule-4b reading-list gate.
  have rule4bTie : input.compareLocalizedRerootCompoundRule4bReadings
      leftKey.prior.readings rightKey.prior.readings = Ordering.eq := by
    rw [leftReadingsEq, rightReadingsEq]
    have descriptorTie : OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority
        leftPriorReading.rule4bKey.descriptor
        rightPriorReading.rule4bKey.descriptor = Ordering.eq := by
      rw [← rule4bDescriptor]
      exact CompilerProjectionFidelity.compareSparseLayers_self
        compareLocalizedCumulativeRule45Priority
        (fun value => compareLocalizedCumulativeRule45Priority_self value)
        leftPriorReading.rule4bKey.descriptor
    exact (input.compareLocalizedRerootCompoundRule4bReadings_singleton_eq
      leftPriorReading rightPriorReading).mpr descriptorTie
  -- Rule-4c reading-list gate.
  have rule4cTie : input.compareLocalizedRerootCompoundRule4cReadings
      leftKey.prior.readings rightKey.prior.readings = Ordering.eq := by
    rw [leftReadingsEq, rightReadingsEq]
    have descriptorTie : OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority
        leftPriorReading.rule4cKey.descriptor
        rightPriorReading.rule4cKey.descriptor = Ordering.eq := by
      rw [← rule4cDescriptor]
      exact CompilerProjectionFidelity.compareSparseLayers_self
        compareLocalizedCumulativeRule45Priority
        (fun value => compareLocalizedCumulativeRule45Priority_self value)
        leftPriorReading.rule4cKey.descriptor
    exact (input.compareLocalizedRerootCompoundRule4cReadings_singleton_eq
      leftPriorReading rightPriorReading).mpr descriptorTie
  -- Reference-count gate.
  have countTie : compare leftKey.prior.referenceCountPriority
      rightKey.prior.referenceCountPriority = Ordering.eq := by
    rw [leftCount, rightCount]
    rw [localizedPhysicalCompoundSelectorShape_referenceCountPriority shape]
    exact Std.ReflOrd.compare_self
  -- The complete four-gate prior tie.
  have priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.eq :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      leftKey.prior rightKey.prior).mpr
      ⟨rule4aTie, countTie, rule4bTie, rule4cTie⟩
  -- Common-reference readings, split by the transport orientation.
  cases mirror with
  | false =>
      have transportedSame : ∀ stage : LocalizedCumulativeRule45Stage,
          (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel
              leftCursor).map input.localizedRerootCumulativeRule45Observable =
            (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel
              rightCursor).map input.localizedRerootCumulativeRule45Observable := by
        intro stage
        simpa using transported stage
      have commonR : leftReading.commonR.descriptor = rightReading.commonR.descriptor :=
        input.descriptor_eq_of_transported_commonStage target view false transportedSame
          referenceOwnEq .R leftCommonRBuilt rightCommonRBuilt
      have commonS : leftReading.commonS.descriptor = rightReading.commonS.descriptor :=
        input.descriptor_eq_of_transported_commonStage target view false transportedSame
          referenceOwnEq .S leftCommonSBuilt rightCommonSBuilt
      exact ⟨leftPriorReading, rightPriorReading, leftReading, rightReading,
        leftReadingsEq, rightReadingsEq, leftRule5Eq, rightRule5Eq, leftReadingPriorEq,
        rightReadingPriorEq, priorTie, ⟨commonR, commonS⟩⟩
  | true =>
      have transportedReflect : ∀ stage : LocalizedCumulativeRule45Stage,
          (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel
              leftCursor).map input.localizedRerootCumulativeRule45Observable =
            (input.buildLocalizedRerootCumulativeRule45Key?
              (reflectLocalizedCumulativeRule45Stage stage) target view fuel
              rightCursor).map input.localizedRerootCumulativeRule45Observable := by
        intro stage
        simpa using transported stage
      have commonR : leftReading.commonR.descriptor = rightReading.commonS.descriptor :=
        input.descriptor_eq_of_transported_commonStage target view true transportedReflect
          referenceOwnEq .R leftCommonRBuilt rightCommonSBuilt
      have commonS : leftReading.commonS.descriptor = rightReading.commonR.descriptor :=
        input.descriptor_eq_of_transported_commonStage target view true transportedReflect
          referenceOwnEq .S leftCommonSBuilt rightCommonRBuilt
      exact ⟨leftPriorReading, rightPriorReading, leftReading, rightReading,
        leftReadingsEq, rightReadingsEq, leftRule5Eq, rightRule5Eq, leftReadingPriorEq,
        rightReadingPriorEq, priorTie, ⟨commonR, commonS⟩⟩

/-! ## Frame-level physical form

The physical keys below are the actual production keys `compoundKeyAt` at the actual final-root
frame slots.  `localizedPhysicalCompoundFrameView` is the actual reference-state dependency view. -/

/-- The actual reference-state dependency view at the physical top occurrence. -/
noncomputable def localizedPhysicalCompoundFrameView
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (c : m.Center) :
    input.certified.LocalizedDependencyView
      (localizedPhysicalTopOccurrence input m graphEq c) :=
  input.certified.localizedDependencyView (LocalizedUniversalReference.referenceState input)
    (localizedPhysicalTopOccurrence input m graphEq c)

/-- The actual production compound key at one slot of a computed four-ligand frame, at the
production occurrence fuel. -/
noncomputable def localizedPhysicalCompoundFrameKeyOfComputed
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (c : m.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input m graphEq c) = some frame)
    (index : Fin 4) : input.certified.LocalizedRerootCompoundRule45Key :=
  frame.compoundKeyAt input.certified
    (localizedPhysicalTopOccurrence input m graphEq c)
    (localizedPhysicalCompoundFrameView input m graphEq c)
    (input.certified.localizedOccurrenceFourLigandFrame?_sound
      (localizedPhysicalTopOccurrence input m graphEq c) frame frameComputed)
    index






theorem localizedPhysicalCompoundFrame_priorTie_and_commonReading
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (c : m.Center) (e : m.Aut)
    (i j : Fin 4) (mirror : Bool)
    (centerFixed : m.centerPerm e c = c)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input m domain.graphEq c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (m.ligandAtomAt c (alpha index)))
    (correspondence : LocalizedAutCursorCorrespondence input.certified
      (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
      (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)))
    (shape : LocalizedPhysicalCompoundSelectorShape
      ((localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
        frameComputed (alpha.symm i)).prior.references)
      ((localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
        frameComputed (alpha.symm j)).prior.references)
      mirror) :
    ∃ (leftReading rightReading : input.certified.LocalizedRerootRule5Reading),
      (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
        frameComputed (alpha.symm i)).rule5Readings = [leftReading] ∧
        (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
          frameComputed (alpha.symm j)).rule5Readings = [rightReading] ∧
          input.certified.compareLocalizedRerootCompoundRule4bcKeys
              (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                frameComputed (alpha.symm i)).prior
              (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                frameComputed (alpha.symm j)).prior = Ordering.eq ∧
            LocalizedCompoundCommonReadingRelation input.certified mirror
              leftReading rightReading := by
  classical
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  let view := localizedPhysicalCompoundFrameView input m domain.graphEq c
  let derived := input.certified.localizedOccurrenceFourLigandFrame?_sound
    target frame frameComputed
  let leftKey := frame.compoundKeyAt input.certified target view derived (alpha.symm i)
  let rightKey := frame.compoundKeyAt input.certified target view derived (alpha.symm j)
  have shapeHere : LocalizedPhysicalCompoundSelectorShape
      leftKey.prior.references rightKey.prior.references mirror := by
    simpa only [leftKey, rightKey, localizedPhysicalCompoundFrameKeyOfComputed, target, view,
      derived] using shape
  have leftBuilt : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor => input.certified.localizedDependencyLabel target view cursor)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt (alpha.symm i)) = some leftKey := by
    rw [input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
      target view (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt (alpha.symm i))]
    exact frame.compoundKeyAt_built input.certified target view derived (alpha.symm i)
  have rightBuilt : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor => input.certified.localizedDependencyLabel target view cursor)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt (alpha.symm j)) = some rightKey := by
    rw [input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
      target view (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt (alpha.symm j))]
    exact frame.compoundKeyAt_built input.certified target view derived (alpha.symm j)
  have relatedStart : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
      (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j))
      (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) :=
    ⟨correspondence, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  have transported : ∀ stage : LocalizedCumulativeRule45Stage,
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage target view
          (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
          (frame.cursorAt (alpha.symm i))).map
        (input.certified.localizedRerootCumulativeRule45Observable) =
      (input.certified.buildLocalizedRerootCumulativeRule45Key?
          (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
          target view (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
          (frame.cursorAt (alpha.symm j))).map
        (input.certified.localizedRerootCumulativeRule45Observable) := by
    intro stage
    cases mirror with
    | false =>
        exact localizedPhysicalBranchRelation_productionKey_observable_eq_proper_globalDomain
          input singleBonded acyclic noDouble m cfg c e i j centerFixed
          (fun d h => by simpa using signLaw d h) domain coverage frame alpha
          frameComputed slotSpec stage
          (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
          (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) relatedStart
    | true =>
        exact localizedPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
          input singleBonded acyclic noDouble m cfg c e i j centerFixed
          (fun d h => by simpa using signLaw d h) domain coverage frame alpha
          frameComputed slotSpec stage
          (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
          (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) relatedStart
  obtain ⟨leftPriorReading, rightPriorReading, leftReading, rightReading,
    leftPriorReadingsEq, rightPriorReadingsEq, leftRule5Eq, rightRule5Eq,
    leftReadingPriorEq, rightReadingPriorEq, priorTie, relation⟩ :=
    input.certified.localizedCompoundPriorTie_and_commonReading_of_transported
      target view mirror transported leftBuilt rightBuilt shapeHere
  refine ⟨leftReading, rightReading, ?_, ?_, ?_, relation⟩
  · simpa only [leftKey, localizedPhysicalCompoundFrameKeyOfComputed, target, view,
      derived] using leftRule5Eq
  · simpa only [rightKey, localizedPhysicalCompoundFrameKeyOfComputed, target, view,
      derived] using rightRule5Eq
  · simpa only [leftKey, rightKey, localizedPhysicalCompoundFrameKeyOfComputed, target, view,
      derived] using priorTie

/-! ## Final physical endpoints -/








theorem localizedPhysicalCompound_finalOccurrence_priorTie_and_commonReading
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (c : m.Center) (e : m.Aut)
    (i j : Fin 4) (mirror : Bool)
    (centerFixed : m.centerPerm e c = c)
    (ligandMaps : m.ligandPermAt e c i = j)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      ∃ frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input m domain.graphEq c) = some frame,
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (m.ligandAtomAt c (alpha index))) ∧
          (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
            some (m.ligandAtomAt c i) ∧
            (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
              some (m.ligandAtomAt c j) ∧
              (LocalizedPhysicalCompoundSelectorShape
                  ((localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                    frameComputed (alpha.symm i)).prior.references)
                  ((localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                    frameComputed (alpha.symm j)).prior.references)
                  mirror →
                ∃ (leftReading rightReading : input.certified.LocalizedRerootRule5Reading),
                  (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                    frameComputed (alpha.symm i)).rule5Readings = [leftReading] ∧
                    (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                      frameComputed (alpha.symm j)).rule5Readings = [rightReading] ∧
                      input.certified.compareLocalizedRerootCompoundRule4bcKeys
                          (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c
                            frame frameComputed (alpha.symm i)).prior
                          (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c
                            frame frameComputed (alpha.symm j)).prior = Ordering.eq ∧
                        LocalizedCompoundCommonReadingRelation input.certified mirror
                          leftReading rightReading) := by
  classical
  obtain ⟨frame, alpha, frameComputed, slotSpec, correspondence⟩ :=
    exists_localizedPhysicalTopOccurrence_frame_slotCorrespondence input singleBonded acyclic
      m domain.graphEq c e i j centerFixed ligandMaps
  refine ⟨frame, alpha, frameComputed, slotSpec, ?_, ?_, ?_⟩
  · have h := slotSpec (alpha.symm i)
    simpa using h
  · have h := slotSpec (alpha.symm j)
    simpa using h
  · intro shape
    exact localizedPhysicalCompoundFrame_priorTie_and_commonReading
      input singleBonded acyclic noDouble m cfg c e i j mirror centerFixed signLaw
      domain coverage frame alpha frameComputed slotSpec correspondence shape




theorem localizedPhysicalCompound_transport_priorTie_and_commonReading
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport m cfg c i j mirror)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      ∃ frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input m domain.graphEq c) = some frame,
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (m.ligandAtomAt c (alpha index))) ∧
          (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
            some (m.ligandAtomAt c i) ∧
            (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
              some (m.ligandAtomAt c j) ∧
              (LocalizedPhysicalCompoundSelectorShape
                  ((localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                    frameComputed (alpha.symm i)).prior.references)
                  ((localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                    frameComputed (alpha.symm j)).prior.references)
                  mirror →
                ∃ (leftReading rightReading : input.certified.LocalizedRerootRule5Reading),
                  (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                    frameComputed (alpha.symm i)).rule5Readings = [leftReading] ∧
                    (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c frame
                      frameComputed (alpha.symm j)).rule5Readings = [rightReading] ∧
                      input.certified.compareLocalizedRerootCompoundRule4bcKeys
                          (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c
                            frame frameComputed (alpha.symm i)).prior
                          (localizedPhysicalCompoundFrameKeyOfComputed input m domain.graphEq c
                            frame frameComputed (alpha.symm j)).prior = Ordering.eq ∧
                        LocalizedCompoundCommonReadingRelation input.certified mirror
                          leftReading rightReading) := by
  obtain ⟨e, centerFixed, ligandMaps, signLaw⟩ := transport
  exact localizedPhysicalCompound_finalOccurrence_priorTie_and_commonReading
    input singleBonded acyclic noDouble m cfg c e i j mirror centerFixed ligandMaps signLaw
    domain coverage

/-- **Detected-molecule physical compound endpoint.**  The physical molecule is the automatically
detected multi-center molecule, so the graph equality and the center coverage are definitional. -/
theorem localizedPhysicalCompound_detected_priorTie_and_commonReading
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport input.certified.detectedMultiCenterMolecule cfg c i j mirror)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      ∃ frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input
            input.certified.detectedMultiCenterMolecule domain.graphEq c) = some frame,
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index))) ∧
          (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) ∧
            (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
              some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) ∧
              (LocalizedPhysicalCompoundSelectorShape
                  ((localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm i)).prior.references)
                  ((localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm j)).prior.references)
                  mirror →
                ∃ (leftReading rightReading : input.certified.LocalizedRerootRule5Reading),
                  (localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm i)).rule5Readings = [leftReading] ∧
                    (localizedPhysicalCompoundFrameKeyOfComputed input
                      input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                      frameComputed (alpha.symm j)).rule5Readings = [rightReading] ∧
                      input.certified.compareLocalizedRerootCompoundRule4bcKeys
                          (localizedPhysicalCompoundFrameKeyOfComputed input
                            input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                            frameComputed (alpha.symm i)).prior
                          (localizedPhysicalCompoundFrameKeyOfComputed input
                            input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                            frameComputed (alpha.symm j)).prior = Ordering.eq ∧
                        LocalizedCompoundCommonReadingRelation input.certified mirror
                          leftReading rightReading) :=
  localizedPhysicalCompound_transport_priorTie_and_commonReading input singleBonded acyclic
    noDouble input.certified.detectedMultiCenterMolecule cfg c i j mirror transport domain
    (detectedMultiCenter_centers input.certified)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOwnReferenceMirror
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOwnReferenceMirror_false
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOwnReferenceMirror_true
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bOwnStageOf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4cOwnStage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedPhysicalCompoundSelectorShape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalCompoundSelectorShape_alternatives
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalCompoundSelectorShape_referenceCountPriority
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bOwnStage_mirror
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4cOwnStage_mirror
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectLocalizedRule5StageFor_swap
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule5StageFor_mirror
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?_components
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsWithRead?_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_components
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsWithRead?_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingWithRead?_components
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_components
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bReadings_singleton_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4cReadings_singleton_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCumulativeRule45Observable_eq_of_transported_builds
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCumulativeRule45Observable_eq_of_transported_withRead_builds
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptor_eq_of_transported_withRead_builds
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptor_eq_of_transported_ownStage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptor_eq_of_transported_commonStage_crossed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptor_eq_of_transported_commonStage_same
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptor_eq_of_transported_commonStage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedCompoundCommonReadingRelation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCompoundPriorTie_and_commonReading_of_transported
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalCompoundFrameView
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalCompoundFrameKeyOfComputed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalCompoundFrame_priorTie_and_commonReading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalCompound_finalOccurrence_priorTie_and_commonReading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalCompound_transport_priorTie_and_commonReading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalCompound_detected_priorTie_and_commonReading
