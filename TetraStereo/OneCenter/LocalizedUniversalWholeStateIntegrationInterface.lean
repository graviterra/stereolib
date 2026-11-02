import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.OneCenter.LocalizedOutwardExtendedRule3Locality
import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Executable
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.OneCenter.LocalizedDescriptorObservableTransport
import TetraStereo.OneCenter.LocalizedOccurrenceRule3Through5Descriptor
import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
























































































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## 1. Reflexivity of the actual constitutional comparators -/

/-- The compiled Rule-1a/1b/2 comparator is reflexive at every rule major key. -/
theorem officialRuleMajor_compare_self {V : Type*} (key : OfficialRuleMajorKey V) :
    OfficialRuleMajorKey.compare key key = Ordering.eq := by
  rw [ruleMajor_compare_eq_observable]
  exact (compareConstitutionalObservable_eq_iff _ _).mpr rfl

/-- The recursive Rule-3 spatial comparator is reflexive at every recursive key. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_self
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys key key = Ordering.eq := by
  rw [compareLocalizedRerootRecursiveRule3SpatialKeys_of_constitutional_eq input key key
    (officialRuleMajor_compare_self key.constitutional)]
  exact (compareSparseLayers_compareNat_eq_iff key.rule3 key.rule3).mpr rfl

/-- **Diagonal frame independence.**  Comparing one slot of a cumulative key frame with itself
gives the same comparison record for *every* pair of frames: the Rule-3 comparison is reflexive and
the Rules-4/5 fallthrough is the recorded `eq`/non-pseudo reflexivity of the compound comparator. -/
theorem compareLocalizedOccurrenceRule3Through5At_self
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (index : Fin 4) :
    input.compareLocalizedOccurrenceRule3Through5At first index index =
      input.compareLocalizedOccurrenceRule3Through5At second index index := by
  rw [input.compareLocalizedOccurrenceRule3Through5At_of_rule3_eq first index index
        (input.compareLocalizedRerootRecursiveRule3SpatialKeys_self (first.keyAt index).rule3),
      input.compareLocalizedOccurrenceRule3Through5At_of_rule3_eq second index index
        (input.compareLocalizedRerootRecursiveRule3SpatialKeys_self (second.keyAt index).rule3),
      compareLocalizedRerootCompoundThroughRule5_self input (first.keyAt index).rule45,
      compareLocalizedRerootCompoundThroughRule5_self input (second.keyAt index).rule45]

/-! ## 2. Slotwise transport of the cumulative pair comparison record

The three lemmas below are the reusable core.  They never inspect how a key was built: they only
consume the constitutional observable, the Rule-3 priority list and the aligned Rules-4/5 key of
each slot.  This is what makes the interface usable over the actual raw and rebuilt canonical
frames without any reader-totality or successful-frame premise. -/

/-- Two recursive keys with equal constitutional compare and equal Rule-3 priority lists compare
identically, at every outcome. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_congr_of_rule3
    (input : CertifiedLocalizedCIPInput)
    (firstLeft firstRight secondLeft secondRight :
      input.LocalizedRerootRecursiveRule3SpatialKey)
    (constitutional :
      OfficialRuleMajorKey.compare firstLeft.constitutional firstRight.constitutional =
        OfficialRuleMajorKey.compare secondLeft.constitutional secondRight.constitutional)
    (rule3Left : firstLeft.rule3 = secondLeft.rule3)
    (rule3Right : firstRight.rule3 = secondRight.rule3) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys firstLeft firstRight =
      input.compareLocalizedRerootRecursiveRule3SpatialKeys secondLeft secondRight := by
  simp only [compareLocalizedRerootRecursiveRule3SpatialKeys, compareLex, Ordering.byKey]
  rw [constitutional, rule3Left, rule3Right]

/-- A strictly decided constitutional comparison decides the recursive Rule-3 comparison on its
own: the Rule-3 priority lists are never consulted. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_congr_of_constitutional_ne
    (input : CertifiedLocalizedCIPInput)
    (firstLeft firstRight secondLeft secondRight :
      input.LocalizedRerootRecursiveRule3SpatialKey)
    (constitutional :
      OfficialRuleMajorKey.compare firstLeft.constitutional firstRight.constitutional =
        OfficialRuleMajorKey.compare secondLeft.constitutional secondRight.constitutional)
    (separated :
      OfficialRuleMajorKey.compare secondLeft.constitutional secondRight.constitutional ≠
        Ordering.eq) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys firstLeft firstRight =
      input.compareLocalizedRerootRecursiveRule3SpatialKeys secondLeft secondRight := by
  simp only [compareLocalizedRerootRecursiveRule3SpatialKeys, compareLex, Ordering.byKey]
  rw [constitutional]
  cases decided : OfficialRuleMajorKey.compare secondLeft.constitutional
      secondRight.constitutional with
  | eq => exact absurd decided separated
  | lt => rfl
  | gt => rfl

/-- A strictly decided constitutional comparison makes the recursive Rule-3 comparison strict. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_ne_eq_of_constitutional_ne
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey)
    (separated :
      OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.eq) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys left right ≠ Ordering.eq := by
  cases decided : OfficialRuleMajorKey.compare left.constitutional right.constitutional with
  | eq => exact absurd decided separated
  | lt =>
      simp [compareLocalizedRerootRecursiveRule3SpatialKeys, compareLex,
        Ordering.byKey, decided]
  | gt =>
      simp [compareLocalizedRerootRecursiveRule3SpatialKeys, compareLex,
        Ordering.byKey, decided]

/-- **Slotwise agreement of two cumulative key frames.**

`full` marks the slots at which the whole Rule-3 key and the aligned Rules-4/5 key agree literally;
at most one slot may fail to be full.  At every slot the constitutional observable agrees, and every
pair involving a non-full slot is constitutionally separated.  Under these hypotheses the two frames
are interchangeable for every descriptor-facing comparison. -/
structure LocalizedUniversalFrameSlotAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) where
  /-- The slots at which the two frames agree on the full Rule-3 key and the Rules-4/5 key. -/
  full : Fin 4 → Prop
  /-- At most one slot is not full. -/
  atMostOneNonFull : ∀ index other, ¬ full index → ¬ full other → index = other
  /-- Every slot preserves the constitutional observable (Rules 1a, 1b and 2 only). -/
  constitutional : ∀ index,
    constitutionalObservable (first.keyAt index).rule3.constitutional =
      constitutionalObservable (second.keyAt index).rule3.constitutional
  /-- A full slot preserves the Rule-3 priority and observation lists. -/
  rule3_full : ∀ index, full index →
    (first.keyAt index).rule3.rule3 = (second.keyAt index).rule3.rule3
  /-- A full slot preserves the aligned Rules-4a--5 compound key. -/
  rule45_full : ∀ index, full index →
    (first.keyAt index).rule45 = (second.keyAt index).rule45
  /-- Every pair touching a non-full slot is separated by the constitutional comparator. -/
  separated : ∀ index other, index ≠ other → ¬ (full index ∧ full other) →
    OfficialRuleMajorKey.compare (first.keyAt index).rule3.constitutional
      (first.keyAt other).rule3.constitutional ≠ Ordering.eq

/-- **Reusable slotwise frame comparison.**  Under `LocalizedUniversalFrameSlotAgreement` the
actual cumulative pair comparison records of the two frames are identical at every pair of slots.

The three cases are exhaustive and each is non-tautological: the diagonal is the frame-independent
self-comparison; a full/full pair transports both the constitutional comparison and the Rule-3 and
Rules-4/5 components; and a pair touching the unique non-full slot is decided by the strict
constitutional comparison, so the reader-dependent components at that slot are never read. -/
theorem compareLocalizedOccurrenceRule3Through5At_eq_of_slotAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (agreement : LocalizedUniversalFrameSlotAgreement input first second)
    (left right : Fin 4) :
    input.compareLocalizedOccurrenceRule3Through5At first left right =
      input.compareLocalizedOccurrenceRule3Through5At second left right := by
  by_cases same : left = right
  · cases same
    exact input.compareLocalizedOccurrenceRule3Through5At_self first second left
  · have constitutionalCompare := ruleMajor_compare_congr
      (first.keyAt left).rule3.constitutional (first.keyAt right).rule3.constitutional
      (second.keyAt left).rule3.constitutional (second.keyAt right).rule3.constitutional
      (agreement.constitutional left) (agreement.constitutional right)
    by_cases both : agreement.full left ∧ agreement.full right
    · have step := input.compareLocalizedRerootRecursiveRule3SpatialKeys_congr_of_rule3
        (first.keyAt left).rule3 (first.keyAt right).rule3
        (second.keyAt left).rule3 (second.keyAt right).rule3
        constitutionalCompare
        (agreement.rule3_full left both.1) (agreement.rule3_full right both.2)
      unfold compareLocalizedOccurrenceRule3Through5At
      dsimp only
      rw [step]
      cases decided : input.compareLocalizedRerootRecursiveRule3SpatialKeys
          (second.keyAt left).rule3 (second.keyAt right).rule3 with
      | lt => rfl
      | gt => rfl
      | eq =>
          rw [agreement.rule45_full left both.1,
            agreement.rule45_full right both.2]
    · have nonEqFirst : OfficialRuleMajorKey.compare
          (first.keyAt left).rule3.constitutional (first.keyAt right).rule3.constitutional ≠
            Ordering.eq :=
        agreement.separated left right same both
      have nonEqSecond : OfficialRuleMajorKey.compare
          (second.keyAt left).rule3.constitutional (second.keyAt right).rule3.constitutional ≠
            Ordering.eq := by
        rw [← constitutionalCompare]
        exact nonEqFirst
      have step :=
        input.compareLocalizedRerootRecursiveRule3SpatialKeys_congr_of_constitutional_ne
          (first.keyAt left).rule3 (first.keyAt right).rule3
          (second.keyAt left).rule3 (second.keyAt right).rule3
          constitutionalCompare nonEqSecond
      have recursiveNe : input.compareLocalizedRerootRecursiveRule3SpatialKeys
          (second.keyAt left).rule3 (second.keyAt right).rule3 ≠ Ordering.eq :=
        input.compareLocalizedRerootRecursiveRule3SpatialKeys_ne_eq_of_constitutional_ne
          (second.keyAt left).rule3 (second.keyAt right).rule3 nonEqSecond
      unfold compareLocalizedOccurrenceRule3Through5At
      dsimp only
      rw [step]
      cases decided : input.compareLocalizedRerootRecursiveRule3SpatialKeys
          (second.keyAt left).rule3 (second.keyAt right).rule3 with
      | eq => exact absurd decided recursiveNe
      | lt => rfl
      | gt => rfl

/-- Slotwise agreement transports the total comparison function used by the stable sorter. -/
theorem compareLocalizedOccurrenceRule3Through5At?_eq_of_slotAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (agreement : LocalizedUniversalFrameSlotAgreement input first second) :
    input.compareLocalizedOccurrenceRule3Through5At? first =
      input.compareLocalizedOccurrenceRule3Through5At? second := by
  funext left right
  simp only [compareLocalizedOccurrenceRule3Through5At?]
  rw [input.compareLocalizedOccurrenceRule3Through5At_eq_of_slotAgreement
    first second agreement left right]

/-- Slotwise agreement transports the executable tracked order, including its pseudo-comparison
counter and every coherence refusal. -/
theorem localizedNoDoubleTrackedOrderExec?_eq_of_slotAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (agreement : LocalizedUniversalFrameSlotAgreement input first second) :
    input.localizedNoDoubleTrackedOrderExec? first =
      input.localizedNoDoubleTrackedOrderExec? second := by
  have comparisons : ∀ left right : Fin 4,
      input.compareLocalizedOccurrenceRule3Through5At first left right =
        input.compareLocalizedOccurrenceRule3Through5At second left right :=
    fun left right =>
      input.compareLocalizedOccurrenceRule3Through5At_eq_of_slotAgreement
        first second agreement left right
  have compareFunctions : input.compareLocalizedOccurrenceRule3Through5At? first =
      input.compareLocalizedOccurrenceRule3Through5At? second := by
    funext left right
    simp only [compareLocalizedOccurrenceRule3Through5At?]
    rw [comparisons left right]
  unfold localizedNoDoubleTrackedOrderExec?
  rw [compareFunctions]
  cases sorted : sortFourLocalizedLigandsTracked
      (input.compareLocalizedOccurrenceRule3Through5At? second) with
  | none => rfl
  | some tracked =>
      change (if input.localizedOccurrenceRule3Through5OrderCoherent first
            tracked.highestFirst then some tracked else none) =
        (if input.localizedOccurrenceRule3Through5OrderCoherent second
            tracked.highestFirst then some tracked else none)
      rw [input.localizedOccurrenceRule3Through5OrderCoherent_eq_of_comparisons
        first second comparisons tracked.highestFirst]

/-- Slotwise agreement transports the tracked order together with its base-relative
priority-ordered spatial points. -/
theorem localizedNoDoubleTrackedPointsAtBase?_eq_of_slotAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (agreement : LocalizedUniversalFrameSlotAgreement input first second) :
    input.localizedNoDoubleTrackedPointsAtBase? base first =
      input.localizedNoDoubleTrackedPointsAtBase? base second := by
  simp only [localizedNoDoubleTrackedPointsAtBase?,
    input.localizedNoDoubleTrackedOrderExec?_eq_of_slotAgreement first second agreement]

/-- The `some`-bind step of `do` notation, stated in the exact `>>=` form produced by elaboration
for the option monad.  Stating it this way lets the executable `do` blocks be reduced without any
assumption about the remaining, still-symbolic bind. -/
theorem doBindSome_eq {α β : Type} (value : α) (next : α → Option β) :
    (some value >>= next) = next value := rfl

/-- The `none`-bind step of `do` notation, in the same `>>=` form. -/
theorem doBindNone_eq {α β : Type} (next : α → Option β) :
    (none >>= next) = none := rfl

/-- **Slotwise agreement transports the assembled descriptor over one common centre and one
common four-ligand base.**  Only the `points` and `tracked` projections of the evidence are read,
so the `keys` field (which may differ between the two frames) is never inspected. -/
theorem descriptorFromKeys?_eq_of_slotAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (agreement : LocalizedUniversalFrameSlotAgreement input first second) :
    input.descriptorFromKeys? target view center base first =
      input.descriptorFromKeys? target view center base second := by
  unfold descriptorFromKeys? spatialEvidenceFromKeys?
  rw [input.localizedNoDoubleTrackedOrderExec?_eq_of_slotAgreement first second agreement]
  cases computed : input.localizedNoDoubleTrackedOrderExec? second with
  | none => simp only [doBindNone_eq]
  | some tracked =>
      simp only [doBindSome_eq]
      cases pointsComputed : List.mapM
          (fun index => input.localizedRerootCursorSpatialPoint? (base.cursorAt index))
          tracked.highestFirst with
      | none => simp only [doBindNone_eq, doBindSome_eq]
      | some points =>
          simp only [doBindSome_eq]

/-! ## 3. The whole-state descriptor pipeline

The shipped pipeline reads every occurrence through the restricted dependency reader
`input.localizedDependencyLabel target view`.  The whole-state pipeline reads the same occurrences
through `input.localizedWholeStateReader state`.  The definitions below keep every other component
—the descriptor centre, the actual four-ligand base, the two-pass Rule-3 frame machinery, the
Rules-4a--5 budget, the tracked order and the geometry classification— literally unchanged.

The equalities proved in this section are about the *actual* definitions.  The final-root theorem
`descriptorAtWholeState?_root_eq_descriptorAt?` is unconditional in the fuel and in the shared
failures: it compares full `Option` values, so every refusal of one pipeline is a refusal of the
other.  It uses the accepted outward frame equality of `LocalizedOutwardExtendedRule3Locality` and
the accepted outward compound key equality of `LocalizedParametricCompoundRule45Key`. -/

/-- Membership-wise `List.mapM` congruence.  `mapM` only applies the function to the members of the
list, so membership-wise agreement is enough. -/
theorem list_mapM_congr_on {α β : Type*}
    (first second : α → Option β) :
    ∀ values : List α,
      (∀ value, value ∈ values → first value = second value) →
      values.mapM first = values.mapM second
  | [], _ => rfl
  | value :: values, agrees => by
      simp [List.mapM_cons, agrees value (by simp),
        list_mapM_congr_on first second values
          (fun member memberPresent => agrees member (by simp [memberPresent]))]

/-- The whole-state version of the shared Rules-4a--5 tail.  The Rule-3 frame is supplied by the
caller; the Rules-4a--5 keys are built with the unrestricted whole-state reader at the production
Rules-4a--5 budget, and the same four-length refusal is performed. -/
noncomputable def finishKeyFrameWholeState? (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence) rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame
          rule3Length
          rule45Keys
          rule45Length }
    else none
  else none

/-- The whole-state descriptor tail from a fixed four-ligand base and a chosen optional Rule-3
frame.  The Rule-3 frame is supplied by the caller, exactly as in `descriptorFromFrame?`. -/
noncomputable def descriptorFromFrameWholeState? (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame? : Option input.LocalizedRule3CanonicalKeyFrame) :
    Option LocalizedAuxiliaryLabel := do
  let rule3Frame ← rule3Frame?
  let keys ← input.finishKeyFrameWholeState? target state base rule3Frame
  input.descriptorFromKeys? target (input.localizedDependencyView state target) center base keys

/-- The actual whole-state descriptor pipeline at an arbitrary Rule-3 evaluation budget.  The
descriptor centre and four-ligand base readers, the production Rules-4a--5 budget, the tracked
order, the pseudo-comparison count, the coordinate readings and the rational classification are
the existing ones; only the occurrence reader is the unrestricted whole-state reader. -/
noncomputable def descriptorAtWholeState? (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (evaluationBudget : Nat) : Option LocalizedAuxiliaryLabel := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← input.localizedNoDoubleFourLigandFrameExec? target
  input.descriptorFromFrameWholeState? target state center base
    (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
      (input.localizedDependencyView state target)
      (input.localizedWholeStateReader state) evaluationBudget base.cursors)

/-! ### Actual-frame witnesses -/

/-- A cursor of an actual four-ligand frame that is *not* the parent cursor is a strict outward
cursor of the target.  This is the membership form of the indexed root classification, proved
directly from the address dichotomy so that no `Fin`/`List.get` transport is needed. -/
theorem localizedOccurrenceFourLigandFrame_cursor_mem_outward_of_root
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (rootAddress : target.1.address = [])
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors) :
    OutwardRerootCursor input target cursor := by
  have structural :=
    input.localizedOccurrenceFourLigandFrame_cursor_address_classification
      target frame computed cursor present
  rcases structural with parent | child
  · exfalso
    have impossible : cursor.occurrence.1.address.length + 1 = 0 := by
      simpa [rootAddress] using parent.2
    omega
  · obtain ⟨slot, addressForm⟩ := child
    have valid :=
      input.localizedOccurrenceFourLigandFrame_cursor_valid target frame computed cursor present
    have rootEq :=
      input.localizedOccurrenceFourLigandFrame_cursor_root target frame computed cursor present
    have previous :=
      input.localizedOccurrenceFourLigandFrame_cursor_previous target frame computed cursor present
    have strict : target.1.address.length < cursor.occurrence.1.address.length := by
      rw [addressForm]
      simp
    exact ⟨valid, ⟨rootEq, strict⟩, target, previous, strict⟩

/-- **Per-cursor whole-state versus executable Rules-4a--5 key on an actual base cursor.**  Every
cursor of the four-ligand base is an executable child of the target-start cursor and, at a root
target, is strictly outward.  The accepted outward compound equality therefore identifies the
whole-state key with the shipped restricted key, and the executable twin identifies that with
`buildLocalizedRerootCompoundRule45KeyExec?`. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_Exec?_of_baseCursor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (cursorsEq : base.cursors = input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel))
    (allOutward : ∀ cursor ∈ base.cursors, OutwardRerootCursor input target cursor)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (member : cursor ∈ base.cursors) :
    input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun c => state c.occurrence) fuel cursor =
      input.buildLocalizedRerootCompoundRule45KeyExec?
        target (input.localizedDependencyView state target) fuel cursor := by
  have child : cursor ∈ input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) := by
    rw [← cursorsEq]
    exact member
  have deeper : target.1.address.length < cursor.occurrence.1.address.length :=
    (allOutward cursor member).2.1.2
  exact (input.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
      target state cursor cursor child deeper Relation.ReflTransGen.refl fuel).trans
    (input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?
      target (input.localizedDependencyView state target) fuel cursor)

/-! ### Transport of the Rules-4a--5 tail and of the frame tail -/

/-- The whole-state Rules-4a--5 tail equals the shipped tail over the same Rule-3 frame and the
same base as soon as the per-cursor compound keys agree.  The four-length refusals are shared
syntactically. -/
theorem finishKeyFrameWholeState?_eq_finishKeyFrame?_of_cursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame)
    (keysAgree : ∀ cursor ∈ base.cursors,
      input.buildLocalizedRerootCompoundRule45KeyWithRead?
          (fun c => state c.occurrence)
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor =
        input.buildLocalizedRerootCompoundRule45KeyExec?
          target (input.localizedDependencyView state target)
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor) :
    input.finishKeyFrameWholeState? target state base rule3Frame =
      input.finishKeyFrame? target
        (input.localizedDependencyView state target) base rule3Frame := by
  unfold finishKeyFrameWholeState? finishKeyFrame?
  dsimp only
  rw [list_mapM_congr_on _ _ base.cursors keysAgree]

/-- The whole-state frame tail equals the shipped frame tail over the same base and the same
optional Rule-3 frame as soon as the per-cursor compound keys agree. -/
theorem descriptorFromFrameWholeState?_eq_descriptorFromFrame?_of_cursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keysAgree : ∀ cursor ∈ base.cursors,
      input.buildLocalizedRerootCompoundRule45KeyWithRead?
          (fun c => state c.occurrence)
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor =
        input.buildLocalizedRerootCompoundRule45KeyExec?
          target (input.localizedDependencyView state target)
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor)
    (rule3Frame? : Option input.LocalizedRule3CanonicalKeyFrame) :
    input.descriptorFromFrameWholeState? target state center base rule3Frame? =
      input.descriptorFromFrame? target (input.localizedDependencyView state target)
        center base rule3Frame? := by
  cases rule3Frame? with
  | none => rfl
  | some rule3Frame =>
      unfold descriptorFromFrameWholeState? descriptorFromFrame?
      simp only [doBindSome_eq]
      rw [input.finishKeyFrameWholeState?_eq_finishKeyFrame?_of_cursors
        target state base rule3Frame keysAgree]

/-! ### The final-root endpoint -/

/-- **Final-root whole-state descriptor equality.**

At a root target, every cursor of the actually computed four-ligand base is strictly outward, so
the two-pass Rule-3 frame built through the whole-state reader is the shipped executable frame and
every Rules-4a--5 key built through the whole-state reader is the shipped executable key.  The
whole-state descriptor pipeline therefore returns exactly the shipped descriptor at *every*
Rule-3 evaluation budget, including every shared failure (`none`).

No parent geometry, no successful-key premise, no desired label and no exclusion-list premise is
assumed: the two-pass topology resolution, the coupled excluded physical units and the shared-unit
exclusion are the actual ones, and the outward frame equality already covers both passes. -/
theorem descriptorAtWholeState?_root_eq_descriptorAt?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rootAddress : target.1.address = [])
    (evaluationBudget : Nat) :
    input.descriptorAtWholeState? target state evaluationBudget =
      input.descriptorAt? target (input.localizedDependencyView state target)
        evaluationBudget := by
  unfold descriptorAtWholeState? descriptorAt?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => rfl
      | some base =>
          simp only [doBindSome_eq]
          have frameComputed :
              input.localizedOccurrenceFourLigandFrame? target = some base := by
            rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
            exact baseComputed
          have allOutward : ∀ cursor ∈ base.cursors,
              OutwardRerootCursor input target cursor :=
            fun cursor member =>
              input.localizedOccurrenceFourLigandFrame_cursor_mem_outward_of_root
                target base frameComputed rootAddress cursor member
          have cursorsEq : base.cursors = input.executableLocalizedRerootChildren
              ({ occurrence := target, previous? := none } :
                input.LocalizedRerootCursor carrierFuel) :=
            input.localizedOccurrenceFourLigandFrame_cursors_eq_executable
              target base frameComputed
          have keysAgree : ∀ cursor ∈ base.cursors,
              input.buildLocalizedRerootCompoundRule45KeyWithRead?
                  (fun c => state c.occurrence)
                  (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor =
                input.buildLocalizedRerootCompoundRule45KeyExec?
                  target (input.localizedDependencyView state target)
                  (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor :=
            fun cursor member =>
              input.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_Exec?_of_baseCursor
                target state base cursorsEq allOutward
                (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor member
          rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_wholeState_eq_Exec?_of_outward
            target state evaluationBudget base.cursors allOutward]
          exact input.descriptorFromFrameWholeState?_eq_descriptorFromFrame?_of_cursors
            target state center base keysAgree
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
              target (input.localizedDependencyView state target) evaluationBudget base.cursors)

/-- **Final-root whole-state descriptor equality against the shipped production descriptor.**

At the production Rule-3 budget `localizedDescriptorBearingRule3EvaluationFuel carrierFuel`, the
whole-state pipeline returns exactly the shipped extended short-circuit descriptor of
`LocalizedOccurrenceRule3Through5Descriptor`, at every root target and for every auxiliary state.
The proof is the root endpoint at that budget followed by the unconditional production identity
`descriptorAt?_production`.  Every shared failure is preserved as a full `Option` equality.

No geometry premise, no successful-frame premise, no desired label and no exclusion-order premise
is used.  The root hypothesis `target.1.address = []` is the actual domain of the statement: it is
exactly what makes every ligand cursor outward. -/
theorem descriptorAtWholeState?_root_production_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rootAddress : target.1.address = []) :
    input.descriptorAtWholeState? target state
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        target (input.localizedDependencyView state target) := by
  rw [input.descriptorAtWholeState?_root_eq_descriptorAt? target state rootAddress
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)]
  exact input.descriptorAt?_production target
    (input.localizedDependencyView state target)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedUniversalFrameSlotAgreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.officialRuleMajor_compare_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootRecursiveRule3SpatialKeys_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule3Through5At_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootRecursiveRule3SpatialKeys_congr_of_rule3
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootRecursiveRule3SpatialKeys_congr_of_constitutional_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootRecursiveRule3SpatialKeys_ne_eq_of_constitutional_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule3Through5At_eq_of_slotAgreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule3Through5At?_eq_of_slotAgreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedNoDoubleTrackedOrderExec?_eq_of_slotAgreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedNoDoubleTrackedPointsAtBase?_eq_of_slotAgreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.doBindSome_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.doBindNone_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorFromKeys?_eq_of_slotAgreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.list_mapM_congr_on
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.finishKeyFrameWholeState?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorFromFrameWholeState?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorAtWholeState?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursor_mem_outward_of_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_Exec?_of_baseCursor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.finishKeyFrameWholeState?_eq_finishKeyFrame?_of_cursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorFromFrameWholeState?_eq_descriptorFromFrame?_of_cursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorAtWholeState?_root_eq_descriptorAt?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorAtWholeState?_root_production_eq
