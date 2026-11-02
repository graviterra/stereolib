import TetraStereo.OneCenter.LocalizedOccurrenceRule45FixedPoint
import TetraStereo.OneCenter.LocalizedRankedIteration
import TetraStereo.OneCenter.LocalizedParametricOccurrenceDescriptor
import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter












































































namespace CertifiedLocalizedCIPInput



/-- The cursor reader induced by a complete occurrence state: read the label stored at the
occurrence carried by the cursor.  This is a *reader over cursors*, not the pair callback consumed
by `LocalizedParametricOccurrenceDescriptor`. -/
def localizedOccurrenceRule45WholeStateReader
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel :=
  fun cursor => state cursor.occurrence






noncomputable def localizedOccurrenceRule45WholeStateFrameComparator
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    LocalizedOccurrenceRule45FrameComparator input carrierFuel :=
  fun frame left right => do
    let evaluationFuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
    let leftKey ← input.buildLocalizedRerootCompoundRule45KeyWithRead?
      (input.localizedOccurrenceRule45WholeStateReader state)
      evaluationFuel (frame.cursorAt left)
    let rightKey ← input.buildLocalizedRerootCompoundRule45KeyWithRead?
      (input.localizedOccurrenceRule45WholeStateReader state)
      evaluationFuel (frame.cursorAt right)
    some (localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))


noncomputable def localizedOccurrenceRule45RestrictedFrameComparator
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    LocalizedOccurrenceRule45FrameComparator input carrierFuel :=
  fun frame left right =>
    input.compareLocalizedOccurrenceThroughRule5At? target view frame left right

/-- Definitional unfolding of the production callback. -/
theorem localizedOccurrenceRule45RestrictedFrameComparator_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) :
    input.localizedOccurrenceRule45RestrictedFrameComparator target view frame left right =
      input.compareLocalizedOccurrenceThroughRule5At? target view frame left right :=
  rfl





noncomputable def localizedOccurrenceRule45WholeStateDescriptor?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    Option LocalizedAuxiliaryLabel :=
  input.localizedOccurrenceRule45DescriptorWith? target
    (input.localizedDependencyView state target)
    (input.localizedOccurrenceRule45WholeStateFrameComparator state)

/-- The simultaneous whole-state Step of the Rule-4a--5 evaluator: every occurrence is updated from
the whole-state descriptor.  The parameter order is `state` then `target`, matching
`executableStateStep`. -/
noncomputable def localizedOccurrenceRule45WholeStateStep
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel) : Option LocalizedAuxiliaryLabel :=
  input.localizedOccurrenceRule45WholeStateDescriptor? target state

/-! ## Branchwise descriptor locality

The three unconditional branches below are the nonbearing, frame-none and strictly-deeper actual
frame cases.  Only the last requires geometric input, which is isolated in the hypotheses. -/

/-- If the occurrence has no real tetrahedral descriptor center, both descriptors refuse. -/
theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_center?_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state =
      input.localizedOccurrenceRule45Descriptor? target
        (input.localizedDependencyView state target) := by
  unfold localizedOccurrenceRule45WholeStateDescriptor?
    localizedOccurrenceRule45DescriptorWith?
    localizedOccurrenceRule45Descriptor?
    localizedOccurrenceRule45SpatialEvidenceWith?
    localizedOccurrenceRule45SpatialEvidence?
  rw [centerComputed]
  rfl

/-- If the four-ligand frame construction fails, both descriptors refuse. -/
theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_frame?_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = none) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state =
      input.localizedOccurrenceRule45Descriptor? target
        (input.localizedDependencyView state target) := by
  unfold localizedOccurrenceRule45WholeStateDescriptor?
    localizedOccurrenceRule45DescriptorWith?
    localizedOccurrenceRule45Descriptor?
  rw [input.localizedOccurrenceRule45SpatialEvidenceWith?_eq_none_of_frame?_eq_none
        target (input.localizedDependencyView state target)
        (input.localizedOccurrenceRule45WholeStateFrameComparator state) frameComputed,
      input.localizedOccurrenceRule45SpatialEvidence?_eq_none_of_frame?_eq_none
        target (input.localizedDependencyView state target) frameComputed]

/-- Every indexed cursor of an actual four-ligand frame is an executable child of the
target-start cursor. -/
theorem localizedOccurrenceRule45FrameCursor_mem_executableChildren
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    frame.cursorAt index ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none } := by
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp frameComputed
  have childrenComputed : input.localizedRerootChildren?
      { occurrence := target, previous? := none } = some frame.cursors :=
    (input.localizedRerootChildren?_eq_some_iff
      { occurrence := target, previous? := none } frame.cursors).mpr derived.1
  have executableEq : input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none } = frame.cursors :=
    Option.some.inj
      ((input.localizedRerootChildren?_eq_some_executable
        { occurrence := target, previous? := none }).symm.trans childrenComputed)
  rw [executableEq]
  exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)





theorem localizedOccurrenceRule45WholeStateFrameComparator_eq_restricted_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (left right : Fin 4)
    (leftDeeper : target.1.address.length <
      (frame.cursorAt left).occurrence.1.address.length)
    (rightDeeper : target.1.address.length <
      (frame.cursorAt right).occurrence.1.address.length) :
    input.localizedOccurrenceRule45WholeStateFrameComparator state frame left right =
      input.localizedOccurrenceRule45RestrictedFrameComparator target
        (input.localizedDependencyView state target) frame left right := by
  have leftEq :=
    input.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
      target state (frame.cursorAt left) (frame.cursorAt left)
      (input.localizedOccurrenceRule45FrameCursor_mem_executableChildren
        target frame frameComputed left)
      leftDeeper Relation.ReflTransGen.refl
  have rightEq :=
    input.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
      target state (frame.cursorAt right) (frame.cursorAt right)
      (input.localizedOccurrenceRule45FrameCursor_mem_executableChildren
        target frame frameComputed right)
      rightDeeper Relation.ReflTransGen.refl
  unfold localizedOccurrenceRule45WholeStateFrameComparator
    localizedOccurrenceRule45RestrictedFrameComparator
    compareLocalizedOccurrenceThroughRule5At?
  have readerEq : input.localizedOccurrenceRule45WholeStateReader state =
      fun cursor => state cursor.occurrence := rfl
  rw [readerEq]
  dsimp only
  rw [leftEq (localizedOccurrenceRerootEvaluationFuel carrierFuel),
    rightEq (localizedOccurrenceRerootEvaluationFuel carrierFuel)]




theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_frame?_eq_some_deeper
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (deeper : ∀ index : Fin 4,
      target.1.address.length < (frame.cursorAt index).occurrence.1.address.length) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state =
      input.localizedOccurrenceRule45Descriptor? target
        (input.localizedDependencyView state target) := by
  unfold localizedOccurrenceRule45WholeStateDescriptor?
  apply input.localizedOccurrenceRule45DescriptorWith?_eq_restricted_of_frame_comparisons
    target (input.localizedDependencyView state target)
    (input.localizedOccurrenceRule45WholeStateFrameComparator state)
  intro frame' frameComputed' left right
  have frameEq : frame' = frame := Option.some.inj (frameComputed'.symm.trans frameComputed)
  rw [frameEq]
  exact (input.localizedOccurrenceRule45WholeStateFrameComparator_eq_restricted_of_frame
    target state frame frameComputed left right (deeper left) (deeper right)).trans
      (input.localizedOccurrenceRule45RestrictedFrameComparator_eq
        target (input.localizedDependencyView state target) frame left right)

/-! ## The descriptor-agreement seam -/




def LocalizedWholeStateRule45DescriptorAgreement
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Prop :=
  ∀ (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel),
    input.localizedOccurrenceRule45WholeStateDescriptor? target state =
      input.localizedOccurrenceRule45Descriptor? target
        (input.localizedDependencyView state target)





theorem LocalizedWholeStateRule45DescriptorAgreement_of_branches
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (branches : ∀ target : input.LocalizedCIPOccurrence fuel,
      input.localizedOccurrenceDescriptorCenter? target = none ∨
        input.localizedOccurrenceFourLigandFrame? target = none ∨
          ∃ frame : input.LocalizedOccurrenceFourLigandFrame fuel,
            input.localizedOccurrenceFourLigandFrame? target = some frame ∧
              ∀ index : Fin 4,
                target.1.address.length <
                  (frame.cursorAt index).occurrence.1.address.length) :
    input.LocalizedWholeStateRule45DescriptorAgreement fuel := by
  intro state target
  rcases branches target with centerNone | frameNone | ⟨frame, frameComputed, deeper⟩
  · exact input.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_center?_eq_none
      target state centerNone
  · exact input.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_frame?_eq_none
      target state frameNone
  · exact
      input.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_frame?_eq_some_deeper
        target state frame frameComputed deeper





theorem LocalizedWholeStateRule45DescriptorAgreement_of_deeper_actual_frames
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (deeper : ∀ (target : input.LocalizedCIPOccurrence fuel)
      (frame : input.LocalizedOccurrenceFourLigandFrame fuel),
      input.localizedOccurrenceFourLigandFrame? target = some frame →
        ∀ index : Fin 4,
          target.1.address.length <
            (frame.cursorAt index).occurrence.1.address.length) :
    input.LocalizedWholeStateRule45DescriptorAgreement fuel := by
  apply input.LocalizedWholeStateRule45DescriptorAgreement_of_branches
  intro target
  cases frameComputed : input.localizedOccurrenceFourLigandFrame? target with
  | none => exact Or.inr (Or.inl rfl)
  | some frame => exact Or.inr (Or.inr ⟨frame, rfl, deeper target frame frameComputed⟩)

/-! ## The whole-state Step is the existing restricted Step -/

/-- The concrete Rules-4a--5 semantics executes exactly the occurrence descriptor. -/
theorem localizedOccurrenceRule45AuxiliarySemantics_executableRule
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule =
      input.localizedOccurrenceRule45Descriptor? :=
  rfl



theorem localizedOccurrenceRule45WholeStateStep_eq_executableStep
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (agreement : input.LocalizedWholeStateRule45DescriptorAgreement fuel) :
    input.localizedOccurrenceRule45WholeStateStep (fuel := fuel) =
      input.localizedExecutableStep (fuel := fuel)
        input.localizedOccurrenceRule45Descriptor? := by
  funext state target
  exact agreement state target

/-! ## The unique whole-state fixed point -/

/-- A whole-state fixed point of the Rule-4a--5 evaluator: the simultaneous whole-state Step leaves
the complete occurrence state unchanged. -/
def LocalizedWholeStateRule45FixedPoint
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) : Prop :=
  input.localizedOccurrenceRule45WholeStateStep state = state

/-- The `fuel + 2` computable iteration is a fixed point of the whole-state Step. -/
theorem localizedOccurrenceRule45WholeStateStep_fixed
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (agreement : input.LocalizedWholeStateRule45DescriptorAgreement fuel) :
    input.localizedOccurrenceRule45WholeStateStep (fuel := fuel)
        (input.evaluateLocalizedOccurrences fuel
          (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule) =
      input.evaluateLocalizedOccurrences fuel
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule := by
  rw [input.localizedOccurrenceRule45WholeStateStep_eq_executableStep fuel agreement]
  have fixed := input.localizedRawStep_evaluateLocalizedOccurrences_fixed fuel
    (input.localizedOccurrenceRule45AuxiliarySemantics fuel)
  simp only [localizedRawStep,
    input.localizedOccurrenceRule45AuxiliarySemantics_executableRule fuel] at fixed
  exact fixed

/-- The unique whole-state fixed point is exactly the existing restricted Rule-45 `CIPModel`.  The
forward direction rewrites the whole-state Step to the restricted executable Step and applies the
existing `cipModel_iff_executableStateStep_fixed` with
`localizedAuxiliaryDerivationStepCorrespondence`; no model is assumed. -/
theorem localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (agreement : input.LocalizedWholeStateRule45DescriptorAgreement fuel) :
    input.LocalizedWholeStateRule45FixedPoint fuel state ↔
      (input.localizedAuxiliaryOccurrenceSystem
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state := by
  unfold LocalizedWholeStateRule45FixedPoint
  rw [input.localizedOccurrenceRule45WholeStateStep_eq_executableStep fuel agreement]
  exact ((input.localizedAuxiliaryOccurrenceSystem
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).cipModel_iff_executableStateStep_fixed
          (input.localizedAuxiliaryDerivationStepCorrespondence
            (input.localizedOccurrenceRule45AuxiliarySemantics fuel)) state).symm

/-- The whole-state Step has exactly one fixed point, and it is the existing `fuel + 2`
computable iteration.  Uniqueness uses `evaluateLocalizedOccurrences_eq_model`: any whole-state
fixed point is a Rule-45 `CIPModel`, hence equal to the computed state. -/
theorem existsUnique_localizedOccurrenceRule45WholeStateFixedPoint
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (agreement : input.LocalizedWholeStateRule45DescriptorAgreement fuel) :
    ∃! state, input.LocalizedWholeStateRule45FixedPoint fuel state := by
  refine ⟨input.evaluateLocalizedOccurrences fuel
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule,
    input.localizedOccurrenceRule45WholeStateStep_fixed fuel agreement, ?_⟩
  intro state fixed
  have model :=
    (input.localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel fuel state agreement).mp fixed
  exact (input.evaluateLocalizedOccurrences_eq_model fuel
    (input.localizedOccurrenceRule45AuxiliarySemantics fuel) model).symm

/-- Every whole-state fixed point equals the existing `fuel + 2` computable iteration. -/
theorem localizedOccurrenceRule45WholeStateFixedPoint_eq_iterate
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (agreement : input.LocalizedWholeStateRule45DescriptorAgreement fuel)
    {state : input.LocalizedAuxiliaryState fuel}
    (fixed : input.LocalizedWholeStateRule45FixedPoint fuel state) :
    state = input.evaluateLocalizedOccurrences fuel
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule := by
  have model :=
    (input.localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel fuel state agreement).mp fixed
  exact (input.evaluateLocalizedOccurrences_eq_model fuel
    (input.localizedOccurrenceRule45AuxiliarySemantics fuel) model).symm




theorem evaluateLocalizedOccurrences_eq_wholeStateIterate
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (agreement : input.LocalizedWholeStateRule45DescriptorAgreement fuel) :
    input.evaluateLocalizedOccurrences fuel
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule =
      DeclarativeCIP.RankedIteration.iterate
        (input.localizedOccurrenceRule45WholeStateStep (fuel := fuel))
        (fun _ => none) (fuel + 2) := by
  unfold evaluateLocalizedOccurrences
  rw [input.localizedOccurrenceRule45AuxiliarySemantics_executableRule fuel]
  exact congrArg
    (fun step => DeclarativeCIP.RankedIteration.iterate step (fun _ => none) (fuel + 2))
    (input.localizedOccurrenceRule45WholeStateStep_eq_executableStep fuel agreement).symm

/-- In the unique whole-state fixed point, an occurrence carries a descriptor exactly when the
canonical molecule-backed Rule-45 derivation holds under that state's restricted dependency view.
This transfers `localizedOccurrenceRule45Model_eq_some_iff_canonical` along the fixed-point/CIPModel
equivalence. -/
theorem localizedOccurrenceRule45WholeStateFixedPoint_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (agreement : input.LocalizedWholeStateRule45DescriptorAgreement fuel)
    {state : input.LocalizedAuxiliaryState fuel}
    (fixed : input.LocalizedWholeStateRule45FixedPoint fuel state)
    (target : input.LocalizedCIPOccurrence fuel)
    (descriptor : LocalizedAuxiliaryLabel) :
    state target = some descriptor ↔
      input.CanonicalLocalizedOccurrenceRule45Descriptor target
        (input.localizedDependencyView state target) descriptor := by
  have model :=
    (input.localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel fuel state agreement).mp fixed
  exact input.localizedOccurrenceRule45Model_eq_some_iff_canonical
    state model target descriptor

/-- The unique whole-state fixed point emits no label exactly when no canonical Rule-45 descriptor
derivation exists. -/
theorem localizedOccurrenceRule45WholeStateFixedPoint_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (agreement : input.LocalizedWholeStateRule45DescriptorAgreement fuel)
    {state : input.LocalizedAuxiliaryState fuel}
    (fixed : input.LocalizedWholeStateRule45FixedPoint fuel state)
    (target : input.LocalizedCIPOccurrence fuel) :
    state target = none ↔
      ¬ ∃ descriptor,
        input.CanonicalLocalizedOccurrenceRule45Descriptor target
          (input.localizedDependencyView state target) descriptor := by
  constructor
  · intro noneOutcome ⟨descriptor, derived⟩
    have positive :=
      (input.localizedOccurrenceRule45WholeStateFixedPoint_eq_some_iff_canonical
        fuel agreement fixed target descriptor).mpr derived
    rw [noneOutcome] at positive
    cases positive
  · intro absent
    cases outcome : state target with
    | none => rfl
    | some descriptor =>
        exact absurd ⟨descriptor,
          (input.localizedOccurrenceRule45WholeStateFixedPoint_eq_some_iff_canonical
            fuel agreement fixed target descriptor).mp outcome⟩ absent

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

All exports of this module are structural transports of existing kernel-checked theorems.  The
guarded declarations cover the whole-state reader and pair callback, the two descriptors and the
Step, the three unconditional locality branches, the branchwise agreement constructors, and every
fixed-point/CIPModel/iteration theorem.  `assert_kernel_only` permits exactly `propext`,
`Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and native/compiler
trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateReader
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFrameComparator
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45RestrictedFrameComparator
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45RestrictedFrameComparator_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateStep
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_center?_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_frame?_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45FrameCursor_mem_executableChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFrameComparator_eq_restricted_of_frame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_frame?_eq_some_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedWholeStateRule45DescriptorAgreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedWholeStateRule45DescriptorAgreement_of_branches
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedWholeStateRule45DescriptorAgreement_of_deeper_actual_frames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45AuxiliarySemantics_executableRule
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateStep_eq_executableStep
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedWholeStateRule45FixedPoint
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateStep_fixed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.existsUnique_localizedOccurrenceRule45WholeStateFixedPoint
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_eq_iterate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.evaluateLocalizedOccurrences_eq_wholeStateIterate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_eq_some_iff_canonical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_iff_no_canonical
