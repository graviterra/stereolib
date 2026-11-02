import TetraStereo.OneCenter.LocalizedWholeStateRule45FixedPoint
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedCarrierRealCenterActiveSimple
import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
Whole-state descriptor locality for the original-root proposed-2018 localized Rule-45 model.
The full reader is never restricted. Actual frames are classified into parent/outward cursors;
strict constitutional separation handles either orientation involving the parent, while actual
outward keys agree. This module does not concern Rule 3 or center-owned raw comparison frames.
-/
namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

private theorem compound_observable_eq
    (input : CertifiedLocalizedCIPInput) {n : Nat}
    (read₁ read₂ : input.LocalizedRerootCursor n → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor n)
    (key₁ key₂ : input.LocalizedRerootCompoundRule45Key)
    (h₁ : input.buildLocalizedRerootCompoundRule45KeyWithRead? read₁ fuel cursor = some key₁)
    (h₂ : input.buildLocalizedRerootCompoundRule45KeyWithRead? read₂ fuel cursor = some key₂) :
    constitutionalObservable key₁.prior.rule4aKey.constitutional =
      constitutionalObservable key₂.prior.rule4aKey.constitutional := by
  exact input.declarative_constitutional_observable_unique fuel fuel cursor _ _
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
      .rule4a read₁ fuel cursor _
      (input.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
        read₁ fuel cursor key₁ h₁))
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
      .rule4a read₂ fuel cursor _
      (input.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
        read₂ fuel cursor key₂ h₂))

private theorem compound_root_head
    (input : CertifiedLocalizedCIPInput) {n : Nat}
    (read : input.LocalizedRerootCursor n → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor n)
    (key : input.LocalizedRerootCompoundRule45Key)
    (built : input.buildLocalizedRerootCompoundRule45KeyWithRead? read fuel cursor = some key) :
    key.prior.rule4aKey.constitutional.rule1b.head? =
      some [([], cursor.occurrence.1.node.rule1bRootDistance)] := by
  exact WholeStateCumulativeLabels.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_rule1b_head
    input .rule4a read fuel cursor _
    (input.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      read fuel cursor key built)

/-- Two actual compound compilations with arbitrary label readers have equal comparison records
when the two cursor root distances differ. The statement applies in either pair orientation. -/
theorem localizedCompoundReaderComparison_eq_of_rootDistance_ne
    (input : CertifiedLocalizedCIPInput) {n : Nat}
    (read₁ read₂ : input.LocalizedRerootCursor n → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (left right : input.LocalizedRerootCursor n)
    (left₁ right₁ left₂ right₂ : input.LocalizedRerootCompoundRule45Key)
    (hl₁ : input.buildLocalizedRerootCompoundRule45KeyWithRead? read₁ fuel left = some left₁)
    (hr₁ : input.buildLocalizedRerootCompoundRule45KeyWithRead? read₁ fuel right = some right₁)
    (hl₂ : input.buildLocalizedRerootCompoundRule45KeyWithRead? read₂ fuel left = some left₂)
    (hr₂ : input.buildLocalizedRerootCompoundRule45KeyWithRead? read₂ fuel right = some right₂)
    (different : left.occurrence.1.node.rule1bRootDistance ≠
      right.occurrence.1.node.rule1bRootDistance) :
    input.compareLocalizedRerootCompoundThroughRule5 left₁ right₁ =
      input.compareLocalizedRerootCompoundThroughRule5 left₂ right₂ := by
  have first := input.builtCumulativeKeys_constitutionalCompare_ne_eq
    left₁.prior.rule4aKey right₁.prior.rule4aKey
    (compound_root_head input read₁ fuel left left₁ hl₁)
    (compound_root_head input read₁ fuel right right₁ hr₁) different
  have second := input.builtCumulativeKeys_constitutionalCompare_ne_eq
    left₂.prior.rule4aKey right₂.prior.rule4aKey
    (compound_root_head input read₂ fuel left left₂ hl₂)
    (compound_root_head input read₂ fuel right right₂ hr₂) different
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_constitutional_of_rule4a
      left₁ right₁ first.2 first.1,
    input.compareLocalizedRerootCompoundThroughRule5_eq_constitutional_of_rule4a
      left₂ right₂ second.2 second.1]
  have eq := ruleMajor_compare_congr _ _ _ _
    (compound_observable_eq input read₁ read₂ fuel left left₁ left₂ hl₁ hl₂)
    (compound_observable_eq input read₁ read₂ fuel right right₁ right₂ hr₁ hr₂)
  rw [eq]

/-- An actual outward frame cursor remains after cutting the actual carrier parent. -/
theorem localizedActualFrame_outward_mem_parentCut
    (input : CertifiedLocalizedCIPInput) {n : Nat}
    (target : input.LocalizedCIPOccurrence n) (active : target.1.node.ActiveSimple)
    (frame : input.LocalizedOccurrenceFourLigandFrame n)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (certificate : input.LocalizedParentFrameHistory target)
    (index : Fin 4) (slot : Nat)
    (address : (frame.cursorAt index).occurrence.1.address = target.1.address ++ [slot]) :
    frame.cursorAt index ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := some certificate.parent } := by
  let child := frame.cursorAt index
  have present : child ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  have neighbor := input.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    target frame computed child present
  have previous := input.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame computed child present
  have different : child.occurrence.1.address ≠ certificate.parent.1.address := by
    intro eq
    have lengths := congrArg List.length eq
    have parentLength := certificate.parent_address_length input
    have childLength : child.occurrence.1.address.length = target.1.address.length + 1 := by
      change (frame.cursorAt index).occurrence.1.address.length = _
      rw [address, List.length_append]
      rfl
    omega
  have notDuplicate : target.1.node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, active.1]
  have intended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames
      { occurrence := target, previous? := some certificate.parent } := by
    simp [intendedLocalizedRerootChildFrames, notDuplicate, neighbor, different]
  unfold executableLocalizedRerootChildren
  rw [List.mem_map]
  refine ⟨⟨child.occurrence.1, intended⟩, List.mem_attach _ _, ?_⟩
  apply LocalizedRerootCursor.ext
  · exact Subtype.ext rfl
  · exact previous.symm

private theorem frame_pair_eq_of_self_or_distance
    (input : CertifiedLocalizedCIPInput) {n : Nat}
    (target : input.LocalizedCIPOccurrence n) (state : input.LocalizedAuxiliaryState n)
    (frame : input.LocalizedOccurrenceFourLigandFrame n)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (left right : Fin 4)
    (separated : left = right ∨
      (frame.cursorAt left).occurrence.1.node.rule1bRootDistance ≠
        (frame.cursorAt right).occurrence.1.node.rule1bRootDistance) :
    input.localizedOccurrenceRule45WholeStateFrameComparator state frame left right =
      input.compareLocalizedOccurrenceThroughRule5At? target
        (input.localizedDependencyView state target) frame left right := by
  let full := input.localizedOccurrenceRule45WholeStateReader state
  let restricted := fun cursor => input.localizedDependencyLabel target
    (input.localizedDependencyView state target) cursor
  have valid (index : Fin 4) : input.LocalizedRerootCursorValid (frame.cursorAt index) :=
    input.localizedOccurrenceFourLigandFrame_cursor_valid target frame computed _
      (List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index))
  obtain ⟨l₁, hl₁⟩ := input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
    full (frame.cursorAt left) (valid left)
  obtain ⟨r₁, hr₁⟩ := input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
    full (frame.cursorAt right) (valid right)
  obtain ⟨l₂, hl₂⟩ := input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
    restricted (frame.cursorAt left) (valid left)
  obtain ⟨r₂, hr₂⟩ := input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
    restricted (frame.cursorAt right) (valid right)
  have records : input.compareLocalizedRerootCompoundThroughRule5 l₁ r₁ =
      input.compareLocalizedRerootCompoundThroughRule5 l₂ r₂ := by
    rcases separated with same | different
    · subst right
      have first : l₁ = r₁ := Option.some.inj (hl₁.symm.trans hr₁)
      have second : l₂ = r₂ := Option.some.inj (hl₂.symm.trans hr₂)
      rw [first, second, input.compareLocalizedRerootCompoundThroughRule5_self,
        input.compareLocalizedRerootCompoundThroughRule5_self]
    · exact input.localizedCompoundReaderComparison_eq_of_rootDistance_ne
        full restricted _ (frame.cursorAt left) (frame.cursorAt right)
        l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂ different
  have hl₂' : input.buildLocalizedRerootCompoundRule45Key? target
      (input.localizedDependencyView state target) (2 * (n + 1)) (frame.cursorAt left) = some l₂ := by
    rw [← input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel]
    exact hl₂
  have hr₂' : input.buildLocalizedRerootCompoundRule45Key? target
      (input.localizedDependencyView state target) (2 * (n + 1)) (frame.cursorAt right) = some r₂ := by
    rw [← input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel]
    exact hr₂
  unfold localizedOccurrenceRule45WholeStateFrameComparator
    compareLocalizedOccurrenceThroughRule5At?
  change (do
    let l ← input.buildLocalizedRerootCompoundRule45KeyWithRead? full (2 * (n + 1)) (frame.cursorAt left)
    let r ← input.buildLocalizedRerootCompoundRule45KeyWithRead? full (2 * (n + 1)) (frame.cursorAt right)
    pure (localizedOccurrenceRule45ComparisonRecord (input.compareLocalizedRerootCompoundThroughRule5 l r))) = _
  simp only [hl₁, hr₁, hl₂', hr₂', localizedOccurrenceRerootEvaluationFuel]
  change some (localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 l₁ r₁)) =
    some (localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 l₂ r₂))
  rw [records]

/-- Equality of the actual whole-state and restricted callbacks on every pair of an actual
four-ligand frame at a real descriptor-bearing carrier occurrence. -/
theorem localizedActualFrame_wholeState_comparisons_eq
    (input : CertifiedLocalizedCIPInput) {n : Nat}
    (target : input.LocalizedCIPOccurrence n) (active : target.1.node.ActiveSimple)
    (state : input.LocalizedAuxiliaryState n)
    (frame : input.LocalizedOccurrenceFourLigandFrame n)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (left right : Fin 4) :
    input.localizedOccurrenceRule45WholeStateFrameComparator state frame left right =
      input.compareLocalizedOccurrenceThroughRule5At? target
        (input.localizedDependencyView state target) frame left right := by
  by_cases same : left = right
  · exact frame_pair_eq_of_self_or_distance input target state frame computed left right (Or.inl same)
  rcases input.localizedOccurrenceFourLigandFrame_cursorAt_classification
      target frame computed left with leftParent | leftOutward
  · rcases leftParent with ⟨certificate, parentEq, parentAddress⟩
    rcases input.localizedOccurrenceFourLigandFrame_cursorAt_classification
        target frame computed right with rightParent | rightOutward
    · exact False.elim (input.localizedOccurrenceFourLigandFrame_no_two_parent_cursors
        target frame computed same ⟨parentAddress, rightParent.choose_spec.2⟩)
    · rcases rightOutward.1 with ⟨slot, address⟩
      have cut := input.localizedActualFrame_outward_mem_parentCut
        target active frame computed certificate right slot address
      have different := input.outwardChild_rule1bRootDistance_ne_parent
        target active certificate (frame.cursorAt right) slot cut address
      apply frame_pair_eq_of_self_or_distance input target state frame computed left right
      apply Or.inr
      rw [parentEq]
      exact different
  · rcases leftOutward.1 with ⟨leftSlot, leftAddress⟩
    rcases input.localizedOccurrenceFourLigandFrame_cursorAt_classification
        target frame computed right with rightParent | rightOutward
    · rcases rightParent with ⟨certificate, parentEq, _parentAddress⟩
      have cut := input.localizedActualFrame_outward_mem_parentCut
        target active frame computed certificate left leftSlot leftAddress
      have different := input.outwardChild_rule1bRootDistance_ne_parent
        target active certificate (frame.cursorAt left) leftSlot cut leftAddress
      apply frame_pair_eq_of_self_or_distance input target state frame computed left right
      apply Or.inr
      rw [parentEq]
      exact Ne.symm different
    · rcases rightOutward.1 with ⟨rightSlot, rightAddress⟩
      have leftDeeper : target.1.address.length <
          (frame.cursorAt left).occurrence.1.address.length := by
        rw [leftAddress, List.length_append]
        simp
      have rightDeeper : target.1.address.length <
          (frame.cursorAt right).occurrence.1.address.length := by
        rw [rightAddress, List.length_append]
        simp
      exact (input.localizedOccurrenceRule45WholeStateFrameComparator_eq_restricted_of_frame
        target state frame computed left right leftDeeper rightDeeper).trans
        (input.localizedOccurrenceRule45RestrictedFrameComparator_eq target
          (input.localizedDependencyView state target) frame left right)

/-- The actual whole-state occurrence descriptor equals the shipped restricted descriptor.
Activity is derived from actual descriptor-center recognition, not supplied as a premise. -/
theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted
    (input : CertifiedLocalizedCIPInput) {n : Nat}
    (target : input.LocalizedCIPOccurrence n) (state : input.LocalizedAuxiliaryState n) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state =
      input.localizedOccurrenceRule45Descriptor? target
        (input.localizedDependencyView state target) := by
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      exact input.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_center?_eq_none
        target state centerComputed
  | some center =>
      have active := input.localizedOccurrenceDescriptorCenter?_activeSimple target center centerComputed
      unfold localizedOccurrenceRule45WholeStateDescriptor?
      apply input.localizedOccurrenceRule45DescriptorWith?_eq_restricted_of_frame_comparisons
      intro frame computed left right
      exact input.localizedActualFrame_wholeState_comparisons_eq
        target active state frame computed left right


theorem localizedWholeStateRule45DescriptorAgreement
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedWholeStateRule45DescriptorAgreement fuel := by
  intro state target
  exact input.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted target state

/-- The existing finite iteration is a fixed point of the genuine whole-state step. -/
theorem localizedOccurrenceRule45WholeStateStep_fixed_unconditional
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.localizedOccurrenceRule45WholeStateStep (fuel := fuel)
      (input.evaluateLocalizedOccurrences fuel
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule) =
      input.evaluateLocalizedOccurrences fuel
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule :=
  input.localizedOccurrenceRule45WholeStateStep_fixed fuel
    (input.localizedWholeStateRule45DescriptorAgreement fuel)

/-- Unique whole-state fixed point in the stated localized original-root Rule-45 model. -/
theorem existsUnique_localizedOccurrenceRule45WholeStateFixedPoint_unconditional
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ∃! state, input.LocalizedWholeStateRule45FixedPoint fuel state :=
  input.existsUnique_localizedOccurrenceRule45WholeStateFixedPoint fuel
    (input.localizedWholeStateRule45DescriptorAgreement fuel)

/-- Exact whole-state iteration equality, with no descriptor-agreement premise. -/
theorem evaluateLocalizedOccurrences_eq_wholeStateIterate_unconditional
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.evaluateLocalizedOccurrences fuel
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel).executableRule =
      DeclarativeCIP.RankedIteration.iterate
        (input.localizedOccurrenceRule45WholeStateStep (fuel := fuel))
        (fun _ => none) (fuel + 2) :=
  input.evaluateLocalizedOccurrences_eq_wholeStateIterate fuel
    (input.localizedWholeStateRule45DescriptorAgreement fuel)

/-- Whole-state fixed points coincide with the existing canonical Rule-45 model. -/
theorem localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel_unconditional
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    input.LocalizedWholeStateRule45FixedPoint fuel state ↔
      (input.localizedAuxiliaryOccurrenceSystem
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state :=
  input.localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel fuel state
    (input.localizedWholeStateRule45DescriptorAgreement fuel)

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCompoundReaderComparison_eq_of_rootDistance_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedActualFrame_outward_mem_parentCut

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedActualFrame_wholeState_comparisons_eq

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedWholeStateRule45DescriptorAgreement

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateStep_fixed_unconditional

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.existsUnique_localizedOccurrenceRule45WholeStateFixedPoint_unconditional

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.evaluateLocalizedOccurrences_eq_wholeStateIterate_unconditional

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel_unconditional
