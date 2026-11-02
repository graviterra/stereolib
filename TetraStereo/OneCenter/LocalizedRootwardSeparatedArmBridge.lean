import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedRetainedConstitutionalReaderIndependence
import TetraStereo.OneCenter.LocalizedRootBranchAuxiliaryLocality
import TetraStereo.OneCenter.LocalizedRootwardConstitutionalSeparation
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Actual parent-slot separation inside a Rule-1a tied root arm

`rootArmRule1aTie_rootward_rule1a_ne_outward` compares retained cuts. This module
places that comparison on the actual four-ligand frame: the derived parent slot
satisfies `ArmConstitutionalRule1aSeparated`, and branch-only map agreement then
gives the actual descriptor. The root-pair tie remains the earlier comparison's
case premise.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open LocalizedRootwardConstitutionalSeparation (carrierFuel)

/-- Standard evaluation budget: twice one more than the carrier fuel. -/
abbrev evaluationFuel (input : CertifiedLocalizedCIPInput) : Nat :=
  localizedOccurrenceRerootEvaluationFuel (carrierFuel input)

/-- Constant absence of an auxiliary label. -/
abbrev constNoneRead (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootCursor (carrierFuel input) → Option LocalizedAuxiliaryLabel :=
  fun _ => none

private theorem cursorAt_mem_executable
    (input : CertifiedLocalizedCIPInput)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    frame.cursorAt index ∈ input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor (carrierFuel input)) := by
  rw [← input.localizedOccurrenceFourLigandFrame_cursors_eq_executable target frame computed]
  exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)

private theorem history_reverse_prefix_of_rootBranch
    (input : CertifiedLocalizedCIPInput)
    (branch target : input.LocalizedCIPOccurrence (carrierFuel input))
    (inside : input.RootBranchContains branch target) :
    branch.1.node.history.reverse <+: target.1.node.history.reverse := by
  have suffix := input.history_suffix_of_rootBranch branch target inside.1 inside.2
  obtain ⟨extra, histEq⟩ := suffix
  refine ⟨extra.reverse, ?_⟩
  simp [← histEq, List.reverse_append]

private theorem child_valid_of_mem
    (input : CertifiedLocalizedCIPInput)
    (parent child : input.LocalizedRerootCursor (carrierFuel input))
    (mem : child ∈ input.executableLocalizedRerootChildren parent) :
    input.LocalizedRerootCursorValid child :=
  input.localizedRerootChild_valid parent child
    (input.executableLocalizedRerootChildren parent)
    (input.executableLocalizedRerootChildren_declarative parent) mem

/-- The derived constant-none Rule-4a key at evaluation fuel has the supplied build's
Rule-1a table. The supplied build may use any reader and any recursion budget. -/
theorem constNone_rule4a_rule1a_eq
    (input : CertifiedLocalizedCIPInput)
    (cursor : input.LocalizedRerootCursor (carrierFuel input))
    (valid : input.LocalizedRerootCursorValid cursor)
    (read : input.LocalizedRerootCursor (carrierFuel input) → Option LocalizedAuxiliaryLabel)
    {fuel : Nat} (key : input.LocalizedRerootCumulativeRule45Key)
    (built : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel cursor =
      some key) :
    ∃ noneKey, input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
        (constNoneRead input) (evaluationFuel input) cursor = some noneKey ∧
      noneKey.constitutional.rule1a = key.constitutional.rule1a := by
  obtain ⟨arm⟩ := input.exists_ruleMajorContextArm (carrierFuel input) .rule4a
    (constNoneRead input) cursor valid
  have suppliedMajor : input.buildRuleMajorCumulativeWithRead? .rule4a read fuel cursor =
      some key :=
    (input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized read fuel cursor).trans built
  have tables :=
    RetainedConstitutionalReaderIndependence.ruleMajorBuild_constitutionalTables_eq
      (input := input) (carrierFuel := carrierFuel input)
      .rule4a .rule4a read (constNoneRead input) cursor suppliedMajor arm.built
  refine ⟨arm.key, ?_, tables.1.symm⟩
  rw [← input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (constNoneRead input) (evaluationFuel input) cursor]
  simpa [evaluationFuel, localizedOccurrenceRerootEvaluationFuel] using arm.built

private theorem rule1a_ne_of_contextArms
    {input : CertifiedLocalizedCIPInput}
    {left right : input.LocalizedRerootCursor (carrierFuel input)}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftArm : input.RuleMajorContextArm (carrierFuel input) .rule4a (constNoneRead input) left)
    (rightArm : input.RuleMajorContextArm (carrierFuel input) .rule4a (constNoneRead input) right)
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (constNoneRead input) (evaluationFuel input) left = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (constNoneRead input) (evaluationFuel input) right = some rightKey)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      leftArm.key.constitutional.rule1a rightArm.key.constitutional.rule1a ≠ Ordering.eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      leftKey.constitutional.rule1a rightKey.constitutional.rule1a ≠ Ordering.eq := by
  have leftMajor : input.buildRuleMajorCumulativeWithRead? .rule4a (constNoneRead input)
      (evaluationFuel input) left = some leftKey := by
    rw [input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
      (constNoneRead input) (evaluationFuel input) left]
    simpa [evaluationFuel, localizedOccurrenceRerootEvaluationFuel] using leftBuilt
  have rightMajor : input.buildRuleMajorCumulativeWithRead? .rule4a (constNoneRead input)
      (evaluationFuel input) right = some rightKey := by
    rw [input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
      (constNoneRead input) (evaluationFuel input) right]
    simpa [evaluationFuel, localizedOccurrenceRerootEvaluationFuel] using rightBuilt
  have leftEq : leftKey = leftArm.key := by
    have joined := leftMajor.symm.trans leftArm.built
    injection joined
  have rightEq : rightKey = rightArm.key := by
    have joined := rightMajor.symm.trans rightArm.built
    injection joined
  rw [leftEq, rightEq]
  exact decisive

/-- Every actual parent slot of a real target inside a Rule-1a tied root arm is
constitutionally separated from the other frame slots. -/
theorem armConstitutionalRule1aSeparated_of_rootArmRule1aTie
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ []) :
    ∀ index, IsLocalizedActualFrameParentCursor input target (frame.cursorAt index) →
      input.ArmConstitutionalRule1aSeparated frame index := by
  have armValid := child_valid_of_mem input rootCursor armCursor armMem
  have armValid' := child_valid_of_mem input rootCursor armCursor' armMem'
  obtain ⟨noneArm⟩ := input.exists_ruleMajorContextArm (carrierFuel input) .rule4a
    (constNoneRead input) armCursor armValid
  obtain ⟨noneArm'⟩ := input.exists_ruleMajorContextArm (carrierFuel input) .rule4a
    (constNoneRead input) armCursor' armValid'
  have tieNone : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      noneArm.key.constitutional.rule1a noneArm'.key.constitutional.rule1a = Ordering.eq := by
    obtain ⟨noneKey, noneBuilt, noneEq⟩ :=
      constNone_rule4a_rule1a_eq input armCursor armValid armRead armKey armBuilt
    obtain ⟨noneKey', noneBuilt', noneEq'⟩ :=
      constNone_rule4a_rule1a_eq input armCursor' armValid' armRead' armKey' armBuilt'
    have noneMajor : input.buildRuleMajorCumulativeWithRead? .rule4a (constNoneRead input)
        (evaluationFuel input) armCursor = some noneKey := by
      rw [input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
        (constNoneRead input) (evaluationFuel input) armCursor]
      simpa [evaluationFuel, localizedOccurrenceRerootEvaluationFuel] using noneBuilt
    have noneMajor' : input.buildRuleMajorCumulativeWithRead? .rule4a (constNoneRead input)
        (evaluationFuel input) armCursor' = some noneKey' := by
      rw [input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
        (constNoneRead input) (evaluationFuel input) armCursor']
      simpa [evaluationFuel, localizedOccurrenceRerootEvaluationFuel] using noneBuilt'
    have keyEq : noneKey = noneArm.key := by
      have joined := noneMajor.symm.trans noneArm.built
      injection joined
    have keyEq' : noneKey' = noneArm'.key := by
      have joined := noneMajor'.symm.trans noneArm'.built
      injection joined
    rw [← keyEq, ← keyEq', noneEq, noneEq']
    exact tie
  let targetCursor : input.LocalizedRerootCursor (carrierFuel input) :=
    { occurrence := target, previous? := none }
  have targetOnArm : armCursor.occurrence.1.node.history.reverse <+:
      targetCursor.occurrence.1.node.history.reverse :=
    history_reverse_prefix_of_rootBranch input armCursor.occurrence target inside
  obtain ⟨parentIndex, _certificate, _parentEq, parentClass, others⟩ :=
    input.actualFrame_parentIndex target frame computed nonroot
  have separatedParent : input.ArmConstitutionalRule1aSeparated frame parentIndex := by
    intro other otherNe keyD keyO builtD builtO
    have parentValid := input.frameCursor_valid target frame computed parentIndex
    have outwardValid := input.frameCursor_valid target frame computed other
    obtain ⟨parentArm⟩ := input.exists_ruleMajorContextArm (carrierFuel input) .rule4a
      (constNoneRead input) (frame.cursorAt parentIndex) parentValid
    obtain ⟨outArm⟩ := input.exists_ruleMajorContextArm (carrierFuel input) .rule4a
      (constNoneRead input) (frame.cursorAt other) outwardValid
    have parentMem := cursorAt_mem_executable input target frame computed parentIndex
    have outwardMem := cursorAt_mem_executable input target frame computed other
    obtain ⟨slot, slotAddr⟩ := (others other otherNe).1
    have outwardDistinct : (frame.cursorAt other).occurrence ≠
        (frame.cursorAt parentIndex).occurrence := by
      intro same
      have addrEq : (frame.cursorAt other).occurrence.1.address =
          (frame.cursorAt parentIndex).occurrence.1.address := by
        rw [same]
      rw [slotAddr, parentClass] at addrEq
      have lengthEq := congrArg List.length addrEq
      simp [List.length_append, List.length_dropLast] at lengthEq
      omega
    have decisive :=
      LocalizedRootwardConstitutionalSeparation.rootArmRule1aTie_rootward_rule1a_ne_outward
        input singleBonded rootCursor rootAddress armCursor armCursor' armMem armMem'
        armDistinct armReal armReal' noneArm noneArm' tieNone targetCursor targetReal
        targetOnArm (frame.cursorAt parentIndex) parentMem parentClass parentArm
        (frame.cursorAt other) outwardMem outwardDistinct outArm
    exact rule1a_ne_of_contextArms parentArm outArm builtD builtO decisive
  intro index parentAt
  have sameCursor := input.localizedOccurrenceFourLigandFrame_parent_cursor_unique
    target frame computed (frame.cursorAt index) (frame.cursorAt parentIndex)
    (List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index))
    (List.get_mem frame.cursors (Fin.cast frame.length_eq.symm parentIndex))
    parentAt parentClass
  have indexEq := input.localizedOccurrenceFourLigandFrame_cursorAt_injective
    target frame computed sameCursor
  subst indexEq
  exact separatedParent

/-- Branch-path agreement gives the actual descriptor once the root arms tie at Rule 1a. -/
theorem ruleMajorDescriptor?_eq_of_tiedRootBranch
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ [])
    (agree : ∀ unit, input.OccurrenceUnitExtendsRootBranch armCursor.occurrence unit.1 →
      map₁ unit = map₂ unit) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) :=
  input.ruleMajorDescriptor?_eq_of_rootBranchParentSeparated armCursor.occurrence target
    inside map₁ map₂ frame computed nonroot
    (armConstitutionalRule1aSeparated_of_rootArmRule1aTie input singleBonded rootCursor
      rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead
      armRead' armKey armKey' armBuilt armBuilt' tie target targetReal inside frame computed
      nonroot)
    agree

theorem ruleMajorDescriptorExec?_eq_of_tiedRootBranch
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ [])
    (agree : ∀ unit, input.OccurrenceUnitExtendsRootBranch armCursor.occurrence unit.1 →
      map₁ unit = map₂ unit) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact ruleMajorDescriptor?_eq_of_tiedRootBranch input singleBonded rootCursor rootAddress
    armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead' armKey
    armKey' armBuilt armBuilt' tie target targetReal inside map₁ map₂ frame computed nonroot agree

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP

theorem ruleMajorDescriptor?_eq_of_tiedCyclicRootBranch
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (nonroot : target.1.address ≠ [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (agree : ∀ unit, input.certified.OccurrenceUnitExtendsRootBranch
      armCursor.occurrence unit.1 → map₁ unit = map₂ unit) :
    input.certified.ruleMajorDescriptor? target (input.certified.molecularView map₁ target) =
      input.certified.ruleMajorDescriptor? target
        (input.certified.molecularView map₂ target) := by
  let compilation := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
  have frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target =
      some compilation.frame := by
    rw [← input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target]
    exact compilation.frameComputed
  exact ruleMajorDescriptor?_eq_of_tiedRootBranch input.certified singleBonded rootCursor
    rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead'
    armKey armKey' armBuilt armBuilt' tie target real inside map₁ map₂ compilation.frame
    frameComputed nonroot agree

theorem ruleMajorDescriptorExec?_eq_of_tiedCyclicRootBranch
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (nonroot : target.1.address ≠ [])
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (agree : ∀ unit, input.certified.OccurrenceUnitExtendsRootBranch
      armCursor.occurrence unit.1 → map₁ unit = map₂ unit) :
    input.certified.ruleMajorDescriptorExec? target
        (input.certified.molecularView map₁ target) =
      input.certified.ruleMajorDescriptorExec? target
        (input.certified.molecularView map₂ target) := by
  rw [input.certified.ruleMajorDescriptorExec?_eq target
      (input.certified.molecularView map₁ target),
    input.certified.ruleMajorDescriptorExec?_eq target
      (input.certified.molecularView map₂ target)]
  exact ruleMajorDescriptor?_eq_of_tiedCyclicRootBranch input singleBonded rootCursor rootAddress
    armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead' armKey
    armKey' armBuilt armBuilt' tie target nonroot real unit targetUnit inside map₁ map₂ agree

end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constNone_rule4a_rule1a_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armConstitutionalRule1aSeparated_of_rootArmRule1aTie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_tiedRootBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_tiedRootBranch
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptor?_eq_of_tiedCyclicRootBranch
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptorExec?_eq_of_tiedCyclicRootBranch
