import TetraStereo.OneCenter.LocalizedRuleMajorCompoundRule5Readback
import TetraStereo.OneCenter.LocalizedRuleMajorTaggedReadingOrder
import TetraStereo.OneCenter.LocalizedActualReferenceSelectionBridge
import TetraStereo.OneCenter.LocalizedRuleMajorGeneratedFullComparison
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Shape facts for actual generated compound Rule-5 alternatives. A branch has no reference,
one R/S reference, or both references. The full Rule-5 records are the exact lifts of the
already-built prior readings. This module makes no claim that reference selection is injective
from its count: R and S singleton populations have the same count priority. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput
open DeclarativeCIP LocalizedCumulativeDecoratedTree
noncomputable section
open scoped Classical

private def readingReferences (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCompoundRule45Key) : List (Option RS) :=
  key.prior.readings.map fun reading => reading.reference?

private theorem optionSenseOf_injective :
    Function.Injective (Option.map Rule4aTableBridge.senseOf) := by
  intro left right equal
  cases left with
  | none => cases right <;> simp at equal ⊢
  | some left => cases right with
    | none => simp at equal
    | some right =>
        exact congrArg some
          (Rule4aTableBridge.senseOf_injective (Option.some.inj equal))

/-- The five possible tag/count profiles. The one-reference alternatives keep their actual
sense, and the both-reference alternatives keep the builder's Rule-4b/4c reading order. -/
structure RuleMajorReadingShape (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCompoundRule45Key) : Prop where
  alternatives :
    (key.prior.referenceCountPriority = 0 ∧ key.prior.readings.map (fun reading => reading.reference?) = [none]) ∨
    (key.prior.referenceCountPriority = 2 ∧ key.prior.readings.map (fun reading => reading.reference?) = [some .R]) ∨
    (key.prior.referenceCountPriority = 2 ∧ key.prior.readings.map (fun reading => reading.reference?) = [some .S]) ∨
    (key.prior.referenceCountPriority = 1 ∧ key.prior.readings.map (fun reading => reading.reference?) = [some .R, some .S]) ∨
    (key.prior.referenceCountPriority = 1 ∧ key.prior.readings.map (fun reading => reading.reference?) = [some .S, some .R])
  rule5 : key.rule5Readings = key.prior.readings.map input.ruleMajorExpectedRule5Reading

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {index : Fin 4}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
  (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
  (stages : input.RuleMajorBranchStages center index descriptorMap target)
  {W D : Nat} (widthBound : stages.widthBound ≤ W) (depthBound : stages.depthBound ≤ D)
  {compound : input.LocalizedRerootCompoundRule45Key}

include tetrahedralMap targetRoot targetAddress singleBonded acyclic stages widthBound depthBound

/-- Every successful actual compound build has one of the five legal reference tag/count shapes,
and its whole Rule-5 list is exactly the reference-sensitive lift of its prior reading list. -/
theorem buildActualRuleMajorCompoundRule45Key?_readingShape
    (built : input.buildActualRuleMajorCompoundRule45Key? target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center index) = some compound) :
    RuleMajorReadingShape input compound := by
  have data := input.buildActualRuleMajorCompoundRule45Key?_independentReadback
    descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic
    stages widthBound depthBound built
  have mappedTags := input.buildActualRuleMajorCompoundRule45Key?_taggedAlternativeReferences
    descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic
    stages widthBound depthBound built
  have readback := input.buildActualRuleMajorCompoundRule45Key?_rule5Readings_eq_map
    descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic
    stages widthBound depthBound built
  have tags : (readingReferences input compound).map
      (fun reference => reference.map Rule4aTableBridge.senseOf) =
      taggedAlternativeReferencesAt input.moleculeGraph descriptorMap (input.topUnit center)
        stages.graph W D := by
    simpa [readingReferences] using mappedTags
  have count : compound.prior.referenceCountPriority =
      (referenceSelection input.moleculeGraph descriptorMap (input.topUnit center)
        stages.graph).countPriority := data.count
  have tagShape :
      (compound.prior.referenceCountPriority = 0 ∧ readingReferences input compound = [none]) ∨
      (compound.prior.referenceCountPriority = 2 ∧ readingReferences input compound = [some .R]) ∨
      (compound.prior.referenceCountPriority = 2 ∧ readingReferences input compound = [some .S]) ∨
      (compound.prior.referenceCountPriority = 1 ∧ readingReferences input compound = [some .R, some .S]) ∨
      (compound.prior.referenceCountPriority = 1 ∧ readingReferences input compound = [some .S, some .R]) := by
    have tagsInjective := List.map_injective_iff.mpr optionSenseOf_injective
    cases selection : referenceSelection input.moleculeGraph descriptorMap
        (input.topUnit center) stages.graph with
    | empty =>
        have mapped : (readingReferences input compound).map
            (Option.map Rule4aTableBridge.senseOf) =
            ([none] : List (Option DescriptorSense)) := by
          simpa [taggedAlternativeReferencesAt, selection] using tags
        have raw : readingReferences input compound = [none] := by
          apply tagsInjective
          simpa using mapped
        exact Or.inl ⟨by simpa [selection, ReferenceSelection.countPriority] using count, raw⟩
    | one sense =>
        cases sense with
        | senior =>
            have mapped : (readingReferences input compound).map
                (Option.map Rule4aTableBridge.senseOf) =
                ([some DescriptorSense.senior] : List (Option DescriptorSense)) := by
              simpa [taggedAlternativeReferencesAt, selection, Rule4aTableBridge.senseOf] using tags
            have raw : readingReferences input compound = [some RS.R] := by
              apply tagsInjective
              simpa using mapped
            exact Or.inr (Or.inl ⟨by simpa [selection, ReferenceSelection.countPriority] using count,
              by simpa [RS.R] using raw⟩)
        | junior =>
            have mapped : (readingReferences input compound).map
                (Option.map Rule4aTableBridge.senseOf) =
                ([some DescriptorSense.junior] : List (Option DescriptorSense)) := by
              simpa [taggedAlternativeReferencesAt, selection, Rule4aTableBridge.senseOf] using tags
            have raw : readingReferences input compound = [some RS.S] := by
              apply tagsInjective
              simpa using mapped
            exact Or.inr (Or.inr (Or.inl ⟨by simpa [selection, ReferenceSelection.countPriority] using count,
              by simpa [RS.S] using raw⟩))
    | both =>
        let senior := completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          stages.graph W D (some .senior)
        let junior := completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          stages.graph W D (some .junior)
        by_cases hlt : compare senior junior = .lt
        · have mapped : (readingReferences input compound).map
              (Option.map Rule4aTableBridge.senseOf) =
              ([some DescriptorSense.junior, some DescriptorSense.senior] : List (Option DescriptorSense)) := by
            simpa [taggedAlternativeReferencesAt, selection, senior, junior, hlt] using tags
          have raw : readingReferences input compound = [some RS.S, some RS.R] := by
            apply tagsInjective
            simpa using mapped
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simpa [selection, ReferenceSelection.countPriority] using count,
            by simpa [RS.S, RS.R] using raw⟩)))
        · have mapped : (readingReferences input compound).map
              (Option.map Rule4aTableBridge.senseOf) =
              ([some DescriptorSense.senior, some DescriptorSense.junior] : List (Option DescriptorSense)) := by
            simpa [taggedAlternativeReferencesAt, selection, senior, junior, hlt] using tags
          have raw : readingReferences input compound = [some RS.R, some RS.S] := by
            apply tagsInjective
            simpa using mapped
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by simpa [selection, ReferenceSelection.countPriority] using count,
            by simpa [RS.R, RS.S] using raw⟩)))
  exact ⟨tagShape, readback⟩

end
end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference

/-- The generated own-state data supplies the actual build, so every generated ligand arm has
the same reference-tag and full Rule-5 readback shape. -/
theorem GeneratedRuleMajorFullComparisonData.readingShape
    {input : LocalizedRuleMajorReference.Input}
    {center : input.certified.TetrahedralCenter}
    (data : LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData input center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) (index : Fin 4) :
    CertifiedLocalizedCIPInput.RuleMajorReadingShape input.certified
      (data.compounds index) := by
  let target := LocalizedRuleMajorReference.generatedTarget input center
  let descriptorMap := LocalizedRuleMajorReference.generatedDescriptorMap input
  have builtView : input.certified.buildActualRuleMajorCompoundRule45Key? target
      (input.certified.molecularView descriptorMap target)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center index) = some (data.compounds index) := by
    change input.certified.buildActualRuleMajorCompoundRule45Key? target
      (input.certified.molecularView (LocalizedRuleMajorReference.descriptorMap input) target)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center index) = some (data.compounds index)
    rw [LocalizedRuleMajorReference.molecularView_eq_generatedView
      input singleBonded acyclic target]
    exact data.built index
  exact input.certified.buildActualRuleMajorCompoundRule45Key?_readingShape
    descriptorMap (LocalizedRuleMajorReference.descriptorMap_tetrahedral input)
    target (ActualReaderPhysicalBranchInverse.topTarget_root input center)
    (ActualReaderPhysicalBranchInverse.topTarget_address input center)
    singleBonded acyclic (data.stages index) (data.widthBound index) (data.depthBound index)
    builtView

end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorReadingShape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45Key?_readingShape
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.readingShape
