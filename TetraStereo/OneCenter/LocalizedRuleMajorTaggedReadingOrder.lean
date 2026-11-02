import TetraStereo.OneCenter.DeclarativeCIPTaggedCompleteReadings
import TetraStereo.OneCenter.LocalizedRuleMajorActualAlternativeOrdering
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundIndependentReadings
import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcOutcomeOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual compound reading list retains exactly the reference tags in the independent
complete-reading order.  The two-reading tie case is proved from the actual comparator and its
stage-key provenance, so equal readings retain the production [R, S] input order. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open Rule4aTableBridge
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {index : Fin 4}
  {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)}

private def actualTaggedBranchCompiler (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)) :
    input.RuleMajorCompoundStageCompiler
      (input.certified.input.molecule.atomCount + 1) :=
  fun stage cursor => input.buildRuleMajorCumulativeWithRead? stage
    (input.molecularReader descriptorMap target)
    (2 * (input.certified.input.molecule.atomCount + 1 + 1)) cursor

private def taggedBranchReading
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference : Option RS) : input.LocalizedRerootRule4bcReading :=
  match reference with
  | none =>
      { reference? := none, rule4bKey := stages.a.key,
        rule4cKey := stages.noReference.key }
  | some selected =>
      { reference? := some selected, rule4bKey := (stages.b selected).key,
        rule4cKey := (stages.c selected).key }

private theorem taggedBranchReading_build
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference : Option RS) :
    input.buildRuleMajorCompoundRule4bcReadingWith?
        (actualTaggedBranchCompiler input descriptorMap target)
        (input.localizedLigandRootCursor center index) reference =
      some (taggedBranchReading stages reference) := by
  cases reference with
  | none =>
      simp [CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingWith?,
        actualTaggedBranchCompiler, taggedBranchReading, stages.a.built,
        stages.noReference.built]
  | some selected =>
      simp [CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingWith?,
        actualTaggedBranchCompiler, taggedBranchReading, (stages.b selected).built,
        (stages.c selected).built]

private theorem taggedBranchReadings_build
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (references : List (Option RS)) :
    input.buildRuleMajorCompoundRule4bcReadingsWith?
        (actualTaggedBranchCompiler input descriptorMap target)
        (input.localizedLigandRootCursor center index) references =
      some (references.map (taggedBranchReading stages)) := by
  induction references with
  | nil => rfl
  | cons reference references ih =>
      simp only [CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingsWith?,
        Option.bind_eq_bind, taggedBranchReading_build stages reference, ih,
        Option.bind_some]
      rfl

/-- Successful actual compound construction gives the exact independently ordered reference
tags.  The result preserves sense identity even when both complete readings tie. -/
theorem buildActualRuleMajorCompoundRule45Key?_taggedAlternativeReferences
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    {W D : Nat} (widthBound : stages.widthBound ≤ W) (depthBound : stages.depthBound ≤ D)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildActualRuleMajorCompoundRule45Key? target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center index) = some compound) :
    compound.prior.readings.map (fun reading => reading.reference?.map senseOf) =
      DeclarativeCIP.taggedAlternativeReferencesAt input.moleculeGraph descriptorMap
        (input.topUnit center) stages.graph W D := by
  let fuel := 2 * (input.certified.input.molecule.atomCount + 1 + 1)
  let cursor := input.localizedLigandRootCursor center index
  let compiler := actualTaggedBranchCompiler input descriptorMap target
  let selection := DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
    (input.topUnit center) stages.graph
  let stageData := input.buildActualRuleMajorCompoundRule45Key?_independentReadback
    descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic stages
    widthBound depthBound built
  have uniformBuilt : input.buildRuleMajorCompoundRule45KeyWith? compiler cursor =
      some compound := by
    have uniform := input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor
      target (input.molecularView descriptorMap target) fuel cursor
    simpa [compiler, actualTaggedBranchCompiler, fuel, cursor] using uniform.symm.trans built
  obtain ⟨_, _, _, rawReadings, rawBuilt, rankedReadings, _⟩ :=
    input.buildRuleMajorCompoundRule45KeyWith?_readback compiler cursor uniformBuilt
  let alternatives := localizedRule4bcReferenceAlternatives compound.prior.references
  have expectedRaw := taggedBranchReadings_build stages alternatives
  have rawEq : rawReadings = alternatives.map (taggedBranchReading stages) :=
    Option.some.inj (rawBuilt.symm.trans expectedRaw)
  have referencesEq : compound.prior.references = toReferenceList
      (DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
        (input.topUnit center) stages.graph) := stageData.references
  have alternativesEq :
      alternatives = localizedRule4bcReferenceAlternatives (toReferenceList
        (DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
          (input.topUnit center) stages.graph)) := by
    dsimp [alternatives]
    rw [referencesEq]
  rw [rankedReadings, rawEq, alternativesEq]
  cases selectionEq : DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
      (input.topUnit center) stages.graph with
  | empty =>
      simp [localizedRule4bcReferenceAlternatives, toReferenceList,
        DeclarativeCIP.taggedAlternativeReferencesAt, selectionEq, rankReadings,
        taggedBranchReading]
  | one sense =>
      cases sense with
      | senior =>
          simp [localizedRule4bcReferenceAlternatives, toReferenceList,
            DeclarativeCIP.taggedAlternativeReferencesAt, selectionEq, rankReadings,
            taggedBranchReading, Rule4aTableBridge.senseOf]
      | junior =>
          simp [localizedRule4bcReferenceAlternatives, toReferenceList,
            DeclarativeCIP.taggedAlternativeReferencesAt, selectionEq, rankReadings,
            taggedBranchReading, Rule4aTableBridge.senseOf]
  | both =>
      have comparison := Rule4aTableBridge.actual_ruleMajor_completeReading_compare
        descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic
        stages.a (stages.b .R) (stages.c .R) (stages.b .S) (stages.c .S)
        stages.graph stages.a.faithful
        (stages.b_width_le .R |>.trans widthBound)
        (stages.b_depth_le .R |>.trans depthBound)
        (stages.c_width_le .R |>.trans widthBound)
        (stages.c_depth_le .R |>.trans depthBound)
        (stages.b_width_le .S |>.trans widthBound)
        (stages.b_depth_le .S |>.trans depthBound)
        (stages.c_width_le .S |>.trans widthBound)
        (stages.c_depth_le .S |>.trans depthBound)
      have taggedCompare :
          input.compareRule4bcReadingsComplete (taggedBranchReading stages (some .R))
              (taggedBranchReading stages (some .S)) =
            compare
              (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
                stages.graph W D (some .senior))
              (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
                stages.graph W D (some .junior)) := by
        simpa [taggedBranchReading, Rule4aTableBridge.senseOf] using comparison
      simp only [localizedRule4bcReferenceAlternatives, toReferenceList, selectionEq,
        DeclarativeCIP.taggedAlternativeReferencesAt, rankReadings,
        List.map_cons, List.map_nil]
      rw [taggedCompare]
      split_ifs <;> simp [taggedBranchReading, Rule4aTableBridge.senseOf]

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45Key?_taggedAlternativeReferences
