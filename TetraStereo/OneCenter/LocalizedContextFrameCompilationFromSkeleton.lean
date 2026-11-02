import TetraStereo.OneCenter.LocalizedContextFrameCompilation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Compile all six actual arm stages and the actual compound callback from an already
constructed physical four-ligand frame. This step is independent of molecular acyclicity;
ring-specific frame existence is a separate obligation. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical

/-- Every physical frame skeleton compiles through the actual finite evaluator. No successful
stage build, comparison, or descriptor result is assumed. -/
theorem exists_contextFrameCompilation_of_skeleton
    (input : LocalizedUniversalReference.Input)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (skeleton : ContextFrameSkeleton input target unit targetUnit) :
    Nonempty (ContextFrameCompilation input target unit targetUnit) := by
  let stages : ∀ index : Fin 4, input.certified.RuleMajorContextStages
      (LocalizedUniversalReference.carrierFuel input) (contextOccurrenceRead input target)
      (skeleton.frame.cursorAt index) := fun index => Classical.choice
    (input.certified.exists_ruleMajorContextStages_at_actualChild
      (LocalizedUniversalReference.carrierFuel input) (contextOccurrenceRead input target)
      ({ occurrence := target, previous? := none })
      (skeleton.frame.cursorAt index) (skeleton.childAt index))
  have frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target =
      some skeleton.frame := by
    have h := skeleton.frameComputed
    rw [input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target] at h
    exact h
  have compoundsBuiltExists (index : Fin 4) : ∃ compound,
      input.certified.buildActualRuleMajorCompoundRule45KeyExec? target
        (contextOccurrenceView input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1))
        (skeleton.frame.cursorAt index) = some compound := by
    obtain ⟨compound, built⟩ := input.certified.exists_buildActualRuleMajorCompoundRule45Key_at_twice
      target (contextOccurrenceView input target) (skeleton.frame.cursorAt index)
      (LocalizedOccurrenceFourLigandFrame.cursorAt_valid input.certified target skeleton.frame
        (input.certified.localizedOccurrenceFourLigandFrame?_sound target skeleton.frame frameComputed)
        index)
    rw [input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact ⟨compound, built⟩
  let compounds : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key :=
    fun index => Classical.choose (compoundsBuiltExists index)
  have execBuilt (index : Fin 4) :
      input.certified.buildActualRuleMajorCompoundRule45KeyExec? target
        (contextOccurrenceView input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1))
        (skeleton.frame.cursorAt index) = some (compounds index) :=
    Classical.choose_spec (compoundsBuiltExists index)
  have callbackEq : (fun left right => input.certified.compareRuleMajorOccurrenceExecAt?
      target (contextOccurrenceView input target) skeleton.frame left right) =
        compoundActualCompareAt input.certified compounds := by
    funext left
    funext right
    rw [CertifiedLocalizedCIPInput.compareRuleMajorOccurrenceExecAt?,
      localizedOccurrenceRerootEvaluationFuel, execBuilt left, execBuilt right]
    rfl
  let W := Finset.univ.sup fun index : Fin 4 => (stages index).widthBound
  let D := Finset.univ.sup fun index : Fin 4 => (stages index).depthBound
  have widthBound (index : Fin 4) : (stages index).widthBound ≤ W := by
    exact Finset.le_sup (f := fun i : Fin 4 => (stages i).widthBound)
      (Finset.mem_univ index)
  have depthBound (index : Fin 4) : (stages index).depthBound ≤ D := by
    exact Finset.le_sup (f := fun i : Fin 4 => (stages i).depthBound)
      (Finset.mem_univ index)
  exact ⟨{
    toContextFrameSkeleton := skeleton
    stages := stages
    compounds := compounds
    compoundBuilt := execBuilt
    callbackEq := callbackEq
    W := W
    D := D
    widthBound := widthBound
    depthBound := depthBound }⟩

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.exists_contextFrameCompilation_of_skeleton
