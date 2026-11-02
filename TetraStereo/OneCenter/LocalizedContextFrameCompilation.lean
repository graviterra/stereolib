import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedRuleMajorReferencePipeline
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundBuilder
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.OneCenter.LocalizedActualReferenceMolecularEvidence
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual four-arm frame and rule-major stage compilation at any detected carrier occurrence.
The target may have a nonempty carrier path. Frame and compound construction are derived from
the finite acyclic single-bond graph and the actual occurrence cursor; no comparison or geometry
success is assumed. -/

namespace TetraStereo.OneCenter
namespace LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical

set_option maxHeartbeats 2000000

def contextOccurrenceView (input : LocalizedUniversalReference.Input)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input)) :
    input.certified.LocalizedDependencyView target :=
  input.certified.localizedDependencyView (referenceState input) target

def contextOccurrenceRead (input : LocalizedUniversalReference.Input)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input)) :
    input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input) →
      Option LocalizedAuxiliaryLabel :=
  input.certified.localizedDependencyLabel target (contextOccurrenceView input target)

/-! The actual detected center and four-cursor frame at an arbitrary carrier occurrence. -/
structure ContextFrameSkeleton (input : LocalizedUniversalReference.Input)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) where
  center : input.certified.TetrahedralCenter
  centerEq : center.1 = unit.1.atom
  centerComputed : input.certified.localizedOccurrenceDescriptorCenter? target = some center
  frame : input.certified.LocalizedOccurrenceFourLigandFrame
    (LocalizedUniversalReference.carrierFuel input)
  frameComputed : input.certified.localizedNoDoubleFourLigandFrameExec? target = some frame
  detectedLigandPermutation : Equiv.Perm (Fin 4)
  ligandAt : ∀ index,
    (frame.cursorAt index).occurrence.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.ligandAtomAt center
        (detectedLigandPermutation index))
  childAt : ∀ index, frame.cursorAt index ∈ input.certified.executableLocalizedRerootChildren
    ({ occurrence := target, previous? := none })

/-- Four actual arm stages and their successful compound builds, with a common finite window
large enough for every stage graph. -/
structure ContextFrameCompilation (input : LocalizedUniversalReference.Input)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    extends ContextFrameSkeleton input target unit targetUnit where
  stages : ∀ index, input.certified.RuleMajorContextStages
    (LocalizedUniversalReference.carrierFuel input)
    (contextOccurrenceRead input target) (frame.cursorAt index)
  compounds : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key
  compoundBuilt : ∀ index,
    input.certified.buildActualRuleMajorCompoundRule45KeyExec? target
      (contextOccurrenceView input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frame.cursorAt index) =
        some (compounds index)
  callbackEq : (fun left right => input.certified.compareRuleMajorOccurrenceExecAt?
      target (contextOccurrenceView input target) frame left right) =
        compoundActualCompareAt input.certified compounds
  W : Nat
  D : Nat
  widthBound : ∀ index, (stages index).widthBound ≤ W
  depthBound : ∀ index, (stages index).depthBound ≤ D

namespace ContextFrameCompilation

variable {input : LocalizedUniversalReference.Input}
  {target : input.certified.LocalizedCIPOccurrence
    (LocalizedUniversalReference.carrierFuel input)}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  (compiled : ContextFrameCompilation input target unit targetUnit)

/-- Physical coordinate lookup at each detected ligand is exactly the actual cursor lookup at
the corresponding compiled frame slot. -/
theorem spatialPoint_readback (points : Fin 4 → CartesianPoint3)
    (physical : ∀ index,
      input.certified.spatialPointAt?
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt compiled.center
          (compiled.detectedLigandPermutation index)) = some (points index)) :
    ∀ index, input.certified.localizedRerootCursorSpatialPoint?
      (compiled.frame.cursorAt index) = some (points index) :=
  input.certified.localizedRerootCursorSpatialPoint?_eq_of_spatialPointAt
    compiled.frame
    (fun index => input.certified.detectedMultiCenterMolecule.ligandAtomAt compiled.center
      (compiled.detectedLigandPermutation index))
    points compiled.ligandAt physical

end ContextFrameCompilation

/-- On a simple-bonded acyclic certified input, every detected carrier occurrence has an actual
four-ligand executable frame. The occurrence may be anywhere in its carrier path. -/
theorem exists_contextFrameSkeleton
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
  Nonempty (ContextFrameSkeleton input target unit targetUnit) := by
  have centerMember : unit.1.atom ∈ input.certified.tetrahedralCenterSet := by
    change unit.1.atom ∈ input.certified.moleculeGraph.tetrahedralCenterSet
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet unit.1.atom).2
      ((input.certified.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card
        unit.1.atom).2 unit.2)
  let center : input.certified.TetrahedralCenter := ⟨unit.1.atom, centerMember⟩
  have detectedCenterMember : unit.1.atom ∈
      input.certified.detectedMultiCenterMolecule.centers := by
    exact (input.certified.moleculeGraph.mem_detectedMultiCenterMolecule_centers_iff
      unit.1.atom).2
      ((input.certified.moleculeGraph.mem_tetrahedralCenterSet unit.1.atom).1 centerMember)
  let detectedCenter : input.certified.detectedMultiCenterMolecule.Center :=
    ⟨unit.1.atom, detectedCenterMember⟩
  obtain ⟨current, currentObserved⟩ :=
    input.certified.localizedRerootCursor_current_exists
      ({ occurrence := target, previous? := none } :
        input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input))
  have realPath := input.certified.carrierOccurrence_realPath singleBonded acyclic target
  have currentHead : target.1.node.history.head? = some current := by
    have h := input.certified.declarativeLocalizedOccurrence_node_history_head_eq_current
      ((input.certified.mem_localizedOccurrences_iff
        (LocalizedUniversalReference.carrierFuel input) target.1).mp target.2)
    rw [currentObserved] at h
    exact h
  have rootLast := input.certified.realPathNode_history_getLast realPath
  have unitAtomCurrent := input.certified.molecularFrameUnit_atom_eq_current target.1
    currentHead rootLast
  have unitAtomEq : unit.1.atom = current := by
    calc
      unit.1.atom = (input.certified.molecularFrameUnit target.1).atom :=
        (congrArg OccurrenceUnit.atom targetUnit).symm
      _ = current := unitAtomCurrent
  have centerEq : detectedCenter.1 = current := unitAtomEq
  have targetCurrent : target.1.node.current? = some center.1 := by
    rw [currentObserved, ← unitAtomEq]
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node center :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target,
      targetCurrent⟩
  have centerComputed : input.certified.localizedOccurrenceDescriptorCenter? target =
      some center :=
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).2 centerReal
  have enough' : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := globalCarrierFuel_adequate input
  obtain ⟨frame, alpha, frameComputed, ligandAt⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      singleBonded acyclic enough' target currentObserved detectedCenter centerEq
  have noDoubleFrameComputed :
      input.certified.localizedNoDoubleFourLigandFrameExec? target = some frame := by
    rw [input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target]
    exact frameComputed
  let targetCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input) :=
    ⟨target, none⟩
  have childAt (index : Fin 4) : frame.cursorAt index ∈
      input.certified.executableLocalizedRerootChildren targetCursor := by
    rw [← input.certified.localizedOccurrenceFourLigandFrame_cursors_eq_executable
      target frame frameComputed]
    exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  exact ⟨{
    center := center
    centerEq := rfl
    centerComputed := centerComputed
    frame := frame
    frameComputed := noDoubleFrameComputed
    detectedLigandPermutation := alpha
    ligandAt := ligandAt
    childAt := childAt }⟩

/-- Every actual frame slot admits all six cumulative stages and an executable compound build.
The common finite windows are the maxima of the four actual stage bounds. -/
theorem exists_contextFrameCompilation
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
  Nonempty (ContextFrameCompilation input target unit targetUnit) := by
  obtain ⟨skeleton⟩ := exists_contextFrameSkeleton input singleBonded acyclic target unit targetUnit
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
end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.contextOccurrenceView
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.contextOccurrenceRead
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameSkeleton
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.exists_contextFrameSkeleton
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.spatialPoint_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.exists_contextFrameCompilation
