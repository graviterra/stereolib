import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame (target actual_lookup frame actual_frame frame_atoms)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData occurrenceData_exists referenceAt)
open LocalizedMarkedRetainedOrdinaryRanking (rawStateFrames)

noncomputable section

/-- Actual detected center at atom0. -/
def center : input.detectedMultiCenterMolecule.Center :=
  ⟨(0 : Fin 25), by
    change (0 : Fin 25) ∈ graph.tetrahedralCenterSet
    rw [detected_inventory]
    decide⟩

def data : OccurrenceData input mol center root :=
  Classical.choice (occurrenceData_exists input mol (structure_agreement true) admissible
    supported single_bonded center root
    (LocalizedMarkedReachableConfigurations.reached_root mol 0 (by decide)) rfl rfl)

theorem data_target : data.target = target :=
  Option.some.inj (data.found.symm.trans actual_lookup)

theorem data_frame : data.frame = frame := by
  have computed := data.frameExec
  rw [data_target] at computed
  exact Option.some.inj (computed.symm.trans actual_frame)

theorem data_atoms : data.atoms = [1, 2, 4, 15] :=
  Option.some.inj (data.rawFrame.symm.trans raw_frames.1)

theorem reference_slot (i : Fin 4) :
    referenceAt input mol center root data i =
      (![(1 : Fin 25), 2, 4, 15] : Fin 4 → Fin 25) i := by
  apply Fin.ext
  have value : (data.frame.cursorAt i).occurrence.1.node.current? =
      some ((![(1 : Fin 25), 2, 4, 15] : Fin 4 → Fin 25) i) :=
    (congrArg (fun f : input.LocalizedOccurrenceFourLigandFrame 26 =>
      (f.cursorAt i).occurrence.1.node.current?) data_frame).trans (frame_atoms i)
  have mapped := congrArg (fun value : Option (Fin 25) => value.map Fin.val) value
  have observed := data.atomAt_eq i
  change (data.frame.cursorAt i).occurrence.1.node.current?.map Fin.val =
    some (referenceAt input mol center root data i).val at observed
  exact Option.some.inj (observed.symm.trans mapped)

/-- Runtime raw-frame positions are exactly the native certified slots. -/
theorem data_index (i : Fin 4) : data.read.index i = i.val := by
  generalize indexEq : data.read.index i = position
  have found := (data.read.atom i).trans (data.atomAt_eq i)
  change data.atoms[data.read.index i]? =
    some (referenceAt input mol center root data i).val at found
  rw [indexEq] at found
  have atomsEq := congrArg (fun atoms : List Nat => atoms[position]?) data_atoms
  have referenceEq := congrArg (fun atom : Fin 25 => some atom.val) (reference_slot i)
  have concrete := atomsEq.symm.trans (found.trans referenceEq)
  have bound : position < 4 := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp concrete
    exact bound
  interval_cases position <;> fin_cases i <;> simp_all

abbrev unit : DetectedOccurrence input.moleculeGraph :=
  ⟨input.molecularFrameUnit data.target.1, data.detected⟩

abbrev execution (state : OccurrenceAuxState) :=
  rawStateFrames input single_bonded state data.target data.real unit rfl

theorem execution_frame (state : OccurrenceAuxState) :
    (execution state).frame = frame :=
  (Option.some.inj ((execution state).frameComputed.symm.trans data.frameExec)).trans data_frame

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData.center
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData.data
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData.data_target
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData.data_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData.data_atoms
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData.reference_slot
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData.data_index
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData.execution_frame
