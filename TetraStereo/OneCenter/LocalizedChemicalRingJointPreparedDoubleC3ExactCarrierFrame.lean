import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier

def cursors : List (input.LocalizedRerootCursor 26) :=
  (LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice.readChildren
    { occurrence := target, previous? := none }).getD []


theorem cursors_actual : cursors =
    input.executableLocalizedRerootChildren { occurrence := target, previous? := none } := by
  unfold cursors
  rw [LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice.readChildren_eq]
  rfl

theorem cursors_length : cursors.length = 4 := by decide +kernel

def frame : input.LocalizedOccurrenceFourLigandFrame 26 :=
  ⟨cursors, cursors_length⟩

theorem actual_frame : input.localizedNoDoubleFourLigandFrameExec? target = some frame := by
  unfold localizedNoDoubleFourLigandFrameExec?
  simp only [executableLocalizedRerootChildren?, ← cursors_actual]
  change (if h : cursors.length = 4 then
    some ({ cursors := cursors, length_eq := h } : input.LocalizedOccurrenceFourLigandFrame 26)
    else none) = some frame
  rw [dif_pos cursors_length]
  rfl

/-- Actual certified frame slots use exactly the explicit raw atom order. -/
theorem frame_atoms (i : Fin 4) :
    (frame.cursorAt i).occurrence.1.node.current? =
      some ((![(4 : Fin 25), 5, 6, 7] : Fin 4 → Fin 25) i) := by
  fin_cases i <;> decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame.cursors_length
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame.frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame.actual_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame.frame_atoms

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame.cursors_actual
