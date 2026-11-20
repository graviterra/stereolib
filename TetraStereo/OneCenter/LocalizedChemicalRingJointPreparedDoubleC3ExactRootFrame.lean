import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-! Focused root-only comparison under two explicitly supplied auxiliary facts. Their actual
execution is a separate theorem to substitute later; no actual-output claim is made here. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingDoubleC3Input (root)

def occurrenceFrame : input.LocalizedCIPOccurrenceFrame :=
  { root := (0 : Fin 25), address := [], node := OfficialCIPNode.root (0 : Fin 25), remaining := 27 }

theorem occurrenceFrame_mem : occurrenceFrame ∈ input.localizedOccurrences 26 := by
  apply (input.mem_localizedOccurrences_iff 26 occurrenceFrame).mpr
  change input.DeclarativeLocalizedOccurrenceSubtree (0 : Fin 25) [] 27
    (OfficialCIPNode.root (0 : Fin 25)) occurrenceFrame
  exact @DeclarativeLocalizedOccurrenceSubtree.subtreeRoot input (0 : Fin 25) [] 27
    (OfficialCIPNode.root (0 : Fin 25))

def target : input.LocalizedCIPOccurrence 26 := ⟨occurrenceFrame, occurrenceFrame_mem⟩

theorem actual_lookup : LocalizedMarkedCarrierLookup.lookup? input root = some target := by
  change LocalizedMarkedCarrierLookup.lookupAtRoot? input (0 : Fin 25) root = some target
  unfold LocalizedMarkedCarrierLookup.lookupAtRoot?
  rw [← LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier.computableRooted_eq]
  decide +kernel

def cursors : List (input.LocalizedRerootCursor 26) :=
  (LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice.readChildren
    { occurrence := target, previous? := none }).getD []

theorem cursors_actual : cursors =
    input.executableLocalizedRerootChildren { occurrence := target, previous? := none } := by
  unfold cursors
  rw [LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice.readChildren_eq]
  rfl

theorem cursors_length : cursors.length = 4 := by decide +kernel

def frame : input.LocalizedOccurrenceFourLigandFrame 26 := ⟨cursors, cursors_length⟩

theorem actual_frame : input.localizedNoDoubleFourLigandFrameExec? target = some frame := by
  unfold localizedNoDoubleFourLigandFrameExec?
  simp only [executableLocalizedRerootChildren?, ← cursors_actual]
  change (if h : cursors.length = 4 then
    some ({ cursors := cursors, length_eq := h } : input.LocalizedOccurrenceFourLigandFrame 26)
    else none) = some frame
  rw [dif_pos cursors_length]
  rfl

theorem frame_atoms (i : Fin 4) :
    (frame.cursorAt i).occurrence.1.node.current? =
      some ((![(1 : Fin 25), 2, 4, 15] : Fin 4 → Fin 25) i) := by
  fin_cases i <;> decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame.occurrenceFrame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame.target
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame.cursors_actual
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame.cursors_length
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame.frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame.actual_lookup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame.actual_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame.frame_atoms
