import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-! Finite local cursor/child and sparse-label checks only; no cumulative keys are evaluated. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame (target frame)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice (reader)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader (factFirstView)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts (twoFacts)

abbrev Cursor := input.LocalizedRerootCursor 26

def read (cursor : Cursor) : Option LocalizedAuxiliaryLabel :=
  input.localizedDependencyLabel target (factFirstView input twoFacts target) cursor

def oxygenChild (slot : Fin 4) : Cursor :=
  ((reader.readChildren (frame.cursorAt slot)).getD []).headD (frame.cursorAt slot)

theorem oxygen4_child : reader.readChildren (frame.cursorAt 2) = some [oxygenChild 2] := by
  decide +kernel

theorem oxygen15_child : reader.readChildren (frame.cursorAt 3) = some [oxygenChild 3] := by
  decide +kernel

theorem oxygen4_read : read (frame.cursorAt 2) = none := by decide +kernel

theorem oxygen15_read : read (frame.cursorAt 3) = none := by decide +kernel

theorem center3_read : read (oxygenChild 2) = some (.chiral .R) := by decide +kernel

theorem center14_read : read (oxygenChild 3) = some (.chiral .S) := by decide +kernel


end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins.oxygen4_child
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins.oxygen15_child
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins.oxygen4_read
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins.oxygen15_read
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins.center3_read
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins.center14_read
