import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Transfer a cross-state actual compound comparison to one concrete spliced root state.
The retained frame windows may differ between states: equality is asserted only between
the two keys of the same spliced frame, using its proved comparison correspondence. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceComparison

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedRootArmLocality
open LocalizedChemicalRingJointPreparedRootBranchSelector
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointPreparedRootEmptyContext (refinedKey_nil)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)
  (rootAddress : data.target.1.address = [])
  (leftState rightState : OccurrenceAuxState) (left right : Fin 4)

include rootAddress

theorem compound_left :
    (rootFrame input mol single c node data
      (rootSplice input (referenceAt input mol c node data left) leftState rightState)).compounds left =
      (rootFrame input mol single c node data leftState).compounds left := by
  have first := (rootFrame input mol single c node data
    (rootSplice input (referenceAt input mol c node data left) leftState rightState)).compoundBuilt left
  have second := (rootFrame input mol single c node data leftState).compoundBuilt left
  simp only [rootFrame_eq] at first second
  rw [rootSplice_compound_left input mol single c node data rootAddress leftState rightState left] at first
  exact Option.some.inj (first.symm.trans second)

theorem compound_right (distinct : left ≠ right) :
    (rootFrame input mol single c node data
      (rootSplice input (referenceAt input mol c node data left) leftState rightState)).compounds right =
      (rootFrame input mol single c node data rightState).compounds right := by
  have first := (rootFrame input mol single c node data
    (rootSplice input (referenceAt input mol c node data left) leftState rightState)).compoundBuilt right
  have second := (rootFrame input mol single c node data rightState).compoundBuilt right
  simp only [rootFrame_eq] at first second
  rw [rootSplice_compound_right input mol single c node data rootAddress leftState rightState left right
    distinct] at first
  exact Option.some.inj (first.symm.trans second)

theorem rawKeys_eq_of_crossCompound_tie (distinct : left ≠ right)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5
      ((rootFrame input mol single c node data leftState).compounds left)
      ((rootFrame input mol single c node data rightState).compounds right)).ordering = .eq) :
    let state := rootSplice input (referenceAt input mol c node data left) leftState rightState
    rawStateKeys input single state data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left =
      rawStateKeys input single state data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl right := by
  let state := rootSplice input (referenceAt input mol c node data left) leftState rightState
  have ordering := (rootFrame input mol single c node data state).fullOrdering
    (rawStateDescriptorMap_tetrahedral input state) single
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left right
  rw [compound_left input mol single c node data rootAddress leftState rightState left,
    compound_right input mol single c node data rootAddress leftState rightState left right distinct,
    tie] at ordering
  exact (completeLigandRule5Key_compare_eq_iff _ _).mp ordering.symm

theorem slotKeys_eq_of_crossCompound_tie (distinct : left ≠ right)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5
      ((rootFrame input mol single c node data leftState).compounds left)
      ((rootFrame input mol single c node data rightState).compounds right)).ordering = .eq) :
    let state := rootSplice input (referenceAt input mol c node data left) leftState rightState
    slotKeys input mol single c node data state [] left =
      slotKeys input mol single c node data state [] right := by
  have equal := rawKeys_eq_of_crossCompound_tie input mol single c node data rootAddress
    leftState rightState left right distinct tie
  dsimp only
  unfold slotKeys
  rw [refinedKey_nil, refinedKey_nil, equal]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceComparison

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceComparison.compound_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceComparison.compound_right
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceComparison.rawKeys_eq_of_crossCompound_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceComparison.slotKeys_eq_of_crossCompound_tie
