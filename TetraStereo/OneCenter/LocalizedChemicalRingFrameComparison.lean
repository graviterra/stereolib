import TetraStereo.OneCenter.LocalizedChemicalRingRetainedKeyTransport
import TetraStereo.OneCenter.LocalizedChemicalRingLookupTransport
import TetraStereo.OneCenter.LocalizedRetainedActualFrameTransport
import TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual four-ligand comparison matrices under molecular relabelling. The executable frame
permutation is constructed by the existing frame-transport theorem. Raw state labels enter only
through the proved retained-reader transport; comparison success is derived from valid frames. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingFrameComparison

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingStateTransport LocalizedChemicalRingRetainedKeyTransport
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedMolecularSelection

variable (input : CertifiedLocalizedCIPInput)

theorem frame_compound_exists {fuel : Nat}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) (slot : Fin 4) :
    ∃ key, input.buildActualRuleMajorCompoundRule45KeyExec? target
      (input.molecularView descriptorMap target) (2 * (fuel + 1)) (frame.cursorAt slot) = some key := by
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq]
  exact input.exists_buildActualRuleMajorCompoundRule45Key_at_twice target
    (input.molecularView descriptorMap target) (frame.cursorAt slot)
    (LocalizedOccurrenceFourLigandFrame.cursorAt_valid input target frame
      (input.localizedOccurrenceFourLigandFrame?_sound target frame computed) slot)

theorem frame_child {fuel : Nat} (target : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) (slot : Fin 4) :
    frame.cursorAt slot ∈ input.executableLocalizedRerootChildren ⟨target, none⟩ := by
  rw [← input.fourLigandFrame_cursors_eq_executable target frame computed]
  exact List.get_mem frame.cursors _

/-- Every entry of the actual ordinary comparison matrix is preserved by the derived frame
permutation. The state is arbitrary with unique occurrence keys, so generated snapshots qualify. -/
theorem rawStateBefore_transport {mol : RawMolecule}
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)) (center : input.TetrahedralCenter)
    (frames : input.ActualFrameSlotTransport single e target center) (left right : Fin 4) :
    rawStateBefore input state' (input.transportOccurrence single e target) frames.imageFrame
      (frames.slotPerm left) (frames.slotPerm right) =
    rawStateBefore input state target frames.sourceFrame left right := by
  let descriptorMap := rawStateDescriptorMap input state
  let imageMap := input.transportDescriptorMap e descriptorMap
  obtain ⟨a, ha⟩ := frame_compound_exists input descriptorMap target frames.sourceFrame frames.sourceComputed left
  obtain ⟨b, hb⟩ := frame_compound_exists input descriptorMap target frames.sourceFrame frames.sourceComputed right
  obtain ⟨a', ha'⟩ := frame_compound_exists input imageMap _ frames.imageFrame frames.imageComputed (frames.slotPerm left)
  obtain ⟨b', hb'⟩ := frame_compound_exists input imageMap _ frames.imageFrame frames.imageComputed (frames.slotPerm right)
  rw [frames.cursorAt_eq] at ha' hb'
  have same := actual_pair_ordering_transport input single e descriptorMap
    (rawStateDescriptorMap_tetrahedral input state) ⟨target, none⟩
    (frames.sourceFrame.cursorAt left) (frames.sourceFrame.cursorAt right)
    (input.cursorPreviousRootAligned_of_none _ rfl)
    (frame_child input target frames.sourceFrame frames.sourceComputed left)
    (frame_child input target frames.sourceFrame frames.sourceComputed right) a b a' b' ha hb ha' hb'
  dsimp only [imageMap, descriptorMap] at ha hb ha' hb'
  unfold rawStateBefore
  rw [rawStateView_eq_molecularView, rawStateView_eq_molecularView,
    rawStateDescriptorMap_transport input e sym state state' perm unique]
  simp only [compareRuleMajorOccurrenceExecAt?, localizedOccurrenceRerootEvaluationFuel,
    frames.cursorAt_eq, ha, hb, ha', hb', Option.bind_eq_bind, Option.bind_some, Option.map_some]
  exact congrArg some same

end TetraStereo.OneCenter.LocalizedChemicalRingFrameComparison

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrameComparison.frame_compound_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrameComparison.rawStateBefore_transport
