import TetraStereo.OneCenter.LocalizedRuleMajorGeneratedFullComparison
import TetraStereo.OneCenter.LocalizedActualLigandRootSlotCursor
import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual four-ligand callback succeeds and realizes independent complete Rules 1–5
priority at every detected centre of a finite acyclic single-bond input. The frame and the
ligand-to-slot correspondence are derived, and the reader uses the revised evaluator's own
generated state. The pairwise reference-sensitivity flag is not asserted to be physical
enantiomorphism on this unrestricted auxiliary-label domain. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section

structure GeneratedRuleMajorFrameComparisonData (input : Input)
    (center : input.certified.TetrahedralCenter) where
  data : GeneratedRuleMajorFullComparisonData input center
  frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)
  frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
    (generatedTarget input center) = some frame
  ligandToSlot : Equiv.Perm (Fin 4)
  cursorAt : ∀ slot : Fin 4, frame.cursorAt slot =
    input.certified.localizedLigandRootCursor center (ligandToSlot.symm slot)

namespace GeneratedRuleMajorFrameComparisonData

variable {input : Input} {center : input.certified.TetrahedralCenter}
  (frames : GeneratedRuleMajorFrameComparisonData input center)

/-- The actual executable callback returns the compound comparison at the corresponding
canonical ligand indices, on the evaluator's generated dependency view. -/
theorem callback_eq_compound (left right : Fin 4) :
    input.certified.compareRuleMajorOccurrenceExecAt? (generatedTarget input center)
      (input.certified.localizedDependencyView (referenceState input)
        (generatedTarget input center)) frames.frame left right =
      some (localizedOccurrenceRule45ComparisonRecord
        (input.certified.compareLocalizedRerootCompoundThroughRule5
          (frames.data.compounds (frames.ligandToSlot.symm left))
          (frames.data.compounds (frames.ligandToSlot.symm right)))) := by
  rw [input.certified.compareRuleMajorOccurrenceExecAt?_eq]
  unfold compareRuleMajorOccurrenceAt?
  rw [frames.cursorAt left, frames.cursorAt right]
  change (do
    let leftKey ← input.certified.buildActualRuleMajorCompoundRule45Key?
      (generatedTarget input center)
      (input.certified.localizedDependencyView (referenceState input)
        (generatedTarget input center))
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center (frames.ligandToSlot.symm left))
    let rightKey ← input.certified.buildActualRuleMajorCompoundRule45Key?
      (generatedTarget input center)
      (input.certified.localizedDependencyView (referenceState input)
        (generatedTarget input center))
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center (frames.ligandToSlot.symm right))
    some (localizedOccurrenceRule45ComparisonRecord
      (input.certified.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))) = _
  rw [frames.data.built, frames.data.built]
  rfl

/-- Success, exact independent ordering, and exact independent reference-sensitivity for
every actual slot pair. No successful comparison or strictness is assumed. -/
theorem callback_success (left right : Fin 4) :
    ∃ result : ConstitutionalDescriptorHierarchyComparison,
      input.certified.compareRuleMajorOccurrenceExecAt? (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) frames.frame left right = some result ∧
      result.ordering = compare (frames.data.fullKey (frames.ligandToSlot.symm left))
        (frames.data.fullKey (frames.ligandToSlot.symm right)) ∧
      result.ordering = compare (frames.data.rank (frames.ligandToSlot.symm left))
        (frames.data.rank (frames.ligandToSlot.symm right)) ∧
      (result.pseudo = true ↔ ReferenceSensitiveRule5PairAt input.certified.moleculeGraph
        (generatedDescriptorMap input) (input.certified.topUnit center)
        (frames.data.stages (frames.ligandToSlot.symm left)).graph
        (frames.data.stages (frames.ligandToSlot.symm right)).graph frames.data.W frames.data.D) := by
  refine ⟨_, frames.callback_eq_compound left right, ?_, ?_, ?_⟩
  · exact frames.data.actualOrdering _ _
  · exact frames.data.actualOrdering_eq_rankCompare _ _
  · exact frames.data.pseudoFlag _ _

end GeneratedRuleMajorFrameComparisonData

/-- The detected-centre inventory supplies a real successful frame and complete comparisons
in its own generated state, uniformly in molecule size and branch depth. -/
theorem generated_frame_comparison (input : Input)
    (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    Nonempty (GeneratedRuleMajorFrameComparisonData input center) := by
  obtain ⟨data⟩ := generated_full_comparison input center singleBonded acyclic
  obtain ⟨frame, frameComputed⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_of_detectedCenter
      singleBonded acyclic (carrierFuel := carrierFuel input) (by
        change input.certified.certified.input.molecule.atomCount ≤
          input.certified.certified.input.molecule.atomCount + 1
        omega)
      (generatedTarget input center)
      (ActualReaderPhysicalBranchInverse.topTarget_current input center) center rfl
  let sigma : Equiv.Perm (Fin 4) := Equiv.ofBijective
    (ligandSlot input center frame frameComputed center rfl)
    (ligandSlot_bijective input center frame frameComputed center rfl)
  refine ⟨{
    data := data
    frame := frame
    frameComputed := frameComputed
    ligandToSlot := sigma
    cursorAt := ?_ }⟩
  intro slot
  have cursor := cursorAt_ligandSlot input center frame frameComputed center rfl
    (sigma.symm slot)
  change frame.cursorAt (sigma (sigma.symm slot)) = _ at cursor
  simpa only [sigma.apply_symm_apply] using cursor

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_frame_comparison
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.callback_eq_compound
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.callback_success
