import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerMarkedSlot
import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000









namespace TetraStereo.OneCenter.LocalizedChemicalRingJointOrientationExecution

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots slotKeys)
open LocalizedChemicalRingJointMarkerEligibility
open LocalizedChemicalRingJointMarkerMarkedSlot
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedMolecularSelection
open LocalizedChemicalRingSelectedOutwardTie
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedActualBoundaryObservationReadback (occurrence_history_facts)
open LocalizedChemicalRingJointMarkerRanking (frames)
open LocalizedChemicalRingTwoFixedNeighbors (local_odd_of_two_fixed_neighbors)

noncomputable section
open scoped Classical
variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (references : List input.Atom)

theorem selected_slots_of_tie (state : OccurrenceAuxState) (left right : Fin 4)
    (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data state references left =
      slotKeys input mol single c node data state references right) :
    left ∈ selectedSlots input mol single c node data state references ∧
      right ∈ selectedSlots input mol single c node data state references := by
  have member (a b : Fin 4) (different : a ≠ b)
      (equal : slotKeys input mol single c node data state references a =
        slotKeys input mol single c node data state references b) :
      a ∈ selectedSlots input mol single c node data state references := by
    change a ∈ LocalizedChemicalRingJointMarkerEligibility.eligibleSlots input single state
      data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
      references (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
    exact (LocalizedChemicalRingJointMarkerEligibility.eligible_iff_other input single state
      data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
      references (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) a).mpr
      ⟨b, Ne.symm different, equal.symm⟩
  exact ⟨member left right distinct tie, member right left (Ne.symm distinct) tie.symm⟩

private theorem current_of_value {value : Option input.Atom} {atom : input.Atom}
    (equal : value.map Fin.val = some atom.val) : value = some atom := by
  cases value with
  | none => cases equal
  | some a =>
      simp only [Option.map_some, Option.some.injEq] at equal
      exact congrArg some (Fin.ext equal)

private theorem frame_slot_current (slot : Fin 4) :
    (data.frame.cursorAt slot).occurrence.1.node.current? =
      some (referenceAt input mol c node data slot) :=
  current_of_value input (data.atomAt_eq slot)

/-- In a tied root arm, a selected joint fallback slot is distinct from the actual incoming parent,
and that parent is a history atom adjacent to the occurrence centre. -/
theorem selected_parent (branch : TiedRootBranch input data.target)
    (state : OccurrenceAuxState) (slot : Fin 4)
    (selected : slot ∈ selectedSlots input mol single c node data state references) :
    ∃ parent : input.Atom, parent ∈ data.target.1.node.history ∧
      input.moleculeGraph.Adj c.1 parent ∧
      parent ≠ referenceAt input mol c node data slot := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let execution := frames input single state data.target data.real unit rfl
  obtain ⟨parentSlot, parentClass, separated⟩ :=
    LocalizedChemicalRingJointMarkerEligibility.parent_joint_singleton input single state
      data.target data.real unit rfl references (retainedCarrierFuel input)
      (2 * (retainedCarrierFuel input + 1)) branch
  have differentSlot : slot ≠ parentSlot := by
    intro same
    obtain ⟨other, otherNe, tie⟩ :=
      (LocalizedChemicalRingJointMarkerEligibility.eligible_iff_other input single state
        data.target data.real unit rfl references (retainedCarrierFuel input)
        (2 * (retainedCarrierFuel input + 1)) slot).mp selected
    apply separated other
    · intro sameOther
      exact otherNe (sameOther.trans same.symm)
    · rw [← same]
      exact tie
  have frameEq : execution.frame = data.frame :=
    Option.some.inj (execution.frameComputed.symm.trans data.frameExec)
  have computed : input.localizedOccurrenceFourLigandFrame? data.target = some execution.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? data.target]
    exact execution.frameComputed
  have present : execution.frame.cursorAt parentSlot ∈ execution.frame.cursors :=
    List.get_mem execution.frame.cursors (Fin.cast execution.frame.length_eq.symm parentSlot)
  obtain ⟨certificate, parentEq⟩ := input.localizedOccurrenceFourLigandFrame_parent_cursor_history
    data.target execution.frame computed _ present parentClass
  let parent := referenceAt input mol c node data parentSlot
  have parentCurrent : certificate.parent.1.node.current? = some parent := by
    rw [← parentEq, frameEq]
    exact frame_slot_current input mol c node data parentSlot
  have history := occurrence_history_facts input certificate.parent
    (certificate.parent_provenance input)
  refine ⟨parent, ?_, ?_, ?_⟩
  · rw [certificate.history_eq]
    exact List.mem_cons_of_mem _ (List.mem_of_head? (history.2.symm.trans parentCurrent))
  · exact input.detectedMultiCenterMolecule.ligandAtomAt_adj c (data.ligandOf parentSlot)
  · intro equal
    have same : parentSlot = slot := data.ligandOf.injective
      (input.detectedMultiCenterMolecule.ligandAtomAt_injective c equal)
    exact differentSlot same.symm

/-- A nontrivial molecular map fixing the actual history and the extended reference context
is locally odd. Both fixed neighboring atoms are obtained from the actual selected slot. -/
theorem selected_fixed_context_odd (branch : TiedRootBranch input data.target)
    (state : OccurrenceAuxState) (slot : Fin 4)
    (selected : slot ∈ selectedSlots input mol single c node data state references)
    (e : input.detectedMultiCenterMolecule.Aut)
    (centerFixed : (e : Equiv.Perm input.Atom) c.1 = c.1)
    (historyFixed : ∀ atom ∈ data.target.1.node.history,
      (e : Equiv.Perm input.Atom) atom = atom)
    (marksFixed : ∀ atom ∈ references ++ [referenceAt input mol c node data slot],
      (e : Equiv.Perm input.Atom) atom = atom)
    (moved : ∃ atom, input.moleculeGraph.Adj c.1 atom ∧
      (e : Equiv.Perm input.Atom) atom ≠ atom) :
    permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = -1 := by
  obtain ⟨parent, member, adjacent, different⟩ :=
    selected_parent input mol single c node data references branch state slot selected
  exact (local_odd_of_two_fixed_neighbors input.detectedMultiCenterMolecule e c centerFixed
    parent (referenceAt input mol c node data slot) different adjacent
    (input.detectedMultiCenterMolecule.ligandAtomAt_adj c (data.ligandOf slot))
    (historyFixed parent member)
    (marksFixed _ (by simp)) moved).2

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointOrientationExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOrientationExecution.selected_slots_of_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOrientationExecution.selected_parent

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOrientationExecution.selected_fixed_context_odd
