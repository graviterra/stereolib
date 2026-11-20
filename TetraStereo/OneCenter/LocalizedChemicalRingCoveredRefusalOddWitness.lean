import TetraStereo.OneCenter.LocalizedChemicalRingCoveredThreeCycleConsensus
import TetraStereo.OneCenter.LocalizedChemicalRingOutwardKeyWitness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
A failed eligible local reading in a Rule-1a-tied carrier arm reconstructs one actual
history- and local-reference-fixing symmetry. The incoming parent is derived from the
actual frame's parent certificate. Its exclusion from the eligible population makes it
distinct from the local reference, so the same reconstructed symmetry is locally odd.
Its support, ranks and optional generated-label witnesses are retained.

On a covered history, the actual three-cycle covariance eliminates disagreement of
successful readings, hence candidate refusal supplies this odd witness. This asserts
neither properness at other centers nor fixation of a different inherited reference.
An independent absence-of-odd-history-symmetry hypothesis then gives step success.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCoveredRefusalOddWitness

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSelectedRefusalWitness LocalizedChemicalRingSelectedParentEligibility
open LocalizedChemicalRingSelectedOutwardTie LocalizedChemicalRingOutwardKeyWitness
open LocalizedChemicalRingTwoFixedNeighbors LocalizedActualBoundaryObservationReadback
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

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

/-- The actual incoming parent is a history atom and a physical neighbor distinct from
every eligible local reference. No parent/reference correspondence is supplied. -/
theorem eligible_reference_parent (branch : TiedRootBranch input data.target)
    (slot : Fin 4) (member : slot ∈ eligibleSlots input mol single c node data) :
    ∃ parent : input.Atom, parent ∈ data.target.1.node.history ∧
      input.moleculeGraph.Adj c.1 parent ∧
      parent ≠ referenceAt input mol c node data slot := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let execution := frames input single [] data.target data.real unit rfl
  have frameEq : execution.frame = data.frame :=
    Option.some.inj (execution.frameComputed.symm.trans data.frameExec)
  have computed : input.localizedOccurrenceFourLigandFrame? data.target = some execution.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? data.target]
    exact execution.frameComputed
  obtain ⟨parentSlot, parentClass, parentExcluded⟩ :=
    parent_not_eligible input mol single c node data branch
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
  refine ⟨parent, ?_, input.detectedMultiCenterMolecule.ligandAtomAt_adj c
    (data.ligandOf parentSlot), ?_⟩
  · rw [certificate.history_eq]
    exact List.mem_cons_of_mem _ (List.mem_of_head? (history.2.symm.trans parentCurrent))
  · intro equal
    have same : parentSlot = slot := data.ligandOf.injective
      (input.detectedMultiCenterMolecule.ligandAtomAt_injective c equal)
    rw [same] at parentExcluded
    exact parentExcluded member

variable
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
  (current : node.atom = c.1.val)

include agreement admissible supported calibrated current in
/-- A failed actual eligible reading yields the SAME matched symmetry with an odd local
frame action. Actual outwardness, marker bounds, parent and reference fixes are derived. -/
theorem failed_eligible_reading_odd_witness (branch : TiedRootBranch input data.target)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (depth : Nat) (reflected : Bool) (slot : Fin 4)
    (member : slot ∈ eligibleSlots input mol single c node data)
    (failed : generatedReading input mol c node data depth reflected slot = none) :
    ∃ (left right : Fin 4) (a b : input.Atom), left ≠ right ∧ a ≠ b ∧
      ∃ w : MatchedSymmetry input single
          (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
          data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
          (referenceAt input mol c node data slot) left right a b,
        input.detectedMultiCenterMolecule.centerPerm w.symmetry c = c ∧
          permHandedness (input.detectedMultiCenterMolecule.ligandPermAt w.symmetry c) = -1 := by
  obtain ⟨left, right, distinct, tie⟩ := (generatedReading_none_iff input mol single cfg c calibrated
    node data agreement admissible supported depth reflected slot).mp failed
  let reference := referenceAt input mol c node data slot
  let state := generated input mol node depth reflected reference.val
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  have targetCurrent : data.target.1.node.current? = some c.1 := by
    apply current_of_value input
    have h := (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).current
    rw [current] at h
    exact h
  change refinedKey input single state data.target data.real unit rfl reference
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
    refinedKey input single state data.target data.real unit rfl reference
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right at tie
  obtain ⟨_, pair, a, b, _, _, _, targetEq, leftEq, rightEq, different,
      currentL, currentR, realL, realR⟩ := selected_refined_tie_real_outward input single
    branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
    branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
    branch.built branch.built' branch.tie state data.target data.real branch.inside branch.nonroot
    c.1 targetCurrent unit rfl reference (retainedCarrierFuel input)
    (2 * (retainedCarrierFuel input + 1)) left right distinct tie
  have rootL := pair.leftRoot
  have rootR := pair.rightRoot
  have addressL := pair.leftAddress
  have addressR := pair.rightAddress
  rw [targetEq, leftEq] at rootL addressL
  rw [targetEq, rightEq] at rootR addressR
  rw [leftEq] at currentL realL
  rw [rightEq] at currentR realR
  obtain ⟨g, rank, fixed, entry, referenceFixed, support, matched⟩ :=
    actual_outward_default_tie_witness input single state data.target data.real unit rfl reference
      left right a b currentL currentR realL realR rootL rootR pair.leftSlot pair.rightSlot
      addressL addressR tie charge
  obtain ⟨parent, parentHistory, parentAdjacent, parentDifferent⟩ :=
    eligible_reference_parent input mol single c node data branch slot member
  have centerHistory : c.1 ∈ data.target.1.node.history :=
    List.mem_of_head? ((occurrence_history_facts input data.target data.real).2.symm.trans targetCurrent)
  let execution := frames input single state data.target data.real unit rfl
  have frameEq : execution.frame = data.frame :=
    Option.some.inj (execution.frameComputed.symm.trans data.frameExec)
  have atAtom : input.detectedMultiCenterMolecule.ligandAtomAt c (data.ligandOf left) = a := by
    have h := data.atomAt_eq left
    change (data.frame.cursorAt left).occurrence.1.node.current?.map Fin.val = _ at h
    rw [← frameEq, currentL, Option.map_some] at h
    exact Fin.ext (Option.some.inj h).symm
  have adjacentA : input.moleculeGraph.Adj c.1 a := by
    rw [← atAtom]
    exact input.detectedMultiCenterMolecule.ligandAtomAt_adj c (data.ligandOf left)
  have odd := local_odd_of_two_fixed_neighbors input.detectedMultiCenterMolecule g c
    (fixed c.1 centerHistory) parent reference parentDifferent parentAdjacent
    (input.detectedMultiCenterMolecule.ligandAtomAt_adj c (data.ligandOf slot))
    (fixed parent parentHistory) referenceFixed ⟨a, adjacentA, by rw [entry]; exact Ne.symm different⟩
  exact ⟨left, right, a, b, distinct, different,
    ⟨currentL, currentR, realL, realR, g, rank, fixed, entry, referenceFixed, support, matched⟩, odd⟩

variable (e : input.detectedMultiCenterMolecule.Aut)
  (reached : Reached mol node) (real : node.provenance = .realAtom)
  (historyFixed : ∀ atom ∈ node.history, relabelOf input (e : Equiv.Perm input.Atom) atom = atom)
  (covered : ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val ∈ node.history)

include agreement admissible supported calibrated current reached real historyFixed covered in
/-- Actual covered-history refusal produces an odd history-fixing molecular symmetry,
retaining the local reference and all evidence from its single key reconstruction. -/
theorem covered_refusal_odd_witness (branch : TiedRootBranch input data.target)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (cube : (slotAction input mol e c node data) ^ 3 = 1)
    (nontrivial : slotAction input mol e c node data ≠ 1)
    (depth : Nat) (ctx : Option Nat) (reflected : Bool)
    (refused : LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input reflected) [] ctx node (generated input mol node depth reflected) = none) :
    ∃ slot ∈ eligibleSlots input mol single c node data,
      generatedReading input mol c node data depth reflected slot = none ∧
      ∃ (left right : Fin 4) (a b : input.Atom), left ≠ right ∧ a ≠ b ∧
        ∃ w : MatchedSymmetry input single
            (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
            data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
            (referenceAt input mol c node data slot) left right a b,
          input.detectedMultiCenterMolecule.centerPerm w.symmetry c = c ∧
            permHandedness (input.detectedMultiCenterMolecule.ligandPermAt w.symmetry c) = -1 := by
  obtain ⟨slot, member, failed, _⟩ :=
    LocalizedChemicalRingCoveredThreeCycleConsensus.refusal_has_failed_eligible input mol single e c
      node data agreement admissible supported reached real current historyFixed covered cfg calibrated
      branch cube nontrivial depth ctx reflected refused
  exact ⟨slot, member, failed, failed_eligible_reading_odd_witness input mol single c node data
    agreement admissible supported cfg calibrated current branch charge depth reflected slot member failed⟩

include agreement admissible supported single calibrated current reached real historyFixed covered in
/-- An independent graph stabilizer condition excludes refusal in this covered three-cycle
case. This concerns one actual geometry-side step, not the complete root report. -/
theorem step_exists_of_no_odd_history_symmetry (branch : TiedRootBranch input data.target)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (cube : (slotAction input mol e c node data) ^ 3 = 1)
    (nontrivial : slotAction input mol e c node data ≠ 1)
    (noOdd : ∀ g : input.detectedMultiCenterMolecule.Aut,
      (∀ atom ∈ data.target.1.node.history, (g : Equiv.Perm input.Atom) atom = atom) →
      permHandedness (input.detectedMultiCenterMolecule.ligandPermAt g c) ≠ -1)
    (depth : Nat) (ctx : Option Nat) (reflected : Bool) :
    ∃ value, LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input reflected) [] ctx node (generated input mol node depth reflected) = some value := by
  cases result : LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input reflected) [] ctx node (generated input mol node depth reflected) with
  | some value => exact ⟨value, rfl⟩
  | none =>
      obtain ⟨_, _, _, _, _, _, _, _, _, w, _, odd⟩ := covered_refusal_odd_witness input mol single c
        node data agreement admissible supported cfg calibrated current e reached real historyFixed covered
        branch charge cube nontrivial depth ctx reflected result
      exact False.elim (noOdd w.symmetry w.fixedHistory odd)

end
end TetraStereo.OneCenter.LocalizedChemicalRingCoveredRefusalOddWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredRefusalOddWitness.eligible_reference_parent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredRefusalOddWitness.failed_eligible_reading_odd_witness
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredRefusalOddWitness.covered_refusal_odd_witness
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredRefusalOddWitness.step_exists_of_no_odd_history_symmetry
