import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot
import TetraStereo.OneCenter.LocalizedChemicalRingOrientationDisagreement
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
The actual no-context assigner succeeds on the 46-atom cyclic input. Every eligible
reference and its generated reading comes from the actual selector and recursion.
The result is identified with the two coordinate readings of the derived common
rankings. No desired descriptor or agreement premise is supplied.

This does not yet identify the parity relationship between the original and reflected
rankings, or assert uppercase/lowercase physical correctness or a whole-molecule report.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitConsensusExecution

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitRootEligibility
open LocalizedChemicalRingReferenceOrbitActualReferenceReading
open LocalizedChemicalRingReferenceConsensusRoot
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSelectedParentEligibility (eligible_iff_other)
open LocalizedChemicalRingSenseTransport
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (structuralDepth caseFromMirror? consensus)

noncomputable section
open scoped Classical

private abbrev depth := structuralDepth mol (canonicalCenterRoot 0)
private abbrev slots := eligibleSlots certified mol single_bonded rootCenter
  (canonicalCenterRoot 0) rootData

private theorem reference28_eligible : (28 : Nat) ∈ rootEligible :=
  (root_eligible_iff 28).mpr (by decide)

private theorem root_eligible_map : rootEligible = slots.map (fun slot =>
    (referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot).val) :=
  eligible_eq certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData

private theorem slot_reference_eligible (slot : Fin 4) (member : slot ∈ slots) :
    (referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot).val ∈
      rootEligible := by
  rw [root_eligible_map]
  exact List.mem_map.mpr ⟨slot, member, rfl⟩

private theorem eligible_nonempty : slots ≠ [] := by
  intro empty
  have member := reference28_eligible
  rw [root_eligible_map, empty] at member
  simp at member

private theorem ordinary_not_injective :
    ¬ Function.Injective (ordinaryKeys certified mol single_bonded rootCenter
      (canonicalCenterRoot 0) rootData) := by
  obtain ⟨slot, member⟩ := List.exists_mem_of_ne_nil slots eligible_nonempty
  obtain ⟨other, different, tied⟩ :=
    (eligible_iff_other certified mol single_bonded rootCenter
      (canonicalCenterRoot 0) rootData slot).mp member
  intro injective
  exact different (injective tied)

/-- Each actual no-context step returns the coordinate reading of the common ranking. -/
theorem root_step (side : Bool) :
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
      (observedGeometry certified side) [] none (canonicalCenterRoot 0)
      (generated certified mol (canonicalCenterRoot 0) depth side) =
        some (referenceRaw side 28) := by
  rw [LocalizedChemicalRingInheritedFallback.rawStep_none,
    noContext_eq certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData,
    if_neg ordinary_not_injective]
  apply (consensus_eq_some_iff _ _).mpr
  constructor
  · intro empty
    exact eligible_nonempty (List.map_eq_nil_iff.mp empty)
  · intro value member
    obtain ⟨slot, present, rfl⟩ := List.mem_map.mp member
    change actualReading side
      (referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot) = _
    exact (actualReading_consensus side _ 28
      (slot_reference_eligible slot present) reference28_eligible).trans
        (actualReading_eq side 28 reference28_eligible)

/-- Exact execution through the original/mirrored classifier, with no inherited context. -/
theorem root_assignCenter_eq :
    LocalizedChemicalRingInheritedFallback.assignCenter? mol (sparseOperations certified mol)
      (inputGeometry certified) 0 =
      caseFromMirror? (some (referenceRaw false 28)) (some (referenceRaw true 28)) := by
  unfold LocalizedChemicalRingInheritedFallback.assignCenter?
    LocalizedChemicalRingInheritedFallback.descriptor? descriptorWith
  change caseFromMirror?
    (LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
      (observedGeometry certified false) [] none (canonicalCenterRoot 0)
      (generated certified mol (canonicalCenterRoot 0) depth false))
    (LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
      (observedGeometry certified true) [] none (canonicalCenterRoot 0)
      (generated certified mol (canonicalCenterRoot 0) depth true)) = _
  rw [root_step false, root_step true]

/-- The actual no-context assignment returns a descriptor; its letter and case are not
postulated as inputs to the theorem. -/
theorem root_assignCenter_exists :
    ∃ descriptor, LocalizedChemicalRingInheritedFallback.assignCenter?
      mol (sparseOperations certified mol) (inputGeometry certified) 0 = some descriptor := by
  rw [root_assignCenter_eq]
  cases first : referenceRaw false 28 <;> cases second : referenceRaw true 28 <;>
    exact ⟨_, rfl⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitConsensusExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitConsensusExecution.root_step
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitConsensusExecution.root_assignCenter_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitConsensusExecution.root_assignCenter_exists
