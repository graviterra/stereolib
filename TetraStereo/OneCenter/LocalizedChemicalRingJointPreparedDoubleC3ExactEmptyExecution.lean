import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyExecution

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedExecution (keys generated)
open LocalizedChemicalRingJointMarkerFrameExecution (slotOrder)
open LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyPartition
open LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrder
open LocalizedGenericMarkedRecalculation (Geometry)

noncomputable section

/-- The actual generated empty-context sort puts oxygen first and preserves the native order
of the three tied boron slots. All slot identities and key relations are derived. -/
theorem left_actual_empty_slot_order
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter) (depth : Nat) (geom : Geometry) :
    ∃ q : Equiv.Perm (Fin 4),
      (∀ i, (referenceAt (certified true) mol c leftCenter data (q i)).val = 4 + i.val) ∧
      slotOrder (certified true) mol single_bonded c leftCenter data
        (generated (certified true) mol depth geom leftCenter []) [] =
        q 0 :: (List.finRange 4).filter (fun i => i ≠ q 0) := by
  obtain ⟨q, atoms, tie12, tie23, strict⟩ := left_actual_empty_partition c data depth geom
  let key := keys (certified true) mol single_bonded c leftCenter data depth geom []
  have strictAll (i : Fin 4) (different : i ≠ q 0) : key i < key (q 0) := by
    obtain ⟨j, rfl⟩ := q.surjective i
    apply strict j
    intro same
    exact different (congrArg q same)
  have each (i : Fin 4) (different : i ≠ q 0) : key i = key (q 1) := by
    obtain ⟨j, rfl⟩ := q.surjective i
    fin_cases j
    · exact False.elim (different rfl)
    · rfl
    · exact tie12.symm
    · exact (tie12.trans tie23).symm
  refine ⟨q, atoms, ?_⟩
  exact keyOrder_single_max key (q 0) strictAll
    (fun i j hi hj => (each i hi).trans (each j hj).symm)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyExecution.left_actual_empty_slot_order
