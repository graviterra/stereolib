import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFrameSlots
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyPartition

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedExecution (keys generated)
open LocalizedChemicalRingJointPreparedDoubleC3ExactFrameSlots
open LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation
open LocalizedChemicalRingJointPreparedDoubleC3ExactFirstSphere
open LocalizedGenericMarkedRecalculation (Geometry)

noncomputable section

/-- The actual empty-context generated keys have exactly the O > (B=B=B) partition.
Every frame identity and comparison in the conclusion is derived, at every recursion depth. -/
theorem left_actual_empty_partition
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter) (depth : Nat) (geom : Geometry) :
    ∃ q : Equiv.Perm (Fin 4),
      (∀ i, (referenceAt (certified true) mol c leftCenter data (q i)).val = 4 + i.val) ∧
      keys (certified true) mol single_bonded c leftCenter data depth geom [] (q 1) =
        keys (certified true) mol single_bonded c leftCenter data depth geom [] (q 2) ∧
      keys (certified true) mol single_bonded c leftCenter data depth geom [] (q 2) =
        keys (certified true) mol single_bonded c leftCenter data depth geom [] (q 3) ∧
      ∀ i : Fin 4, i ≠ 0 →
        keys (certified true) mol single_bonded c leftCenter data depth geom [] (q i) <
          keys (certified true) mol single_bonded c leftCenter data depth geom [] (q 0) := by
  obtain ⟨q, atoms⟩ := left_slots_by_raw_atom c data
  have at0 : referenceAt (certified true) mol c leftCenter data (q 0) = (4 : Fin 25) :=
    Fin.ext (by simpa using atoms 0)
  have at1 : referenceAt (certified true) mol c leftCenter data (q 1) = (5 : Fin 25) :=
    Fin.ext (by simpa using atoms 1)
  have at2 : referenceAt (certified true) mol c leftCenter data (q 2) = (6 : Fin 25) :=
    Fin.ext (by simpa using atoms 2)
  have at3 : referenceAt (certified true) mol c leftCenter data (q 3) = (7 : Fin 25) :=
    Fin.ext (by simpa using atoms 3)
  obtain ⟨tie12, tie23⟩ := left_boron_keys_equal c data depth geom (q 1) (q 2) (q 3) at1 at2 at3
  refine ⟨q, atoms, tie12, tie23, ?_⟩
  intro i nonzero
  apply left_boron_lt_oxygen c data (generated (certified true) mol depth geom leftCenter []) []
    (q 0) (q i) at0
  fin_cases i
  · exact False.elim (nonzero rfl)
  · exact Or.inl at1
  · exact Or.inr (Or.inl at2)
  · exact Or.inr (Or.inr at3)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyPartition

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyPartition.left_actual_empty_partition
