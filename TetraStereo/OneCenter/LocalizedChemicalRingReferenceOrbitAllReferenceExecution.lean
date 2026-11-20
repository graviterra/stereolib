import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootEligibility
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInheritedExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Every actually eligible root reference has strict generated keys and successful
readback on both geometries, hence a successful inherited descriptor. The reference
inventory is derived from the actual selector. Agreement of the four raw readings
is the remaining no-context consensus obligation; it is not assumed or concluded here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllReferenceExecution

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitRootCalibration
open LocalizedChemicalRingReferenceOrbitMarkedInjectivity
open LocalizedChemicalRingReferenceOrbitSecondReferenceSeparation
open LocalizedChemicalRingReferenceOrbitMirrorInjectivity
open LocalizedChemicalRingReferenceOrbitOtherKeySeparation
open LocalizedChemicalRingReferenceOrbitRootEligibility
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingInheritedReferenceTie
open LocalizedChemicalRingPhysicalSense
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedOperationEvaluator (markedReading?)
open LocalizedGenericMarkedRecalculation (structuralDepth)

noncomputable section

private theorem mark_cases (mark : Fin 46) (member : mark.val ∈ rootEligible) :
    mark = (28 : Fin 46) ∨ mark = 29 ∨ mark = 30 ∨ mark = 31 := by
  have values := (root_eligible_iff mark.val).mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at values
  rcases values with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

theorem eligible_keys_injective (side : Bool) (mark : Fin 46) (member : mark.val ∈ rootEligible) :
    Function.Injective (markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0)
      rootData (generated certified mol (canonicalCenterRoot 0)
        (structuralDepth mol (canonicalCenterRoot 0)) side mark.val) mark) := by
  rcases mark_cases mark member with rfl | rfl | rfl | rfl
  · exact other_markedKeys_injective side 28 (Or.inl rfl)
  · exact other_markedKeys_injective side 29 (Or.inr rfl)
  · cases side with
    | false => exact root_markedKeys_injective
    | true => exact mirror_markedKeys_injective reference (Or.inl rfl)
  · cases side with
    | false => exact second_markedKeys_injective
    | true => exact mirror_markedKeys_injective secondReference (Or.inr rfl)

theorem eligible_marked_reading_exists (side : Bool) (mark : Fin 46)
    (member : mark.val ∈ rootEligible) :
    ∃ raw, markedReading? mol (sparseOperations certified mol) (observedGeometry certified side)
      (generated certified mol (canonicalCenterRoot 0)
        (structuralDepth mol (canonicalCenterRoot 0)) side mark.val)
      (canonicalCenterRoot 0) mark.val = some raw := by
  rw [marked_reading_eq certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData,
    if_pos (eligible_keys_injective side mark member)]
  exact readback_some certified cfg rootCenter root_calibrated side _

/-- Every actual eligible reference produces an actual inherited descriptor; both
geometry-side sorts are derived from their own recursively generated observations. -/
theorem eligible_inherited_descriptor_exists (mark : Fin 46) (member : mark.val ∈ rootEligible) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified) []
      (some mark.val) (canonicalCenterRoot 0) = some value := by
  cases result : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified) []
      (some mark.val) (canonicalCenterRoot 0) with
  | none =>
      obtain ⟨side, i, j, _, different, tied⟩ := descriptor_none_original_reference_tie certified mol
        structure_agreement admissible supported single_bonded cfg rootCenter root_calibrated
        (canonicalCenterRoot 0) rootData (structuralDepth mol (canonicalCenterRoot 0)) mark result
      exact False.elim (different (eligible_keys_injective side mark member tied))
  | some value => exact ⟨value, rfl⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllReferenceExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllReferenceExecution.eligible_keys_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllReferenceExecution.eligible_marked_reading_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllReferenceExecution.eligible_inherited_descriptor_exists
