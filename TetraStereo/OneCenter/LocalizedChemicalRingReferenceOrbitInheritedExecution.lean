import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorInjectivity
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedInjectivity
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual finite recursive evaluator returns a descriptor at the cyclic root
with either inherited O18 reference. Both geometry sides derive key injectivity from
their own generated covering observations. This does not select a reference or establish
the no-context consensus, the absolute letter, or the independent lowercase criterion.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInheritedExecution

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitMarkedInjectivity
open LocalizedChemicalRingReferenceOrbitRootCalibration
open LocalizedChemicalRingReferenceOrbitSecondReferenceSeparation
open LocalizedChemicalRingReferenceOrbitMirrorInjectivity
open LocalizedChemicalRingInheritedReferenceTie LocalizedChemicalRingPhysicalSense
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (structuralDepth)

noncomputable section

/-- No sorting, reader, observation, or desired descriptor premise remains. -/
theorem root_inherited_descriptor_ne_none (mark : Fin 46)
    (allowed : mark = reference ∨ mark = secondReference) :
    LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified) []
      (some mark.val) (canonicalCenterRoot 0) ≠ none := by
  intro refused
  obtain ⟨side, i, j, _, different, tied⟩ := descriptor_none_original_reference_tie certified mol
    structure_agreement admissible supported single_bonded cfg rootCenter root_calibrated
    (canonicalCenterRoot 0) rootData (structuralDepth mol (canonicalCenterRoot 0)) mark refused
  cases side with
  | false =>
      rcases allowed with rfl | rfl
      · exact different (root_markedKeys_injective tied)
      · exact different (second_markedKeys_injective tied)
  | true => exact different (mirror_markedKeys_injective mark allowed tied)

theorem root_inherited_descriptor_exists (mark : Fin 46)
    (allowed : mark = reference ∨ mark = secondReference) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified) []
      (some mark.val) (canonicalCenterRoot 0) = some value := by
  cases result : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified) []
      (some mark.val) (canonicalCenterRoot 0) with
  | none => exact False.elim (root_inherited_descriptor_ne_none mark allowed result)
  | some value => exact ⟨value, rfl⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInheritedExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInheritedExecution.root_inherited_descriptor_ne_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInheritedExecution.root_inherited_descriptor_exists
