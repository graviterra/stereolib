import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedInjectivity
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Successful marked root execution on the actual generated reference-30 snapshot.
The returned letter is determined by the actual sorted keys and physical coordinates.
This is one marked reading, not yet the root's consensus over eligible references.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedReadback

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitMarkedInjectivity
open LocalizedChemicalRingReferenceOrbitRootCalibration
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingPhysicalSense
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedOperationEvaluator (markedReading?)

noncomputable section

def rootRank := rank certified mol rootCenter (canonicalCenterRoot 0) rootData
  (markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
    rootSnapshot reference)

/-- The actual candidate marked reading succeeds with the coordinate orientation of
its actual sorted keys. Neither a label nor sorting success is supplied. -/
theorem root_marked_reading :
    markedReading? mol (sparseOperations certified mol) (inputGeometry certified) rootSnapshot
      (canonicalCenterRoot 0) reference.val =
      some (letterOfSign (physical.configurationSign cfg rootCenter * permHandedness rootRank)) := by
  rw [marked_reading_eq certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData,
    if_pos root_markedKeys_injective]
  exact readback_enumeration certified cfg rootCenter root_calibrated rootRank

theorem root_marked_reading_present :
    markedReading? mol (sparseOperations certified mol) (inputGeometry certified) rootSnapshot
      (canonicalCenterRoot 0) reference.val ≠ none := by
  rw [root_marked_reading]
  exact Option.some_ne_none _

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedReadback.root_marked_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedReadback.root_marked_reading_present
