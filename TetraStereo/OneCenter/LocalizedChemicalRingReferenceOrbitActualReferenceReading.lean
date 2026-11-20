import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllReferenceExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact readings for every actual eligible reference. Generated-state insertion,
four-key strictness, geometry and readback are all derived. The remaining consensus
question is the parity of these actual reference-specific permutations.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitActualReferenceReading

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitRootCalibration
open LocalizedChemicalRingReferenceOrbitRootEligibility
open LocalizedChemicalRingReferenceOrbitAllReferenceExecution
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingPhysicalSense
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (structuralDepth appendFacts? readback_mirror)

noncomputable section

def referenceRank (side : Bool) (mark : Fin 46) : Equiv.Perm (Fin 4) :=
  rank certified mol rootCenter (canonicalCenterRoot 0) rootData
    (markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
      (generated certified mol (canonicalCenterRoot 0) (structuralDepth mol (canonicalCenterRoot 0))
        side mark.val) mark)

def referenceRaw (side : Bool) (mark : Fin 46) : RS :=
  let raw := letterOfSign (physical.configurationSign cfg rootCenter * permHandedness (referenceRank side mark))
  if side then raw.swap else raw

def actualReading (side : Bool) (mark : Fin 46) : Option RS :=
  LocalizedPhysicalMarkedDistantReference.inheritedRead? mol (sparseOperations certified mol)
    (observedGeometry certified side) [] (canonicalCenterRoot 0)
    (generated certified mol (canonicalCenterRoot 0) (structuralDepth mol (canonicalCenterRoot 0)) side)
    mark.val

/-- The actual inherited reading is the coordinate orientation of its actual key order. -/
theorem actualReading_eq (side : Bool) (mark : Fin 46) (member : mark.val ∈ rootEligible) :
    actualReading side mark = some (referenceRaw side mark) := by
  have extension := LocalizedChemicalRingCompletenessGeneratedFacts.extension_succeeds
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
    admissible.1.1
    (raw_single mol certified structure_agreement admissible.1.1 admissible.1.2 supported single_bonded)
    admissible.1.2 (structuralDepth mol (canonicalCenterRoot 0)) (observedGeometry certified side)
    (canonicalCenterRoot 0) mark.val
  change appendFacts? [] (generated certified mol (canonicalCenterRoot 0)
    (structuralDepth mol (canonicalCenterRoot 0)) side mark.val) =
    some (generated certified mol (canonicalCenterRoot 0)
      (structuralDepth mol (canonicalCenterRoot 0)) side mark.val) at extension
  unfold actualReading LocalizedPhysicalMarkedDistantReference.inheritedRead?
  change ((appendFacts? [] (generated certified mol (canonicalCenterRoot 0)
      (structuralDepth mol (canonicalCenterRoot 0)) side mark.val)).bind fun temp =>
        LocalizedMarkedOperationEvaluator.markedReading? mol (sparseOperations certified mol)
          (observedGeometry certified side) temp (canonicalCenterRoot 0) mark.val) = _
  rw [extension, Option.bind_some,
    marked_reading_eq certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData,
    if_pos (eligible_keys_injective side mark member)]
  cases side with
  | false => exact readback_enumeration certified cfg rootCenter root_calibrated (referenceRank false mark)
  | true =>
      change LocalizedGenericMarkedRecalculation.readback?
        (LocalizedGenericMarkedRecalculation.mirror (inputGeometry certified))
        (LocalizedChemicalRingCompletenessMarked.enumeration certified rootCenter (referenceRank true mark)) = _
      rw [readback_mirror]
      exact congrArg (Option.map RS.swap)
        (readback_enumeration certified cfg rootCenter root_calibrated (referenceRank true mark))

/-- Equality of the actual ranking parities suffices for equality of the actual readings.
This theorem does not assert that the parities are equal. -/
theorem actualReading_eq_of_parity (side : Bool) (first second : Fin 46)
    (firstEligible : first.val ∈ rootEligible) (secondEligible : second.val ∈ rootEligible)
    (same : permHandedness (referenceRank side first) = permHandedness (referenceRank side second)) :
    actualReading side first = actualReading side second := by
  rw [actualReading_eq side first firstEligible, actualReading_eq side second secondEligible]
  unfold referenceRaw
  rw [same]

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitActualReferenceReading

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitActualReferenceReading.actualReading_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitActualReferenceReading.actualReading_eq_of_parity
