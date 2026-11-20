import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A strict actual context-order result determines the actual joint marked reading.
The promotion count is recovered from the same partition; no ranking is supplied separately. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocalExecution

open CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingJointMarkerOperations
open LocalizedChemicalRingMultiMarkRecursion (markedReadingJoint?)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)

 theorem marked_reading_of_strict_context_order (input : CertifiedLocalizedCIPInput)
    (mol : RawMolecule) (geom : Geometry) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (ctx : List Nat) (mark : Nat)
    (atoms positions : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (order : contextOrder? input mol state node ctx = some (positions, adjacent))
    (strictOrder : strict adjacent = true) :
    markedReadingJoint? mol (jointOperations input mol) geom state node ctx mark =
      (do let ranked ← atomsAt? atoms positions; readback? geom ranked) := by
  cases hrefs : referenceAtoms? input ctx with
  | none => simp [contextOrder?, hrefs] at order
  | some refs =>
      cases hpart : jointPartition? input mol state node refs
          (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) with
      | none => simp [contextOrder?, hrefs, hpart] at order
      | some part =>
          obtain ⟨positions', adjacent', count⟩ := part
          have equal : positions' = positions ∧ adjacent' = adjacent := by
            simpa [contextOrder?, hrefs, hpart] using order
          rcases equal with ⟨rfl, rfl⟩
          simp [markedReadingJoint?, jointOperations, markedJoint?, hrefs, hpart,
            frame, rankedAtoms?, strictOrder, atomsAt?]

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocalExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocalExecution.marked_reading_of_strict_context_order
