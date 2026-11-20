import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor

open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading
open LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder
open LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even (fallback2_eq1 fallback3_eq2)
open LocalizedChemicalRingJointPreparedDoubleC3ExactData (reference_slot)
open LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants (left_prepared_children_empty)
open LocalizedChemicalRingJointPreparedExecution (fallback)
open LocalizedChemicalRingInheritedRefusalCases (observedGeometry)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculation (Geometry mirror appendFacts? consensus caseFromMirror?)

noncomputable section

abbrev under (depth : Nat) (geom : Geometry) :=
  childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) geom [] leftCenter

abbrev selected (depth : Nat) (reflected : Bool) (mark : Nat) :=
  evaluateFallback? mol (jointOperations input mol) (observedGeometry input reflected) [] leftCenter []
    (under depth (observedGeometry input reflected)) mark

theorem selected6_eq5 (depth : Nat) (reflected : Bool) :
    selected depth reflected 6 = selected depth reflected 5 := by
  have actual := fallback2_eq1 depth reflected
  simpa only [fallback, reference_slot] using actual

theorem selected7_eq6 (depth : Nat) (reflected : Bool) :
    selected depth reflected 7 = selected depth reflected 6 := by
  have actual := fallback3_eq2 depth reflected
  simpa only [fallback, reference_slot] using actual

theorem selected5 (depth : Nat) (reflected : Bool) :
    selected depth reflected 5 = some (if reflected then RS.S else RS.R) := by
  cases reflected with
  | false => exact prepared_fallback5 depth
  | true => exact prepared_fallback5_mirror depth

theorem selected_success (depth : Nat) (reflected : Bool) (mark : Nat)
    (member : mark ∈ [5, 6, 7]) :
    selected depth reflected mark = some (if reflected then RS.S else RS.R) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact selected5 depth reflected
  · exact (selected6_eq5 depth reflected).trans (selected5 depth reflected)
  · exact ((selected7_eq6 depth reflected).trans (selected6_eq5 depth reflected)).trans
      (selected5 depth reflected)

/-- All three ACTUAL prepared fallbacks agree, and their exact raw value is derived. -/
theorem raw_step (depth : Nat) (reflected : Bool) :
    rawStepPrepared? (jointOperations input mol) mol (observedGeometry input reflected) [] []
      leftCenter (under depth (observedGeometry input reflected)) =
        some (if reflected then RS.S else RS.R) := by
  let geom := observedGeometry input reflected
  have childNil : under depth geom = fun _ => [] :=
    left_prepared_children_empty (jointOperations input mol) depth geom []
  have append : appendFacts? [] (under depth geom []) = some [] := by rw [childNil]; rfl
  have actual := rawStepPrepared?_consensus_uses_original (jointOperations input mol) mol
    geom [] [] leftCenter (under depth geom) [4, 5, 6, 7] [0, 1, 2, 3]
    [some .gt, some .eq, some .eq] [] raw_frames.2.1 append context_order_nil
    (by decide) (by decide) (by decide)
  change rawStepPrepared? (jointOperations input mol) mol geom [] [] leftCenter (under depth geom) =
    consensus [selected depth reflected 5, selected depth reflected 6, selected depth reflected 7] at actual
  rw [selected_success depth reflected 5 (by simp),
    selected_success depth reflected 6 (by simp), selected_success depth reflected 7 (by simp)] at actual
  simpa [consensus] using actual

/-- The actual generated left auxiliary descriptor is chiral R, at every prepared depth.
No local descriptor, comparison outcome or root label is assumed. -/
theorem left_descriptor (depth : Nat) :
    preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) [] [] leftCenter =
      some (.chiral .R) := by
  have original : rawStepPrepared? (jointOperations input mol) mol (inputGeometry input) [] []
      leftCenter (under depth (inputGeometry input)) = some .R := raw_step depth false
  have reflected : rawStepPrepared? (jointOperations input mol) mol (mirror (inputGeometry input)) [] []
      leftCenter (under depth (mirror (inputGeometry input))) = some .S := raw_step depth true
  unfold preparedDescriptor? descriptorOfStep descriptorWithPrepared
  change caseFromMirror?
      (rawStepPrepared? (jointOperations input mol) mol (inputGeometry input) [] [] leftCenter
        (under depth (inputGeometry input)))
      (rawStepPrepared? (jointOperations input mol) mol (mirror (inputGeometry input)) [] [] leftCenter
        (under depth (mirror (inputGeometry input)))) = some (.chiral .R)
  rw [original, reflected]
  rfl

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor.selected6_eq5
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor.selected7_eq6
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor.selected5
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor.selected_success
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor.raw_step
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor.left_descriptor
