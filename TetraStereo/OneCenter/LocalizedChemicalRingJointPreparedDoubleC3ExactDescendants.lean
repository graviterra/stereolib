import TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion
import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Refusal
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Prepared recursion emits no facts in a child-closed region without frames.
The DoubleC3 instance is independent of the incoming state, context and geometry. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants

open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)

 theorem factsOfStep_nil_of_no_frames (mol : RawMolecule) (step : PreparedStep)
    (noFrame : PreparedStepNoFrame step) (P : Node → Prop)
    (closed : ∀ parent child, P parent → child ∈ mol.canonicalChildren parent → P child)
    (absent : ∀ node, P node → frameAtoms? mol node = none) :
    ∀ depth geom state ctx node, P node → factsOfStep step mol depth geom state ctx node = [] := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro geom state ctx node member
      rw [factsOfStep_succ]
      have descriptor : descriptorOfStep step mol depth geom state ctx node = none :=
        descriptorWithPrepared_none_of_frame step mol noFrame geom state ctx node
          (factsOfStep step mol depth) (absent node member)
      rw [descriptor]
      simp only [Option.toList_none, List.map_nil, List.nil_append]
      rw [flatMap_congr_mem _ _ (fun _ => [])
        (fun child edge => ih geom state ctx child (closed node child member edge))]
      simp

 theorem childrenUnder_nil_of_no_frames (mol : RawMolecule) (step : PreparedStep)
    (noFrame : PreparedStepNoFrame step) (source : Node)
    (absent : ∀ node, StrictDescendant mol source node → frameAtoms? mol node = none)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) :
    childrenUnder mol (factsOfStep step mol depth) geom state source = fun _ => [] := by
  have closed : ∀ parent child, StrictDescendant mol source parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol source child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  funext ctx
  unfold childrenUnder
  rw [flatMap_congr_mem _ _ (fun _ => [])
    (fun child edge => factsOfStep_nil_of_no_frames mol step noFrame
      (StrictDescendant mol source) closed absent depth geom state ctx child
      ⟨child, edge, .refl⟩)]
  simp

open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations)

/-- Actual prepared child facts of the left auxiliary center, at every context and depth. -/
theorem left_prepared_children_empty (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) :
    childrenUnder mol (preparedFacts mol ops depth) geom state leftCenter = fun _ => [] :=
  childrenUnder_nil_of_no_frames mol (rawStepPrepared? ops) (rawStepPrepared?_noFrame ops)
    leftCenter LocalizedChemicalRingDoubleC3Refusal.left_descendants_no_frames depth geom state


/-- The left auxiliary reading is exactly its local zero-depth prepared reading.
This equality retains both independently generated geometries and supplies no label. -/
theorem left_prepared_descriptor_eq_depth_zero (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : MarkContext) :
    preparedDescriptor? mol ops depth geom state ctx leftCenter =
      preparedDescriptor? mol ops 0 geom state ctx leftCenter := by
  unfold preparedDescriptor? descriptorOfStep descriptorWithPrepared
  change caseFromMirror?
      (rawStepPrepared? ops mol geom state ctx leftCenter
        (childrenUnder mol (preparedFacts mol ops depth) geom state leftCenter))
      (rawStepPrepared? ops mol (mirror geom) state ctx leftCenter
        (childrenUnder mol (preparedFacts mol ops depth) (mirror geom) state leftCenter)) =
    caseFromMirror?
      (rawStepPrepared? ops mol geom state ctx leftCenter
        (childrenUnder mol (preparedFacts mol ops 0) geom state leftCenter))
      (rawStepPrepared? ops mol (mirror geom) state ctx leftCenter
        (childrenUnder mol (preparedFacts mol ops 0) (mirror geom) state leftCenter))
  rw [left_prepared_children_empty ops depth geom state,
    left_prepared_children_empty ops depth (mirror geom) state,
    left_prepared_children_empty ops 0 geom state,
    left_prepared_children_empty ops 0 (mirror geom) state]

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants.factsOfStep_nil_of_no_frames
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants.childrenUnder_nil_of_no_frames
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants.left_prepared_children_empty

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants.left_prepared_descriptor_eq_depth_zero
