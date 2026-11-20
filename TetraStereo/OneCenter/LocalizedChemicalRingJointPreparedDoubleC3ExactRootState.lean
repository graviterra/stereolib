import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! A structural reduction of the actual DoubleC3 root's prepared child state.
Only the two local generated descriptors remain; no labels are supplied. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootState

open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations)
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactLocal

private def hydrogen : Node :=
  { atom := 1, parent := 0, history := [1, 0], provenance := .realAtom }
private def chlorine : Node :=
  { atom := 2, parent := 0, history := [2, 0], provenance := .realAtom }

private theorem root_children :
    mol.canonicalChildren root = [hydrogen, chlorine, leftArm, rightArm] := by decide +kernel
private theorem left_arm_children : mol.canonicalChildren leftArm = [leftCenter] := by decide +kernel
private theorem right_arm_children : mol.canonicalChildren rightArm = [rightCenter] := by decide +kernel
private theorem hydrogen_children : mol.canonicalChildren hydrogen = [] := by decide +kernel
private theorem chlorine_children : mol.canonicalChildren chlorine = [] := by decide +kernel
private theorem hydrogen_frame : frameAtoms? mol hydrogen = none := by decide +kernel
private theorem chlorine_frame : frameAtoms? mol chlorine = none := by decide +kernel
private theorem left_arm_frame : frameAtoms? mol leftArm = none := by decide +kernel
private theorem right_arm_frame : frameAtoms? mol rightArm = none := by decide +kernel

private theorem descriptor_none (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : MarkContext) (node : Node)
    (absent : frameAtoms? mol node = none) :
    preparedDescriptor? mol ops depth geom state ctx node = none :=
  descriptorWithPrepared_none_of_frame (rawStepPrepared? ops) mol (rawStepPrepared?_noFrame ops)
    geom state ctx node (factsOfStep (rawStepPrepared? ops) mol depth) absent

private theorem terminal_facts (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : MarkContext) (node : Node)
    (absent : frameAtoms? mol node = none) (terminal : mol.canonicalChildren node = []) :
    preparedFacts mol ops depth geom state ctx node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
      rw [preparedFacts_succ, descriptor_none ops depth geom state ctx node absent, terminal]
      rfl

/-- At every nontrivial subtree depth, the actual same-context prepared child state at
root is just the concatenation of the two local generated descriptor facts. -/
theorem root_prepared_children_eq_local (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) :
    childrenUnder mol (preparedFacts mol ops (depth + 2)) geom state root =
      fun ctx =>
        (preparedDescriptor? mol ops 0 geom state ctx leftCenter).toList.map (factOf leftCenter) ++
        (preparedDescriptor? mol ops 0 geom state ctx rightCenter).toList.map (factOf rightCenter) := by
  funext ctx
  have left : preparedFacts mol ops (depth + 2) geom state ctx leftArm =
      preparedFacts mol ops (depth + 1) geom state ctx leftCenter := by
    rw [show depth + 2 = (depth + 1) + 1 by omega, preparedFacts_succ,
      descriptor_none ops (depth + 1) geom state ctx leftArm left_arm_frame, left_arm_children]
    simp
  have right : preparedFacts mol ops (depth + 2) geom state ctx rightArm =
      preparedFacts mol ops (depth + 1) geom state ctx rightCenter := by
    rw [show depth + 2 = (depth + 1) + 1 by omega, preparedFacts_succ,
      descriptor_none ops (depth + 1) geom state ctx rightArm right_arm_frame, right_arm_children]
    simp
  unfold childrenUnder
  rw [root_children]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [terminal_facts ops (depth + 2) geom state ctx hydrogen hydrogen_frame hydrogen_children,
    terminal_facts ops (depth + 2) geom state ctx chlorine chlorine_frame chlorine_children,
    left, right, left_prepared_facts_eq_local, right_prepared_facts_eq_local]
  simp

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootState

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootState.root_prepared_children_eq_local
