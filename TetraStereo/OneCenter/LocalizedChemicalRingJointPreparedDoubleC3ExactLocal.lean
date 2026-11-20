import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal
open LocalizedChemicalRingDoubleC3Input LocalizedChemicalRingDoubleC3Physical
open LocalizedChemicalRingFixedOccurrenceRefusal LocalizedChemicalRingRawResidualDescendants
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant strictDescendant_atom_ne)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms?)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations)
open LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants

theorem right_reached : Reached mol rightCenter :=
  ⟨0, by decide, (Relation.ReflTransGen.single actual_children.2.1).tail actual_children.2.2.2⟩

private theorem frame_count_excludes (a : Fin 25) (notRoot : a.val ≠ 0)
    (notLeft : a.val ≠ 3) (notRight : a.val ≠ 14) :
    (mol.ligandsWithLonePair a.val).length ≠ 4 := by
  fin_cases a <;> first | contradiction | decide +kernel

theorem right_descendants_no_frames (node : RawMolecule.CanonicalBranchNode)
    (descent : StrictDescendant mol rightCenter node) : frameAtoms? mol node = none := by
  cases frame : frameAtoms? mol node with
  | none => rfl
  | some atoms =>
      have real : node.forcedLeaf = false := by
        cases leaf : node.forcedLeaf with
        | false => rfl
        | true => rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol node leaf] at frame; cases frame
      obtain ⟨child, edge, rest⟩ := descent
      have different : node.atom ≠ 14 :=
        strictDescendant_atom_ne right_reached ⟨child, edge, rest⟩ real
      obtain ⟨atom, atomEq, connected⟩ := descendant_component (certified false) mol
        (structure_agreement false) admissible supported single_bonded
        [(0 : Fin 25), (15 : Fin 25)] rightCenter node (14 : Fin 25) rfl (by decide)
        (by
          intro a member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> decide)
        ((Relation.ReflTransGen.single edge).trans rest) real
      have bounds := right_residual_component atom connected
      have range : 16 ≤ atom.val ∧ atom.val ≤ 24 := by
        rcases bounds with same | bounded
        · exact False.elim (different (atomEq.symm.trans (congrArg Fin.val same)))
        · exact bounded
      have count := frame_count_excludes atom (by omega)
        (by omega) (by intro eq; exact different (atomEq.symm.trans eq))
      have absent : frameAtoms? mol node = none := by
        rw [atomEq] at count
        simp [frameAtoms?, occurrenceLigandFrame?, count]
      rw [absent] at frame
      cases frame


/-- The right auxiliary center has no generated child facts, for every inherited context. -/
theorem right_prepared_children_empty (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) :
    childrenUnder mol (preparedFacts mol ops depth) geom state rightCenter = fun _ => [] :=
  childrenUnder_nil_of_no_frames mol (rawStepPrepared? ops) (rawStepPrepared?_noFrame ops)
    rightCenter right_descendants_no_frames depth geom state


/-- All facts below the left center reduce to its own generated descriptor. -/
theorem left_prepared_facts_eq_local (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : MarkContext) :
    preparedFacts mol ops (depth + 1) geom state ctx leftCenter =
      (preparedDescriptor? mol ops 0 geom state ctx leftCenter).toList.map
        (LocalizedGenericMarkedRecalculation.factOf leftCenter) := by
  rw [preparedFacts_succ, left_prepared_descriptor_eq_depth_zero]
  change _ ++ childrenUnder mol (preparedFacts mol ops depth) geom state leftCenter ctx = _
  rw [left_prepared_children_empty]
  simp

/-- The right auxiliary reading is exactly its local zero-depth prepared reading. -/
theorem right_prepared_descriptor_eq_depth_zero (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : MarkContext) :
    preparedDescriptor? mol ops depth geom state ctx rightCenter =
      preparedDescriptor? mol ops 0 geom state ctx rightCenter := by
  unfold preparedDescriptor? descriptorOfStep descriptorWithPrepared
  change LocalizedGenericMarkedRecalculation.caseFromMirror?
      (rawStepPrepared? ops mol geom state ctx rightCenter
        (childrenUnder mol (preparedFacts mol ops depth) geom state rightCenter))
      (rawStepPrepared? ops mol (LocalizedGenericMarkedRecalculation.mirror geom) state ctx rightCenter
        (childrenUnder mol (preparedFacts mol ops depth)
          (LocalizedGenericMarkedRecalculation.mirror geom) state rightCenter)) =
    LocalizedGenericMarkedRecalculation.caseFromMirror?
      (rawStepPrepared? ops mol geom state ctx rightCenter
        (childrenUnder mol (preparedFacts mol ops 0) geom state rightCenter))
      (rawStepPrepared? ops mol (LocalizedGenericMarkedRecalculation.mirror geom) state ctx rightCenter
        (childrenUnder mol (preparedFacts mol ops 0)
          (LocalizedGenericMarkedRecalculation.mirror geom) state rightCenter))
  rw [right_prepared_children_empty ops depth geom state,
    right_prepared_children_empty ops depth (LocalizedGenericMarkedRecalculation.mirror geom) state,
    right_prepared_children_empty ops 0 geom state,
    right_prepared_children_empty ops 0 (LocalizedGenericMarkedRecalculation.mirror geom) state]

/-- All facts below the right center reduce to its own generated descriptor. -/
theorem right_prepared_facts_eq_local (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : MarkContext) :
    preparedFacts mol ops (depth + 1) geom state ctx rightCenter =
      (preparedDescriptor? mol ops 0 geom state ctx rightCenter).toList.map
        (LocalizedGenericMarkedRecalculation.factOf rightCenter) := by
  rw [preparedFacts_succ, right_prepared_descriptor_eq_depth_zero]
  change _ ++ childrenUnder mol (preparedFacts mol ops depth) geom state rightCenter ctx = _
  rw [right_prepared_children_empty]
  simp

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal.right_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal.right_descendants_no_frames
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal.right_prepared_children_empty

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal.left_prepared_facts_eq_local

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal.right_prepared_descriptor_eq_depth_zero

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal.right_prepared_facts_eq_local
