import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical
import TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The cyclic missing-label case occurs at a reached descendant of a detected root.
This proves the local inherited-reference refusal at every recursion depth. Membership of
that occurrence in the root's selected auxiliary forest is a separate operational fact. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Refusal

open LocalizedChemicalRingDoubleC3Input LocalizedChemicalRingDoubleC3Physical
open LocalizedChemicalRingFixedOccurrenceRefusal LocalizedChemicalRingRawResidualDescendants
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationInduction
open LocalizedChemicalRingSemanticSymmetry (actual_covariant)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedReachedFrameNeighbors (reached_atom_valid)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant descendant_reached strictDescendant_atom_ne)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? mirror)

theorem left_reached : Reached mol leftCenter :=
  ⟨0, by decide, (Relation.ReflTransGen.single actual_children.1).tail actual_children.2.2.1⟩

private theorem frame_count_excludes (a : Fin 25) (notRoot : a.val ≠ 0)
    (notLeft : a.val ≠ 3) (notRight : a.val ≠ 14) :
    (mol.ligandsWithLonePair a.val).length ≠ 4 := by
  fin_cases a <;> first | contradiction | decide +kernel

theorem left_descendants_no_frames (node : RawMolecule.CanonicalBranchNode)
    (descent : StrictDescendant mol leftCenter node) : frameAtoms? mol node = none := by
  cases frame : frameAtoms? mol node with
  | none => rfl
  | some atoms =>
      have real : node.forcedLeaf = false := by
        cases leaf : node.forcedLeaf with
        | false => rfl
        | true => rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol node leaf] at frame; cases frame
      obtain ⟨child, edge, rest⟩ := descent
      have different : node.atom ≠ 3 :=
        strictDescendant_atom_ne left_reached ⟨child, edge, rest⟩ real
      obtain ⟨atom, atomEq, connected⟩ := descendant_component (certified false) mol
        (structure_agreement false) admissible supported single_bonded
        [(0 : Fin 25), (4 : Fin 25)] leftCenter node (3 : Fin 25) rfl (by decide)
        (by
          intro a member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> decide)
        ((Relation.ReflTransGen.single edge).trans rest) real
      have bounds := left_residual_component atom connected
      have range : 5 ≤ atom.val ∧ atom.val ≤ 13 := by
        rcases bounds with same | bounded
        · exact False.elim (different (atomEq.symm.trans (congrArg Fin.val same)))
        · exact bounded
      have count := frame_count_excludes atom (by omega)
        (by intro eq; exact different (atomEq.symm.trans eq)) (by omega)
      have absent : frameAtoms? mol node = none := by
        rw [atomEq] at count
        simp [frameAtoms?, occurrenceLigandFrame?, count]
      rw [absent] at frame
      cases frame

theorem left_snapshot_empty (opposite : Bool) (depth : Nat) (geometry : Geometry) (mark : Nat) :
    LocalizedMarkedOperationEvaluator.underWith mol (ops opposite) geometry [] leftCenter
      (factsWith LocalizedPhysicalMarkedDistantReference.rawStep? mol (ops opposite) depth) mark = [] :=
  underWith_nil_of_no_frames mol (ops opposite) LocalizedPhysicalMarkedDistantReference.rawStep?
    (distantStep_noFrame mol (ops opposite)) leftCenter left_descendants_no_frames depth geometry [] mark

/-- No successful auxiliary label is available at this actual root-descendant occurrence
under the inherited root-ligand reference. No label or evaluator outcome is assumed. -/
theorem left_inherited_refusal (opposite : Bool) (depth : Nat) (geometry : Geometry) :
    LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol (ops opposite) depth geometry []
      (some 4) leftCenter = none := by
  let σ := relabelOf (certified opposite) leftRotation
  have cov : Covariant mol (ops opposite) σ := actual_covariant (certified opposite) mol
    (structure_agreement opposite) admissible supported single_bonded leftPhysicalRotation
  have fixedNode : mapNode σ leftCenter = leftCenter := rfl
  have fixedMark : σ 4 = 4 := rfl
  have moved : ∃ atom ∈ ([4, 5, 6, 7] : List Nat), σ atom ≠ atom :=
    ⟨5, by simp, by change (6 : Nat) ≠ 5; decide⟩
  have refused (g : Geometry) := distantStep_none_of_fixed mol (ops opposite) σ cov
    leftCenter left_reached [4, 5, 6, 7] raw_frames.2.1 fixedNode 4 fixedMark
    (by simp) moved g
  rw [distant_descriptor_eq_descriptorWith]
  unfold descriptorWith
  have under (g : Geometry) :
      LocalizedMarkedOperationEvaluator.underWith mol (ops opposite) g [] leftCenter
        (factsWith LocalizedPhysicalMarkedDistantReference.rawStep? mol (ops opposite) depth) =
          fun _ => [] := by
    funext mark
    exact left_snapshot_empty opposite depth g mark
  rw [under geometry, under (mirror geometry), refused geometry, refused (mirror geometry)]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Refusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Refusal.left_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Refusal.left_descendants_no_frames
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Refusal.left_snapshot_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Refusal.left_inherited_refusal
