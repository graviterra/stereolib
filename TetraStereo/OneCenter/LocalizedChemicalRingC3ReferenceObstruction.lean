import TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture
import TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! An actual cyclic auxiliary occurrence refuses under its inherited incoming reference,
although every molecular automorphism acts evenly at its only detected center. Thus
absence of a recorded label does not imply an odd local gauge exists. This is a diagnostic
for that proposed proof step, not a counterexample to the full key-to-physical theorem:
in this fixture every automorphism already has proper sense at the detected center.

The tested history starts at the non-detected fluorine atom. It is a valid reached
descriptor API call, not a fact consumed by this fixture's detected-root report. An
embedding into such a report is a separate, unproved step. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction

open LocalizedChemicalRingC3ReferenceFixture
open LocalizedChemicalRingFixedOccurrenceRefusal
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationInduction
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedReachedFrameNeighbors (reached_atom_valid)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant descendant_reached strictDescendant_atom_ne)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? mirror)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign transportedSign)

abbrev ops := sparseOperations certified mol
def σ : Nat → Nat := relabelOf certified (physicalRotation : Equiv.Perm certified.Atom)

theorem atoms_preserved (x : Nat) (bound : x < mol.atomCount) :
    mol.atomAt? (σ x) = mol.atomAt? x := by
  let a : Fin 11 := ⟨x, bound⟩
  change mol.atomAt? (relabelOf certified (physicalRotation : Equiv.Perm certified.Atom) a.val) =
    mol.atomAt? a.val
  rw [relabelOf_val]
  have finite (b : Fin 11) : mol.atomAt? (rotation b).val = mol.atomAt? b.val := by
    fin_cases b <;> rfl
  exact finite a

theorem incoming_reached : Reached mol incoming :=
  ⟨1, by decide, Relation.ReflTransGen.single incoming_child⟩

theorem frame_only_center (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms) : node.atom = 0 := by
  by_contra different
  have bound := reached_atom_valid mol admissible.1.1 node reached
  have count := other_ligand_count (⟨node.atom, bound⟩ : Fin 11)
    (fun eq => different (congrArg Fin.val eq))
  have absent : frameAtoms? mol node = none := by
    simp [frameAtoms?, occurrenceLigandFrame?, count]
  rw [absent] at frame
  cases frame

theorem incoming_descendants_no_frames (node : RawMolecule.CanonicalBranchNode)
    (descent : StrictDescendant mol incoming node) : frameAtoms? mol node = none := by
  have reached : Reached mol node := by
    obtain ⟨child, edge, rest⟩ := descent
    exact descendant_reached
      (LocalizedMarkedReachableConfigurations.reached_child mol incoming child incoming_reached edge) rest
  cases frame : frameAtoms? mol node with
  | none => rfl
  | some atoms =>
      have real : node.forcedLeaf = false := by
        cases leaf : node.forcedLeaf with
        | false => rfl
        | true => rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol node leaf] at frame; cases frame
      exact False.elim (strictDescendant_atom_ne incoming_reached descent real
        (frame_only_center node reached atoms frame))

theorem incoming_snapshot_empty (depth : Nat) (geom : Geometry) (mark : Nat) :
    LocalizedMarkedOperationEvaluator.underWith mol ops geom [] incoming
      (factsWith LocalizedPhysicalMarkedDistantReference.rawStep? mol ops depth) mark = [] :=
  underWith_nil_of_no_frames mol ops LocalizedPhysicalMarkedDistantReference.rawStep?
    (distantStep_noFrame mol ops) incoming incoming_descendants_no_frames depth geom [] mark

/-- Actual arbitrary-depth distant-reference execution, with no supplied auxiliary labels.
The inherited atom is in the frame, so the policy retains its refusing marked reading. -/
theorem incoming_descriptor_none (depth : Nat) (geom : Geometry) :
    LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol ops depth geom [] (some 1) incoming = none := by
  have cov : Covariant mol ops σ := actual_covariant certified mol structure_agreement admissible
    supported single_bonded physicalRotation atoms_preserved
  have fixedNode : mapNode σ incoming = incoming := rfl
  have fixedMark : σ 1 = 1 := rfl
  have moved : ∃ atom ∈ ([1, 2, 3, 4] : List Nat), σ atom ≠ atom :=
    ⟨2, by simp, by decide⟩
  have refused (g : Geometry) := distantStep_none_of_fixed mol ops σ cov incoming incoming_reached
    [1, 2, 3, 4] raw_frames.2 fixedNode 1 fixedMark (by simp) moved g
  rw [distant_descriptor_eq_descriptorWith]
  unfold descriptorWith
  have under (g : Geometry) : LocalizedMarkedOperationEvaluator.underWith mol ops g [] incoming
      (factsWith LocalizedPhysicalMarkedDistantReference.rawStep? mol ops depth) = fun _ => [] := by
    funext mark
    exact incoming_snapshot_empty depth g mark
  rw [under geom, under (mirror geom), refused geom, refused (mirror geom)]
  rfl

theorem every_automorphism_proper (configuration : physical.Configuration) (e : physical.Aut) :
    relativeSign physical configuration e center = 1 := by
  unfold relativeSign transportedSign
  rw [every_local_permutation_even, center_unique (physical.centerPerm e center), mul_one]
  exact permHandedness_mul_self (configuration center)

/-- The proposed inference "refusal supplies an odd correcting automorphism" is false
even on this admitted cyclic input with calibrated coordinates. Properness holds here by
the independent C3 classification, rather than by decoding a successful label. -/
theorem refusal_without_odd_gauge (depth : Nat) :
    LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol ops depth (inputGeometry certified)
        [] (some 1) incoming = none ∧
      ¬ ∃ e : physical.Aut, relativeSign physical cfg e center = -1 := by
  refine ⟨incoming_descriptor_none depth _, ?_⟩
  rintro ⟨e, odd⟩
  rw [every_automorphism_proper cfg e] at odd
  norm_num at odd

end TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction.atoms_preserved
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction.incoming_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction.frame_only_center
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction.incoming_descendants_no_frames
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction.incoming_snapshot_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction.incoming_descriptor_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction.every_automorphism_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction.refusal_without_odd_gauge
