import TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator
import TetraStereo.OneCenter.LocalizedMarkedInheritedReferenceScope
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations

set_option autoImplicit false

/-!
# Concrete preservation instances for distant-reference evaluation

The existing frame-local uncapped backend has identical complete reports under the new policy:
it cannot make a distant reading, so the new fallback restores its prior behavior at every
recursive step. This derives a real preservation instance rather than assuming agreement.

For the retained backend, sparse/dense equivalence transfers unchanged to the new policy.
This does not identify the new policy with the old one on that backend and makes no chemical
correctness claim for its additional assignments.
-/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantPreservation

open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? frameAtomsOf)
open LocalizedPhysicalMarkedDistantReference (FrameLocalOperations)

theorem uncapped_frameLocal (mol : RawMolecule) :
    FrameLocalOperations mol (LocalizedMarkedUncappedEvaluator.operations mol) := by
  intro state node atoms mark frame absent
  cases hg : occurrenceLigandFrame? mol node with
  | none => simp [frameAtoms?, hg] at frame
  | some roots =>
      have same : frameAtomsOf roots = atoms := by simpa [frameAtoms?, hg] using frame
      subst atoms
      exact LocalizedMarkedInheritedReferenceScope.marked_none_of_absent
        mol state node roots mark hg absent

/-- Unconditional preservation of every legacy frame-local uncapped fact, for all inputs. -/
theorem uncapped_facts_eq (mol : RawMolecule) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) :
    LocalizedPhysicalMarkedDistantEvaluator.facts mol
        (LocalizedMarkedUncappedEvaluator.operations mol) depth geom state ctx node =
      LocalizedMarkedOperationEvaluator.facts mol
        (LocalizedMarkedUncappedEvaluator.operations mol) depth geom state ctx node :=
  LocalizedPhysicalMarkedDistantEvaluator.facts_eq_of_frameLocal mol _
    (uncapped_frameLocal mol) depth geom state ctx node

theorem uncapped_assign_eq (mol : RawMolecule) (geom : Geometry) :
    LocalizedPhysicalMarkedDistantEvaluator.assign mol
        (LocalizedMarkedUncappedEvaluator.operations mol) geom =
      LocalizedMarkedUncappedEvaluator.assign mol geom :=
  LocalizedPhysicalMarkedDistantEvaluator.assign_eq_of_frameLocal mol _
    (uncapped_frameLocal mol) geom

/-- The executable sparse backend implements the same candidate policy as the dense backend. -/
theorem sparse_assign_eq (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (geom : Geometry) :
    LocalizedPhysicalMarkedDistantEvaluator.assign mol
        (LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations input mol) geom =
      LocalizedPhysicalMarkedDistantEvaluator.assign mol
        (LocalizedMarkedRetainedPromotedOperations.operations input mol) geom := by
  rw [LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations_eq]

end TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantPreservation

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantPreservation.uncapped_frameLocal
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantPreservation.uncapped_facts_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantPreservation.uncapped_assign_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantPreservation.sparse_assign_eq
