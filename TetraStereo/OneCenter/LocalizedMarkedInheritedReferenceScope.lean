import TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The exact scope of inherited references in the current marked evaluator

An inherited atom outside the current four-atom frame is discarded, regardless of how deeply
it occurs in the ligand graph. This is an operational equality, at every recursion depth and
for arbitrary operation tables, geometry and auxiliary state. It does not assert that discarding
the reference is chemically justified. The subdivision probe tests that semantic obligation.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedInheritedReferenceScope

open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? frameAtomsOf mirror)
open LocalizedMarkedOperationEvaluator

theorem rawStep_forgets_absent (mol : RawMolecule) (ops : Operations)
    (geom : Geometry) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (atoms : List Nat) (mark : Nat)
    (frame : frameAtoms? mol node = some atoms) (absent : mark ∉ atoms)
    (under : Nat → OccurrenceAuxState) :
    rawStep? mol ops geom state (some mark) node under =
      rawStep? mol ops geom state none node under := by
  simp [rawStep?, frame, absent]

theorem rawWith_forgets_absent (mol : RawMolecule) (ops : Operations)
    (geom : Geometry) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (atoms : List Nat) (mark : Nat)
    (frame : frameAtoms? mol node = some atoms) (absent : mark ∉ atoms)
    (sub : Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState) :
    rawWith? mol ops geom state (some mark) node sub =
      rawWith? mol ops geom state none node sub :=
  rawStep_forgets_absent mol ops geom state node atoms mark frame absent _

theorem descriptor_forgets_absent (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (atoms : List Nat) (mark : Nat)
    (frame : frameAtoms? mol node = some atoms) (absent : mark ∉ atoms) :
    LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom state (some mark) node =
      LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom state none node := by
  unfold LocalizedMarkedOperationEvaluator.descriptor? descriptorWith?
  rw [rawWith_forgets_absent mol ops geom state node atoms mark frame absent,
    rawWith_forgets_absent mol ops (mirror geom) state node atoms mark frame absent]

theorem marked_none_of_absent (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) (mark : Nat)
    (frame : occurrenceLigandFrame? mol node = some roots)
    (absent : mark ∉ frameAtomsOf roots) :
    LocalizedMarkedUncappedOperations.marked? mol state node mark = none := by
  have bound : (frameAtomsOf roots).length ≤ (frameAtomsOf roots).idxOf mark :=
    Nat.le_of_not_gt (by simpa only [List.idxOf_lt_length_iff] using absent)
  simp [LocalizedMarkedUncappedOperations.marked?, frame, bound]

end TetraStereo.OneCenter.LocalizedMarkedInheritedReferenceScope

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedInheritedReferenceScope.rawStep_forgets_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedInheritedReferenceScope.rawWith_forgets_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedInheritedReferenceScope.descriptor_forgets_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedInheritedReferenceScope.marked_none_of_absent
