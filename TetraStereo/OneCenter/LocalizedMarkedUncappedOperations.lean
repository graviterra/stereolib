import TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Uncapped operations at reached promotion-context frames

The experimental marked constructor currently calls capped comparators with `atomCount + 1`
fuel. That budget has no general sufficiency proof for rerooted cyclic occurrences. The repository
already contains uncapped ordinary and promoted comparators, and proves their operational
totality at `2 * atomCount + 1` under chemical intake conditions.

This module connects that existing theorem to every frame reached by the experimental recursion,
for any auxiliary state, including its internally generated states. The marked reference is read
from the actual frame and an out-of-frame reference still refuses. No ordering strictness, unique
ranking, geometric letter, successful descriptor or chemical-priority conclusion is assumed or
proved here. The current experimental constructor and production defaults are unchanged.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedOperations

open LocalizedMarkedReachableConfigurations
open LocalizedGenericMarkedRecalculation (frameAtomsOf)
open AuthoritativeCIPMoleculeCursorRanking AuthoritativeCIPRule6Scheduler
open AuthoritativeCIPRule6P92Enumeration AuthoritativeCIPMancudeTotality

theorem generated_of_reachedFrom (mol : RawMolecule) (center : Nat) (node : Node)
    (reached : ReachedFrom mol center node) : CanonicalCenterTreeNode mol center node := by
  induction reached with
  | refl => exact .root
  | tail path edge ih => exact .child ih edge

theorem reachedFrom_of_generated (mol : RawMolecule) (center : Nat) (node : Node)
    (generated : CanonicalCenterTreeNode mol center node) : ReachedFrom mol center node := by
  induction generated with
  | root => exact .refl
  | child parent edge ih => exact ih.tail edge

/-- The existing general reroot-support bound, generated from the input size. -/
def comparisonFuel (mol : RawMolecule) : Nat := 2 * mol.atomCount + 1

/-- Actual ordinary partition through the existing uncapped comparator. -/
def ordinary? (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node) :
    Option (List Nat × List (Option Ordering)) := do
  let roots ← occurrenceLigandFrame? mol node
  let sorted ← sortAuthoritativeRule6InitialPositions? mol state (comparisonFuel mol)
    roots (List.range roots.length)
  let adjacent ← compareAuthoritativeRule6InitialAdjacent? mol state (comparisonFuel mol)
    roots sorted
  some (sorted, adjacent)

/-- Actual uncapped marked ranking with the chosen atom resolved through its frame position. -/
def marked? (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node) (mark : Nat) :
    Option Rule6TrackedRanking := do
  let roots ← occurrenceLigandFrame? mol node
  let atoms := frameAtomsOf roots
  let reference := atoms.idxOf mark
  if reference >= atoms.length then none else
    authoritativeOccurrenceRule6PositionRankingBackend mol state (comparisonFuel mol)
      roots atoms reference

theorem ordinary_exists (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (state : OccurrenceAuxState) (node : Node) (reached : Reached mol node)
    (roots : List CanonicalRerootCursor) (frame : occurrenceLigandFrame? mol node = some roots) :
    ∃ sorted adjacent, ordinary? mol state node = some (sorted, adjacent) ∧
      sorted.Perm [0, 1, 2, 3] ∧ adjacent.length = 3 := by
  obtain ⟨center, valid, path⟩ := reached
  have generated := generated_of_reachedFrom mol center node path
  have four := occurrenceLigandFrame?_result_length mol node roots frame
  obtain ⟨sorted, adjacent, sorting, compared⟩ :=
    authoritativeRule6InitialPartition_exists_of_chemical_frame valid wellFormed unique valence
      kekule generated frame (state := state)
  refine ⟨sorted, adjacent, ?_, ?_, ?_⟩
  · simp [ordinary?, frame, comparisonFuel, four, sorting, compared]
  · exact sortAuthoritativeRule6InitialPositions?_perm mol state _ roots _ _ sorting
  · have length := compareAuthoritativeRule6InitialAdjacent?_length mol state _ roots _ _ compared
    have perm := sortAuthoritativeRule6InitialPositions?_perm mol state _ roots _ _ sorting
    have sortedLength : sorted.length = 4 := by simpa using perm.length_eq
    simpa [sortedLength] using length

theorem marked_exists (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (state : OccurrenceAuxState) (node : Node) (reached : Reached mol node)
    (roots : List CanonicalRerootCursor) (frame : occurrenceLigandFrame? mol node = some roots)
    (mark : Nat) (member : mark ∈ frameAtomsOf roots) :
    ∃ ranking, marked? mol state node mark = some ranking ∧
      ranking.positions.Perm [0, 1, 2, 3] := by
  obtain ⟨center, valid, path⟩ := reached
  have generated := generated_of_reachedFrom mol center node path
  have four := occurrenceLigandFrame?_result_length mol node roots frame
  obtain ⟨ranking, computed⟩ :=
    authoritativeOccurrenceRule6PositionRankingBackend_total_of_chemical_frame
      valid wellFormed unique valence kekule generated frame (frameAtomsOf roots)
      ((frameAtomsOf roots).idxOf mark) (state := state)
  have reference : (frameAtomsOf roots).idxOf mark < (frameAtomsOf roots).length :=
    List.idxOf_lt_length_iff.mpr member
  refine ⟨ranking, ?_, ?_⟩
  · simp [marked?, frame, comparisonFuel, Nat.not_le_of_lt reference, computed]
  · have perm := authoritativeOccurrenceRule6PositionRankingBackend_positions_perm mol state _
      roots (frameAtomsOf roots) ((frameAtomsOf roots).idxOf mark) ranking computed
    simpa [four] using perm

/-- Existing comparison totality covers every reached context and every generated auxiliary state.
The returned ranking is allowed to be nonunique, so this does not assert descriptor success. -/
theorem operations_exist (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (state : OccurrenceAuxState) (node : Node) (reached : Reached mol node)
    (roots : List CanonicalRerootCursor) (frame : occurrenceLigandFrame? mol node = some roots) :
    (∃ sorted adjacent, ordinary? mol state node = some (sorted, adjacent) ∧
      sorted.Perm [0, 1, 2, 3] ∧ adjacent.length = 3) ∧
    (∀ mark ∈ frameAtomsOf roots, ∃ ranking, marked? mol state node mark = some ranking ∧
      ranking.positions.Perm [0, 1, 2, 3]) :=
  ⟨ordinary_exists mol wellFormed unique valence kekule state node reached roots frame,
    fun mark member => marked_exists mol wellFormed unique valence kekule state node reached
      roots frame mark member⟩

end TetraStereo.OneCenter.LocalizedMarkedUncappedOperations

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedOperations.generated_of_reachedFrom
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedOperations.reachedFrom_of_generated
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedOperations.ordinary_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedOperations.marked_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedOperations.operations_exist
