import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Actual tracked Rule-6 rankings preserve their frame positions

The insertion and monadic fold used by `rankOccurrencePositionsThroughRule6Tracked?` retain
exactly the supplied positions, including multiplicity. No ordering, uniqueness, successful
comparison or chemical correctness law is assumed beyond the observed successful computation.
This supplies the structural prerequisite for transporting a calibrated frame orientation to
the priority order that the marked evaluator actually reads.
-/

namespace TetraStereo.OneCenter.OccurrenceRule6RankingPermutation

open DeclarativeCIP.ProductionOccurrenceRules456 LocalizedGenericMarkedRecalculation

theorem insertion_perm (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands : List Nat) (reference candidate : Nat) :
    ∀ input output,
      insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots ligands reference
          candidate input = some output → output.1.Perm (candidate :: input)
  | [], output, computed => by
      simp [insertOccurrencePositionRule6Tracked?] at computed
      subst output
      rfl
  | low :: tail, output, computed => by
      unfold insertOccurrencePositionRule6Tracked? at computed
      cases hd : comparePositionsThroughRule6? (mol := mol) state fuel roots ligands
          reference low candidate with
      | none => simp [hd] at computed
      | some decision =>
          cases ho : decision.ordering with
          | lt =>
              cases hi : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
                  ligands reference candidate tail with
              | none => simp [hd, ho, hi] at computed
              | some inserted =>
                  simp [hd, ho, hi] at computed
                  subst output
                  exact (List.Perm.cons low
                    (insertion_perm mol state fuel roots ligands reference candidate tail
                      inserted hi)).trans (List.Perm.swap candidate low tail)
          | eq =>
              simp [hd, ho] at computed
              subst output
              rfl
          | gt =>
              simp [hd, ho] at computed
              subst output
              rfl

private abbrev Accumulator := List Nat × Nat × Bool

/-- The production fold callback, used definitionally rather than as a second ranker. -/
private def step (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands : List Nat) (reference : Nat)
    (acc : Accumulator) (candidate : Nat) : Option Accumulator := do
  let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots ligands
    reference candidate acc.1
  some (inserted.1, acc.2.1 + inserted.2.1, acc.2.2 && inserted.2.2)

private theorem step_perm (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands : List Nat) (reference candidate : Nat)
    (acc out : Accumulator)
    (computed : step mol state fuel roots ligands reference acc candidate = some out) :
    out.1.Perm (candidate :: acc.1) := by
  cases hi : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots ligands
      reference candidate acc.1 with
  | none => simp [step, hi] at computed
  | some inserted =>
      simp [step, hi] at computed
      subst out
      exact insertion_perm mol state fuel roots ligands reference candidate acc.1 inserted hi

private theorem fold_perm (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands : List Nat) (reference : Nat) :
    ∀ input (acc out : Accumulator),
      input.foldlM (step mol state fuel roots ligands reference) acc = some out →
      out.1.Perm (input ++ acc.1)
  | [], acc, out, computed => by
      simp at computed
      subst out
      rfl
  | candidate :: tail, acc, out, computed => by
      cases hs : step mol state fuel roots ligands reference acc candidate with
      | none => simp [List.foldlM_cons, hs] at computed
      | some next =>
          have rest : tail.foldlM (step mol state fuel roots ligands reference) next =
              some out := by simpa [List.foldlM_cons, hs] using computed
          exact (fold_perm mol state fuel roots ligands reference tail next out rest).trans
            ((List.Perm.append_left tail
              (step_perm mol state fuel roots ligands reference candidate acc next hs)).trans
              List.perm_middle)

/-- The actual tracked ranker's output is a permutation of its complete input. -/
theorem ranking_positions_perm (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands start : List Nat) (reference : Nat)
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots
      ligands start reference = some ranking) : ranking.positions.Perm start := by
  change (do
    let tracked ← start.foldlM (step mol state fuel roots ligands reference) ([], 0, true)
    some
      { positions := tracked.1.reverse
        pseudoComparisons := tracked.2.1
        unique := tracked.2.2 }) = some ranking at computed
  cases hf : start.foldlM (step mol state fuel roots ligands reference) ([], 0, true) with
  | none => simp [hf] at computed
  | some tracked =>
      simp [hf] at computed
      subst ranking
      have hp : tracked.1.Perm start := by
        simpa using fold_perm mol state fuel roots ligands reference start ([], 0, true) tracked hf
      exact (List.reverse_perm tracked.1).trans hp

/-- Every successful marked call used by the generic evaluator retains positions 0–3. -/
theorem marked_positions_perm (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (mark : Nat) (ranking : Rule6TrackedRanking)
    (computed : marked? mol fuel state node mark = some ranking) :
    ranking.positions.Perm [0, 1, 2, 3] := by
  cases hf : occurrenceLigandFrame? mol node with
  | none => simp [marked?, hf] at computed
  | some roots =>
      simp [marked?, hf] at computed
      exact ranking_positions_perm mol state fuel roots
        (roots.map fun cursor => cursor.node.atom) [0, 1, 2, 3]
        ((roots.map fun cursor => cursor.node.atom).idxOf mark) ranking computed.2

end TetraStereo.OneCenter.OccurrenceRule6RankingPermutation

assert_kernel_only TetraStereo.OneCenter.OccurrenceRule6RankingPermutation.insertion_perm
assert_kernel_only TetraStereo.OneCenter.OccurrenceRule6RankingPermutation.ranking_positions_perm
assert_kernel_only TetraStereo.OneCenter.OccurrenceRule6RankingPermutation.marked_positions_perm
