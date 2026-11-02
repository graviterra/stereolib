import TetraStereo.OneCenter.LocalizedMarkedUncappedOperations
import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceDescriptorComparatorLaws

set_option autoImplicit false

/-!
# Actual ordinary ties exclude the strict fast path

The evaluator tests the adjacent outcomes of its actual sorted frame. This module derives
strict order from that test using the existing comparator law, then excludes the test when
two distinct frame cursors tie. No desired sorting or comparison property is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedOrdinaryStrictness

open AuthoritativeCIPRule6Scheduler AuthoritativeCIPOccurrenceDescriptorComparatorLaws
open LocalizedGenericMarkedRecalculation (strict)

def positionKey (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (position : Nat) : FailClosedOccurrenceBranchProjectedKey :=
  buildFailClosedOccurrenceBranchProjectedKey mol state fuel
    ((roots[position]?).getD { node := canonicalCenterRoot 0 })

def positionCompare (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (left right : Nat) : Ordering :=
  compareFailClosedOccurrenceBranchProjectedKeys
    (positionKey mol state fuel roots left) (positionKey mol state fuel roots right)

instance positionCompare_transCmp (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : Nat) (roots : List CanonicalRerootCursor) :
    Std.TransCmp (positionCompare mol state fuel roots) := by
  unfold positionCompare
  letI := compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  exact inferInstanceAs (Std.TransCmp (Ordering.byKey (positionKey mol state fuel roots)
    compareFailClosedOccurrenceBranchProjectedKeys))

theorem position_success_factors (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : Nat) (roots : List CanonicalRerootCursor) (left right : Nat)
    (decision : OccurrenceComparison)
    (computed : compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
      some decision) : positionCompare mol state fuel roots left right = decision.ordering := by
  cases leftEq : roots[left]? with
  | none => simp [compareAuthoritativeRule6InitialPositions?, leftEq] at computed
  | some leftRoot =>
      cases rightEq : roots[right]? with
      | none => simp [compareAuthoritativeRule6InitialPositions?, leftEq, rightEq] at computed
      | some rightRoot =>
          have branch : compareOccurrenceBranchesUnrestrictedAuthoritative? mol state fuel
              leftRoot rightRoot = some decision := by
            simpa [compareAuthoritativeRule6InitialPositions?, leftEq, rightEq] using computed
          simpa [positionCompare, positionKey, leftEq, rightEq] using
            compareOccurrenceBranchesUnrestricted_ordering_success_factors mol state fuel
              leftRoot rightRoot decision branch

theorem adjacent_strict_pairwise (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : Nat) (roots : List CanonicalRerootCursor) : ∀ positions adjacent,
    compareAuthoritativeRule6InitialAdjacent? mol state fuel roots positions = some adjacent →
    strict adjacent = true →
    positions.Pairwise (fun a b => positionCompare mol state fuel roots a b = .gt)
  | [], _, _, _ => by simp
  | [_], _, _, _ => by simp
  | left :: right :: remaining, adjacent, computed, allStrict => by
      cases compared : compareAuthoritativeRule6InitialPositions? mol state fuel roots
          left right with
      | none => simp [compareAuthoritativeRule6InitialAdjacent?, compared] at computed
      | some decision =>
          cases tailEq : compareAuthoritativeRule6InitialAdjacent? mol state fuel roots
              (right :: remaining) with
          | none => simp [compareAuthoritativeRule6InitialAdjacent?, compared, tailEq] at computed
          | some tail =>
              simp [compareAuthoritativeRule6InitialAdjacent?, compared, tailEq] at computed
              subst adjacent
              have pieces : decision.ordering = .gt ∧ strict tail = true := by
                simpa [strict] using allStrict
              have headStrict := (position_success_factors mol state fuel roots left right
                decision compared).trans pieces.1
              have tailOrdered := adjacent_strict_pairwise mol state fuel roots (right :: remaining)
                tail tailEq pieces.2
              refine List.pairwise_cons.mpr ⟨?_, tailOrdered⟩
              intro position member
              rcases List.mem_cons.mp member with rfl | member
              · exact headStrict
              · exact Std.TransCmp.gt_trans headStrict
                  ((List.pairwise_cons.mp tailOrdered).1 position member)

theorem partition_not_strict_of_tie (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : Nat) (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacent : List (Option Ordering))
    (sorting : sortAuthoritativeRule6InitialPositions? mol state fuel roots
      (List.range roots.length) = some sorted)
    (adjacency : compareAuthoritativeRule6InitialAdjacent? mol state fuel roots sorted = some adjacent)
    (left right : Nat) (leftBound : left < roots.length) (rightBound : right < roots.length)
    (distinct : left ≠ right) (decision : OccurrenceComparison)
    (compared : compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
      some decision) (tied : decision.ordering = .eq) : strict adjacent = false := by
  by_contra notFalse
  have allStrict : strict adjacent = true := Bool.eq_true_of_not_eq_false notFalse
  have ordered := adjacent_strict_pairwise mol state fuel roots sorted adjacent adjacency allStrict
  have separated : sorted.Pairwise (fun a b => positionCompare mol state fuel roots a b ≠ .eq) :=
    ordered.imp (by intro a b h; rw [h]; decide)
  have symmetric : Symmetric (fun a b => positionCompare mol state fuel roots a b ≠ .eq) := by
    intro a b different equal
    apply different
    simpa [equal] using (Std.OrientedCmp.eq_swap
      (cmp := positionCompare mol state fuel roots) (a := a) (b := b))
  have perm := sortAuthoritativeRule6InitialPositions?_perm mol state fuel roots _ _ sorting
  have leftMember : left ∈ sorted := perm.mem_iff.mpr (List.mem_range.mpr leftBound)
  have rightMember : right ∈ sorted := perm.mem_iff.mpr (List.mem_range.mpr rightBound)
  exact separated.forall symmetric leftMember rightMember distinct
    ((position_success_factors mol state fuel roots left right decision compared).trans tied)

/-- The literal ordinary operation cannot advertise a strict frame if two distinct actual
frame cursors tie. -/
theorem ordinary_not_strict_of_tie (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (frame : occurrenceLigandFrame? mol node = some roots)
    (left right : CanonicalRerootCursor) (leftMem : left ∈ roots) (rightMem : right ∈ roots)
    (distinct : left ≠ right) (decision : OccurrenceComparison)
    (compared : compareOccurrenceBranchesUnrestrictedAuthoritative? mol state
      (LocalizedMarkedUncappedOperations.comparisonFuel mol) left right = some decision)
    (tied : decision.ordering = .eq) (sorted : List Nat) (adjacent : List (Option Ordering))
    (computed : LocalizedMarkedUncappedOperations.ordinary? mol state node = some (sorted, adjacent)) :
    strict adjacent = false := by
  have leftEq := List.getElem?_idxOf leftMem
  have rightEq := List.getElem?_idxOf rightMem
  have indices : roots.idxOf left ≠ roots.idxOf right := by
    intro equal
    rw [equal, rightEq] at leftEq
    exact distinct (Option.some.inj leftEq.symm)
  cases sorting : sortAuthoritativeRule6InitialPositions? mol state
      (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots (List.range roots.length) with
  | none => simp [LocalizedMarkedUncappedOperations.ordinary?, frame, sorting] at computed
  | some actualSorted =>
      cases adjacency : compareAuthoritativeRule6InitialAdjacent? mol state
          (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots actualSorted with
      | none => simp [LocalizedMarkedUncappedOperations.ordinary?, frame, sorting, adjacency]
          at computed
      | some actualAdjacent =>
          have pairEq : (actualSorted, actualAdjacent) = (sorted, adjacent) := by
            simpa [LocalizedMarkedUncappedOperations.ordinary?, frame, sorting, adjacency]
              using computed
          cases pairEq
          apply partition_not_strict_of_tie mol state _ roots _ _ sorting adjacency
            (roots.idxOf left) (roots.idxOf right) (List.idxOf_lt_length_iff.mpr leftMem)
            (List.idxOf_lt_length_iff.mpr rightMem) indices decision _ tied
          simpa [compareAuthoritativeRule6InitialPositions?, leftEq, rightEq] using compared

end TetraStereo.OneCenter.LocalizedMarkedOrdinaryStrictness

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOrdinaryStrictness.positionCompare_transCmp
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOrdinaryStrictness.position_success_factors
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOrdinaryStrictness.adjacent_strict_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOrdinaryStrictness.partition_not_strict_of_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOrdinaryStrictness.ordinary_not_strict_of_tie
