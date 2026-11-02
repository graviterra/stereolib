import TetraStereo.OneCenter.CIPAuthoritativeRule6ReferenceFamily
import TetraStereo.OneCenter.CIPAuthoritativeRule6PromotedComparatorLaws
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Strictness and refusal for the actual uncapped marked sorter

The tracked sort's uniqueness bit is justified by the existing unary-key law for
successful comparisons. A tied pair of distinct input cursors precludes uniqueness,
regardless of auxiliary state, reference, fuel, or the other input branches.
This is an execution law, not a chemical interpretation of the promoted keys.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedRankingLaws

open AuthoritativeCIPRule6ReferenceFamily AuthoritativeCIPRule6PromotedComparatorLaws

def cursorCompare (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    (left right : CanonicalRerootCursor) : Ordering :=
  comparePromotedOccurrenceBranchKeys
    (buildPromotedOccurrenceBranchKeyUnrestricted mol state reference fuel left)
    (buildPromotedOccurrenceBranchKeyUnrestricted mol state reference fuel right)

instance cursorCompare_transCmp (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference fuel : Nat) : Std.TransCmp (cursorCompare mol state reference fuel) := by
  unfold cursorCompare
  letI := comparePromotedOccurrenceBranchKeys_transCmp
  exact inferInstanceAs (Std.TransCmp (Ordering.byKey
    (buildPromotedOccurrenceBranchKeyUnrestricted mol state reference fuel)
    comparePromotedOccurrenceBranchKeys))

theorem insert_strict_of_unique (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference fuel : Nat) (candidate : IndexedOccurrenceCursor) :
    ∀ entries,
      entries.Pairwise (fun a b => cursorCompare mol state reference fuel a.1 b.1 = .gt) →
    ∀ inserted,
      insertIndexedOccurrenceThroughRule6Authoritative? mol state reference fuel candidate
        entries = some inserted → inserted.2.2 = true →
      inserted.1.Pairwise (fun a b => cursorCompare mol state reference fuel a.1 b.1 = .gt)
  | [], _, inserted, computed, _ => by
      simp [insertIndexedOccurrenceThroughRule6Authoritative?] at computed
      subst inserted
      simp
  | low :: remaining, ordered, inserted, computed, unique => by
      obtain ⟨lowBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
      cases decisionEq : compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          mol state reference fuel candidate.1 low.1 with
      | none => simp [insertIndexedOccurrenceThroughRule6Authoritative?, decisionEq] at computed
      | some decision =>
          have factor :=
            compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
              mol state reference fuel candidate.1 low.1 decision decisionEq
          change cursorCompare mol state reference fuel candidate.1 low.1 = decision.ordering
            at factor
          cases orderingEq : decision.ordering with
          | lt =>
              cases deeperEq : insertIndexedOccurrenceThroughRule6Authoritative? mol state
                  reference fuel candidate remaining with
              | none => simp [insertIndexedOccurrenceThroughRule6Authoritative?, decisionEq,
                  orderingEq, deeperEq] at computed
              | some deeper =>
                  simp [insertIndexedOccurrenceThroughRule6Authoritative?, decisionEq,
                    orderingEq, deeperEq] at computed
                  subst inserted
                  refine List.pairwise_cons.mpr ⟨?_,
                    insert_strict_of_unique mol state reference fuel candidate remaining
                      tailOrdered deeper deeperEq unique⟩
                  intro entry member
                  have perm := insertIndexedOccurrenceThroughRule6Authoritative?_perm mol state
                    reference fuel candidate remaining deeper deeperEq
                  rcases List.mem_cons.mp (perm.mem_iff.mp member) with rfl | member
                  · have swap := Std.OrientedCmp.eq_swap
                      (cmp := cursorCompare mol state reference fuel) (a := low.1) (b := entry.1)
                    simpa [factor, orderingEq] using swap
                  · exact lowBefore entry member
          | eq =>
              simp [insertIndexedOccurrenceThroughRule6Authoritative?, decisionEq, orderingEq]
                at computed
              subst inserted
              simp at unique
          | gt =>
              simp [insertIndexedOccurrenceThroughRule6Authoritative?, decisionEq, orderingEq]
                at computed
              subst inserted
              refine List.pairwise_cons.mpr ⟨?_, ordered⟩
              intro entry member
              have first := factor.trans orderingEq
              rcases List.mem_cons.mp member with rfl | member
              · exact first
              · exact Std.TransCmp.gt_trans first (lowBefore entry member)

theorem sort_strict_of_unique (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference fuel : Nat) : ∀ entries sorted,
    sortIndexedOccurrencesThroughRule6Authoritative? mol state reference fuel entries =
      some sorted → sorted.2.2 = true →
    sorted.1.Pairwise (fun a b => cursorCompare mol state reference fuel a.1 b.1 = .gt)
  | [], sorted, computed, _ => by
      simp [sortIndexedOccurrencesThroughRule6Authoritative?] at computed
      subst sorted
      simp
  | candidate :: remaining, sorted, computed, unique => by
      cases tailEq : sortIndexedOccurrencesThroughRule6Authoritative? mol state reference fuel
          remaining with
      | none => simp [sortIndexedOccurrencesThroughRule6Authoritative?, tailEq] at computed
      | some tail =>
          cases insertedEq : insertIndexedOccurrenceThroughRule6Authoritative? mol state reference
              fuel candidate tail.1 with
          | none => simp [sortIndexedOccurrencesThroughRule6Authoritative?, tailEq, insertedEq]
              at computed
          | some inserted =>
              simp [sortIndexedOccurrencesThroughRule6Authoritative?, tailEq, insertedEq] at computed
              subst sorted
              have both : tail.2.2 = true ∧ inserted.2.2 = true := by simpa using unique
              obtain ⟨tailUnique, insertedUnique⟩ := both
              exact insert_strict_of_unique mol state reference fuel candidate tail.1
                (sort_strict_of_unique mol state reference fuel remaining tail tailEq tailUnique)
                inserted insertedEq insertedUnique

/-- Successful tied comparisons prevent the actual ranker from claiming uniqueness. No
comparison-totality, sortedness, or desired refusal premise is needed. -/
theorem ranking_not_unique_of_tie (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference fuel : Nat) (roots : List CanonicalRerootCursor)
    (left right : CanonicalRerootCursor) (leftMem : left ∈ roots) (rightMem : right ∈ roots)
    (distinct : left ≠ right) (decision : Rule6TrackedDecision)
    (compared : compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
      mol state reference fuel left right = some decision) (tied : decision.ordering = .eq)
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?
      mol state reference fuel roots = some ranking) : ranking.unique = false := by
  cases sortedEq : sortIndexedOccurrencesThroughRule6Authoritative? mol state reference fuel
      roots.zipIdx with
  | none => simp [rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?, sortedEq] at computed
  | some sorted =>
      simp [rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?, sortedEq] at computed
      subst ranking
      by_contra notFalse
      have unique : sorted.2.2 = true := Bool.eq_true_of_not_eq_false notFalse
      have ordered := sort_strict_of_unique mol state reference fuel roots.zipIdx sorted
        sortedEq unique
      have cursorOrdered : (sorted.1.map Prod.fst).Pairwise
          (fun a b => cursorCompare mol state reference fuel a b = .gt) :=
        List.pairwise_map.mpr ordered
      have separated : (sorted.1.map Prod.fst).Pairwise
          (fun a b => cursorCompare mol state reference fuel a b ≠ .eq) :=
        cursorOrdered.imp (by intro a b h; rw [h]; decide)
      have symmetric : Symmetric (fun a b => cursorCompare mol state reference fuel a b ≠ .eq) := by
        intro a b different equal
        apply different
        simpa [equal] using (Std.OrientedCmp.eq_swap
          (cmp := cursorCompare mol state reference fuel) (a := a) (b := b))
      have perm := (sortIndexedOccurrencesThroughRule6Authoritative?_perm mol state reference
        fuel roots.zipIdx sorted sortedEq).map Prod.fst
      have leftMember : left ∈ sorted.1.map Prod.fst := perm.mem_iff.mpr (by simpa using leftMem)
      have rightMember : right ∈ sorted.1.map Prod.fst := perm.mem_iff.mpr (by simpa using rightMem)
      apply separated.forall symmetric leftMember rightMember distinct
      exact (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
        mol state reference fuel left right decision compared).trans tied

end TetraStereo.OneCenter.LocalizedMarkedUncappedRankingLaws

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedRankingLaws.cursorCompare_transCmp
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedRankingLaws.insert_strict_of_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedRankingLaws.sort_strict_of_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedRankingLaws.ranking_not_unique_of_tie
