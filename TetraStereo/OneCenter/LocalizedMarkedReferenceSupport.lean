import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Molecular occurrence support of an actual Rule-6 decision

A promotion decision requires reference presence somewhere in the actual reroot traversal, not
necessarily in the immediate ligand frame. If both traversals avoid a reference, a successful complete comparison
has exactly its earlier-rule ordering and reports no promotion decision. Conversely, an actual
promotion decision witnesses an occurrence of the reference in one of those traversals.

The molecular endpoint derives execution success from chemical intake and the actual generated
occurrence. Auxiliary states are arbitrary, so no correctness of supplied or generated labels is
assumed here. This establishes a necessary support condition for a Rule-6 decision; it does not
prove chemical correctness of recursive auxiliary labels or adopt a recalculation profile.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedReferenceSupport

open LocalizedMarkedTerminalGaugeKeys
open AuthoritativeCIPMancudeTotality AuthoritativeCIPOccurrenceCompleteness
open AuthoritativeCIPMoleculeCursorRanking AuthoritativeCIPOccurrenceCompleteness.DescriptorRule6HierarchySupport
open RawMolecule

/-- Presence in the retained reroot expansion, including ring-duplicate occurrences. -/
def ReferenceOccurs (mol : RawMolecule) (reference : Nat) (cursor : CanonicalRerootCursor) : Prop :=
  ∃ descendant, Below mol cursor descendant ∧ descendant.node.atom = reference

theorem avoids_singleton_iff (mol : RawMolecule) (reference : Nat)
    (cursor : CanonicalRerootCursor) :
    Avoids mol [reference] cursor ↔ ¬ ReferenceOccurs mol reference cursor := by
  simp [Avoids, ReferenceOccurs]

/-- All paired observations agree on whether their atom is the reference. -/
def SameReferenceBits (reference : Nat)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) : Prop :=
  ∀ pair ∈ pairs, (pair.1.node.atom = reference ↔ pair.2.node.atom = reference)

/-- Left is senior at the first unequal reference observation. This predicate contains no
comparison call, key construction, or assumed descriptor. -/
def FirstReferencePreference (reference : Nat) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) → Prop
  | [] => False
  | pair :: rest =>
      (pair.1.node.atom = reference ∧ pair.2.node.atom ≠ reference) ∨
        ((pair.1.node.atom = reference ↔ pair.2.node.atom = reference) ∧
          FirstReferencePreference reference rest)

theorem pairLabels_tie_iff (reference : Nat)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) :
    compareOccurrenceRule6PairLabels reference pairs = .eq ↔ SameReferenceBits reference pairs := by
  induction pairs with
  | nil => simp [compareOccurrenceRule6PairLabels, SameReferenceBits]
  | cons pair rest ih =>
      by_cases left : pair.1.node.atom = reference <;>
      by_cases right : pair.2.node.atom = reference <;>
        simp_all [compareOccurrenceRule6PairLabels, SameReferenceBits]

theorem pairLabels_gt_iff (reference : Nat)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) :
    compareOccurrenceRule6PairLabels reference pairs = .gt ↔
      FirstReferencePreference reference pairs := by
  induction pairs with
  | nil => simp [compareOccurrenceRule6PairLabels, FirstReferencePreference]
  | cons pair rest ih =>
      by_cases left : pair.1.node.atom = reference <;>
      by_cases right : pair.2.node.atom = reference <;>
        simp_all [compareOccurrenceRule6PairLabels, FirstReferencePreference] <;> decide

/-- One actual frontier expansion, permitted only after every current reference observation ties.
The traversal order is still the runtime's order; canonical-address independence is a separate
obligation, not a premise hidden in this relation. -/
def TiedFrontierStep (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) (reference : Nat)
    (current next : List (CanonicalRerootCursor × CanonicalRerootCursor)) : Prop :=
  SameReferenceBits reference current ∧
    nextOccurrenceDescriptorPairsAuthoritative? mol before before current = some next

/-- A strict scan has a first-difference witness at an actually generated frontier, with all
earlier frontier observations tied. Unlike mere subtree presence, this locates a scanned witness. -/
theorem rule6_gt_has_first_difference (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) (reference : Nat) :
    ∀ fuel pairs,
      compareOccurrenceRule6Authoritative mol before reference fuel pairs = some .gt →
      ∃ winning, Relation.ReflTransGen (TiedFrontierStep mol before reference) pairs winning ∧
        FirstReferencePreference reference winning := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs computed
      cases labels : compareOccurrenceRule6PairLabels reference pairs with
      | lt => simp [compareOccurrenceRule6Authoritative, labels] at computed
      | gt => exact ⟨pairs, .refl, (pairLabels_gt_iff reference pairs).mp labels⟩
      | eq =>
          simp only [compareOccurrenceRule6Authoritative, labels] at computed
          split at computed <;> contradiction
  | succ fuel ih =>
      intro pairs computed
      cases labels : compareOccurrenceRule6PairLabels reference pairs with
      | lt => simp [compareOccurrenceRule6Authoritative, labels] at computed
      | gt => exact ⟨pairs, .refl, (pairLabels_gt_iff reference pairs).mp labels⟩
      | eq =>
          simp only [compareOccurrenceRule6Authoritative, labels] at computed
          split at computed
          · contradiction
          · contradiction
          · obtain ⟨winning, chain, decisive⟩ := ih _ computed
            exact ⟨winning, (Relation.ReflTransGen.single
              ⟨(pairLabels_tie_iff reference pairs).mp labels, by assumption⟩).trans chain,
              decisive⟩

/-- A reference-free scan can fail for insufficient fuel, but cannot return a strict decision. -/
theorem rule6_ties_of_avoid (mol : RawMolecule) (reference : Nat)
    (valid : reference < mol.atomCount)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∀ fuel pairs, PairsAvoid mol [reference] pairs → ∀ outcome,
      compareOccurrenceRule6Authoritative mol before reference fuel pairs = some outcome →
      outcome = .eq := by
  have inRange : ∀ r ∈ [reference], r < mol.atomCount := by simpa using valid
  intro fuel
  induction fuel with
  | zero =>
      intro pairs good outcome computed
      have labels := rule6PairLabels_eq_of_avoid mol [reference] reference (by simp) pairs good
      simp only [compareOccurrenceRule6Authoritative, labels] at computed
      split at computed
      · exact (Option.some.inj computed).symm
      · contradiction
  | succ fuel ih =>
      intro pairs good outcome computed
      have labels := rule6PairLabels_eq_of_avoid mol [reference] reference (by simp) pairs good
      have nextGood := (nextPairs_congr mol [reference] inRange before before
        (fun _ _ _ _ => rfl) pairs good).2
      simp only [compareOccurrenceRule6Authoritative, labels] at computed
      split at computed
      · contradiction
      · exact (Option.some.inj computed).symm
      · exact ih _ (nextGood _ (by assumption)) outcome computed

/-- An absent reference changes neither the ordering nor the promotion-use bit of a successful
comparison. The earlier comparison is obtained from the actual execution, not supplied. -/
theorem promoted_of_avoid (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference : Nat) (valid : reference < mol.atomCount) (fuel : Nat)
    (left right : CanonicalRerootCursor)
    (leftAbsent : Avoids mol [reference] left) (rightAbsent : Avoids mol [reference] right)
    (result : Rule6TrackedDecision)
    (computed : compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
      mol state reference fuel left right = some result) :
    ∃ prior, compareOccurrenceBranchesUnrestrictedAuthoritative? mol state fuel left right =
      some prior ∧ result.ordering = prior.ordering ∧ result.pseudo = false := by
  have leftNe : left.node.atom ≠ reference := by simpa using leftAbsent.self
  have rightNe : right.node.atom ≠ reference := by simpa using rightAbsent.self
  cases fuel with
  | zero =>
      cases hp : compareOccurrenceBranchesUnrestrictedAuthoritative? mol state 0 left right with
      | none => simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp] at computed
      | some prior =>
          by_cases tied : prior.ordering = Ordering.eq
          · simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp,
              tied, leftNe, rightNe] at computed
            subst result
            exact ⟨prior, rfl, tied.symm, rfl⟩
          · simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp, tied] at computed
            subst result
            exact ⟨prior, rfl, rfl, rfl⟩
  | succ fuel =>
      cases hp : compareOccurrenceBranchesUnrestrictedAuthoritative? mol state (fuel + 1)
          left right with
      | none => simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp] at computed
      | some prior =>
          by_cases tied : prior.ordering = Ordering.eq
          · have good : PairsAvoid mol [reference] [(left, right)] := by
              intro pair member
              simp only [List.mem_singleton] at member
              subst pair
              exact ⟨leftAbsent, rightAbsent⟩
            simp only [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp,
              tied, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
            obtain ⟨outcome, scanned, equal⟩ := computed
            have ht := rule6_ties_of_avoid mol reference valid _ _ _ good outcome scanned
            subst outcome
            simp only [bne_self_eq_false, Option.some.injEq] at equal
            subst result
            exact ⟨prior, rfl, tied.symm, rfl⟩
          · simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp, tied] at computed
            subst result
            exact ⟨prior, rfl, rfl, rfl⟩

/-- A promotion-use flag has an actual atom-occurrence witness at some depth. It is not a
pseudoasymmetry claim: this flag belongs to the Rule-6 comparison API. -/
theorem promotion_has_reference (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference : Nat) (valid : reference < mol.atomCount) (fuel : Nat)
    (left right : CanonicalRerootCursor) (result : Rule6TrackedDecision)
    (computed : compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
      mol state reference fuel left right = some result)
    (used : result.pseudo = true) :
    ReferenceOccurs mol reference left ∨ ReferenceOccurs mol reference right := by
  by_contra absent
  push_neg at absent
  obtain ⟨prior, _, _, unused⟩ := promoted_of_avoid mol state reference valid fuel left right
    ((avoids_singleton_iff mol reference left).mpr absent.1)
    ((avoids_singleton_iff mol reference right).mpr absent.2) result computed
  rw [used] at unused
  contradiction

/-- The full comparator's promotion-decided seniority has the same first-difference meaning.
The ordinary tie is derived by opening the actual comparator, rather than required of the caller. -/
theorem promoted_gt_has_first_difference (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference fuel : Nat) (left right : CanonicalRerootCursor)
    (computed : compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
      mol state reference (fuel + 1) left right = some { ordering := .gt, pseudo := true }) :
    ∃ winning, Relation.ReflTransGen
        (TiedFrontierStep mol
          (fun a b => (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
            mol state reference fuel a b).map Rule6TrackedDecision.ordering) reference)
        [(left, right)] winning ∧ FirstReferencePreference reference winning := by
  cases hp : compareOccurrenceBranchesUnrestrictedAuthoritative? mol state (fuel + 1) left right with
  | none => simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp] at computed
  | some prior =>
      by_cases tied : prior.ordering = Ordering.eq
      · simp only [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp,
          tied, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
        obtain ⟨outcome, scanned, equal⟩ := computed
        have positive : outcome = .gt := congrArg Rule6TrackedDecision.ordering (Option.some.inj equal)
        subst outcome
        exact rule6_gt_has_first_difference mol _ reference _ _ scanned
      · simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, hp, tied] at computed

/-- At actual chemically admitted molecular occurrences, success and the reference-support law
hold together, at the derived full-depth bound and for any auxiliary state. -/
theorem actual_comparison_with_reference_support
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (reference : Nat) (valid : reference < mol.atomCount)
    {occurrence : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center occurrence)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol occurrence)
    (rightMember : right ∈ occurrenceLigandCursors mol occurrence) :
    ∃ result, compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
        mol state reference (2 * mol.atomCount + 1) left right = some result ∧
      (result.pseudo = true →
        ReferenceOccurs mol reference left ∨ ReferenceOccurs mol reference right) := by
  obtain ⟨result, computed⟩ :=
    promoted_occurrence_ligand_comparison_exists_of_chemical_applicability
      centerBound wellFormed unique valence kekule reference generated leftMember rightMember
  exact ⟨result, computed, promotion_has_reference mol state reference valid _ _ _ result computed⟩

/-- No comparison-success or ordinary-tie premise: the actual molecular call succeeds, and any
promotion-decided left seniority has an actual tied-frontier chain ending in the independent
first-reference-preference observation. The auxiliary state remains arbitrary. -/
theorem actual_comparison_with_first_difference
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (reference : Nat) {occurrence : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center occurrence)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol occurrence)
    (rightMember : right ∈ occurrenceLigandCursors mol occurrence) :
    ∃ result, compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
        mol state reference (2 * mol.atomCount + 1) left right = some result ∧
      (result.ordering = .gt → result.pseudo = true →
        ∃ winning, Relation.ReflTransGen
          (TiedFrontierStep mol
            (fun a b => (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
              mol state reference (2 * mol.atomCount) a b).map Rule6TrackedDecision.ordering)
            reference) [(left, right)] winning ∧ FirstReferencePreference reference winning) := by
  obtain ⟨result, computed⟩ :=
    promoted_occurrence_ligand_comparison_exists_of_chemical_applicability
      centerBound wellFormed unique valence kekule reference generated leftMember rightMember
  refine ⟨result, computed, ?_⟩
  intro positive used
  have resultEq : result = { ordering := .gt, pseudo := true } := by
    cases result
    simp_all
  rw [resultEq] at computed
  exact promoted_gt_has_first_difference mol state reference _ _ _ computed

end TetraStereo.OneCenter.LocalizedMarkedReferenceSupport

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.avoids_singleton_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.pairLabels_tie_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.pairLabels_gt_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.rule6_gt_has_first_difference
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.rule6_ties_of_avoid
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.promoted_of_avoid
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.promotion_has_reference
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.promoted_gt_has_first_difference
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.actual_comparison_with_reference_support
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSupport.actual_comparison_with_first_difference
