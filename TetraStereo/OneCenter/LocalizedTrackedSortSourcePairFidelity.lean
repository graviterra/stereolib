import TetraStereo.OneCenter.LocalizedPseudoasymmetricClassification
import TetraStereo.OneCenter.P92StereogenicUnitSemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-!
# Independent source enantiomorphism versus the tracked localized sort

`LocalizedPseudoasymmetricClassification` records the `pseudo` flag of every comparison actually
made by the stable four-ligand insertion sort and counts them.  That module deliberately says
nothing about where the `pseudo` flags come from, so by itself it cannot connect the counted
comparisons to an independent source-level enantiomorphism relation.

This module supplies the missing bridge for the exact four-position domain.  The source side is
completely independent of the sort: an injective priority rank, a symmetric irreflexive
enantiomorphism relation that is a matching, and the mirror-convexity condition that no third
ligand lies strictly between two enantiomorphic partners in the priority order.  The comparator is
assumed to succeed on every ordered pair and to report exactly the rank ordering together with
exactly the source enantiomorphism relation.  No desired sorting result, comparison count, or
comparison history is assumed.

Under those hypotheses the actual production sort function
`sortFourLocalizedLigandsTracked` returns a result whose `highestFirst` list is a permutation of the
canonical positions `0, 1, 2, 3` in rank order, and whose `pseudoComparisons` field is the
independently defined number of unordered source enantiomorphic pairs.  Consequently lowercase
output is equivalent to the source relation having exactly one enantiomorphic pair (the P-92.1.1
pseudoasymmetric-unit condition when all four ligands are mutually distinguishable), and two
constitutionally separated enantiomorphic pairs give a numerical count of two and therefore
uppercase output.  Convexity is necessary: without it the sort can fail to compare an
enantiomorphic pair at all, and that obstruction is recorded concretely at the end of the module.

All conclusions are explicitly conditional on the comparator-agreement hypothesis and on the source
structure (injective rank, symmetry, irreflexivity, matching, convexity).  Neither the agreement of
the production comparator with the source relation nor convexity is derived here from primitive
chemical input; those are the remaining obligations of the separate chemical-fidelity work.
-/

/-! ## Comparison projection, source structure, and independent pair count -/

/-- The only two fields of a comparison that the tracked stable sort reads. -/
def trackedComparisonTrace
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (first second : Fin 4) : Option (Ordering × Bool) :=
  (compareAt first second).map fun comparison =>
    (comparison.ordering, comparison.pseudo)

/-- A projection witness: a trace value comes from an actual comparison with those two fields. -/
theorem trackedComparisonTrace_some
    {compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison}
    {first second : Fin 4} {trace : Ordering × Bool}
    (observed : trackedComparisonTrace compareAt first second = some trace) :
    ∃ comparison,
      compareAt first second = some comparison ∧
      comparison.ordering = trace.1 ∧ comparison.pseudo = trace.2 := by
  obtain ⟨ordering, pseudo⟩ := trace
  unfold trackedComparisonTrace at observed
  cases computed : compareAt first second with
  | none =>
      rw [computed] at observed
      change none = some (ordering, pseudo) at observed
      cases observed
  | some comparison =>
      rw [computed] at observed
      change some (comparison.ordering, comparison.pseudo) = some (ordering, pseudo) at observed
      obtain rfl : comparison.ordering = ordering := congrArg Prod.fst (Option.some.inj observed)
      obtain rfl : comparison.pseudo = pseudo := congrArg Prod.snd (Option.some.inj observed)
      exact ⟨comparison, rfl, rfl, rfl⟩

/-- The comparator contract used by this module.

It is intentionally stronger than "the sort happens to return the right answer": every ordered pair
must be compared successfully, the ordering field must be exactly the comparison of an independent
priority rank, and the `pseudo` flag must be exactly an independent enantiomorphism relation.  This
removes the actual-sorting/history gap but says nothing about the primitive chemical obligations
that would establish such a comparator in production. -/
def ComparatorAgreesWithSource
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic] : Prop :=
  ∀ first second,
    trackedComparisonTrace compareAt first second =
      some (compare (rank first) (rank second), decide (enantiomorphic first second))

/-- A lowest-to-highest priority list: every earlier element has strictly smaller rank. -/
def SortedByRank (rank : Fin 4 → ℕ) (ligands : List (Fin 4)) : Prop :=
  ligands.Pairwise fun first second => rank first < rank second

/-- Independent source domain for the four ligands of one tetrahedral center.

* `rank_injective`: the strict total priority order, represented by an injective rank.  The rank is
  source data; it is not read back from the sort's output.
* `symmetric`, `irreflexive`: enantiomorphism is a symmetric irreflexive relation.
* `matching`: at most one enantiomorphic partner per ligand.
* `convex`: no third ligand lies strictly between two enantiomorphic partners in the priority
  order.  This is the physical mirror-convexity condition: an enantiomorphic pair is adjacent in
  the priority order once every ligand between them is excluded.
-/
structure SourceEnantiomorphicPriorityStructure
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop) : Prop where
  rank_injective : Function.Injective rank
  symmetric : ∀ first second, enantiomorphic first second → enantiomorphic second first
  irreflexive : ∀ first, ¬ enantiomorphic first first
  matching : ∀ first second third,
    enantiomorphic first second → enantiomorphic first third → second = third
  convex : ∀ first second third, enantiomorphic first second →
    ¬ ((rank first < rank third ∧ rank third < rank second) ∨
       (rank second < rank third ∧ rank third < rank first))

/-- Independent source count of unordered enantiomorphic pairs.

The six terms are the six unordered pairs of four ligand positions, each written once in increasing
position order.  This definition never mentions the sort, its comparator, or a comparison history.
-/
def sourceEnantiomorphicPairCount
    (enantiomorphic : Fin 4 → Fin 4 → Prop) [DecidableRel enantiomorphic] : ℕ :=
  (if enantiomorphic 0 1 then 1 else 0) +
  (if enantiomorphic 0 2 then 1 else 0) +
  (if enantiomorphic 1 2 then 1 else 0) +
  (if enantiomorphic 0 3 then 1 else 0) +
  (if enantiomorphic 1 3 then 1 else 0) +
  (if enantiomorphic 2 3 then 1 else 0)

/-- The six unordered pairs of four ligand positions, each written once in increasing order. -/
def sourceUnorderedPairList : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)]

/-- The independent count is exactly the number of enumerated unordered pairs satisfying the
source relation, making explicit that the six summands are one per unordered pair. -/
theorem sourceEnantiomorphicPairCount_eq_filter_length
    (enantiomorphic : Fin 4 → Fin 4 → Prop) [DecidableRel enantiomorphic] :
    sourceEnantiomorphicPairCount enantiomorphic =
      (sourceUnorderedPairList.filter
        fun pair => decide (enantiomorphic pair.1 pair.2)).length := by
  by_cases h01 : enantiomorphic 0 1 <;>
    by_cases h02 : enantiomorphic 0 2 <;>
    by_cases h12 : enantiomorphic 1 2 <;>
    by_cases h03 : enantiomorphic 0 3 <;>
    by_cases h13 : enantiomorphic 1 3 <;>
    by_cases h23 : enantiomorphic 2 3 <;>
    simp [sourceEnantiomorphicPairCount, sourceUnorderedPairList,
      h01, h02, h12, h03, h13, h23]

/-! ## Evaluating filter counts over the concrete position prefixes -/

theorem length_filter_single
    (enantiomorphic : Fin 4 → Fin 4 → Prop) [DecidableRel enantiomorphic] (candidate : Fin 4) :
    ([(0 : Fin 4)].filter fun low => decide (enantiomorphic low candidate)).length =
      (if enantiomorphic 0 candidate then 1 else 0) := by
  by_cases h : enantiomorphic 0 candidate <;> simp [h]

theorem length_filter_pair
    (enantiomorphic : Fin 4 → Fin 4 → Prop) [DecidableRel enantiomorphic] (candidate : Fin 4) :
    ([(0 : Fin 4), 1].filter fun low => decide (enantiomorphic low candidate)).length =
      (if enantiomorphic 0 candidate then 1 else 0) +
      (if enantiomorphic 1 candidate then 1 else 0) := by
  by_cases h0 : enantiomorphic 0 candidate <;>
    by_cases h1 : enantiomorphic 1 candidate <;> simp [h0, h1]

theorem length_filter_triple
    (enantiomorphic : Fin 4 → Fin 4 → Prop) [DecidableRel enantiomorphic] (candidate : Fin 4) :
    ([(0 : Fin 4), 1, 2].filter fun low => decide (enantiomorphic low candidate)).length =
      (if enantiomorphic 0 candidate then 1 else 0) +
      (if enantiomorphic 1 candidate then 1 else 0) +
      (if enantiomorphic 2 candidate then 1 else 0) := by
  by_cases h0 : enantiomorphic 0 candidate <;>
    by_cases h1 : enantiomorphic 1 candidate <;>
      by_cases h2 : enantiomorphic 2 candidate <;> simp [h0, h1, h2]

/-! ## Comparison fields extracted from the agreement hypothesis -/

theorem comparison_fields_of_agrees
    {compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison}
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : ComparatorAgreesWithSource compareAt rank enantiomorphic)
    {low candidate : Fin 4} {comparison : ConstitutionalDescriptorHierarchyComparison}
    (compared : compareAt low candidate = some comparison) :
    comparison.ordering = compare (rank low) (rank candidate) ∧
      comparison.pseudo = decide (enantiomorphic low candidate) := by
  obtain ⟨witness, hwitness, hordering, hpseudo⟩ :=
    trackedComparisonTrace_some (agrees low candidate)
  rw [compared] at hwitness
  obtain rfl : comparison = witness := Option.some.inj hwitness
  exact ⟨hordering, hpseudo⟩

/-! ## A successful insertion always exists, with a declarative derivation -/

theorem exists_declarative_insert_of_source
    {compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison}
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : ComparatorAgreesWithSource compareAt rank enantiomorphic)
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    {candidate : Fin 4} :
    ∀ {existing : List (Fin 4)},
      SortedByRank rank existing →
      candidate ∉ existing →
      ∃ inserted,
        DeclarativeTrackedLocalizedLigandInsertion compareAt candidate existing inserted
  | [], _, _ => ⟨_, DeclarativeTrackedLocalizedLigandInsertion.nil⟩
  | low :: rest, hsorted, hnotin => by
      have hnotRest : candidate ∉ rest := fun member =>
        hnotin (List.mem_cons.mpr (Or.inr member))
      have hnotLow : candidate ≠ low := fun equal =>
        hnotin (List.mem_cons.mpr (Or.inl equal))
      change List.Pairwise (fun first second => rank first < rank second) (low :: rest)
        at hsorted
      obtain ⟨hbelow, hsortedRest⟩ := List.pairwise_cons.mp hsorted
      obtain ⟨comparison, compared, hordering, hpseudo⟩ :=
        trackedComparisonTrace_some (agrees low candidate)
      cases hcase : compare (rank low) (rank candidate) with
      | eq =>
          have hrank : rank low = rank candidate := Nat.compare_eq_eq.mp hcase
          exact absurd (source.rank_injective hrank).symm hnotLow
      | lt =>
          obtain ⟨deeper, tail⟩ :=
            exists_declarative_insert_of_source agrees source hsortedRest hnotRest
          exact ⟨_, DeclarativeTrackedLocalizedLigandInsertion.placeAfter
            compared (hordering.trans hcase) tail⟩
      | gt =>
          exact ⟨_, DeclarativeTrackedLocalizedLigandInsertion.placeBefore
            compared (hordering.trans hcase)⟩

/-! ## Source properties of one declarative insertion -/

theorem declarative_insert_source_properties
    {compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison}
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : ComparatorAgreesWithSource compareAt rank enantiomorphic)
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    {candidate : Fin 4} :
    ∀ {existing : List (Fin 4)} {inserted : TrackedLocalizedLigandInsertion},
      SortedByRank rank existing →
      candidate ∉ existing →
      DeclarativeTrackedLocalizedLigandInsertion compareAt candidate existing inserted →
      inserted.lowestFirst.Perm (candidate :: existing) ∧
      SortedByRank rank inserted.lowestFirst ∧
      inserted.pseudoComparisons =
        (existing.filter fun low => decide (enantiomorphic low candidate)).length
  | [], inserted, _, _, derivation => by
      cases derivation
      exact ⟨by simp, by simp [SortedByRank], by simp⟩
  | low :: rest, inserted, hsorted, hnotin, derivation => by
      have hnotRest : candidate ∉ rest := fun member =>
        hnotin (List.mem_cons.mpr (Or.inr member))
      have hnotLow : candidate ≠ low := fun equal =>
        hnotin (List.mem_cons.mpr (Or.inl equal))
      change List.Pairwise (fun first second => rank first < rank second) (low :: rest)
        at hsorted
      obtain ⟨hbelow, hsortedRest⟩ := List.pairwise_cons.mp hsorted
      cases derivation with
      | placeBefore compared higherLow =>
          obtain ⟨hordering, hpseudo⟩ := comparison_fields_of_agrees agrees compared
          have hcompareGt : compare (rank low) (rank candidate) = Ordering.gt :=
            hordering ▸ higherLow
          have hgt : rank candidate < rank low := Nat.compare_eq_gt.mp hcompareGt
          refine ⟨by simp, ?_, ?_⟩
          · refine List.pairwise_cons.mpr ⟨?_, hsorted⟩
            intro x member
            rcases List.mem_cons.mp member with rfl | hx
            · exact hgt
            · exact lt_trans hgt (hbelow x hx)
          · dsimp only
            rw [hpseudo]
            have hempty : (rest.filter fun x => decide (enantiomorphic x candidate)) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro x member holds
              have hbetween : rank candidate < rank low ∧ rank low < rank x :=
                ⟨hgt, hbelow x member⟩
              exact source.convex x candidate low (of_decide_eq_true holds)
                (Or.inr ⟨hbetween.1, hbetween.2⟩)
            rw [List.filter_cons, hempty]
            by_cases h : enantiomorphic low candidate <;> simp [h]
      | placeAfter compared lowerLow tail =>
          obtain ⟨hordering, hpseudo⟩ := comparison_fields_of_agrees agrees compared
          have hcompareLt : compare (rank low) (rank candidate) = Ordering.lt :=
            hordering ▸ lowerLow
          have hlt : rank low < rank candidate := Nat.compare_eq_lt.mp hcompareLt
          obtain ⟨hpermDeeper, hsortedDeeper, hcountDeeper⟩ :=
            declarative_insert_source_properties agrees source hsortedRest hnotRest tail
          refine ⟨?_, ?_, ?_⟩
          · exact (List.Perm.cons low hpermDeeper).trans
              (List.Perm.swap candidate low rest)
          · refine List.pairwise_cons.mpr ⟨?_, hsortedDeeper⟩
            intro x member
            have member' : x ∈ candidate :: rest := hpermDeeper.mem_iff.mp member
            rcases List.mem_cons.mp member' with rfl | hx
            · exact hlt
            · exact hbelow x hx
          · rw [hpseudo, hcountDeeper]
            dsimp only
            by_cases h : enantiomorphic low candidate <;> simp [h, Nat.add_comm]

/-! ## Packaged tracked insertion fidelity -/

theorem insertLocalizedLigandTracked_sourceFidelity
    {compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison}
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : ComparatorAgreesWithSource compareAt rank enantiomorphic)
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    {candidate : Fin 4} {existing : List (Fin 4)}
    (hsorted : SortedByRank rank existing)
    (hnotin : candidate ∉ existing) :
    ∃ inserted,
      insertLocalizedLigandTracked compareAt candidate existing = some inserted ∧
      inserted.lowestFirst.Perm (candidate :: existing) ∧
      SortedByRank rank inserted.lowestFirst ∧
      inserted.pseudoComparisons =
        (existing.filter fun low => decide (enantiomorphic low candidate)).length := by
  obtain ⟨inserted, derivation⟩ :=
    exists_declarative_insert_of_source agrees source hsorted hnotin
  have computed :=
    (insertLocalizedLigandTracked_eq_some_iff compareAt candidate existing inserted).mpr derivation
  obtain ⟨hperm, hsortedInserted, hcount⟩ :=
    declarative_insert_source_properties agrees source hsorted hnotin derivation
  exact ⟨inserted, computed, hperm, hsortedInserted, hcount⟩

/-! ## The production four-position input list -/

theorem finRange_four : List.finRange 4 = ([(0 : Fin 4), 1, 2, 3]) := by decide

/-! ## Main source-to-actual-sort fidelity theorem -/

/-- The actual production tracked stable sort of the four canonical ligand positions succeeds and
counts exactly the independently defined unordered source enantiomorphic pairs.

The only bridge hypotheses are the explicit comparator agreement and the physical
mirror-convexity/source structure.  Nothing assumes the desired sorting result, comparison count,
or comparison history. -/
theorem sortFourLocalizedLigandsTracked_sourcePairFidelity
    {compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison}
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : ComparatorAgreesWithSource compareAt rank enantiomorphic)
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic) :
    ∃ result,
      sortFourLocalizedLigandsTracked compareAt = some result ∧
      result.highestFirst.Perm ([(0 : Fin 4), 1, 2, 3]) ∧
      SortedByRank rank result.highestFirst.reverse ∧
      result.pseudoComparisons = sourceEnantiomorphicPairCount enantiomorphic := by
  -- The candidate sequence is `0, 1, 2, 3` and the accumulated list before step `k` is a
  -- permutation of `0, ..., k-1` sorted by rank.
  obtain ⟨i1, hi1, hperm1, hsorted1, hcount1⟩ :=
    insertLocalizedLigandTracked_sourceFidelity (compareAt := compareAt) (rank := rank)
      (enantiomorphic := enantiomorphic) agrees source
      (candidate := (1 : Fin 4)) (existing := [(0 : Fin 4)])
      (by simp [SortedByRank]) (by decide)
  have hperm1' : i1.lowestFirst.Perm ([(0 : Fin 4), 1]) :=
    hperm1.trans (by decide)
  have hnotin2 : (2 : Fin 4) ∉ i1.lowestFirst :=
    fun member => absurd (hperm1'.mem_iff.mp member) (by decide)
  obtain ⟨i2, hi2, hperm2, hsorted2, hcount2⟩ :=
    insertLocalizedLigandTracked_sourceFidelity (compareAt := compareAt) (rank := rank)
      (enantiomorphic := enantiomorphic) agrees source
      (candidate := (2 : Fin 4)) (existing := i1.lowestFirst) hsorted1 hnotin2
  have hperm2' : i2.lowestFirst.Perm ([(0 : Fin 4), 1, 2]) :=
    hperm2.trans ((List.Perm.cons 2 hperm1').trans (by decide))
  have hnotin3 : (3 : Fin 4) ∉ i2.lowestFirst :=
    fun member => absurd (hperm2'.mem_iff.mp member) (by decide)
  obtain ⟨i3, hi3, hperm3, hsorted3, hcount3⟩ :=
    insertLocalizedLigandTracked_sourceFidelity (compareAt := compareAt) (rank := rank)
      (enantiomorphic := enantiomorphic) agrees source
      (candidate := (3 : Fin 4)) (existing := i2.lowestFirst) hsorted2 hnotin3
  have hperm3' : i3.lowestFirst.Perm ([(0 : Fin 4), 1, 2, 3]) :=
    hperm3.trans ((List.Perm.cons 3 hperm2').trans (by decide))
  -- The first insertion is fully determined: inserting `0` into the empty list.
  have h0 : insertLocalizedLigandTracked compareAt (0 : Fin 4) [] =
      some ({ lowestFirst := [(0 : Fin 4)], pseudoComparisons := 0 } :
        TrackedLocalizedLigandInsertion) := rfl
  -- Count contributions of the three non-trivial insertions.
  have hcount1' : i1.pseudoComparisons = (if enantiomorphic 0 1 then 1 else 0) := by
    rw [hcount1, length_filter_single]
  have hcount2' : i2.pseudoComparisons =
      (if enantiomorphic 0 2 then 1 else 0) + (if enantiomorphic 1 2 then 1 else 0) := by
    rw [hcount2, (hperm1'.filter (fun low => decide (enantiomorphic low (2 : Fin 4)))).length_eq,
      length_filter_pair]
  have hcount3' : i3.pseudoComparisons =
      (if enantiomorphic 0 3 then 1 else 0) + (if enantiomorphic 1 3 then 1 else 0) +
        (if enantiomorphic 2 3 then 1 else 0) := by
    rw [hcount3, (hperm2'.filter (fun low => decide (enantiomorphic low (3 : Fin 4)))).length_eq,
      length_filter_triple]
  -- The concrete production computation.
  have hcompute : sortFourLocalizedLigandsTracked compareAt =
      some
        { highestFirst := i3.lowestFirst.reverse
          pseudoComparisons :=
            i1.pseudoComparisons + i2.pseudoComparisons + i3.pseudoComparisons } := by
    unfold sortFourLocalizedLigandsTracked sortLocalizedLigandsTracked
    rw [finRange_four]
    simp [sortLocalizedLigandsTrackedFrom, h0, hi1, hi2, hi3]
  refine ⟨_, hcompute, ?_, ?_, ?_⟩
  · exact (List.reverse_perm i3.lowestFirst).trans hperm3'
  · simpa using hsorted3
  · simp only
    rw [hcount1', hcount2', hcount3', sourceEnantiomorphicPairCount]
    ac_rfl

/-- Every successful result of the actual production sort carries the independent source pair
count.  Success is deterministic, so the existential in the main theorem transports to any
particular `some` result. -/
theorem sortFourLocalizedLigandsTracked_pseudoComparisons_eq_sourcePairCount
    {compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison}
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : ComparatorAgreesWithSource compareAt rank enantiomorphic)
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic) :
    ∀ result, sortFourLocalizedLigandsTracked compareAt = some result →
      result.pseudoComparisons = sourceEnantiomorphicPairCount enantiomorphic := by
  intro result computed
  obtain ⟨witness, hwitness, _, _, hcount⟩ :=
    sortFourLocalizedLigandsTracked_sourcePairFidelity (compareAt := compareAt)
      (rank := rank) (enantiomorphic := enantiomorphic) agrees source
  have hresult : result = witness := by
    rw [computed] at hwitness
    exact Option.some.inj hwitness
  rw [hresult, hcount]

/-! ## Identifying the unique source pair with `ExactlyOneEnantiomorphicPair`

The independent count is one exactly when the ordered-pair uniqueness predicate of the Blue Book
semantics holds.  The proof is a finite-list argument: the six enumerated pairs are precisely the
pairs of distinct positions in increasing order, so a single satisfying pair in that list is the
same as exactly one unordered pair. -/

/-- A list all of whose elements equal `p`, containing `p`, and with no duplicates, is `[p]`. -/
theorem eq_singleton_of_mem_of_nodup_of_forall_eq {α : Type*} {l : List α} {p : α}
    (hmem : p ∈ l) (hnd : l.Nodup) (hall : ∀ q ∈ l, q = p) : l = [p] := by
  rcases l with _ | ⟨x, xs⟩
  · cases hmem
  · rcases xs with _ | ⟨y, ys⟩
    · have hx : x = p := hall x (by simp)
      rw [hx]
    · exfalso
      have hx : x = p := hall x (by simp)
      have hy : y = p := hall y (by simp)
      have hxy : x ∈ y :: ys := by
        rw [hx, hy]
        exact List.mem_cons_self
      exact (List.nodup_cons.mp hnd).1 hxy

/-- The six enumerated pairs are exactly the pairs of distinct positions in increasing order. -/
theorem mem_sourceUnorderedPairList_iff (first second : Fin 4) :
    (first, second) ∈ sourceUnorderedPairList ↔ first < second := by
  revert first second
  decide

/-- The six enumerated unordered pairs contain no repetitions. -/
theorem nodup_sourceUnorderedPairList : sourceUnorderedPairList.Nodup := by decide

/-- For a symmetric relation on the four positions, the independent count is one exactly when
there is a unique unordered enantiomorphic pair, expressed as ordered-pair uniqueness. -/
theorem sourceEnantiomorphicPairCount_eq_one_iff
    (relation : Fin 4 → Fin 4 → Prop) [DecidableRel relation]
    (symmetric : ∀ first second, relation first second → relation second first) :
    sourceEnantiomorphicPairCount relation = 1 ↔
      ∃ first second, first ≠ second ∧ relation first second ∧
        ∀ otherFirst otherSecond, otherFirst ≠ otherSecond →
          relation otherFirst otherSecond →
          ((otherFirst = first ∧ otherSecond = second) ∨
           (otherFirst = second ∧ otherSecond = first)) := by
  constructor
  · intro hcount
    have hlen :
        (sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2))).length = 1 := by
      rw [← sourceEnantiomorphicPairCount_eq_filter_length]
      exact hcount
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hlen
    have hp_in_filter : p ∈ sourceUnorderedPairList.filter
        (fun pair => decide (relation pair.1 pair.2)) := by
      rw [hp]
      exact List.mem_singleton_self p
    obtain ⟨hp_mem, hp_decide⟩ := List.mem_filter.mp hp_in_filter
    have hp_relation : relation p.1 p.2 := of_decide_eq_true hp_decide
    have hp_lt : p.1 < p.2 := (mem_sourceUnorderedPairList_iff p.1 p.2).mp hp_mem
    refine ⟨p.1, p.2, ne_of_lt hp_lt, hp_relation, ?_⟩
    intro c d hne hcd
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : (c, d) ∈ sourceUnorderedPairList :=
        (mem_sourceUnorderedPairList_iff c d).mpr hlt
      have hfilter : (c, d) ∈ sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2)) :=
        List.mem_filter.mpr ⟨hmem, decide_eq_true hcd⟩
      rw [hp] at hfilter
      have hEq : (c, d) = p := List.mem_singleton.mp hfilter
      exact Or.inl ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩
    · have hdc : relation d c := symmetric c d hcd
      have hmem : (d, c) ∈ sourceUnorderedPairList :=
        (mem_sourceUnorderedPairList_iff d c).mpr hgt
      have hfilter : (d, c) ∈ sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2)) :=
        List.mem_filter.mpr ⟨hmem, decide_eq_true hdc⟩
      rw [hp] at hfilter
      have hEq : (d, c) = p := List.mem_singleton.mp hfilter
      exact Or.inr ⟨congrArg Prod.snd hEq, congrArg Prod.fst hEq⟩
  · rintro ⟨first, second, hne, hRelation, hunique⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : (first, second) ∈ sourceUnorderedPairList :=
        (mem_sourceUnorderedPairList_iff first second).mpr hlt
      have hfilter_mem : (first, second) ∈ sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2)) :=
        List.mem_filter.mpr ⟨hmem, decide_eq_true hRelation⟩
      have hall : ∀ q ∈ sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2)), q = (first, second) := by
        intro q hq
        obtain ⟨hq_mem, hq_decide⟩ := List.mem_filter.mp hq
        have hq_lt : q.1 < q.2 := (mem_sourceUnorderedPairList_iff q.1 q.2).mp hq_mem
        have hq_relation : relation q.1 q.2 := of_decide_eq_true hq_decide
        rcases hunique q.1 q.2 (ne_of_lt hq_lt) hq_relation with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · exfalso
          rw [h1, h2] at hq_lt
          exact (not_lt_of_ge (le_of_lt hlt)) hq_lt
      have hnd : (sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2))).Nodup :=
        List.Nodup.sublist List.filter_sublist nodup_sourceUnorderedPairList
      have hfilter_eq : sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2)) = [(first, second)] :=
        eq_singleton_of_mem_of_nodup_of_forall_eq hfilter_mem hnd hall
      have hlen : (sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2))).length = 1 := by
        rw [hfilter_eq]
        rfl
      rw [sourceEnantiomorphicPairCount_eq_filter_length]
      exact hlen
    · have hRelation' : relation second first := symmetric first second hRelation
      have hmem : (second, first) ∈ sourceUnorderedPairList :=
        (mem_sourceUnorderedPairList_iff second first).mpr hgt
      have hfilter_mem : (second, first) ∈ sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2)) :=
        List.mem_filter.mpr ⟨hmem, decide_eq_true hRelation'⟩
      have hall : ∀ q ∈ sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2)), q = (second, first) := by
        intro q hq
        obtain ⟨hq_mem, hq_decide⟩ := List.mem_filter.mp hq
        have hq_lt : q.1 < q.2 := (mem_sourceUnorderedPairList_iff q.1 q.2).mp hq_mem
        have hq_relation : relation q.1 q.2 := of_decide_eq_true hq_decide
        rcases hunique q.1 q.2 (ne_of_lt hq_lt) hq_relation with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exfalso
          rw [h1, h2] at hq_lt
          exact (not_lt_of_ge (le_of_lt hgt)) hq_lt
        · exact Prod.ext h1 h2
      have hnd : (sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2))).Nodup :=
        List.Nodup.sublist List.filter_sublist nodup_sourceUnorderedPairList
      have hfilter_eq : sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2)) = [(second, first)] :=
        eq_singleton_of_mem_of_nodup_of_forall_eq hfilter_mem hnd hall
      have hlen : (sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2))).length = 1 := by
        rw [hfilter_eq]
        rfl
      rw [sourceEnantiomorphicPairCount_eq_filter_length]
      exact hlen

/-- The ligand-level form of the count-one bridge: the independent positional count is one exactly
when the Blue Book P-92.1.1 ordered-pair predicate holds for the induced ligand relation. -/
theorem sourceEnantiomorphicPairCount_ligand_eq_one_iff
    {Ligand : Type*} (ligand : Fin 4 → Ligand)
    (enantiomorphic : Ligand → Ligand → Prop) [DecidableRel enantiomorphic]
    (symmetric : ∀ first second,
      enantiomorphic first second → enantiomorphic second first) :
    sourceEnantiomorphicPairCount
        (fun first second => enantiomorphic (ligand first) (ligand second)) = 1 ↔
      BlueBookP92.ExactlyOneEnantiomorphicPair ligand enantiomorphic := by
  have h := sourceEnantiomorphicPairCount_eq_one_iff
    (fun first second => enantiomorphic (ligand first) (ligand second))
    (fun first second hrel => symmetric (ligand first) (ligand second) hrel)
  simpa only [BlueBookP92.ExactlyOneEnantiomorphicPair] using h

/-- Lowercase output is produced exactly when the numerical pseudo-comparison count is one. -/
theorem classifyTetrahedralRSPseudo_eq_pseudoasymmetric_iff
    (descriptor : RS) (pseudoComparisons : ℕ) :
    classifyTetrahedralRSPseudo descriptor pseudoComparisons =
        .pseudoasymmetric (pseudoRSOfRS descriptor) ↔
      pseudoComparisons = 1 := by
  by_cases one : pseudoComparisons = 1
  · simp [classifyTetrahedralRSPseudo, one]
  · have hne : classifyTetrahedralRSPseudo descriptor pseudoComparisons ≠
        .pseudoasymmetric (pseudoRSOfRS descriptor) := by
      rw [classifyTetrahedralRSPseudo_chiral_of_ne_one descriptor one]
      simp
    simp [hne, one]

/-- The actual tracked sort's result has pseudo-comparison count one exactly when the independent
ligand-level relation has exactly one enantiomorphic pair. -/
theorem sortFourLocalizedLigandsTracked_pseudoComparisons_eq_one_iff
    {compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison}
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : ComparatorAgreesWithSource compareAt rank enantiomorphic)
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    {Ligand : Type*} (ligand : Fin 4 → Ligand)
    (ligandEnantiomorphic : Ligand → Ligand → Prop) [DecidableRel ligandEnantiomorphic]
    (relationAgrees : ∀ first second,
      enantiomorphic first second ↔ ligandEnantiomorphic (ligand first) (ligand second))
    (ligandSymmetric : ∀ first second,
      ligandEnantiomorphic first second → ligandEnantiomorphic second first) :
    ∀ result, sortFourLocalizedLigandsTracked compareAt = some result →
      (result.pseudoComparisons = 1 ↔
        BlueBookP92.ExactlyOneEnantiomorphicPair ligand ligandEnantiomorphic) := by
  intro result computed
  rw [sortFourLocalizedLigandsTracked_pseudoComparisons_eq_sourcePairCount
    (compareAt := compareAt) (rank := rank) (enantiomorphic := enantiomorphic)
    agrees source result computed]
  have hcountRel : sourceEnantiomorphicPairCount enantiomorphic =
      sourceEnantiomorphicPairCount
        (fun first second => ligandEnantiomorphic (ligand first) (ligand second)) := by
    unfold sourceEnantiomorphicPairCount
    simp only [relationAgrees]
  rw [hcountRel]
  exact sourceEnantiomorphicPairCount_ligand_eq_one_iff ligand ligandEnantiomorphic
    ligandSymmetric

/-- When all four ligands are mutually distinguishable, the actual classification is lowercase
exactly for the independent P-92.1.1 pseudoasymmetric-unit condition. -/
theorem classifyTetrahedralRSPseudo_lowercase_iff_isPseudoasymmetricUnit
    {Ligand : Type*} (descriptor : RS) (ligand : Fin 4 → Ligand)
    (distinguishable : Ligand → Ligand → Prop)
    (enantiomorphic : Ligand → Ligand → Prop) [DecidableRel enantiomorphic]
    (symmetric : ∀ first second, enantiomorphic first second → enantiomorphic second first)
    (distinct : ∀ first second, first ≠ second →
      distinguishable (ligand first) (ligand second)) :
    classifyTetrahedralRSPseudo descriptor
        (sourceEnantiomorphicPairCount
          (fun first second => enantiomorphic (ligand first) (ligand second))) =
        .pseudoasymmetric (pseudoRSOfRS descriptor) ↔
      BlueBookP92.IsPseudoasymmetricUnit ligand distinguishable enantiomorphic := by
  rw [classifyTetrahedralRSPseudo_eq_pseudoasymmetric_iff,
    sourceEnantiomorphicPairCount_ligand_eq_one_iff ligand enantiomorphic symmetric]
  exact ⟨fun exactlyOne => ⟨distinct, exactlyOne⟩, fun unit => unit.2⟩

/-! ## Concrete two-pair classification: count two is uppercase

The production rule counts strict pseudo comparisons numerically and lowercases only at count one.
This example keeps that numerical rule: two constitutionally separated enantiomorphic pairs give
count two and uppercase output.  No parity reduction is applied. -/

/-- Two constitutionally separated enantiomorphic pairs `{0,1}` and `{2,3}`. -/
def separatedPairRelation (first second : Fin 4) : Prop :=
  (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) ∨
    (first = 2 ∧ second = 3) ∨ (first = 3 ∧ second = 2)

instance separatedPairRelationDecidableRel : DecidableRel separatedPairRelation :=
  fun first second => by
    unfold separatedPairRelation
    infer_instance

/-- The canonical priority rank of the four positions. -/
def fourPositionRank (position : Fin 4) : ℕ := position.val

theorem separatedPairRelation_symmetric :
    ∀ first second, separatedPairRelation first second →
      separatedPairRelation second first := by
  decide

theorem separatedPairRelation_irreflexive :
    ∀ first, ¬ separatedPairRelation first first := by
  decide

theorem separatedPairRelation_matching :
    ∀ first second third, separatedPairRelation first second →
      separatedPairRelation first third → second = third := by
  decide

theorem fourPositionRank_injective : Function.Injective fourPositionRank := by
  intro first second equal
  apply Fin.ext
  simpa [fourPositionRank] using equal

theorem separatedPairRelation_convex :
    ∀ first second third : Fin 4, separatedPairRelation first second →
      ¬ ((fourPositionRank first < fourPositionRank third ∧
            fourPositionRank third < fourPositionRank second) ∨
         (fourPositionRank second < fourPositionRank third ∧
            fourPositionRank third < fourPositionRank first)) := by
  decide

/-- The separated-pair relation with the canonical rank satisfies every source field, including
convexity: the two pairs are adjacent in the priority order. -/
theorem separatedPairSourceStructure :
    SourceEnantiomorphicPriorityStructure fourPositionRank separatedPairRelation where
  rank_injective := fourPositionRank_injective
  symmetric := separatedPairRelation_symmetric
  irreflexive := separatedPairRelation_irreflexive
  matching := separatedPairRelation_matching
  convex := separatedPairRelation_convex

/-- The independent source count is exactly two, not one and not zero. -/
theorem separatedPair_count :
    sourceEnantiomorphicPairCount separatedPairRelation = 2 := by decide

/-- A concrete comparator whose ordering is the independent rank order and whose pseudo flag is
exactly the independent separated-pair relation. -/
def separatedPairCompareAt (first second : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison :=
  some
    { ordering := compare (fourPositionRank first) (fourPositionRank second)
      pseudo := decide (separatedPairRelation first second) }

theorem separatedPairCompareAt_agrees :
    ComparatorAgreesWithSource separatedPairCompareAt fourPositionRank
      separatedPairRelation := by
  intro first second
  simp [trackedComparisonTrace, separatedPairCompareAt]

/-- The actual production sort of the separated-pair input succeeds with numerical count two. -/
theorem separatedPair_sort_pseudoComparisons :
    ∃ result,
      sortFourLocalizedLigandsTracked separatedPairCompareAt = some result ∧
      result.pseudoComparisons = 2 := by
  obtain ⟨result, computed, _, _, count⟩ :=
    sortFourLocalizedLigandsTracked_sourcePairFidelity
      (compareAt := separatedPairCompareAt) (rank := fourPositionRank)
      (enantiomorphic := separatedPairRelation)
      separatedPairCompareAt_agrees separatedPairSourceStructure
  exact ⟨result, computed, by rw [count, separatedPair_count]⟩

/-- Count two classifies as uppercase `chiral`, never as a lowercase parity label. -/
theorem separatedPair_classify_uppercase (descriptor : RS) :
    classifyTetrahedralRSPseudo descriptor
        (sourceEnantiomorphicPairCount separatedPairRelation) = .chiral descriptor := by
  rw [separatedPair_count]
  exact classifyTetrahedralRSPseudo_two descriptor

/-- The actual sort's output for the separated-pair input is uppercase. -/
theorem separatedPair_sort_classify_uppercase (descriptor : RS) :
    ∀ result, sortFourLocalizedLigandsTracked separatedPairCompareAt = some result →
      classifyTetrahedralRSPseudo descriptor result.pseudoComparisons = .chiral descriptor := by
  intro result computed
  obtain ⟨witness, hwitness, count⟩ := separatedPair_sort_pseudoComparisons
  have hresult : result = witness := by
    rw [computed] at hwitness
    exact Option.some.inj hwitness
  rw [hresult, count]
  exact classifyTetrahedralRSPseudo_two descriptor

/-! ## Necessity of convexity: a matching-only counterexample

The remaining source fields (injective rank, symmetry, irreflexivity, matching, and full comparator
agreement) do not imply the conclusion.  With ascending priority order `0, 3, 1, 2` and the sole
enantiomorphic pair `{2,3}`, the canonical insertion sequence `0, 1, 2, 3` never compares `2` with
`3`.  The actual sort therefore reports zero pseudo comparisons while the independent source count
is one: convexity is a genuine hypothesis, not a derived consequence. -/

/-- Priority rank with ascending order `0, 3, 1, 2`. -/
def obstructionRank (position : Fin 4) : ℕ :=
  match position.val with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | _ => 1

/-- The sole enantiomorphic pair `{2,3}`. -/
def obstructionRelation (first second : Fin 4) : Prop :=
  (first = 2 ∧ second = 3) ∨ (first = 3 ∧ second = 2)

instance obstructionRelationDecidableRel : DecidableRel obstructionRelation :=
  fun first second => by
    unfold obstructionRelation
    infer_instance

theorem obstructionRelation_symmetric :
    ∀ first second, obstructionRelation first second → obstructionRelation second first := by
  decide

theorem obstructionRelation_irreflexive :
    ∀ first, ¬ obstructionRelation first first := by decide

theorem obstructionRelation_matching :
    ∀ first second third, obstructionRelation first second →
      obstructionRelation first third → second = third := by
  decide

theorem obstructionRank_injective : Function.Injective obstructionRank := by decide

/-- The pair `{2,3}` has `1` strictly between its ranks in the priority order. -/
theorem obstructionRank_between :
    obstructionRelation 2 3 ∧
      ((obstructionRank 2 < obstructionRank 1 ∧ obstructionRank 1 < obstructionRank 3) ∨
       (obstructionRank 3 < obstructionRank 1 ∧ obstructionRank 1 < obstructionRank 2)) := by
  decide

/-- Convexity fails for this matching-only datum. -/
theorem obstruction_not_convex :
    ¬ (∀ first second third : Fin 4, obstructionRelation first second →
      ¬ ((obstructionRank first < obstructionRank third ∧
            obstructionRank third < obstructionRank second) ∨
         (obstructionRank second < obstructionRank third ∧
            obstructionRank third < obstructionRank first))) := by
  intro convex
  obtain ⟨pair, between⟩ := obstructionRank_between
  exact convex 2 3 1 pair between

/-- A comparator fully agreeing with the obstruction rank and relation. -/
def obstructionCompareAt (first second : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison :=
  some
    { ordering := compare (obstructionRank first) (obstructionRank second)
      pseudo := decide (obstructionRelation first second) }

theorem obstructionCompareAt_agrees :
    ComparatorAgreesWithSource obstructionCompareAt obstructionRank obstructionRelation := by
  intro first second
  simp [trackedComparisonTrace, obstructionCompareAt]

/-- The actual sort succeeds but never compares the sole enantiomorphic pair `{2,3}`: its
numerical pseudo count is zero. -/
theorem obstruction_sort_pseudoComparisons_zero :
    sortFourLocalizedLigandsTracked obstructionCompareAt =
      some { highestFirst := ([(2 : Fin 4), 1, 3, 0]), pseudoComparisons := 0 } := by
  decide

/-- The independent source count for the obstruction datum is one. -/
theorem obstruction_count :
    sourceEnantiomorphicPairCount obstructionRelation = 1 := by decide

/-- Convexity is not removable: with every other source field and full comparator agreement, the
actual sort can report zero while the independent source count is one. -/
theorem obstruction_sourceCount_ne_pseudoComparisons :
    ∃ result,
      sortFourLocalizedLigandsTracked obstructionCompareAt = some result ∧
      result.pseudoComparisons = 0 ∧
      sourceEnantiomorphicPairCount obstructionRelation = 1 :=
  ⟨_, obstruction_sort_pseudoComparisons_zero, rfl, obstruction_count⟩

/-! ## Direct kernel-authority guards for the public exports -/

assert_kernel_only trackedComparisonTrace
assert_kernel_only trackedComparisonTrace_some
assert_kernel_only ComparatorAgreesWithSource
assert_kernel_only SortedByRank
assert_kernel_only SourceEnantiomorphicPriorityStructure
assert_kernel_only sourceEnantiomorphicPairCount
assert_kernel_only sourceUnorderedPairList
assert_kernel_only sourceEnantiomorphicPairCount_eq_filter_length
assert_kernel_only length_filter_single
assert_kernel_only length_filter_pair
assert_kernel_only length_filter_triple
assert_kernel_only comparison_fields_of_agrees
assert_kernel_only exists_declarative_insert_of_source
assert_kernel_only declarative_insert_source_properties
assert_kernel_only insertLocalizedLigandTracked_sourceFidelity
assert_kernel_only finRange_four
assert_kernel_only sortFourLocalizedLigandsTracked_sourcePairFidelity
assert_kernel_only sortFourLocalizedLigandsTracked_pseudoComparisons_eq_sourcePairCount
assert_kernel_only eq_singleton_of_mem_of_nodup_of_forall_eq
assert_kernel_only mem_sourceUnorderedPairList_iff
assert_kernel_only nodup_sourceUnorderedPairList
assert_kernel_only sourceEnantiomorphicPairCount_eq_one_iff
assert_kernel_only sourceEnantiomorphicPairCount_ligand_eq_one_iff
assert_kernel_only classifyTetrahedralRSPseudo_eq_pseudoasymmetric_iff
assert_kernel_only sortFourLocalizedLigandsTracked_pseudoComparisons_eq_one_iff
assert_kernel_only classifyTetrahedralRSPseudo_lowercase_iff_isPseudoasymmetricUnit
assert_kernel_only separatedPairRelation
assert_kernel_only separatedPairRelationDecidableRel
assert_kernel_only fourPositionRank
assert_kernel_only separatedPairRelation_symmetric
assert_kernel_only separatedPairRelation_irreflexive
assert_kernel_only separatedPairRelation_matching
assert_kernel_only fourPositionRank_injective
assert_kernel_only separatedPairRelation_convex
assert_kernel_only separatedPairSourceStructure
assert_kernel_only separatedPair_count
assert_kernel_only separatedPairCompareAt
assert_kernel_only separatedPairCompareAt_agrees
assert_kernel_only separatedPair_sort_pseudoComparisons
assert_kernel_only separatedPair_classify_uppercase
assert_kernel_only separatedPair_sort_classify_uppercase
assert_kernel_only obstructionRank
assert_kernel_only obstructionRelation
assert_kernel_only obstructionRelationDecidableRel
assert_kernel_only obstructionRelation_symmetric
assert_kernel_only obstructionRelation_irreflexive
assert_kernel_only obstructionRelation_matching
assert_kernel_only obstructionRank_injective
assert_kernel_only obstructionRank_between
assert_kernel_only obstruction_not_convex
assert_kernel_only obstructionCompareAt
assert_kernel_only obstructionCompareAt_agrees
assert_kernel_only obstruction_sort_pseudoComparisons_zero
assert_kernel_only obstruction_count
assert_kernel_only obstruction_sourceCount_ne_pseudoComparisons

end TetraStereo.OneCenter
