import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key

set_option autoImplicit false

/-!
# Rule-4b first-ranked-population invariance for independent cumulative keys

This module investigates the derivation-backed invariance of the P-92.5.2.1(b) reference
population.  The independent cumulative key relation
`DeclarativeLocalizedRerootCumulativeRule45Key` admits *arbitrary descending sibling
permutations* (`ranking : sorted.Perm childKeys`), while the executable build uses one stable
sort.  Two facts are established here:

1. `localizedRule4bReferencesFromPopulation` depends only on the `R`/`S` counts of its input, so
   it is invariant under `List.Perm`.
2. The population collected at one *fixed* hierarchy rank (`localizedChiralDescriptorsAtRank`) is
   a `filterMap`, hence `List.Perm`-invariant in its output up to `Perm`.

An explicit counterexample shows that permuting outer observation layers can change the selected
population. A projection/prefix commutation lemma and a tied-head sibling rank permutation lemma
provide further foundations. Full derivation-backed population invariance is not established here.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## Part 1: Permutation invariance of the reference population and fixed-rank extraction -/

/-- Project one hierarchy-rank-addressed label observation to its uppercase chiral descriptor
exactly when that observation lives at `rank`.  Non-chiral and off-rank observations project to
`none`. -/
def chiralDescriptorAtRank (rank : List Nat) :
    OfficialSparseEntry (Option LocalizedAuxiliaryLabel) → Option RS
  | (observedRank, some (.chiral descriptor)) =>
      if observedRank = rank then some descriptor else none
  | _ => none

/-- `localizedChiralDescriptorsAtRank` is exactly the `filterMap` of the single-observation
projection.  Multiplicity is preserved, matching the P-92.5.2.1(b) requirement to count
occurrences. -/
theorem localizedChiralDescriptorsAtRank_eq_filterMap (rank : List Nat) :
    ∀ observations,
      localizedChiralDescriptorsAtRank rank observations =
        observations.filterMap (chiralDescriptorAtRank rank)
  | [] => rfl
  | (observedRank, label) :: observations => by
      by_cases sameRank : observedRank = rank
      · cases label with
        | none =>
            simp [localizedChiralDescriptorsAtRank, chiralDescriptorAtRank, sameRank]
            exact localizedChiralDescriptorsAtRank_eq_filterMap rank observations
        | some label =>
            cases label with
            | pseudoasymmetric descriptor =>
                simp [localizedChiralDescriptorsAtRank, chiralDescriptorAtRank, sameRank]
                exact localizedChiralDescriptorsAtRank_eq_filterMap rank observations
            | chiral descriptor =>
                simp [localizedChiralDescriptorsAtRank, chiralDescriptorAtRank, sameRank,
                  localizedChiralDescriptorsAtRank_eq_filterMap rank observations]
      · cases label with
        | none =>
            simp [localizedChiralDescriptorsAtRank, chiralDescriptorAtRank, sameRank]
            exact localizedChiralDescriptorsAtRank_eq_filterMap rank observations
        | some label =>
            cases label with
            | pseudoasymmetric descriptor =>
                simp [localizedChiralDescriptorsAtRank, chiralDescriptorAtRank, sameRank]
                exact localizedChiralDescriptorsAtRank_eq_filterMap rank observations
            | chiral descriptor =>
                simp [localizedChiralDescriptorsAtRank, chiralDescriptorAtRank, sameRank,
                  localizedChiralDescriptorsAtRank_eq_filterMap rank observations]

/-- The population of uppercase chiral descriptors at one fixed hierarchy rank is invariant under
permuting the observation list: the result is the same multiset of descriptors up to `Perm`. -/
theorem localizedChiralDescriptorsAtRank_perm (rank : List Nat)
    {observations permuted : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))}
    (perm : observations.Perm permuted) :
    (localizedChiralDescriptorsAtRank rank observations).Perm
      (localizedChiralDescriptorsAtRank rank permuted) := by
  rw [localizedChiralDescriptorsAtRank_eq_filterMap rank observations,
    localizedChiralDescriptorsAtRank_eq_filterMap rank permuted]
  exact perm.filterMap (chiralDescriptorAtRank rank)

/-- `localizedRule4bReferencesFromPopulation` only counts `R` and `S`, so it is invariant under
`List.Perm` of the population.  This is the immediate compile foundation requested. -/
theorem localizedRule4bReferencesFromPopulation_perm
    {descriptors permuted : List RS}
    (perm : descriptors.Perm permuted) :
    localizedRule4bReferencesFromPopulation descriptors =
      localizedRule4bReferencesFromPopulation permuted := by
  have rCountEq :
      (descriptors.filter fun descriptor => descriptor == RS.R).length =
        (permuted.filter fun descriptor => descriptor == RS.R).length :=
    (List.Perm.filter (fun descriptor : RS => descriptor == RS.R) perm).length_eq
  have sCountEq :
      (descriptors.filter fun descriptor => descriptor == RS.S).length =
        (permuted.filter fun descriptor => descriptor == RS.S).length :=
    (List.Perm.filter (fun descriptor : RS => descriptor == RS.S) perm).length_eq
  unfold localizedRule4bReferencesFromPopulation
  rw [perm.isEmpty_eq, rCountEq, sCountEq]

/-! ## Part 2: first-ranked population support and order-sensitivity -/

/-- The first-ranked uppercase-chiral population of one already-ordered sphere exists exactly when
that sphere contains at least one uppercase chiral observation.  This is the "first occupied rank"
support condition: the population is `some` precisely on the support of the chiral rank class. -/
theorem localizedFirstChiralRankPopulationInLayer_some_iff_exists_chiral
    (observations : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    (∃ population, localizedFirstChiralRankPopulationInLayer observations = some population) ↔
      ∃ rank descriptor,
        (rank, some (.chiral descriptor)) ∈ observations := by
  induction observations with
  | nil =>
      constructor
      · rintro ⟨_, impossible⟩
        cases impossible
      · rintro ⟨_, _, present⟩
        cases present
  | cons observation observations ih =>
      rcases observation with ⟨rank, label⟩
      cases label with
      | none =>
          constructor
          · rintro ⟨population, computed⟩
            have computed' :
                localizedFirstChiralRankPopulationInLayer observations = some population := by
              simpa [localizedFirstChiralRankPopulationInLayer] using computed
            rcases (ih.mp ⟨population, computed'⟩) with ⟨rank', descriptor, present⟩
            exact ⟨rank', descriptor, List.mem_cons_of_mem (rank, none) present⟩
          · rintro ⟨rank', descriptor, present⟩
            rcases List.mem_cons.mp present with head | tail
            · cases head
            · exact ih.mpr ⟨rank', descriptor, tail⟩
      | some label =>
          cases label with
          | pseudoasymmetric pseudo =>
              constructor
              · rintro ⟨population, computed⟩
                have computed' :
                    localizedFirstChiralRankPopulationInLayer observations = some population := by
                  simpa [localizedFirstChiralRankPopulationInLayer] using computed
                rcases (ih.mp ⟨population, computed'⟩) with ⟨rank', descriptor, present⟩
                exact ⟨rank', descriptor,
                  List.mem_cons_of_mem (rank, some (.pseudoasymmetric pseudo)) present⟩
              · rintro ⟨rank', descriptor, present⟩
                rcases List.mem_cons.mp present with head | tail
                · cases head
                · exact ih.mpr ⟨rank', descriptor, tail⟩
          | chiral descriptor =>
              constructor
              · intro _
                exact ⟨rank, descriptor, List.mem_cons_self⟩
              · intro _
                exact ⟨descriptor :: localizedChiralDescriptorsAtRank rank observations, rfl⟩

/-- `localizedFirstChiralRankPopulation` is genuinely order-sensitive: two lists of outer observation layers that are
`Perm`-equivalent can select different first-ranked populations (`[R]` versus `[S]`), because the
first *applicable* sphere is chosen by list order, not by multiset.  This is an outer-layer permutation counterexample, not a counterexample concerning two
valid comparator-tied molecular sibling derivations. -/
theorem localizedFirstChiralRankPopulation_not_perm_invariant :
    ¬ (∀ {layers permuted : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))},
        layers.Perm permuted →
        (localizedFirstChiralRankPopulation layers).Perm
          (localizedFirstChiralRankPopulation permuted)) := by
  intro invariant
  have swapped :
      (localizedFirstChiralRankPopulation
        [[([0], (some (.chiral RS.R) : Option LocalizedAuxiliaryLabel))],
          [([0], (some (.chiral RS.S) : Option LocalizedAuxiliaryLabel))]]).Perm
        (localizedFirstChiralRankPopulation
          [[([0], (some (.chiral RS.S) : Option LocalizedAuxiliaryLabel))],
            [([0], (some (.chiral RS.R) : Option LocalizedAuxiliaryLabel))]]) :=
    invariant (List.Perm.swap
      [([0], (some (.chiral RS.S) : Option LocalizedAuxiliaryLabel))]
      [([0], (some (.chiral RS.R) : Option LocalizedAuxiliaryLabel))]
      [])
  change List.Perm [RS.R] [RS.S] at swapped
  have bad : RS.R ∈ [RS.S] := swapped.mem_iff.mp (by simp)
  simp at bad

/-! ## Part 3: Rule-4a descriptor alignment is with physical-slot `labels`, not `rankedLabels` -/

/-- Project one exact-label observation to its Rule-4a cumulative priority vector while keeping its
physical-slot address.  Rule 4a reads only the unit kind (`chiral`/`pseudoasymmetric`/`none`), so
the projection discards the specific `R`/`S`/`r`/`s` descriptor. -/
def projectRule4aEntry
    (entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) :
    OfficialSparseEntry (List Nat) :=
  (entry.1, localizedCumulativeRule45Priority .rule4a entry.2)

/-- Project a whole physical-slot label sphere to its Rule-4a descriptor sphere. -/
def projectRule4aLayer
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    List (OfficialSparseEntry (List Nat)) :=
  layer.map projectRule4aEntry

/-- The Rule-4a projection commutes with *physical-slot* prefixing.  This is the definitional
alignment: a key's `descriptor` field (built by `mergeLocalizedRerootDescriptorChildren` over
`children.zipIdx`) is, at the `.rule4a` stage, exactly `projectRule4aLayer` of its `labels` field
(built by `mergeLocalizedRerootLabelChildren` over the same `children.zipIdx`).  The `rankedLabels`
field instead uses hierarchy ranks from `localizedRerootRankedChildren`, so it does *not* carry
this slot alignment. -/
theorem projectRule4aLayer_prefixLayer (slot : Nat)
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    projectRule4aLayer (OfficialRuleMajorKey.prefixLayer slot layer) =
      OfficialRuleMajorKey.prefixLayer slot (projectRule4aLayer layer) := by
  unfold projectRule4aLayer OfficialRuleMajorKey.prefixLayer
  rw [List.map_map, List.map_map]
  apply congrArg (fun f => layer.map f)
  funext entry
  rcases entry with ⟨address, label⟩
  rfl

/-! ## Part 4: stable ranking of comparator-tied siblings -/

/-- A child that is comparator-equal to its predecessor inherits that predecessor's hierarchy rank.
This is exactly how `localizedRerootRankedChildren` collapses an equivalence class to one rank. -/
theorem localizedRerootRankedChildTail_eq_of_compare_eq
    (input : CertifiedLocalizedCIPInput)
    (previous child : input.LocalizedRerootCumulativeRule45Key) (rank : Nat)
    (tied : input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq) :
    ∀ children,
      input.localizedRerootRankedChildTail previous rank (child :: children) =
        (child, rank) :: input.localizedRerootRankedChildTail child rank children := by
  intro children
  simp [localizedRerootRankedChildTail, tied]

/-- Replacing the previous key by an equivalent one does not change the rank tail: every subsequent
child compares the same against both, by oriented transitivity of the comparator. -/
theorem localizedRerootRankedChildTail_congr_previous
    (input : CertifiedLocalizedCIPInput)
    (previous other : input.LocalizedRerootCumulativeRule45Key)
    (tied : input.compareLocalizedRerootCumulativeRule45Keys previous other = Ordering.eq) :
    ∀ (rank : Nat) children,
      input.localizedRerootRankedChildTail previous rank children =
        input.localizedRerootRankedChildTail other rank children := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  intro rank children
  induction children with
  | nil => rfl
  | cons child rest _ih =>
      simp [localizedRerootRankedChildTail, Std.TransCmp.congr_right (a := child) tied]

/-- Swapping two comparator-equal (tied) siblings at the head of the descending child list preserves
the hierarchy ranking up to `Perm`: both receive rank `0`, and the tail is unchanged.  This is the
safe core for the tie-invariance goal — it holds for *arbitrary* keys because it needs only the
comparator's oriented transitivity, not the (non-existent) generic label equality. -/
theorem localizedRerootRankedChildren_swap_head_perm
    (input : CertifiedLocalizedCIPInput)
    (a b : input.LocalizedRerootCumulativeRule45Key)
    (rest : List input.LocalizedRerootCumulativeRule45Key)
    (tied : input.compareLocalizedRerootCumulativeRule45Keys a b = Ordering.eq) :
    (input.localizedRerootRankedChildren (b :: a :: rest)).Perm
      (input.localizedRerootRankedChildren (a :: b :: rest)) := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  have baEq : input.compareLocalizedRerootCumulativeRule45Keys b a = Ordering.eq :=
    Std.OrientedCmp.eq_symm tied
  have lhsEq :
      input.localizedRerootRankedChildren (b :: a :: rest) =
        (b, 0) :: (a, 0) :: input.localizedRerootRankedChildTail a 0 rest := by
    simp [localizedRerootRankedChildren, localizedRerootRankedChildTail, tied]
  have rhsEq :
      input.localizedRerootRankedChildren (a :: b :: rest) =
        (a, 0) :: (b, 0) :: input.localizedRerootRankedChildTail b 0 rest := by
    simp [localizedRerootRankedChildren, localizedRerootRankedChildTail, baEq]
  have tailEq :
      input.localizedRerootRankedChildTail a 0 rest =
        input.localizedRerootRankedChildTail b 0 rest :=
    localizedRerootRankedChildTail_congr_previous input a b tied 0 rest
  rw [lhsEq, rhsEq, ← tailEq]
  exact List.Perm.swap (a, 0) (b, 0) (input.localizedRerootRankedChildTail a 0 rest)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
