import TetraStereo.OneCenter.LocalizedRule4bPopulationInvariance
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableUnique

set_option autoImplicit false

/-!
# Rule-4b selected-reference agreement from ranked-label invariants (generic core)

`LocalizedCumulativeKeyObservableUnique` establishes that independent cumulative-key derivations
agree on their comparison-visible observations.  Those observations do **not** pin down the
`rankedLabels` field: the broad derivations allow arbitrary descending permutations of
comparator-equivalent children, and `LocalizedRule4bPopulationInvariance` shows that permuting outer
observation layers can change the first-rank population that feeds
`localizedRule4bReferencesFromRankedLabels`.

This module supplies the **generic implication** from two explicit ranked-label invariants to
equality of the selected Rule-4b reference list:

* `rankedLabelProjection` — the exact Rule-4a projection sequence (rank addresses together with
  priority kinds, with uppercase `R`/`S` values erased); and
* `localizedChiralDescriptorsAtRank` — at every sphere depth and hierarchy rank path, the
  uppercase `R`/`S` populations are related by `List.Perm`
  (packaged as `RankedChiralAgrees`).

The first invariant is used to *derive* equal rank-address skeletons and equal first occupied chiral
rank paths (it is not assumed as a separate first-rank hypothesis).  Combined with per-rank
population agreement, this gives `Perm` agreement of the first-chiral-rank population; since
`localizedRule4bReferencesFromPopulation` only counts `R` and `S`, the selected reference lists are
equal.

Scope: this is a generic implication over arbitrary ranked-label layer lists.  It does not itself
prove that two same-cursor declarative derivations satisfy the two invariants, and it contains no
assembly-permutation lemma.  Discharging the invariants from same-cursor derivation semantics is
supplied by separate modules; those semantic modules may depend on this one, not the reverse.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## Address skeletons and the chiral-agreement invariant -/

/-- Drop every `R`/`S` value and keep only the hierarchy rank path of each observation, sphere by
sphere.  Two independent derivations agree on this skeleton even though the exact descriptor values
at a tie are not forced by the observation. -/
def rankedLabelShape
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    List (List (List Nat)) :=
  layers.map fun layer => layer.map fun entry => entry.1

/-- The first hierarchy rank path at which an uppercase chiral observation occurs in one already
ordered sphere, or `none` if the sphere contains none. -/
def firstChiralRank :
    List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) → Option (List Nat)
  | [] => none
  | (rank, label) :: rest =>
      match label with
      | some (.chiral _) => some rank
      | none | some (.pseudoasymmetric _) => firstChiralRank rest

/-- Project a whole ranked-label layer list to its Rule-4a address+priority skeleton.  This is the
exact projection invariant `(A)` consumed by the generic core: equal projections force equal
rank-address skeletons and equal first occupied rank paths (chiral priority `2`). -/
def rankedLabelProjection
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    List (List (OfficialSparseEntry (List Nat))) :=
  layers.map projectRule4aLayer

/-- First occupied chiral rank read off a Rule-4a projected sphere: the first entry whose priority
is the chiral value `2`. -/
def firstChiralRankOfProjection :
    List (OfficialSparseEntry (List Nat)) → Option (List Nat)
  | [] => none
  | (rank, priority) :: rest =>
      if priority = [2] then some rank else firstChiralRankOfProjection rest

/-- `firstChiralRank` is exactly `firstChiralRankOfProjection` after the Rule-4a projection. -/
theorem firstChiralRank_eq_firstChiralRankOfProjection :
    ∀ layer, firstChiralRank layer = firstChiralRankOfProjection (projectRule4aLayer layer)
  | [] => rfl
  | (rank, label) :: rest => by
      cases label with
      | none => simp [firstChiralRank, firstChiralRankOfProjection, projectRule4aLayer,
          projectRule4aEntry, localizedCumulativeRule45Priority, localizedRule4aPriority,
          firstChiralRank_eq_firstChiralRankOfProjection rest]
      | some label => cases label with
        | pseudoasymmetric descriptor =>
            simp [firstChiralRank, firstChiralRankOfProjection, projectRule4aLayer,
              projectRule4aEntry, localizedCumulativeRule45Priority, localizedRule4aPriority,
              firstChiralRank_eq_firstChiralRankOfProjection rest]
        | chiral descriptor =>
            simp [firstChiralRank, firstChiralRankOfProjection, projectRule4aLayer,
              projectRule4aEntry, localizedCumulativeRule45Priority, localizedRule4aPriority]

/-- Equal Rule-4a projections force equal first occupied rank paths in every sphere: the `(A)`
invariant *derives* the first-occupied-rank condition instead of assuming it. -/
theorem firstChiralRank_eq_of_projection_eq {left right}
    (h : rankedLabelProjection left = rankedLabelProjection right) :
    ∀ depth, firstChiralRank (left.getD depth []) = firstChiralRank (right.getD depth []) := by
  revert right
  induction left with
  | nil =>
      intro right h depth
      cases right with
      | nil => rfl
      | cons layer rest => simp [rankedLabelProjection] at h
  | cons layer rest ih =>
      intro right h depth
      cases right with
      | nil => simp [rankedLabelProjection] at h
      | cons layer' rest' =>
          cases depth with
          | zero =>
              have hlayer : projectRule4aLayer layer = projectRule4aLayer layer' := by
                simp only [rankedLabelProjection, List.map_cons, List.cons.injEq] at h
                exact h.1
              simp only [List.getD_cons_zero]
              rw [firstChiralRank_eq_firstChiralRankOfProjection layer,
                firstChiralRank_eq_firstChiralRankOfProjection layer', hlayer]
          | succ depth =>
              have htail : rankedLabelProjection rest = rankedLabelProjection rest' := by
                simp only [rankedLabelProjection, List.map_cons, List.cons.injEq] at h
                exact h.2
              simp only [List.getD_cons_succ]
              exact ih htail depth

/-- Equal Rule-4a projections force equal address skeletons. -/
theorem rankedLabelShape_eq_of_projection_eq {left right}
    (h : rankedLabelProjection left = rankedLabelProjection right) :
    rankedLabelShape left = rankedLabelShape right := by
  have h' := congrArg
    (fun x : List (List (OfficialSparseEntry (List Nat))) => x.map fun layer => layer.map Prod.fst) h
  simpa [rankedLabelProjection, rankedLabelShape, projectRule4aLayer, projectRule4aEntry,
    List.map_map, Function.comp_def] using h'

/-- The invariant that makes the Rule-4b first-rank population well-defined across two independent
ranked-label layer lists: identical Rule-4a projections `(A)` — which force equal skeletons and
equal first occupied ranks — and at every depth and rank path the same multiset `(B)` of uppercase
chiral descriptors. -/
def RankedChiralAgrees
    (left right : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) : Prop :=
  rankedLabelProjection left = rankedLabelProjection right ∧
    ∀ (depth : Nat) (rank : List Nat),
      (localizedChiralDescriptorsAtRank rank (left.getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank (right.getD depth []))

/-- A non-chiral head observation contributes nothing to the fixed-rank descriptor population. -/
@[simp] theorem localizedChiralDescriptorsAtRank_cons_none (rank r : List Nat) (rest) :
    localizedChiralDescriptorsAtRank r ((rank, none) :: rest) =
      localizedChiralDescriptorsAtRank r rest := by
  simp [localizedChiralDescriptorsAtRank]

/-- A pseudoasymmetric head observation contributes nothing to the fixed-rank uppercase population. -/
@[simp] theorem localizedChiralDescriptorsAtRank_cons_pseudoasymmetric
    (rank r : List Nat) (descriptor : PseudoRS) (rest) :
    localizedChiralDescriptorsAtRank r ((rank, some (.pseudoasymmetric descriptor)) :: rest) =
      localizedChiralDescriptorsAtRank r rest := by
  simp [localizedChiralDescriptorsAtRank]

/-- `localizedFirstChiralRankPopulationInLayer` is the population at `firstChiralRank`. -/
theorem localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank :
    ∀ layer,
      localizedFirstChiralRankPopulationInLayer layer =
        (firstChiralRank layer).map fun rank =>
          localizedChiralDescriptorsAtRank rank layer
  | [] => rfl
  | (rank, label) :: rest => by
      cases label with
      | none => simp [localizedFirstChiralRankPopulationInLayer, firstChiralRank,
          localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank rest]
      | some label => cases label with
        | pseudoasymmetric descriptor =>
            simp [localizedFirstChiralRankPopulationInLayer, firstChiralRank,
              localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank rest]
        | chiral descriptor =>
            simp [localizedFirstChiralRankPopulationInLayer, firstChiralRank,
              localizedChiralDescriptorsAtRank]

/-- Prefixing every address of a sphere with a sibling/rank slot does not change the descriptors
selected at the correspondingly extended rank path: slot-prefixing commutes with rank extraction. -/
theorem localizedChiralDescriptorsAtRank_prefixLayer (slot : Nat) (rank : List Nat) :
    ∀ layer,
      localizedChiralDescriptorsAtRank (slot :: rank)
        (OfficialRuleMajorKey.prefixLayer slot layer) =
        localizedChiralDescriptorsAtRank rank layer := by
  intro layer
  rw [localizedChiralDescriptorsAtRank_eq_filterMap (slot :: rank)
      (OfficialRuleMajorKey.prefixLayer slot layer),
    localizedChiralDescriptorsAtRank_eq_filterMap rank layer]
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro e _
  rcases e with ⟨address, label⟩
  cases label with
  | none => rfl
  | some label => cases label with
    | pseudoasymmetric descriptor => rfl
    | chiral descriptor =>
        by_cases h : address = rank
        · subst address
          simp [chiralDescriptorAtRank]
        · have hne : slot :: address ≠ slot :: rank := by
            intro hc
            exact h (List.cons.inj hc).2
          simp [chiralDescriptorAtRank, h, hne]

/-! ## First-ranked population agreement from the invariant -/

/-- When two spheres share their first chiral rank path and every fixed-rank population, their
first-ranked populations agree. -/
theorem localizedFirstChiralRankPopulationInLayer_eq_of_firstChiralRank_eq
    {left right}
    (hrank : firstChiralRank left = firstChiralRank right) :
    localizedFirstChiralRankPopulationInLayer left =
      (firstChiralRank right).map fun rank => localizedChiralDescriptorsAtRank rank left := by
  rw [localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank left, hrank]

/-- Shape + first-rank agreement alone fixes the first-ranked population: the first occupied sphere
is the same, its first occupied rank path is the same, and the populations there are `Perm`-related. -/
theorem localizedFirstChiralRankPopulation_perm_of_shape_firstChiralRank
    {left right}
    (hshape : rankedLabelShape left = rankedLabelShape right)
    (hrank : ∀ depth, firstChiralRank (left.getD depth []) = firstChiralRank (right.getD depth []))
    (hchiral : ∀ depth rank, (localizedChiralDescriptorsAtRank rank (left.getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank (right.getD depth []))) :
    (localizedFirstChiralRankPopulation left).Perm
      (localizedFirstChiralRankPopulation right) := by
  revert right
  induction left with
  | nil =>
      intro right hshape hrank hchiral
      cases right with
      | nil => rfl
      | cons layer' right' => simp [rankedLabelShape] at hshape
  | cons layer rest ih =>
      intro right hshape hrank hchiral
      cases right with
      | nil => simp [rankedLabelShape] at hshape
      | cons layer' right' =>
          have hshape' : rankedLabelShape rest = rankedLabelShape right' := by
            simp [rankedLabelShape] at hshape
            exact hshape.2
          have hrank' : ∀ depth,
              firstChiralRank (rest.getD depth []) = firstChiralRank (right'.getD depth []) := by
            intro depth
            simpa using hrank (depth + 1)
          have hchiral' : ∀ depth rank,
              (localizedChiralDescriptorsAtRank rank (rest.getD depth [])).Perm
                (localizedChiralDescriptorsAtRank rank (right'.getD depth [])) := by
            intro depth rank
            simpa using hchiral (depth + 1) rank
          cases hfr : firstChiralRank layer with
          | none =>
              have hfr' : firstChiralRank layer' = none := by
                have h0 : firstChiralRank layer = firstChiralRank layer' := by
                  simpa using hrank 0
                rw [hfr] at h0
                exact h0.symm
              have hpop : localizedFirstChiralRankPopulationInLayer layer = none := by
                simp [localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank layer, hfr]
              have hpop' : localizedFirstChiralRankPopulationInLayer layer' = none := by
                simp [localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank layer', hfr']
              simp [localizedFirstChiralRankPopulation, hpop, hpop']
              exact ih hshape' hrank' hchiral'
          | some rank =>
              have hfr' : firstChiralRank layer' = some rank := by
                have h0 : firstChiralRank layer = firstChiralRank layer' := by
                  simpa using hrank 0
                rw [hfr] at h0
                exact h0.symm
              have hpop : localizedFirstChiralRankPopulationInLayer layer =
                  some (localizedChiralDescriptorsAtRank rank layer) := by
                simp [localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank layer, hfr]
              have hpop' : localizedFirstChiralRankPopulationInLayer layer' =
                  some (localizedChiralDescriptorsAtRank rank layer') := by
                simp [localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank layer', hfr']
              simp [localizedFirstChiralRankPopulation, hpop, hpop']
              exact hchiral 0 rank

/-- The reference population is well-defined across two ranked-label layer lists satisfying
`RankedChiralAgrees`: equal Rule-4a projections derive equal skeletons and first occupied ranks,
and the populations there are `Perm`-related. -/
theorem localizedFirstChiralRankPopulation_perm_of_rankedChiralAgrees
    {left right}
    (hprojection : rankedLabelProjection left = rankedLabelProjection right)
    (hchiral : ∀ depth rank, (localizedChiralDescriptorsAtRank rank (left.getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank (right.getD depth []))) :
    (localizedFirstChiralRankPopulation left).Perm
      (localizedFirstChiralRankPopulation right) := by
  exact localizedFirstChiralRankPopulation_perm_of_shape_firstChiralRank
    (rankedLabelShape_eq_of_projection_eq hprojection)
    (firstChiralRank_eq_of_projection_eq hprojection)
    hchiral

/-- The selected Rule-4b reference list depends only on the `R`/`S` counts of the first-ranked
population, so `RankedChiralAgrees` forces equal reference lists. -/
theorem localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees
    {left right}
    (hprojection : rankedLabelProjection left = rankedLabelProjection right)
    (hchiral : ∀ depth rank, (localizedChiralDescriptorsAtRank rank (left.getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank (right.getD depth []))) :
    localizedRule4bReferencesFromRankedLabels left = localizedRule4bReferencesFromRankedLabels right := by
  unfold localizedRule4bReferencesFromRankedLabels
  exact localizedRule4bReferencesFromPopulation_perm
    (localizedFirstChiralRankPopulation_perm_of_rankedChiralAgrees hprojection hchiral)

/-- The package form of the implication: `RankedChiralAgrees` alone forces equal reference lists. -/
theorem localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees'
    {left right} (h : RankedChiralAgrees left right) :
    localizedRule4bReferencesFromRankedLabels left = localizedRule4bReferencesFromRankedLabels right := by
  exact localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees h.1 h.2

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
