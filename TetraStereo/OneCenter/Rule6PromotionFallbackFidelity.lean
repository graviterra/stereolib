import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Rule 6 projected fallback isolation and source-profile refusal

Source profile: the Rule 6 used here is the **proposed** Rule 6 of the May 2018 Hanson
author preprint (`Hanson2018-preprint.txt:959-1030`).  The corrected online 2013 Blue Book
(P9) Rule list does not contain a Rule 6.  This module does not claim journal-version
reconciliation or formal source approval.

The production module `SmilesTetrahedral.lean` has two distinct Rule-6 routes:

* an authoritative occurrence route (`compareOccurrenceBranchesThroughRule6AtAuthoritative?`,
  line 3889) that fails closed when an earlier authoritative comparison is unavailable, and
* a projected route (`compareBranchesThroughRule6Tracked?`, line 3990) whose promotion
  comparison `compareRule6Promotion?` (line 3739) substitutes shortest root-avoiding graph
  distance to the promoted reference when compiled promotion layers are unavailable or tie.

This module records the exact failure/refusal preservation of the authoritative occurrence
route, factors the projected wrapper so the fallback call site is explicit, defines a
source-profile promotion comparator that refuses rather than substituting graph distance, and
builds concrete `RawMolecule` witnesses for both behaviours.  It deliberately leaves the
existing source implementation unchanged.

## What the witnesses establish, and what they do not

The concrete witnesses are hand-built `RawMolecule` values, i.e. actual inputs to the
computable definitions rather than synthetic comparator outputs.  Each witness is formally
admitted by the executable structural, valence-table and Rule-2-mass checks
(`certify?` returns `some`), and each is explicitly recorded below.

* The ten-atom witness is an admitted four-ligand center whose left promotion hierarchy is
  unavailable, so the helper `compareRule6Promotion?` returns a strict graph-distance ordering.
  Its public pre-Rule-6 comparison is nevertheless already strict on the tested ligand pair, so
  the tracked wrapper returns the strict non-pseudo pre-Rule-6 decision and never selects the
  Rule-6 fallback.  This is a helper-level fallback, not a public misassignment.
* The three-ligand star witness has a proved pre-Rule-6 tie and an absent authoritative
  occurrence decision, so the tracked wrapper genuinely reaches the projected promotion call.
  The compatibility comparator then refuses (`none`), because the blocked center separates
  both ligands from the reference; the public result is `none`.
* The fifteen-atom symmetric witness has a certified constitution automorphism fixing the
  center and swapping ligand roots `1` and `3`, and both authoritative promotion hierarchies
  are unavailable, so the helper comparison is again a strict distance ordering.  Its public
  pre-Rule-6 comparison is `none` (the Rules 3--5 observation is unavailable on the unsupported
  anionic halves), so the tracked wrapper returns `none`.  There is no public pre-Rule-6 tie.

Consequently this module exhibits **no** admitted four-ligand input on which the public tracked
wrapper selects a strict distance fallback.  The helper-level distance exits are recorded
exactly, and the public refusals are recorded exactly; no broader defect claim is made.

The source-profile comparator defined below is an isolated proposed fail-closed adapter.  It is
not an integrated repair of the production fallback and it is not proved chemically equivalent
to the full promotion ranking of the proposed Rule 6.
-/

namespace TetraStereo
namespace OneCenter

/-! ## Authoritative occurrence route: failure is preserved -/

/-- If the earlier authoritative occurrence comparison fails, the authoritative Rule-6
occurrence comparison fails at fuel zero.  No graph-distance fallback is consulted. -/
theorem compareOccurrenceBranchesThroughRule6AtAuthoritative?_eq_none_of_prior_eq_none
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (prior : compareOccurrenceBranchesAuthoritative? mol state fuel left right = none) :
    compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel left right =
      none := by
  cases fuel with
  | zero =>
      simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, prior]
  | succ fuel =>
      simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, prior]

/-- A failed authoritative descriptor-sphere expansion remains a failure at every positive
Rule-6 occurrence fuel. -/
theorem compareOccurrenceRule6Authoritative_succ_eq_none_of_next_none
    (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference fuel : ℕ) (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor))
    (labels : compareOccurrenceRule6PairLabels reference pairs = Ordering.eq)
    (next : nextOccurrenceDescriptorPairsAuthoritative? mol before before pairs = none) :
    compareOccurrenceRule6Authoritative mol before reference (fuel + 1) pairs = none := by
  simp [compareOccurrenceRule6Authoritative, labels, next]

/-- The occurrence Rule-6 traversal never reaches a distance fallback: at fuel zero a missing
next sphere is a refusal unless the pair list is already exhausted. -/
theorem compareOccurrenceRule6Authoritative_zero_eq_none_of_next_ne_nil
    (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : ℕ) (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor))
    (labels : compareOccurrenceRule6PairLabels reference pairs = Ordering.eq)
    (next : nextOccurrenceDescriptorPairsAuthoritative? mol before before pairs ≠ some []) :
    compareOccurrenceRule6Authoritative mol before reference 0 pairs = none := by
  cases observed : nextOccurrenceDescriptorPairsAuthoritative? mol before before pairs with
  | none =>
      simp [compareOccurrenceRule6Authoritative, labels, observed]
  | some nextPairs =>
      cases nextPairs with
      | nil => exact absurd observed next
      | cons pair rest =>
          simp [compareOccurrenceRule6Authoritative, labels, observed]

/-- The fully authoritative public occurrence wrapper preserves an authoritative build failure:
without an auxiliary environment there is no Rule-6 decision and no fallback. -/
theorem compareOccurrenceBranchesThroughRule6FullyAuthoritative?_eq_none_of_aux_none
    (mol : RawMolecule) (fuel center reference left right : ℕ)
    (aux : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = none) :
    compareOccurrenceBranchesThroughRule6FullyAuthoritative? mol fuel center reference left right =
      none := by
  simp [compareOccurrenceBranchesThroughRule6FullyAuthoritative?, aux]

/-- The same refusal is inherited by the public occurrence comparator. -/
theorem compareOccurrenceBranchesThroughRule6?_eq_none_of_aux_none
    (mol : RawMolecule) (fuel center reference left right : ℕ)
    (aux : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = none) :
    compareOccurrenceBranchesThroughRule6? mol fuel center reference left right = none := by
  simp [compareOccurrenceBranchesThroughRule6?,
    compareOccurrenceBranchesThroughRule6FullyAuthoritative?, aux]

/-! ## Projected route: explicit factorization of the fallback call site -/

/-- The projected Rules-1--5-then-Rule-6 comparison performed by the tracked wrapper.  This is
the exactly transcribed `projected` local of `compareBranchesThroughRule6Tracked?`; it calls
`compareRule6Promotion?`, whose distance fallback is the object of this module. -/
def projectedRule6Comparison? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ) :
    Option Rule6TrackedDecision :=
  match compareBranchesBeforeRule6Context? result mol state fuel center left right with
  | some Ordering.lt => some { ordering := Ordering.lt, pseudo := false }
  | some Ordering.gt => some { ordering := Ordering.gt, pseudo := false }
  | some Ordering.eq =>
      (compareRule6Promotion? mol fuel center reference left right).map fun ordering =>
        { ordering := ordering, pseudo := ordering != Ordering.eq }
  | none => none

/-- Definitional factorization of the live tracked wrapper: the authoritative occurrence
decision wins whenever it is strict; otherwise the projected comparison (and therefore the
promotion fallback) is selected. -/
theorem compareBranchesThroughRule6Tracked?_factorization
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ) :
    compareBranchesThroughRule6Tracked? result mol state fuel center reference left right =
      match compareOccurrenceBranchesThroughRule6? mol fuel center reference left right with
      | some decision =>
          if decision.ordering == Ordering.eq then
            projectedRule6Comparison? result mol state fuel center reference left right
          else some decision
      | none => projectedRule6Comparison? result mol state fuel center reference left right := by
  rfl

/-- When the authoritative occurrence comparison is absent, the projected comparison is used. -/
theorem compareBranchesThroughRule6Tracked?_eq_projected_of_occurrence_none
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ)
    (occurrence : compareOccurrenceBranchesThroughRule6? mol fuel center reference left right =
      none) :
    compareBranchesThroughRule6Tracked? result mol state fuel center reference left right =
      projectedRule6Comparison? result mol state fuel center reference left right := by
  rw [compareBranchesThroughRule6Tracked?_factorization, occurrence]

/-- A strict authoritative occurrence decision is returned unchanged. -/
theorem compareBranchesThroughRule6Tracked?_eq_occurrence_of_occurrence_strict
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ)
    (decision : Rule6TrackedDecision)
    (occurrence : compareOccurrenceBranchesThroughRule6? mol fuel center reference left right =
      some decision)
    (strict : decision.ordering ≠ Ordering.eq) :
    compareBranchesThroughRule6Tracked? result mol state fuel center reference left right =
      some decision := by
  rw [compareBranchesThroughRule6Tracked?_factorization, occurrence]
  dsimp only
  have beyond : (decision.ordering == Ordering.eq) = false := by
    cases h : decision.ordering with
    | lt => rfl
    | gt => rfl
    | eq => exact absurd h strict
  rw [beyond]
  rfl

/-- A tied authoritative occurrence decision defers to the projected comparison. -/
theorem compareBranchesThroughRule6Tracked?_eq_projected_of_occurrence_tied
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ)
    (decision : Rule6TrackedDecision)
    (occurrence : compareOccurrenceBranchesThroughRule6? mol fuel center reference left right =
      some decision)
    (tied : decision.ordering = Ordering.eq) :
    compareBranchesThroughRule6Tracked? result mol state fuel center reference left right =
      projectedRule6Comparison? result mol state fuel center reference left right := by
  rw [compareBranchesThroughRule6Tracked?_factorization, occurrence]
  dsimp only
  have beyond : (decision.ordering == Ordering.eq) = true := by
    rw [tied]
    rfl
  rw [beyond]
  rfl

/-- Rule-6 `±2` fallback selected through the live projected wrapper exactly when the earlier
Rules-1--5 comparison tied and the authoritative occurrence decision is absent.  This is the
precise call path reviewed at `SmilesTetrahedral.lean:3990-4003`. -/
theorem compareBranchesThroughRule6Tracked?_eq_fallback_of_before_tied_of_occurrence_none
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ)
    (before : compareBranchesBeforeRule6Context? result mol state fuel center left right =
      some Ordering.eq)
    (occurrence : compareOccurrenceBranchesThroughRule6? mol fuel center reference left right =
      none) :
    compareBranchesThroughRule6Tracked? result mol state fuel center reference left right =
      (compareRule6Promotion? mol fuel center reference left right).map
        (fun ordering => { ordering := ordering, pseudo := ordering != Ordering.eq }) := by
  rw [compareBranchesThroughRule6Tracked?_eq_projected_of_occurrence_none
    result mol state fuel center reference left right occurrence]
  simp [projectedRule6Comparison?, before]

/-- A tied (rather than absent) authoritative occurrence decision also defers to the projected
comparison.  Hence a proved pre-Rule-6 tie selects the distance fallback whether the occurrence
route is unavailable or returns `eq`. -/
theorem compareBranchesThroughRule6Tracked?_eq_fallback_of_before_tied_of_occurrence_tied
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ)
    (decision : Rule6TrackedDecision)
    (before : compareBranchesBeforeRule6Context? result mol state fuel center left right =
      some Ordering.eq)
    (occurrence : compareOccurrenceBranchesThroughRule6? mol fuel center reference left right =
      some decision)
    (tied : decision.ordering = Ordering.eq) :
    compareBranchesThroughRule6Tracked? result mol state fuel center reference left right =
      (compareRule6Promotion? mol fuel center reference left right).map
        (fun ordering => { ordering := ordering, pseudo := ordering != Ordering.eq }) := by
  rw [compareBranchesThroughRule6Tracked?_factorization, occurrence]
  dsimp only
  have beyond : (decision.ordering == Ordering.eq) = true := by
    rw [tied]
    rfl
  rw [beyond]
  simp [projectedRule6Comparison?, before]

/-- The projected wrapper refuses when both the earlier comparison and the authoritative
occurrence comparison fail: there is no Rule-6 fallback without a proved pre-Rule-6 tie. -/
theorem compareBranchesThroughRule6Tracked?_eq_none_of_before_none_of_occurrence_none
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ)
    (before : compareBranchesBeforeRule6Context? result mol state fuel center left right = none)
    (occurrence : compareOccurrenceBranchesThroughRule6? mol fuel center reference left right =
      none) :
    compareBranchesThroughRule6Tracked? result mol state fuel center reference left right =
      none := by
  rw [compareBranchesThroughRule6Tracked?_eq_projected_of_occurrence_none
    result mol state fuel center reference left right occurrence]
  simp [projectedRule6Comparison?, before]

/-! ## Source-profile Rule-6 promotion comparison -/

/-- Proposed-2018 source-profile promotion comparison.

On two available promoted occurrence hierarchies this returns the strict promoted-layer
comparison, including an exact `eq` when the promoted layers tie.  If either hierarchy is
unavailable it returns `none`; graph distance is never substituted.  This is the fail-closed
counterpart of the compatibility fallback in `compareRule6Promotion?`. -/
def compareRule6PromotionSourceProfile? (mol : RawMolecule) (fuel center reference left right : ℕ) :
    Option Ordering :=
  match rule6PromotionLayers? mol fuel center left reference,
      rule6PromotionLayers? mol fuel center right reference with
  | some leftLayers, some rightLayers =>
      some (RawMolecule.compareSparseCanonicalLayers compare leftLayers rightLayers)
  | _, _ => none

/-- Source-profile comparator, unavailable case: no promoted hierarchy means refusal. -/
theorem compareRule6PromotionSourceProfile?_eq_none_of_unavailable
    (mol : RawMolecule) (fuel center reference left right : ℕ)
    (unavailable :
      rule6PromotionLayers? mol fuel center left reference = none ∨
        rule6PromotionLayers? mol fuel center right reference = none) :
    compareRule6PromotionSourceProfile? mol fuel center reference left right = none := by
  rcases unavailable with leftUnavailable | rightUnavailable
  · simp [compareRule6PromotionSourceProfile?, leftUnavailable]
  · cases leftLayers : rule6PromotionLayers? mol fuel center left reference with
    | none => simp [compareRule6PromotionSourceProfile?, leftLayers]
    | some layers => simp [compareRule6PromotionSourceProfile?, leftLayers, rightUnavailable]

/-- Source-profile comparator, tied case: equal promoted layers are preserved as `some eq`. -/
theorem compareRule6PromotionSourceProfile?_eq_some_eq_of_tied
    (mol : RawMolecule) (fuel center reference left right : ℕ)
    (leftLayers rightLayers : List (List RawMolecule.CanonicalNatEntry))
    (leftAvailable : rule6PromotionLayers? mol fuel center left reference = some leftLayers)
    (rightAvailable : rule6PromotionLayers? mol fuel center right reference = some rightLayers)
    (tied : RawMolecule.compareSparseCanonicalLayers compare leftLayers rightLayers =
      Ordering.eq) :
    compareRule6PromotionSourceProfile? mol fuel center reference left right =
      some Ordering.eq := by
  simp [compareRule6PromotionSourceProfile?, leftAvailable, rightAvailable, tied]

/-- The source-profile comparator decides strictly exactly when the promoted-layer comparison
does.  On every strict source-profile result the compatibility comparator
`compareRule6Promotion?` agrees; the compatibility fallback only adds outcomes in the
unavailable or tied cases. -/
theorem compareRule6Promotion?_eq_some_of_sourceProfile_some_strict
    (mol : RawMolecule) (fuel center reference left right : ℕ) (ordering : Ordering)
    (profile : compareRule6PromotionSourceProfile? mol fuel center reference left right =
      some ordering)
    (strict : ordering ≠ Ordering.eq) :
    compareRule6Promotion? mol fuel center reference left right = some ordering := by
  cases leftLayers : rule6PromotionLayers? mol fuel center left reference with
  | none => simp [compareRule6PromotionSourceProfile?, leftLayers] at profile
  | some left =>
      cases rightLayers : rule6PromotionLayers? mol fuel center right reference with
      | none => simp [compareRule6PromotionSourceProfile?, leftLayers, rightLayers] at profile
      | some right =>
          have layers : RawMolecule.compareSparseCanonicalLayers compare left right =
              ordering := by
            simpa [compareRule6PromotionSourceProfile?, leftLayers, rightLayers] using profile
          cases ordering with
          | eq => exact absurd rfl strict
          | lt =>
              simp [compareRule6Promotion?, leftLayers, rightLayers, layers]
          | gt =>
              simp [compareRule6Promotion?, leftLayers, rightLayers, layers]

/-- When both promoted hierarchies are available and their comparison is strict, the
compatibility comparator and the source-profile comparator agree exactly. -/
theorem compareRule6Promotion?_eq_sourceProfile_of_layers_ne_eq
    (mol : RawMolecule) (fuel center reference left right : ℕ)
    (leftLayers rightLayers : List (List RawMolecule.CanonicalNatEntry))
    (leftAvailable : rule6PromotionLayers? mol fuel center left reference = some leftLayers)
    (rightAvailable : rule6PromotionLayers? mol fuel center right reference = some rightLayers)
    (strict : RawMolecule.compareSparseCanonicalLayers compare leftLayers rightLayers ≠
      Ordering.eq) :
    compareRule6Promotion? mol fuel center reference left right =
      compareRule6PromotionSourceProfile? mol fuel center reference left right := by
  cases comparison : RawMolecule.compareSparseCanonicalLayers compare leftLayers rightLayers with
  | eq => exact absurd comparison strict
  | lt =>
      simp [compareRule6Promotion?, compareRule6PromotionSourceProfile?,
        leftAvailable, rightAvailable, comparison]
  | gt =>
      simp [compareRule6Promotion?, compareRule6PromotionSourceProfile?,
        leftAvailable, rightAvailable, comparison]

/-! ## The graph-distance fallback in isolation -/

/-- The graph-distance comparison used by the compatibility fallback. -/
def rule6DistanceComparison? (mol : RawMolecule) (center reference left right : ℕ) :
    Option Ordering :=
  match mol.rule6ReferenceDistance? center reference (mol.atomCount + 1) 0 [left] [left],
      mol.rule6ReferenceDistance? center reference (mol.atomCount + 1) 0 [right] [right] with
  | some leftDistance, some rightDistance =>
      if leftDistance < rightDistance then some Ordering.gt
      else if rightDistance < leftDistance then some Ordering.lt
      else some Ordering.eq
  | some _, none => some Ordering.gt
  | none, some _ => some Ordering.lt
  | none, none => none

/-- Promotion unavailable on the left branch: the compatibility comparator is exactly its
graph-distance fallback. -/
theorem compareRule6Promotion?_eq_distance_of_left_unavailable
    (mol : RawMolecule) (fuel center reference left right : ℕ)
    (unavailable : rule6PromotionLayers? mol fuel center left reference = none) :
    compareRule6Promotion? mol fuel center reference left right =
      rule6DistanceComparison? mol center reference left right := by
  unfold compareRule6Promotion? rule6DistanceComparison?
  rw [unavailable]
  cases rule6PromotionLayers? mol fuel center right reference <;> rfl

/-- Promotion unavailable on the right branch: the compatibility comparator is exactly its
graph-distance fallback. -/
theorem compareRule6Promotion?_eq_distance_of_right_unavailable
    (mol : RawMolecule) (fuel center reference left right : ℕ)
    (unavailable : rule6PromotionLayers? mol fuel center right reference = none) :
    compareRule6Promotion? mol fuel center reference left right =
      rule6DistanceComparison? mol center reference left right := by
  unfold compareRule6Promotion? rule6DistanceComparison?
  rw [unavailable]
  cases rule6PromotionLayers? mol fuel center left reference <;> rfl

/-- Equal promoted layers: the compatibility comparator is exactly its graph-distance
fallback.  This records the second unsourced exit, independently of whether distance can
decide. -/
theorem compareRule6Promotion?_eq_distance_of_layers_tied
    (mol : RawMolecule) (fuel center reference left right : ℕ)
    (leftLayers rightLayers : List (List RawMolecule.CanonicalNatEntry))
    (leftAvailable : rule6PromotionLayers? mol fuel center left reference = some leftLayers)
    (rightAvailable : rule6PromotionLayers? mol fuel center right reference = some rightLayers)
    (tied : RawMolecule.compareSparseCanonicalLayers compare leftLayers rightLayers =
      Ordering.eq) :
    compareRule6Promotion? mol fuel center reference left right =
      rule6DistanceComparison? mol center reference left right := by
  unfold compareRule6Promotion? rule6DistanceComparison?
  rw [leftAvailable, rightAvailable]
  dsimp only
  rw [tied]
  rfl

/-- If the two fallback distance lookups agree on an available distance, the fallback returns
`eq`.  Thus the compatibility fallback cannot manufacture a strict distinction from a pair of
equal distance observations.  The `none`/`none` case is a refusal, not an ordering. -/
theorem rule6DistanceComparison?_eq_some_eq_of_equal_some
    (mol : RawMolecule) (center reference left right distance : ℕ)
    (leftDistance :
      mol.rule6ReferenceDistance? center reference (mol.atomCount + 1) 0 [left] [left] =
        some distance)
    (rightDistance :
      mol.rule6ReferenceDistance? center reference (mol.atomCount + 1) 0 [right] [right] =
        some distance) :
    rule6DistanceComparison? mol center reference left right = some Ordering.eq := by
  unfold rule6DistanceComparison?
  rw [leftDistance, rightDistance]
  simp

/-! ## Concrete witnesses

The witnesses are hand-built `RawMolecule` values, i.e. actual inputs to the computable
definitions, not synthetic comparator outputs.  Every witness is admitted by the executable
structural, valence-table and Rule-2-mass checks; the corresponding `certify?` facts are
recorded below.  None of the witnesses asserts a full chemical-suitability claim beyond that
formal admission contract.

The first witness is a ten-atom molecule with one anionic cyclobutene-like component.  That
component has four localized mancude vertices, one written double bond, and a maximum matching
of size two, so the exact maximum-matching averaging refuses the relevant multiple-bond
duplicate label (`stats.size != writtenDoubleCount`).  Consequently the authoritative
promoted-layer compiler is unavailable on the left branch while the shortest root-avoiding
distance is still computable.  The public pre-Rule-6 comparison of the tested ligand pair is
already strict, so this helper-level strict fallback is not selected by the tracked consumer.

The second witness is an ordinary three-ligand star whose promoted layers tie, whose public
pre-Rule-6 comparison ties, and whose authoritative occurrence route is absent.  The projected
fallback is reached but the distance comparison refuses (`none`), because the blocked center
separates both ligands from the reference.

The third witness is a fifteen-atom symmetric molecule with a certified constitution
automorphism.  Both promotion hierarchies are unavailable, but the public pre-Rule-6
comparison is `none`, so the tracked consumer refuses; no public fallback is selected.
-/

/-- Ten-atom witness: center `0`, ligands `1`, `2`, `3`, `9`, reference `2` ring-connected to
the anionic four-membered component `4-5=6-7`. -/
def rule6DistanceFallbackWitness : RawMolecule where
  atoms :=
    [ { AtomSpec.aliphatic Element.C with
        tetrahedral? := some TetrahedralInputParity.clockwise },  -- 0 center
      AtomSpec.aliphatic Element.C,                                -- 1 left ligand
      AtomSpec.aliphatic Element.C,                                -- 2 reference ligand
      AtomSpec.aliphatic Element.C,                                -- 3 right ligand
      AtomSpec.aliphatic Element.C,                                -- 4 ring a
      AtomSpec.aliphatic Element.C,                                -- 5 ring b
      { AtomSpec.aliphatic Element.C with charge := -1 },          -- 6 ring c
      { AtomSpec.aliphatic Element.C with charge := -1 },          -- 7 ring d
      AtomSpec.aliphatic Element.H,                                -- 8 hydrogen on 7
      AtomSpec.aliphatic Element.H ]                               -- 9 fourth ligand
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single },
      { source := 0, target := 2, kind := ParsedBondKind.single },
      { source := 0, target := 3, kind := ParsedBondKind.single },
      { source := 0, target := 9, kind := ParsedBondKind.single },
      { source := 1, target := 4, kind := ParsedBondKind.single },
      { source := 4, target := 5, kind := ParsedBondKind.double },
      { source := 5, target := 6, kind := ParsedBondKind.single },
      { source := 6, target := 7, kind := ParsedBondKind.single },
      { source := 7, target := 4, kind := ParsedBondKind.single },
      { source := 6, target := 2, kind := ParsedBondKind.single },
      { source := 7, target := 8, kind := ParsedBondKind.single } ]

/-- Normalized public result bundle for the ten-atom distance witness. -/
def rule6DistanceFallbackWitnessResult : ChemistryNormalizationResult :=
  normalizeRawMolecule rule6DistanceFallbackWitness

/-- Ordinary star witness: center `0`, ligands `1`, `2`, `3`. -/
def rule6PromotionTieWitness : RawMolecule where
  atoms :=
    [ { AtomSpec.aliphatic Element.C with
        tetrahedral? := some TetrahedralInputParity.clockwise },
      AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C ]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single },
      { source := 0, target := 2, kind := ParsedBondKind.single },
      { source := 0, target := 3, kind := ParsedBondKind.single } ]

/-- Normalized public result bundle for the star witness. -/
def rule6PromotionTieWitnessResult : ChemistryNormalizationResult :=
  normalizeRawMolecule rule6PromotionTieWitness

/-- The promoted hierarchy is unavailable on the left branch of the ten-atom witness. -/
theorem rule6DistanceFallbackWitness_layers_left_unavailable :
    rule6PromotionLayers? rule6DistanceFallbackWitness 0 0 1 2 = none := by
  decide

/-- The promoted hierarchy is available on the right branch of the ten-atom witness. -/
theorem rule6DistanceFallbackWitness_layers_right_available :
    (rule6PromotionLayers? rule6DistanceFallbackWitness 0 0 3 2).isSome = true := by
  decide

/-- The left ligand reaches the reference ligand through the anionic ring in four bonds. -/
theorem rule6DistanceFallbackWitness_distance_left :
    rule6DistanceFallbackWitness.rule6ReferenceDistance? 0 2
        (rule6DistanceFallbackWitness.atomCount + 1) 0 [1] [1] = some 4 := by
  decide

/-- The right ligand cannot reach the reference ligand without crossing the blocked center. -/
theorem rule6DistanceFallbackWitness_distance_right :
    rule6DistanceFallbackWitness.rule6ReferenceDistance? 0 2
        (rule6DistanceFallbackWitness.atomCount + 1) 0 [3] [3] = none := by
  decide

/-- The compatibility comparator returns a strict ordering on the ten-atom witness purely from
graph distance: the promotion comparison is unavailable on the left branch. -/
theorem rule6DistanceFallbackWitness_compat_strict :
    compareRule6Promotion? rule6DistanceFallbackWitness 0 0 2 1 3 = some Ordering.gt := by
  decide

/-- The source-profile comparator refuses the same input: unavailable promotion yields
`none`, not a distance-derived order. -/
theorem rule6DistanceFallbackWitness_sourceProfile_none :
    compareRule6PromotionSourceProfile? rule6DistanceFallbackWitness 0 0 2 1 3 = none := by
  decide

/-- The live pre-Rule-6 comparison is already strict on the ten-atom witness, so the tracked
consumer never selects the Rule-6 promotion fallback for this ligand pair. -/
theorem rule6DistanceFallbackWitness_before_strict :
    compareBranchesBeforeRule6Context? rule6DistanceFallbackWitnessResult
      rule6DistanceFallbackWitness [] 0 0 1 3 = some Ordering.gt := by
  decide

/-- Consequently the public tracked consumer returns the strict pre-Rule-6 decision, with no
Rule-6 pseudo contribution. -/
theorem rule6DistanceFallbackWitness_tracked_strict :
    compareBranchesThroughRule6Tracked? rule6DistanceFallbackWitnessResult
      rule6DistanceFallbackWitness [] 0 0 2 1 3 =
        some { ordering := Ordering.gt, pseudo := false } := by
  decide

/-- The star witness has equal promoted layers: both ligand roots project to the same
all-zero indicator layer. -/
theorem rule6PromotionTieWitness_layers_tied :
    rule6PromotionLayers? rule6PromotionTieWitness 0 0 1 3 =
      some [[([], 0)]] ∧
    rule6PromotionLayers? rule6PromotionTieWitness 0 0 2 3 =
      some [[([], 0)]] := by
  decide

/-- On the star witness the compatibility comparator descends to the distance fallback and
refuses, because the blocked center separates both ligands from the reference. -/
theorem rule6PromotionTieWitness_compat_none :
    compareRule6Promotion? rule6PromotionTieWitness 0 0 3 1 2 = none := by
  decide

/-- The source-profile comparator preserves the tied promoted layers as `some eq` on the same
input. -/
theorem rule6PromotionTieWitness_sourceProfile_tied :
    compareRule6PromotionSourceProfile? rule6PromotionTieWitness 0 0 3 1 2 =
      some Ordering.eq := by
  decide

/-- The public pre-Rule-6 comparison ties on the star witness. -/
theorem rule6PromotionTieWitness_before_tied :
    compareBranchesBeforeRule6Context? rule6PromotionTieWitnessResult
      rule6PromotionTieWitness [] 0 0 1 2 = some Ordering.eq := by
  decide

/-- The public authoritative occurrence comparison is absent at the test fuel. -/
theorem rule6PromotionTieWitness_occurrence_none :
    compareOccurrenceBranchesThroughRule6? rule6PromotionTieWitness 0 0 3 1 2 = none := by
  decide

/-- The live tracked consumer therefore selects the projected comparison.  Since the
compatibility promotion comparator refuses on the star, the consumer returns `none`; this is
an actual public call that reaches the projected fallback call site. -/
theorem rule6PromotionTieWitness_tracked_none :
    compareBranchesThroughRule6Tracked? rule6PromotionTieWitnessResult
      rule6PromotionTieWitness [] 0 0 3 1 2 = none := by
  decide

/-- Symmetric fifteen-atom witness.

Center `0` carries two constitutionally equivalent ligand environments `1,2` and `3,9`,
where the automorphism `(1 3)(2 9)(4 10)(5 11)(6 12)(7 13)(8 14)` swaps the two halves and
fixes the center.  The reference ligand is `2`.  Both promoted branch hierarchies are
unavailable because each half contains the same anionic four-membered mancude component, so
`compareRule6Promotion?` falls back to graph distance, and blocking the center atom `1` reaches
`2` in four bonds while atom `3` cannot reach `2` at all.  This is a strict helper-level
distance outcome.  It is **not** a public selection: the public pre-Rule-6 comparison is
`none` on the unsupported anionic halves, so the tracked wrapper refuses.

The historical declaration name `rule6PublicFallbackWitness` is retained for registry
continuity.  It does not certify a selected public fallback. -/
def rule6PublicFallbackWitness : RawMolecule where
  atoms :=
    [ { AtomSpec.aliphatic Element.C with
        tetrahedral? := some TetrahedralInputParity.clockwise },  -- 0 center
      AtomSpec.aliphatic Element.C,                                -- 1 left ligand
      AtomSpec.aliphatic Element.C,                                -- 2 reference ligand
      AtomSpec.aliphatic Element.C,                                -- 3 right ligand
      AtomSpec.aliphatic Element.C,                                -- 4 ring A
      AtomSpec.aliphatic Element.C,                                -- 5 ring A
      { AtomSpec.aliphatic Element.C with charge := -1 },          -- 6 ring A
      { AtomSpec.aliphatic Element.C with charge := -1 },          -- 7 ring A
      AtomSpec.aliphatic Element.H,                                -- 8 on 7
      AtomSpec.aliphatic Element.C,                                -- 9 symmetric ligand
      AtomSpec.aliphatic Element.C,                                -- 10 ring B
      AtomSpec.aliphatic Element.C,                                -- 11 ring B
      { AtomSpec.aliphatic Element.C with charge := -1 },          -- 12 ring B
      { AtomSpec.aliphatic Element.C with charge := -1 },          -- 13 ring B
      AtomSpec.aliphatic Element.H ]                               -- 14 on 13
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single },
      { source := 0, target := 2, kind := ParsedBondKind.single },
      { source := 0, target := 3, kind := ParsedBondKind.single },
      { source := 0, target := 9, kind := ParsedBondKind.single },
      { source := 1, target := 4, kind := ParsedBondKind.single },
      { source := 4, target := 5, kind := ParsedBondKind.double },
      { source := 5, target := 6, kind := ParsedBondKind.single },
      { source := 6, target := 7, kind := ParsedBondKind.single },
      { source := 7, target := 4, kind := ParsedBondKind.single },
      { source := 6, target := 2, kind := ParsedBondKind.single },
      { source := 7, target := 8, kind := ParsedBondKind.single },
      { source := 3, target := 10, kind := ParsedBondKind.single },
      { source := 10, target := 11, kind := ParsedBondKind.double },
      { source := 11, target := 12, kind := ParsedBondKind.single },
      { source := 12, target := 13, kind := ParsedBondKind.single },
      { source := 13, target := 10, kind := ParsedBondKind.single },
      { source := 12, target := 9, kind := ParsedBondKind.single },
      { source := 13, target := 14, kind := ParsedBondKind.single } ]

/-- Normalized public result bundle for the symmetric fifteen-atom witness. -/
def rule6PublicFallbackWitnessResult : ChemistryNormalizationResult :=
  normalizeRawMolecule rule6PublicFallbackWitness

/-- The exact constitution-automorphism search certifies the intended swap: the center is
fixed and ligand roots `1` and `3` are exchanged (this witness maps `2` to `9` as well). -/
theorem rule6PublicFallbackWitness_automorphism :
    rule6PublicFallbackWitness.hasConstitutionAutomorphismSwapping 0 1 3 = true := by
  decide

/-- The public pre-Rule-6 comparison is absent on the unsupported anionic halves.  It is not a
pre-Rule-6 tie, so the tracked consumer cannot select the Rule-6 fallback. -/
theorem rule6PublicFallbackWitness_before_none :
    compareBranchesBeforeRule6Context? rule6PublicFallbackWitnessResult
      rule6PublicFallbackWitness [] 0 0 1 3 = none := by
  decide

/-- Both promoted hierarchies are unavailable on the symmetric witness. -/
theorem rule6PublicFallbackWitness_layers_left_unavailable :
    rule6PromotionLayers? rule6PublicFallbackWitness 0 0 1 2 = none := by
  decide

theorem rule6PublicFallbackWitness_layers_right_unavailable :
    rule6PromotionLayers? rule6PublicFallbackWitness 0 0 3 2 = none := by
  decide

/-- The compatibility promotion comparator nevertheless produces a strict graph-distance order
on the symmetric witness: the left branch reaches the reference in four bonds, the right branch
cannot reach it at all. -/
theorem rule6PublicFallbackWitness_compat_strict :
    compareRule6Promotion? rule6PublicFallbackWitness 0 0 2 1 3 = some Ordering.gt := by
  decide

/-- The source-profile comparator refuses the symmetric witness as well: the promoted
hierarchy is unavailable on both branches. -/
theorem rule6PublicFallbackWitness_sourceProfile_none :
    compareRule6PromotionSourceProfile? rule6PublicFallbackWitness 0 0 2 1 3 = none :=
  compareRule6PromotionSourceProfile?_eq_none_of_unavailable
    rule6PublicFallbackWitness 0 0 2 1 3
    (Or.inl rule6PublicFallbackWitness_layers_left_unavailable)

/-- The public tracked consumer refuses the same pair because the pre-Rule-6 comparison is
absent; the strict helper-level distance result is not selected. -/
theorem rule6PublicFallbackWitness_tracked_none :
    compareBranchesThroughRule6Tracked? rule6PublicFallbackWitnessResult
      rule6PublicFallbackWitness [] 0 0 2 1 3 = none := by
  decide

/-! ## Admission facts for the witnesses

These kernel-checked facts establish that the witnesses are actual admitted operational
inputs under the repository's executable admission contract (structural admission, exact
written-neighbour view, valence table, Rule-2 mass data).  They do not assert any additional
chemical-suitability property. -/

/-- The ten-atom witness passes the executable structural admission check. -/
theorem rule6DistanceFallbackWitness_admissible :
    rule6DistanceFallbackWitness.admissible? = true := by
  decide

/-- The ten-atom witness passes the executable valence-table check. -/
theorem rule6DistanceFallbackWitness_valenceOK :
    rule6DistanceFallbackWitness.valenceOK? = true := by
  decide

/-- The center of the ten-atom witness carries exactly four ligands. -/
theorem rule6DistanceFallbackWitness_four_ligands :
    (rule6DistanceFallbackWitness.ligandsWithLonePair 0).length = 4 := by
  decide

/-- The ten-atom witness is admitted by the full executable certification pipeline. -/
theorem rule6DistanceFallbackWitness_certified :
    rule6DistanceFallbackWitnessResult.certify?.isSome = true := by
  decide

/-- The star witness is admitted by the full executable certification pipeline. -/
theorem rule6PromotionTieWitness_certified :
    rule6PromotionTieWitnessResult.certify?.isSome = true := by
  decide

/-- The fifteen-atom symmetric witness is admitted by the full executable certification
pipeline and its center carries exactly four ligands. -/
theorem rule6PublicFallbackWitness_certified :
    rule6PublicFallbackWitnessResult.certify?.isSome = true := by
  decide

theorem rule6PublicFallbackWitness_four_ligands :
    (rule6PublicFallbackWitness.ligandsWithLonePair 0).length = 4 := by
  decide

-- Kernel-authority guards: none of these results depends on `sorryAx`, compiler trust, or a
-- project axiom.
assert_kernel_only compareOccurrenceBranchesThroughRule6AtAuthoritative?_eq_none_of_prior_eq_none
assert_kernel_only compareOccurrenceRule6Authoritative_succ_eq_none_of_next_none
assert_kernel_only compareOccurrenceRule6Authoritative_zero_eq_none_of_next_ne_nil
assert_kernel_only compareOccurrenceBranchesThroughRule6FullyAuthoritative?_eq_none_of_aux_none
assert_kernel_only compareOccurrenceBranchesThroughRule6?_eq_none_of_aux_none
assert_kernel_only compareBranchesThroughRule6Tracked?_factorization
assert_kernel_only compareBranchesThroughRule6Tracked?_eq_projected_of_occurrence_none
assert_kernel_only compareBranchesThroughRule6Tracked?_eq_occurrence_of_occurrence_strict
assert_kernel_only compareBranchesThroughRule6Tracked?_eq_projected_of_occurrence_tied
assert_kernel_only compareBranchesThroughRule6Tracked?_eq_fallback_of_before_tied_of_occurrence_none
assert_kernel_only compareBranchesThroughRule6Tracked?_eq_fallback_of_before_tied_of_occurrence_tied
assert_kernel_only compareBranchesThroughRule6Tracked?_eq_none_of_before_none_of_occurrence_none
assert_kernel_only compareRule6PromotionSourceProfile?_eq_none_of_unavailable
assert_kernel_only compareRule6PromotionSourceProfile?_eq_some_eq_of_tied
assert_kernel_only compareRule6Promotion?_eq_some_of_sourceProfile_some_strict
assert_kernel_only compareRule6Promotion?_eq_sourceProfile_of_layers_ne_eq
assert_kernel_only compareRule6Promotion?_eq_distance_of_left_unavailable
assert_kernel_only compareRule6Promotion?_eq_distance_of_right_unavailable
assert_kernel_only compareRule6Promotion?_eq_distance_of_layers_tied
assert_kernel_only rule6DistanceComparison?_eq_some_eq_of_equal_some
assert_kernel_only rule6DistanceFallbackWitness_layers_left_unavailable
assert_kernel_only rule6DistanceFallbackWitness_layers_right_available
assert_kernel_only rule6DistanceFallbackWitness_distance_left
assert_kernel_only rule6DistanceFallbackWitness_distance_right
assert_kernel_only rule6DistanceFallbackWitness_compat_strict
assert_kernel_only rule6DistanceFallbackWitness_sourceProfile_none
assert_kernel_only rule6DistanceFallbackWitness_before_strict
assert_kernel_only rule6DistanceFallbackWitness_tracked_strict
assert_kernel_only rule6PromotionTieWitness_layers_tied
assert_kernel_only rule6PromotionTieWitness_compat_none
assert_kernel_only rule6PromotionTieWitness_sourceProfile_tied
assert_kernel_only rule6PromotionTieWitness_before_tied
assert_kernel_only rule6PromotionTieWitness_occurrence_none
assert_kernel_only rule6PromotionTieWitness_tracked_none
assert_kernel_only rule6PublicFallbackWitness_automorphism
assert_kernel_only rule6PublicFallbackWitness_before_none
assert_kernel_only rule6PublicFallbackWitness_layers_left_unavailable
assert_kernel_only rule6PublicFallbackWitness_layers_right_unavailable
assert_kernel_only rule6PublicFallbackWitness_compat_strict
assert_kernel_only rule6PublicFallbackWitness_sourceProfile_none
assert_kernel_only rule6PublicFallbackWitness_tracked_none
assert_kernel_only rule6DistanceFallbackWitness_admissible
assert_kernel_only rule6DistanceFallbackWitness_valenceOK
assert_kernel_only rule6DistanceFallbackWitness_four_ligands
assert_kernel_only rule6DistanceFallbackWitness_certified
assert_kernel_only rule6PromotionTieWitness_certified
assert_kernel_only rule6PublicFallbackWitness_certified
assert_kernel_only rule6PublicFallbackWitness_four_ligands

end OneCenter
end TetraStereo
