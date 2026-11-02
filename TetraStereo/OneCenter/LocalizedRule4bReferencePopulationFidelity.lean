import TetraStereo.KernelOnly
import TetraStereo.OneCenter.LocalizedRule4aRankPopulation
import TetraStereo.OneCenter.LocalizedRule4aRankedProjection
import TetraStereo.OneCenter.LocalizedRule4bReferenceAgreement
import TetraStereo.OneCenter.LocalizedRule45DeclarativeAgreement

set_option autoImplicit false

/-!
# Rule-4b reference-population fidelity

## Chemical obligation

P-92.5.2.1 selects the Rule-4b reference descriptor(s) of a ligand from its highest-ranked chiral
nodes: (a) the descriptor at the highest-rank node corresponding to a chiral unit; (b) the
descriptor that occurs most often among the equivalent highest-rank nodes; (c) both `R` and `S`
when the two occur equally often.  Criterion (c)(i) then prefers one reference over two, and
(c)(ii) pairs the chosen reference(s) with the ligand descriptors while respecting connectivity
and hierarchy in the digraph.

The executable selector `localizedRule4bReferencesFromRankedLabels` implements exactly this
population rule on the recursively merged, hierarchy-rank-addressed `rankedLabels`.  The
comparison-visible cumulative observable does **not** determine that field: independent
declarative derivations of one cursor may order comparator-tied children differently, and those
different tie orders can in principle expose different first-rank `R`/`S` populations.

Hanson's 2018 author preprint proposes a distinct operational refinement for Rule 4b (a two-stage
re-ranking and four reference readings, two per ligand, scored jointly).  This module makes **no
claim** about that proposed algorithm and does not replace the existing reference-dependent
reading order: the two-reference / maximum-two-readings representation and its sorting are
preserved verbatim.  The result below concerns only the P-92.5.2.1(a)--(c) reference selection
over the existing `rankedLabels`.

## What is proved

`LocalizedRule4bReferenceAgreement` reduces equality of selected reference lists to the packaged
invariant `RankedChiralAgrees`, whose second component is exactly the per-depth, per-rank
`List.Perm` agreement of uppercase `R`/`S` populations.  That invariant was *assumed* at the single
remaining interface:

```
declarative compound Rules-4a--5 keys + referencesAgree : left.references = right.references
  -> comparison transport
```

This module discharges the assumption from the actual derivations:

* `declarative_rule4a_rankedLabelProjection_eq` — same-cursor derivations have equal Rule-4a
  projected `rankedLabels` (invariant (A)).
* `declarative_rule4a_rankedChiralPopulation_perm` — the same derivations have `List.Perm`-related
  uppercase descriptor populations at every sphere depth and hierarchy rank path (invariant (B)).
* `declarative_rule4a_rankedChiralAgrees` — the packaged `RankedChiralAgrees` for the actual
  `rankedLabels` fields.
* `declarative_rule4a_referencesFromRankedLabels_eq`, `declarative_compoundRule4bc_...`,
  `referenceListAgreement_of_declarative` — equality of the selected P-92.5.2.1 reference lists, and
  therefore of the recorded `references` fields, for compound Rules-4b/4c and Rules-4a--5 keys.
* The unconditional comparator consumers: the compound Rules-4b/4c comparator and the
  through-Rule-5 comparator, including the occurrence-level comparison record, its decisive-rule
  field and its pseudoasymmetric flag, are transported without a `referencesAgree` hypothesis.

## Proof structure

Both invariant theorems consume the *actual* sorted tied-child blocks.  The population invariant
`declarative_rule4a_rankedLabels_population_perm` (from `LocalizedRule4aRankPopulation`) inducts on
the fuel and the two derivation trees, matches terminal labels through the dependency view, matches
branch children through the functional physical frame and the induction hypothesis, transports the
left descending representative to the right original child list by `List.perm_comp_forall₂`, proves
the aligned middle list descending from the shared observable, and finishes with the two generic
`LocalizedRankedPopulationMerge` transports.  The projection invariant
`declarative_rule4a_rankedLabels_projection_eq` (from `LocalizedRule4aRankedProjection`) performs the
same induction and transports the projected rank-addressed merge through
`projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren_eq_of_map_eq`; same-cursor
observable equality is supplied by `declarative_cumulative_key_observable_unique`.

No exact-label equality, no `rankedLabels` equality, no population permutation of the outer
observation layers and no desired comparator output is assumed.  The only premise of every result
below is the two declarative derivations themselves.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The two ranked-label invariants from actual same-cursor derivations -/

/-- **Invariant (A) from actual derivations.**  Two declarative Rule-4a derivations of the same
cursor and fuel have the same Rule-4a projection of `rankedLabels`: the exact `R`/`S` payloads may
differ (including terminal `R`/`S` ties), but the addressed unit-kind priorities agree.

The observable equality is derived from `declarative_cumulative_key_observable_unique`; the
projection transport is `declarative_rule4a_rankedLabels_projection_eq`, whose branch step inverts
the physical child-prefix merge slot by slot over the actual sorted child blocks. -/
theorem declarative_rule4a_rankedLabelProjection_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor right) :
    rankedLabelProjection left.rankedLabels = rankedLabelProjection right.rankedLabels := by
  have observableEq :=
    input.declarative_cumulative_key_observable_unique .rule4a target view fuel cursor
      left right leftDerived rightDerived
  simpa only [rankedLabelProjection] using
    input.declarative_rule4a_rankedLabels_projection_eq target view fuel cursor cursor
      left right leftDerived rightDerived observableEq

/-- **Invariant (B) from actual derivations.**  At every sphere depth and hierarchy rank path, two
declarative Rule-4a derivations of the same cursor and fuel carry the same multiset (up to
`List.Perm`) of uppercase `R`/`S` descriptors.  Multiplicity is retained, as P-92.5.2.1(b)
requires.

This is the previously assumed premise: the proof is
`declarative_rule4a_rankedLabels_population_perm`, an induction over the actual sorted equivalent
tied-child blocks whose branch step uses the shared observable, the generic merge transport and
the comparator congruence of `LocalizedRankedPopulationMerge`. -/
theorem declarative_rule4a_rankedChiralPopulation_perm
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor right) :
    ∀ (depth : Nat) (rank : List Nat),
      (localizedChiralDescriptorsAtRank rank (left.rankedLabels.getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank (right.rankedLabels.getD depth [])) :=
  input.declarative_rule4a_rankedLabels_population_perm target view fuel cursor
    leftDerived rightDerived

/-- **Packaged ranked-chiral agreement.**  Actual same-cursor Rule-4a derivations satisfy
`RankedChiralAgrees` on their `rankedLabels` fields.  This is the hypothesis that
`localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees'` had to assume at the generic
core; it is now derived from the two declarative derivations. -/
theorem declarative_rule4a_rankedChiralAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor right) :
    RankedChiralAgrees left.rankedLabels right.rankedLabels :=
  ⟨declarative_rule4a_rankedLabelProjection_eq input target view cursor
      leftDerived rightDerived,
    declarative_rule4a_rankedChiralPopulation_perm input target view cursor
      leftDerived rightDerived⟩

/-- The first-chiral-rank population (the population P-92.5.2.1(b)--(c) actually counts) is
`List.Perm`-related for actual same-cursor derivations.  This unpacks the invariant at the exact
population consumed by the selector. -/
theorem declarative_rule4a_firstChiralRankPopulation_perm
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor right) :
    (localizedFirstChiralRankPopulation left.rankedLabels).Perm
      (localizedFirstChiralRankPopulation right.rankedLabels) := by
  have agrees :=
    declarative_rule4a_rankedChiralAgrees input target view cursor leftDerived rightDerived
  exact localizedFirstChiralRankPopulation_perm_of_rankedChiralAgrees agrees.1 agrees.2

/-- **Selected-reference equality from actual derivations.**  The executable P-92.5.2.1 selector
returns the same list for two declarative Rule-4a derivations of the same cursor and fuel.  Only
`R`/`S` counts of the first-ranked population are read, so `RankedChiralAgrees` suffices. -/
theorem declarative_rule4a_referencesFromRankedLabels_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor right) :
    localizedRule4bReferencesFromRankedLabels left.rankedLabels =
      localizedRule4bReferencesFromRankedLabels right.rankedLabels :=
  localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees'
    (declarative_rule4a_rankedChiralAgrees input target view cursor leftDerived rightDerived)

/-! ## Compound Rules-4b/4c keys

The compound key stores the independently derived Rule-4a key and a reference list that the
declarative meaning ties to that same key's `rankedLabels`.  The derivations below therefore only
need the Rule-4a components `leftDerived.1` and `rightDerived.1`. -/

/-- Actual same-cursor compound Rules-4b/4c derivations satisfy `RankedChiralAgrees` on their stored
Rule-4a `rankedLabels`. -/
theorem declarative_compoundRule4bc_rankedChiralAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right) :
    RankedChiralAgrees left.rule4aKey.rankedLabels right.rule4aKey.rankedLabels :=
  declarative_rule4a_rankedChiralAgrees input target view cursor
    leftDerived.1 rightDerived.1

/-- The executable selector agrees on the two stored Rule-4a keys of actual same-cursor compound
Rules-4b/4c derivations. -/
theorem declarative_compoundRule4bc_referenceListAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right) :
    localizedRule4bReferencesFromRankedLabels left.rule4aKey.rankedLabels =
      localizedRule4bReferencesFromRankedLabels right.rule4aKey.rankedLabels :=
  declarative_rule4a_referencesFromRankedLabels_eq input target view cursor
    leftDerived.1 rightDerived.1

/-- **Selected `references` fields agree** for actual same-cursor compound Rules-4b/4c derivations.
Each derivation's declarative selection identifies its recorded `references` with the executable
selector on its own Rule-4a `rankedLabels`; the two selectors agree by
`declarative_compoundRule4bc_referenceListAgreement`.  No exact label equality is used. -/
theorem references_eq_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right) :
    left.references = right.references := by
  have leftSelector : localizedRule4bReferencesFromRankedLabels
      left.rule4aKey.rankedLabels = left.references :=
    (localizedRule4bReferencesFromRankedLabels_eq_iff
      left.rule4aKey.rankedLabels left.references).mpr leftDerived.2.1
  have rightSelector : localizedRule4bReferencesFromRankedLabels
      right.rule4aKey.rankedLabels = right.references :=
    (localizedRule4bReferencesFromRankedLabels_eq_iff
      right.rule4aKey.rankedLabels right.references).mpr rightDerived.2.1
  rw [← leftSelector, ← rightSelector]
  exact declarative_compoundRule4bc_referenceListAgreement input target view cursor
    left right leftDerived rightDerived

/-! ## Through-Rule-5 keys -/

/-- Actual same-cursor through-Rule-5 derivations satisfy `RankedChiralAgrees` on the Rule-4a
`rankedLabels` stored in their prior compound key. -/
theorem declarative_compoundRule45_rankedChiralAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    RankedChiralAgrees left.prior.rule4aKey.rankedLabels
      right.prior.rule4aKey.rankedLabels :=
  declarative_compoundRule4bc_rankedChiralAgrees input target view cursor
    left.prior right.prior leftDerived.1 rightDerived.1

/-- **The explicit lower-layer reference premise, now discharged.**  Two actual same-cursor
declarative Rules-4a--5 derivations select the same P-92.5.2.1 reference list.  This is the exact
`LocalizedRerootCompoundRule45ReferenceListAgreement` shape consumed by
`compareLocalizedRerootCompoundThroughRule5_congr_of_referenceListAgreement`. -/
theorem referenceListAgreement_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    LocalizedRerootCompoundRule45ReferenceListAgreement input left right := by
  show localizedRule4bReferencesFromRankedLabels left.prior.rule4aKey.rankedLabels =
    localizedRule4bReferencesFromRankedLabels right.prior.rule4aKey.rankedLabels
  exact declarative_compoundRule4bc_referenceListAgreement input target view cursor
    left.prior right.prior leftDerived.1 rightDerived.1

/-- The recorded `references` fields of actual same-cursor through-Rule-5 derivations agree.  This
removes the `referencesAgree` hypothesis from every comparator consumer below. -/
theorem references_eq_of_declarative_rule45
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    left.prior.references = right.prior.references :=
  input.references_eq_of_referenceListAgreement target view cursor left right
    leftDerived rightDerived
    (referenceListAgreement_of_declarative input target view cursor
      left right leftDerived rightDerived)

/-! ## Comparator consumers without a `referencesAgree` hypothesis

Every theorem below is the corresponding existing conditional consumer instantiated at
`references_eq_of_declarative` / `references_eq_of_declarative_rule45`.  The comparator itself is
not redefined; in particular the Rule-4a-first precedence gate and the retained normative
reference/reading order (including the two-reference case) are untouched. -/

/-- Compound Rules-4b/4c keys from actual same-cursor derivations are interchangeable on the left of
the actual compound comparator, with no reference-list premise. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_congr_left_of_declarative_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right) :
    input.compareLocalizedRerootCompoundRule4bcKeys left other =
      input.compareLocalizedRerootCompoundRule4bcKeys right other :=
  input.compareLocalizedRerootCompoundRule4bcKeys_congr_left_of_declarative
    target view cursor left right other leftDerived rightDerived
    (references_eq_of_declarative input target view cursor left right
      leftDerived rightDerived)

/-- Compound Rules-4b/4c keys from actual same-cursor derivations are interchangeable on the right
of the actual compound comparator, with no reference-list premise. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_congr_right_of_declarative_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule4bcKey)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor right) :
    input.compareLocalizedRerootCompoundRule4bcKeys other left =
      input.compareLocalizedRerootCompoundRule4bcKeys other right :=
  input.compareLocalizedRerootCompoundRule4bcKeys_congr_right_of_declarative
    target view cursor left right other leftDerived rightDerived
    (references_eq_of_declarative input target view cursor left right
      leftDerived rightDerived)

/-- **Two-sided through-Rule-5 interchangeability without `referencesAgree`.**  Actual same-cursor
declarative Rules-4a--5 keys have identical comparison behaviour in both argument positions against
every third key.  The complete comparison record is preserved, including the ordering and the
pseudoasymmetric flag. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_of_declarative_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    input.compareLocalizedRerootCompoundThroughRule5 left other =
        input.compareLocalizedRerootCompoundThroughRule5 right other ∧
      input.compareLocalizedRerootCompoundThroughRule5 other left =
        input.compareLocalizedRerootCompoundThroughRule5 other right :=
  input.compareLocalizedRerootCompoundThroughRule5_congr_of_declarative
    target view cursor left right other leftDerived rightDerived
    (references_eq_of_declarative_rule45 input target view cursor left right
      leftDerived rightDerived)

/-- Left substitution form of
`compareLocalizedRerootCompoundThroughRule5_congr_of_declarative_keys`. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_left_of_declarative_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    input.compareLocalizedRerootCompoundThroughRule5 left other =
      input.compareLocalizedRerootCompoundThroughRule5 right other :=
  (compareLocalizedRerootCompoundThroughRule5_congr_of_declarative_keys input
    target view cursor left right other leftDerived rightDerived).1

/-- Right substitution form of
`compareLocalizedRerootCompoundThroughRule5_congr_of_declarative_keys`. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_right_of_declarative_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    input.compareLocalizedRerootCompoundThroughRule5 other left =
      input.compareLocalizedRerootCompoundThroughRule5 other right :=
  (compareLocalizedRerootCompoundThroughRule5_congr_of_declarative_keys input
    target view cursor left right other leftDerived rightDerived).2

/-- The occurrence-level comparison record is unchanged on the left substitution, with no
reference-list premise. -/
theorem compareLocalizedOccurrenceRule45ComparisonRecord_congr_left_of_declarative_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 left other) =
      localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 right other) :=
  input.compareLocalizedOccurrenceRule45ComparisonRecord_congr_left
    target view cursor left right other leftDerived rightDerived
    (references_eq_of_declarative_rule45 input target view cursor left right
      leftDerived rightDerived)

/-- The decisive-rule field of the occurrence comparison record is unchanged on the left
substitution, with no reference-list premise. -/
theorem compareLocalizedOccurrenceRule45ComparisonRecord_decisiveRule?_eq_of_declarative_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 left other)).decisiveRule? =
      (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 right other)).decisiveRule? :=
  input.compareLocalizedOccurrenceRule45ComparisonRecord_decisiveRule?_eq
    target view cursor left right other leftDerived rightDerived
    (references_eq_of_declarative_rule45 input target view cursor left right
      leftDerived rightDerived)

/-- The pseudoasymmetric flag of the occurrence comparison record is unchanged on the left
substitution, with no reference-list premise. -/
theorem compareLocalizedOccurrenceRule45ComparisonRecord_pseudo_eq_of_declarative_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right other : input.LocalizedRerootCompoundRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor right) :
    (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 left other)).pseudo =
      (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 right other)).pseudo :=
  input.compareLocalizedOccurrenceRule45ComparisonRecord_pseudo_eq
    target view cursor left right other leftDerived rightDerived
    (references_eq_of_declarative_rule45 input target view cursor left right
      leftDerived rightDerived)

/-- **Compiled/derived interchangeability without `referencesAgree`.**  A successfully compiled
through-Rule-5 key is interchangeable with any independent derivation at the same cursor.  Compiler
soundness supplies both derivations; no reference-list premise is required. -/
theorem compareLocalizedRerootCompoundThroughRule5_congr_of_compiled_keys
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (compiled derived other : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel cursor = some compiled)
    (derivedMeaning : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor derived) :
    input.compareLocalizedRerootCompoundThroughRule5 compiled other =
        input.compareLocalizedRerootCompoundThroughRule5 derived other ∧
      input.compareLocalizedRerootCompoundThroughRule5 other compiled =
        input.compareLocalizedRerootCompoundThroughRule5 other derived :=
  compareLocalizedRerootCompoundThroughRule5_congr_of_declarative_keys input
    target view cursor compiled derived other
    (input.buildLocalizedRerootCompoundRule45Key?_sound target view fuel cursor
      compiled computed)
    derivedMeaning

/-- **The unconditional comparison-agreement form.**  At every target, dependency view, fuel and
cursor, actual same-cursor declarative Rules-4a--5 keys have identical through-Rule-5 comparison
behaviour in both argument positions.  This is the `LocalizedRerootCompoundRule45ComparisonAgreement`
shape with the reference-list premise discharged, stated explicitly here so that the present module
does not depend on the universal-descriptor module that defines that predicate. -/
theorem compoundRule45_comparisonAgreement_of_rankedReferencePopulation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (left right : input.LocalizedRerootCompoundRule45Key),
      input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel cursor left →
        input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel cursor right →
          ∀ other : input.LocalizedRerootCompoundRule45Key,
            input.compareLocalizedRerootCompoundThroughRule5 left other =
                input.compareLocalizedRerootCompoundThroughRule5 right other ∧
              input.compareLocalizedRerootCompoundThroughRule5 other left =
                input.compareLocalizedRerootCompoundThroughRule5 other right := by
  intro cursor left right leftDerived rightDerived other
  exact compareLocalizedRerootCompoundThroughRule5_congr_of_declarative_keys input
    target view cursor left right other leftDerived rightDerived

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_rule4a_rankedLabelProjection_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_rule4a_rankedChiralPopulation_perm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_rule4a_rankedChiralAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_rule4a_firstChiralRankPopulation_perm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_rule4a_referencesFromRankedLabels_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_compoundRule4bc_rankedChiralAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_compoundRule4bc_referenceListAgreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.references_eq_of_declarative
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_compoundRule45_rankedChiralAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceListAgreement_of_declarative
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.references_eq_of_declarative_rule45
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys_congr_left_of_declarative_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys_congr_right_of_declarative_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_congr_of_declarative_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_congr_left_of_declarative_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_congr_right_of_declarative_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule45ComparisonRecord_congr_left_of_declarative_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule45ComparisonRecord_decisiveRule?_eq_of_declarative_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule45ComparisonRecord_pseudo_eq_of_declarative_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_congr_of_compiled_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundRule45_comparisonAgreement_of_rankedReferencePopulation
