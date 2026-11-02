/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.OrganicStereoHeterogeneousSamples
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Qualitative binary mixture classes and their quantitative realizations

`P93GeneralConfiguration.QualitativeBinaryMixture` records only the information that the
authority actually prints for a two-species mixture: the two ordered species and whether the
mixture is `equimolar` or `nonEquimolar`.  It deliberately stores **no** numerical mole fraction.
Inventing a fraction as if it were authority data would make the formal record stronger than the
source.

This module states the precise quantitative meaning of that qualitative record.  For a qualitative
mixture `q` and an actual `MolarComposition.Composition (Fin 2) Species`, `Admissible q c` says:

* the two ordered components are exactly `q.first` and `q.second` (no third component, and no
  identification of the two components even when the species happen to be equal);
* the normalized amounts are `f` and `1 - f` for the first fraction `f = c.fraction 0`, with
  `0 < f < 1`;
* `q.composition = equimolar` holds exactly when `f = 1/2`.

The set `admissible q` is defined from the qualitative record and a whole composition only; no
chosen fraction is part of the data.  Its projection onto `c.fraction 0` is proved to be exactly
`compositionClassFractions q.composition`, so:

* an equimolar class admits exactly the fraction `1/2`;
* a non-equimolar class admits every **real** `f` with `0 < f < 1` and `f ≠ 1/2` (not merely the
  rationals);
* the class is recoverable from the projection, and the two class projections are disjoint;
* `q.first` and `q.second` (including the source order) are recoverable from any nonempty set of
  whole admissible compositions, with no injectivity, decidable equality or distinctness
  assumption on `Species`.

The witnesses `1/2` and `1/3` occur only in nonemptiness proofs.  They are not stored in the
qualitative mixture and are not claimed to be authority-sourced values.

## Actual samples

The final section integrates the realization set with the approved concrete
`OrganicStereoHeterogeneousSamples` codec.  Two actual `WholeState` records on the concrete
two-atom shape are used as the two named molecular states; each constituent's possibility set is
the singleton containing its own whole state.  The existing `encodeSet`/`decodeSet` round trip is
applied to whole samples, so distinct molecular states and the per-constituent amount correlation
are retained.  The two states are genuinely distinct, and their distinctness is proved rather than
assumed.  No physical enantiomer relationship is inferred from the descriptor policy: the two
states are simply distinct whole records, and no racemate or mirror claim is made.
-/

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoQualitativeMixtureRealization

noncomputable section

open scoped BigOperators

open BlueBookP93.GeneralConfiguration
open MolarComposition

variable {Species : Type*}

/-! ## Admissible quantitative realizations -/

/-- A quantitative realization of a qualitative binary mixture.

The two components are the ordered `Fin 2` pair.  `species_first` and `species_second` require
exactly `q.first` and `q.second`, and the normalized first fraction `c.fraction 0` is the real
amount fraction `f`; the second normalized fraction is then `1 - f` (proved below for every
`Fin 2` composition).  The class field is a genuine equivalence: equimolarity means `f = 1/2`,
and non-equimolarity means `f ≠ 1/2`. -/
structure Admissible (q : QualitativeBinaryMixture Species)
    (c : MolarComposition.Composition (Fin 2) Species) : Prop where
  /-- The first ordered component is the source first species. -/
  species_first : c.species (0 : Fin 2) = q.first
  /-- The second ordered component is the source second species. -/
  species_second : c.species (1 : Fin 2) = q.second
  /-- The first normalized amount is strictly positive. -/
  fraction_pos : 0 < c.fraction (0 : Fin 2)
  /-- The first normalized amount is strictly below one. -/
  fraction_lt_one : c.fraction (0 : Fin 2) < 1
  /-- The qualitative class is exactly the comparison of the first fraction with one half. -/
  class_iff : q.composition = BinaryCompositionClass.equimolar ↔
    c.fraction (0 : Fin 2) = 1 / 2

/-- The independent set of admissible quantitative realizations of a qualitative record.

No fraction is stored: a composition either is an admissible realization or is not, and the
possible first fractions are recovered as a projection below. -/
def admissible (q : QualitativeBinaryMixture Species) :
    Set (MolarComposition.Composition (Fin 2) Species) :=
  {c | Admissible q c}

/-- The admissible first fractions of each qualitative composition class.

For `equimolar` this is exactly the singleton `{1/2}`.  For `nonEquimolar` it is the whole open
real interval `(0,1)` with `1/2` removed; no rational restriction is imposed. -/
def compositionClassFractions : BinaryCompositionClass → Set ℝ
  | BinaryCompositionClass.equimolar => {f : ℝ | f = 1 / 2}
  | BinaryCompositionClass.nonEquimolar => {f : ℝ | 0 < f ∧ f < 1 ∧ f ≠ 1 / 2}

/-- The first-fraction projection of the admissible realization set. -/
def firstFractionProjection (q : QualitativeBinaryMixture Species) : Set ℝ :=
  {f | ∃ c : MolarComposition.Composition (Fin 2) Species, Admissible q c ∧
    c.fraction (0 : Fin 2) = f}

/-- The second-fraction projection of the admissible realization set. -/
def secondFractionProjection (q : QualitativeBinaryMixture Species) : Set ℝ :=
  {g | ∃ c : MolarComposition.Composition (Fin 2) Species, Admissible q c ∧
    c.fraction (1 : Fin 2) = g}

/-! ## The canonical two-component composition at a real fraction -/

/-- The composition with ordered species `q.first`, `q.second` and real amounts `f` and `1 - f`.

This is the canonical realization at a chosen real fraction.  The definition itself does not
assert that `f` is authority data; `realizationOfFraction_admissible` records exactly when it is
admissible for the qualitative record. -/
def realizationOfFraction (q : QualitativeBinaryMixture Species) (f : ℝ)
    (hf0 : 0 < f) (hf1 : f < 1) :
    MolarComposition.Composition (Fin 2) Species :=
  MolarComposition.Composition.binary q.first q.second f (1 - f)
    (le_of_lt hf0) (by linarith) (by linarith)

@[simp] theorem realizationOfFraction_species_zero (q : QualitativeBinaryMixture Species)
    (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (realizationOfFraction q f hf0 hf1).species (0 : Fin 2) = q.first := by
  unfold realizationOfFraction
  exact MolarComposition.Composition.binary_species_zero q.first q.second f (1 - f) _ _ _

@[simp] theorem realizationOfFraction_species_one (q : QualitativeBinaryMixture Species)
    (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (realizationOfFraction q f hf0 hf1).species (1 : Fin 2) = q.second := by
  unfold realizationOfFraction
  exact MolarComposition.Composition.binary_species_one q.first q.second f (1 - f) _ _ _

@[simp] theorem realizationOfFraction_fraction_zero (q : QualitativeBinaryMixture Species)
    (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (realizationOfFraction q f hf0 hf1).fraction (0 : Fin 2) = f := by
  unfold realizationOfFraction
  rw [MolarComposition.Composition.binary_fraction_zero]
  have hsum : f + (1 - f) = (1 : ℝ) := by ring
  rw [hsum, div_one]

@[simp] theorem realizationOfFraction_fraction_one (q : QualitativeBinaryMixture Species)
    (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (realizationOfFraction q f hf0 hf1).fraction (1 : Fin 2) = 1 - f := by
  unfold realizationOfFraction
  rw [MolarComposition.Composition.binary_fraction_one]
  have hsum : f + (1 - f) = (1 : ℝ) := by ring
  rw [hsum, div_one]

/-- Any `Fin 2` composition normalizes its two amounts as `f` and `1 - f`. -/
theorem second_fraction_eq_one_sub
    (c : MolarComposition.Composition (Fin 2) Species) :
    c.fraction (1 : Fin 2) = 1 - c.fraction (0 : Fin 2) := by
  have h := c.sum_fraction_eq_one
  rw [Fin.sum_univ_two] at h
  linarith

/-- An admissible realization has second normalized amount `1 - f`. -/
theorem admissible_fraction_one {q : QualitativeBinaryMixture Species}
    {c : MolarComposition.Composition (Fin 2) Species} (_hc : Admissible q c) :
    c.fraction (1 : Fin 2) = 1 - c.fraction (0 : Fin 2) :=
  second_fraction_eq_one_sub c

/-- The species map of an admissible composition is exactly the ordered pair of source species.

The value at `0` is forced to `q.first` and the value at `1` to `q.second`; because the index type
is exactly `Fin 2` there is no further component.  No distinctness of the two species is used. -/
theorem admissible_species_eq_orderedPair {q : QualitativeBinaryMixture Species}
    {c : MolarComposition.Composition (Fin 2) Species} (hc : Admissible q c) :
    c.species = MolarComposition.Composition.binarySpecies q.first q.second := by
  funext i
  fin_cases i
  · simpa [MolarComposition.Composition.binarySpecies, Fin.cases_zero] using hc.species_first
  · simpa [MolarComposition.Composition.binarySpecies, Fin.cases_succ] using hc.species_second

/-- The canonical realization is admissible exactly when the chosen real fraction matches the
qualitative class. -/
theorem realizationOfFraction_admissible (q : QualitativeBinaryMixture Species) (f : ℝ)
    (hf0 : 0 < f) (hf1 : f < 1)
    (hclass : q.composition = BinaryCompositionClass.equimolar ↔ f = 1 / 2) :
    Admissible q (realizationOfFraction q f hf0 hf1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact realizationOfFraction_species_zero q f hf0 hf1
  · exact realizationOfFraction_species_one q f hf0 hf1
  · rw [realizationOfFraction_fraction_zero]
    exact hf0
  · rw [realizationOfFraction_fraction_zero]
    exact hf1
  · rw [realizationOfFraction_fraction_zero]
    exact hclass

/-! ## Nonemptiness of both qualitative classes

The witnesses `1/2` and `1/3` appear only here and in projection-witness corollaries.  They are
not added to `QualitativeBinaryMixture`, so the source record never acquires a chosen fraction. -/

/-- Both composition classes have a nonempty admissible realization set. -/
theorem admissible_nonempty (q : QualitativeBinaryMixture Species) :
    (admissible q).Nonempty := by
  cases hclass : q.composition
  · have h0 : (0 : ℝ) < 1 / 2 := by norm_num
    have h1 : (1 / 2 : ℝ) < 1 := by norm_num
    refine ⟨realizationOfFraction q (1 / 2) h0 h1, ?_⟩
    exact realizationOfFraction_admissible q (1 / 2) h0 h1 (by simp [hclass])
  · have h0 : (0 : ℝ) < 1 / 3 := by norm_num
    have h1 : (1 / 3 : ℝ) < 1 := by norm_num
    refine ⟨realizationOfFraction q (1 / 3) h0 h1, ?_⟩
    refine realizationOfFraction_admissible q (1 / 3) h0 h1 ?_
    constructor
    · intro hEq
      exact absurd hEq (by rw [hclass]; decide)
    · intro hf
      exact absurd hf (by norm_num)

/-- The equimolar class is nonempty. -/
theorem admissible_nonempty_equimolar (q : QualitativeBinaryMixture Species)
    (_hclass : q.composition = BinaryCompositionClass.equimolar) :
    (admissible q).Nonempty :=
  admissible_nonempty q

/-- The non-equimolar class is nonempty. -/
theorem admissible_nonempty_nonEquimolar (q : QualitativeBinaryMixture Species)
    (_hclass : q.composition = BinaryCompositionClass.nonEquimolar) :
    (admissible q).Nonempty :=
  admissible_nonempty q

/-! ## The exact fraction projection -/

/-- **Exact fraction projection.**  The first fractions of the admissible realizations are exactly
the fractions admitted by the qualitative class.  In particular the equimolar class gives exactly
`{1/2}`, while the non-equimolar class gives all real `f` with `0 < f < 1` and `f ≠ 1/2`. -/
theorem firstFractionProjection_eq_classFractions (q : QualitativeBinaryMixture Species) :
    firstFractionProjection q = compositionClassFractions q.composition := by
  cases hclass : q.composition
  · ext f
    simp only [firstFractionProjection, compositionClassFractions, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, hf⟩
      have hhalf : c.fraction (0 : Fin 2) = 1 / 2 := hc.class_iff.mp hclass
      rw [← hf]
      exact hhalf
    · intro hf
      have h0 : (0 : ℝ) < 1 / 2 := by norm_num
      have h1 : (1 / 2 : ℝ) < 1 := by norm_num
      refine ⟨realizationOfFraction q (1 / 2) h0 h1, ?_, ?_⟩
      · exact realizationOfFraction_admissible q (1 / 2) h0 h1 (by simp [hclass])
      · rw [realizationOfFraction_fraction_zero]
        exact hf.symm
  · ext f
    simp only [firstFractionProjection, compositionClassFractions, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, hf⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← hf]
        exact hc.fraction_pos
      · rw [← hf]
        exact hc.fraction_lt_one
      · intro hhalf
        have hcHalf : c.fraction (0 : Fin 2) = 1 / 2 := hf.trans hhalf
        have hEq : q.composition = BinaryCompositionClass.equimolar :=
          hc.class_iff.mpr hcHalf
        exact absurd hEq (by rw [hclass]; decide)
    · rintro ⟨hf0, hf1, hfne⟩
      refine ⟨realizationOfFraction q f hf0 hf1, ?_, ?_⟩
      · refine realizationOfFraction_admissible q f hf0 hf1 ?_
        constructor
        · intro hEq
          exact absurd hEq (by rw [hclass]; decide)
        · intro hf
          exact absurd hf hfne
      · exact realizationOfFraction_fraction_zero q f hf0 hf1

/-- The second fractions are exactly the complements `1 - f` of the class fractions. -/
theorem secondFractionProjection_eq (q : QualitativeBinaryMixture Species) :
    secondFractionProjection q =
      {g : ℝ | 1 - g ∈ compositionClassFractions q.composition} := by
  ext g
  simp only [secondFractionProjection, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, hg⟩
    have hmem : c.fraction (0 : Fin 2) ∈ compositionClassFractions q.composition := by
      rw [← firstFractionProjection_eq_classFractions q]
      exact ⟨c, hc, rfl⟩
    have : 1 - g = c.fraction (0 : Fin 2) := by
      rw [← hg, admissible_fraction_one hc]
      ring
    rwa [this]
  · intro hg
    rw [← firstFractionProjection_eq_classFractions q] at hg
    obtain ⟨c, hc, hc0⟩ := hg
    refine ⟨c, hc, ?_⟩
    rw [admissible_fraction_one hc, hc0]
    ring

/-! ## All real fractions, class recovery, and disjointness -/

/-- Every real fraction satisfying the class condition is realized.  This is the explicit
"not rational only" completeness statement. -/
theorem exists_admissible_of_fraction (q : QualitativeBinaryMixture Species) {f : ℝ}
    (hf0 : 0 < f) (hf1 : f < 1)
    (hclass : q.composition = BinaryCompositionClass.equimolar ↔ f = 1 / 2) :
    ∃ c : MolarComposition.Composition (Fin 2) Species,
      Admissible q c ∧ c.fraction (0 : Fin 2) = f :=
  ⟨realizationOfFraction q f hf0 hf1,
    realizationOfFraction_admissible q f hf0 hf1 hclass,
    realizationOfFraction_fraction_zero q f hf0 hf1⟩

/-- For a non-equimolar class, every real `f` in `(0,1)` other than `1/2` is realized. -/
theorem nonEquimolar_all_real_fractions (q : QualitativeBinaryMixture Species)
    (hclass : q.composition = BinaryCompositionClass.nonEquimolar) {f : ℝ}
    (hf0 : 0 < f) (hf1 : f < 1) (hfne : f ≠ 1 / 2) :
    ∃ c : MolarComposition.Composition (Fin 2) Species,
      Admissible q c ∧ c.fraction (0 : Fin 2) = f := by
  refine exists_admissible_of_fraction q hf0 hf1 ?_
  constructor
  · intro hEq
    exact absurd hEq (by rw [hclass]; decide)
  · intro hf
    exact absurd hf hfne

/-- An equimolar class has exactly the fraction `1/2`. -/
theorem equimolar_fraction_eq (q : QualitativeBinaryMixture Species)
    (hclass : q.composition = BinaryCompositionClass.equimolar)
    {c : MolarComposition.Composition (Fin 2) Species} (hc : Admissible q c) :
    c.fraction (0 : Fin 2) = 1 / 2 :=
  hc.class_iff.mp hclass

/-- Membership of `1/2` in the fraction projection is equivalent to equimolarity.  This is the
class-recovery invariant read off from the realization set. -/
theorem equimolar_iff_half_mem_firstFractionProjection
    (q : QualitativeBinaryMixture Species) :
    q.composition = BinaryCompositionClass.equimolar ↔
      (1 / 2 : ℝ) ∈ firstFractionProjection q := by
  constructor
  · intro hclass
    have h0 : (0 : ℝ) < 1 / 2 := by norm_num
    have h1 : (1 / 2 : ℝ) < 1 := by norm_num
    refine ⟨realizationOfFraction q (1 / 2) h0 h1, ?_, ?_⟩
    · exact realizationOfFraction_admissible q (1 / 2) h0 h1 (by simp [hclass])
    · exact realizationOfFraction_fraction_zero q (1 / 2) h0 h1
  · rintro ⟨c, hc, hhalf⟩
    exact hc.class_iff.mpr hhalf

/-- The qualitative composition class is recoverable from the first-fraction projection of the
admissible realization set. -/
theorem composition_eq_of_firstFractionProjection_eq
    (q₁ q₂ : QualitativeBinaryMixture Species)
    (h : firstFractionProjection q₁ = firstFractionProjection q₂) :
    q₁.composition = q₂.composition := by
  have hiff₁ := equimolar_iff_half_mem_firstFractionProjection q₁
  have hiff₂ := equimolar_iff_half_mem_firstFractionProjection q₂
  have hmem : (1 / 2 : ℝ) ∈ firstFractionProjection q₁ ↔
      (1 / 2 : ℝ) ∈ firstFractionProjection q₂ := by
    rw [h]
  have hclass : (q₁.composition = BinaryCompositionClass.equimolar) ↔
      (q₂.composition = BinaryCompositionClass.equimolar) :=
    hiff₁.trans (hmem.trans hiff₂.symm)
  cases h₁ : q₁.composition <;> cases h₂ : q₂.composition
  · rfl
  · exact absurd (hclass.mp h₁) (by rw [h₂]; decide)
  · exact absurd (hclass.mpr h₂) (by rw [h₁]; decide)
  · rfl

/-- The two class fraction sets are disjoint. -/
theorem compositionClassFractions_disjoint :
    Disjoint (compositionClassFractions BinaryCompositionClass.equimolar)
      (compositionClassFractions BinaryCompositionClass.nonEquimolar) := by
  rw [Set.disjoint_left]
  intro f he hn
  exact hn.2.2 he

/-- Their union is the whole open real interval `(0,1)`. -/
theorem compositionClassFractions_union :
    compositionClassFractions BinaryCompositionClass.equimolar ∪
        compositionClassFractions BinaryCompositionClass.nonEquimolar =
      {f : ℝ | 0 < f ∧ f < 1} := by
  ext f
  constructor
  · rintro (hf | hf)
    · rw [hf]
      norm_num
    · exact ⟨hf.1, hf.2.1⟩
  · rintro ⟨hf0, hf1⟩
    by_cases heq : f = 1 / 2
    · exact Or.inl heq
    · exact Or.inr ⟨hf0, hf1, heq⟩

/-! ## Recovery of source order and species from whole compositions -/

/-- Two admissible records sharing one whole composition have the same source first species.
No distinctness or decidable equality on `Species` is used. -/
theorem first_eq_of_admissible_common {q₁ q₂ : QualitativeBinaryMixture Species}
    {c : MolarComposition.Composition (Fin 2) Species}
    (h₁ : Admissible q₁ c) (h₂ : Admissible q₂ c) : q₁.first = q₂.first :=
  h₁.species_first.symm.trans h₂.species_first

/-- Two admissible records sharing one whole composition have the same source second species. -/
theorem second_eq_of_admissible_common {q₁ q₂ : QualitativeBinaryMixture Species}
    {c : MolarComposition.Composition (Fin 2) Species}
    (h₁ : Admissible q₁ c) (h₂ : Admissible q₂ c) : q₁.second = q₂.second :=
  h₁.species_second.symm.trans h₂.species_second

/-- Two admissible records sharing one whole composition have the same qualitative class. -/
theorem class_eq_of_admissible_common {q₁ q₂ : QualitativeBinaryMixture Species}
    {c : MolarComposition.Composition (Fin 2) Species}
    (h₁ : Admissible q₁ c) (h₂ : Admissible q₂ c) :
    q₁.composition = q₂.composition := by
  have hclass : (q₁.composition = BinaryCompositionClass.equimolar) ↔
      (q₂.composition = BinaryCompositionClass.equimolar) :=
    h₁.class_iff.trans h₂.class_iff.symm
  cases hc₁ : q₁.composition <;> cases hc₂ : q₂.composition
  · rfl
  · exact absurd (hclass.mp hc₁) (by rw [hc₂]; decide)
  · exact absurd (hclass.mpr hc₂) (by rw [hc₁]; decide)
  · rfl

/-- **Source recovery from a nonempty whole composition.**  If two qualitative records have the
same nonempty set of admissible realizations, then their first species, second species, source
order, and qualitative class all agree.  In particular no injectivity of `species`, no
`DecidableEq Species`, and no `q.first ≠ q.second` assumption is needed. -/
theorem source_recoverable_of_admissible_eq (q₁ q₂ : QualitativeBinaryMixture Species)
    (h : admissible q₁ = admissible q₂) :
    q₁.first = q₂.first ∧ q₁.second = q₂.second ∧
      q₁.composition = q₂.composition := by
  obtain ⟨c, hc⟩ := admissible_nonempty q₁
  have hc₂ : Admissible q₂ c := by
    have : c ∈ admissible q₂ := by
      rw [← h]
      exact hc
    exact this
  exact ⟨first_eq_of_admissible_common hc hc₂,
    second_eq_of_admissible_common hc hc₂,
    class_eq_of_admissible_common hc hc₂⟩

/-- Admissible realization sets of different qualitative classes are disjoint. -/
theorem admissible_disjoint_of_class_ne {q₁ q₂ : QualitativeBinaryMixture Species}
    (h : q₁.composition ≠ q₂.composition) :
    Disjoint (admissible q₁) (admissible q₂) := by
  rw [Set.disjoint_left]
  intro c hc₁ hc₂
  exact h (class_eq_of_admissible_common hc₁ hc₂)

/-! ## Actual whole-state samples

The qualitative record is now instantiated with the repository's concrete two-atom whole
description.  The two named molecular states are `stateLeft` (the concrete example description)
and `stateRight` (the same description with the two atom labels swapped).  They are proved
distinct.  Every constituent's possible set is the singleton containing its own supplied whole
state, so the sample data is full whole-record data rather than a pair of marginals.

No physical enantiomer relationship is asserted: swapping atom labels is a relabelling of a whole
record, not a mirror operation, and the two states are only used as two distinct species data.
-/

namespace ActualSample

open OrganicStereoHeterogeneousSamples

/-- The concrete fixed shape: two constituents, each with two atoms, one edge and no bands. -/
def shape : Shape (Fin 2) where
  Atom := fun _ => Fin 2
  Edge := fun _ => Fin 1
  Band := fun _ => Fin 0
  atomDecidableEq := fun _ => inferInstance
  atomFintype := fun _ => inferInstance
  edgeFintype := fun _ => inferInstance
  bandFintype := fun _ => inferInstance

/-- Explicit enumerations for the fixed shape. -/
def indexing : Indexing shape where
  atomIndex := fun _ => Equiv.refl (Fin 2)
  edgeIndex := fun _ => Equiv.refl (Fin 1)
  bandIndex := fun _ => Equiv.refl (Fin 0)

/-- The first named actual whole state: the repository's concrete two-atom hydrogen description. -/
def stateLeft : FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0) :=
  FiniteClassicalStereoDescriptionExample.description

/-- The second named actual whole state: the same description with the two atom labels swapped.

This is a genuine relabelling of a whole record, not a mirror-image or enantiomer construction. -/
def stateRight : FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0) :=
  relabelDescription (Equiv.swap (0 : Fin 2) (1 : Fin 2))
    FiniteClassicalStereoDescriptionExample.description

/-- The relational type of a constituent state of the fixed shape. -/
abbrev State := FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0)

/-- The ordered pair of named states, indexed by the two constituents. -/
def statePair (i : Fin 2) : ComponentState shape i :=
  Fin.cases stateLeft (fun _ => stateRight) i

/-- The first named state's conformation at atom `0` is the origin. -/
theorem stateLeft_conformation_zero :
    stateLeft.conformation (0 : Fin 2) = (0 : EuclideanSpace ℝ (Fin 3)) := by
  simp [stateLeft, FiniteClassicalStereoDescriptionExample.description,
    FiniteClassicalStereoDescriptionExample.conformation]

/-- The second named state's conformation at atom `0` is the unit vector on coordinate `0`. -/
theorem stateRight_conformation_zero :
    stateRight.conformation (0 : Fin 2) =
      EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  simp [stateRight, relabelDescription, relabelWholeState, MolecularConformation.reindex,
    FiniteClassicalStereoDescriptionExample.description,
    FiniteClassicalStereoDescriptionExample.conformation, Equiv.swap_apply_def]

/-- The two named actual whole states are distinct. -/
theorem stateLeft_ne_stateRight : stateLeft ≠ stateRight := by
  intro equal
  have hconf : stateLeft.conformation (0 : Fin 2) = stateRight.conformation (0 : Fin 2) :=
    congrArg (fun state : State => state.conformation (0 : Fin 2)) equal
  rw [stateLeft_conformation_zero, stateRight_conformation_zero] at hconf
  have hsingle : (0 : EuclideanSpace ℝ (Fin 3)) ≠
      EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
    intro hz
    have hz' : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) =
        (0 : EuclideanSpace ℝ (Fin 3)) := hz.symm
    have hone : (1 : ℝ) = 0 := (EuclideanSpace.single_eq_zero_iff).mp hz'
    norm_num at hone
  exact hsingle hconf

/-- The non-equimolar qualitative record over the two named actual states. -/
def nonEquimolarMixture : QualitativeBinaryMixture State :=
  { first := stateLeft, second := stateRight,
    composition := BinaryCompositionClass.nonEquimolar }

/-- The equimolar qualitative record over the two named actual states. -/
def equimolarMixture : QualitativeBinaryMixture State :=
  { first := stateLeft, second := stateRight,
    composition := BinaryCompositionClass.equimolar }

/-- Sample data with state `statePair`, singleton whole-record possibility sets, and real amounts
`f` and `1 - f`. -/
def data (f : ℝ) : SampleData (Fin 2) shape where
  state := statePair
  possible := fun i => {statePair i}
  amount := MolarComposition.Composition.binaryAmount f (1 - f)

/-- The sample data is valid for every real fraction in `(0,1)`. -/
theorem data_valid (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) : (data f).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [data]
  · intro i
    fin_cases i
    · show 0 ≤ MolarComposition.Composition.binaryAmount f (1 - f) (0 : Fin 2)
      rw [MarginalSeparation.binaryAmount_zero]
      linarith
    · show 0 ≤ MolarComposition.Composition.binaryAmount f (1 - f) (1 : Fin 2)
      rw [MarginalSeparation.binaryAmount_one]
      linarith
  · show 0 < ∑ i : Fin 2, MolarComposition.Composition.binaryAmount f (1 - f) i
    rw [Fin.sum_univ_two, MarginalSeparation.binaryAmount_zero,
      MarginalSeparation.binaryAmount_one]
    linarith

/-- The concrete heterogeneous sample at real fraction `f`. -/
def sample (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    HeterogeneousSample (Fin 2) shape :=
  ⟨data f, data_valid f hf0 hf1⟩

@[simp] theorem sample_state_zero (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).val.state (0 : Fin 2) = stateLeft := rfl

@[simp] theorem sample_state_one (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).val.state (1 : Fin 2) = stateRight := by
  show statePair (1 : Fin 2) = stateRight
  rw [← Fin.succ_zero_eq_one]
  rfl

@[simp] theorem sample_amount_zero (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).val.amount (0 : Fin 2) = f :=
  MarginalSeparation.binaryAmount_zero f (1 - f)

@[simp] theorem sample_amount_one (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).val.amount (1 : Fin 2) = 1 - f :=
  MarginalSeparation.binaryAmount_one f (1 - f)

/-- The sample total is exactly one, so the raw amounts are already normalized. -/
theorem sample_total (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).total = 1 := by
  rw [HeterogeneousSample.total_eq_sum, Fin.sum_univ_two,
    sample_amount_zero, sample_amount_one]
  ring

/-- The first normalized amount of the sample is `f`. -/
theorem sample_fraction_zero (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).fraction (0 : Fin 2) = f := by
  rw [HeterogeneousSample.fraction_eq, sample_amount_zero, sample_total, div_one]

/-- The second normalized amount of the sample is `1 - f`. -/
theorem sample_fraction_one (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).fraction (1 : Fin 2) = 1 - f := by
  rw [HeterogeneousSample.fraction_eq, sample_amount_one, sample_total, div_one]

/-- The whole composition carried by a heterogeneous sample. -/
def wholeComposition (s : HeterogeneousSample (Fin 2) shape) :
    MolarComposition.Composition (Fin 2) State where
  species := s.val.state
  amount := s.val.amount
  amount_nonneg := s.property.2.1
  total_pos := s.property.2.2

@[simp] theorem wholeComposition_species (s : HeterogeneousSample (Fin 2) shape)
    (i : Fin 2) : (wholeComposition s).species i = s.val.state i := rfl

@[simp] theorem wholeComposition_amount (s : HeterogeneousSample (Fin 2) shape)
    (i : Fin 2) : (wholeComposition s).amount i = s.val.amount i := rfl

/-- The normalized fraction of the whole composition is the sample's normalized fraction. -/
theorem wholeComposition_fraction (s : HeterogeneousSample (Fin 2) shape) (i : Fin 2) :
    (wholeComposition s).fraction i = s.fraction i := rfl

/-- The two constituents of a sample carry the two distinct named whole states, so distinct
molecular states are retained within one record. -/
theorem sample_state_pair_distinct (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).val.state (0 : Fin 2) ≠
      (sample f hf0 hf1).val.state (1 : Fin 2) := by
  rw [sample_state_zero, sample_state_one]
  exact stateLeft_ne_stateRight

/-- The amount correlation of each whole sample: component `0` keeps the amount `f` while
component `1` keeps `1 - f`. -/
theorem sample_amount_correlation (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (sample f hf0 hf1).val.amount (0 : Fin 2) = f ∧
      (sample f hf0 hf1).val.amount (1 : Fin 2) = 1 - f :=
  ⟨sample_amount_zero f hf0 hf1, sample_amount_one f hf0 hf1⟩

/-- The sample at real fraction `f` is an admissible quantitative realization of the actual
non-equimolar qualitative record, for every real `f` in `(0,1)` with `f ≠ 1/2`. -/
theorem sample_mem_admissible_nonEquimolar (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1)
    (hfne : f ≠ 1 / 2) :
    Admissible nonEquimolarMixture (wholeComposition (sample f hf0 hf1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [nonEquimolarMixture]
  · simp [nonEquimolarMixture]
  · rw [wholeComposition_fraction, sample_fraction_zero]
    exact hf0
  · rw [wholeComposition_fraction, sample_fraction_zero]
    exact hf1
  · rw [wholeComposition_fraction, sample_fraction_zero]
    constructor
    · intro hEq
      exact absurd hEq (by simp [nonEquimolarMixture])
    · intro hf
      exact absurd hf hfne

/-- The actual sample at fraction `1/2` realizes the equimolar qualitative record. -/
theorem sample_mem_admissible_equimolar :
    Admissible equimolarMixture
      (wholeComposition (sample (1 / 2) (by norm_num) (by norm_num))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [equimolarMixture]
  · simp [equimolarMixture]
  · rw [wholeComposition_fraction, sample_fraction_zero]
    norm_num
  · rw [wholeComposition_fraction, sample_fraction_zero]
    norm_num
  · rw [wholeComposition_fraction, sample_fraction_zero]
    constructor
    · intro _
      norm_num
    · intro _
      rfl

/-- The concrete witness `1/3` realizes the actual non-equimolar record. -/
theorem sample_third_mem_admissible_nonEquimolar :
    Admissible nonEquimolarMixture
      (wholeComposition (sample (1 / 3) (by norm_num) (by norm_num))) :=
  sample_mem_admissible_nonEquimolar (1 / 3) (by norm_num) (by norm_num) (by norm_num)

/-- The actual sample is recovered exactly by the approved whole-sample codec. -/
theorem decode_encode_sample (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    OrganicStereoHeterogeneousSamples.decode shape indexing
        (OrganicStereoHeterogeneousSamples.encode shape indexing (sample f hf0 hf1)) =
      sample f hf0 hf1 :=
  OrganicStereoHeterogeneousSamples.decode_encode shape indexing (sample f hf0 hf1)

/-- Encoding preserves the first component amount. -/
theorem encode_sample_amount_zero (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (OrganicStereoHeterogeneousSamples.encode shape indexing (sample f hf0 hf1)).val.amount
        (0 : Fin 2) = f := by
  rw [OrganicStereoHeterogeneousSamples.encode_amount]
  exact sample_amount_zero f hf0 hf1

/-- Encoding preserves the second component amount. -/
theorem encode_sample_amount_one (f : ℝ) (hf0 : 0 < f) (hf1 : f < 1) :
    (OrganicStereoHeterogeneousSamples.encode shape indexing (sample f hf0 hf1)).val.amount
        (1 : Fin 2) = 1 - f := by
  rw [OrganicStereoHeterogeneousSamples.encode_amount]
  exact sample_amount_one f hf0 hf1

/-- The concrete sample at fraction `1/3`. -/
def thirdSample : HeterogeneousSample (Fin 2) shape :=
  sample (1 / 3) (by norm_num) (by norm_num)

/-- The concrete sample at fraction `2/5`. -/
def twoFifthsSample : HeterogeneousSample (Fin 2) shape :=
  sample (2 / 5) (by norm_num) (by norm_num)

/-- A whole-record uncertainty set containing the two correlated samples.  Membership is of the
whole sample, so state and amount remain paired. -/
def correlatedUncertainty : UncertainSample (Fin 2) shape :=
  {thirdSample, twoFifthsSample}

/-- The two whole samples are distinct: their first-component amounts differ. -/
theorem thirdSample_ne_twoFifthsSample : thirdSample ≠ twoFifthsSample := by
  intro equal
  have ha : thirdSample.val.amount (0 : Fin 2) = twoFifthsSample.val.amount (0 : Fin 2) := by
    simpa using
      congrArg (fun s : HeterogeneousSample (Fin 2) shape => s.val.amount (0 : Fin 2)) equal
  rw [show thirdSample.val.amount (0 : Fin 2) = 1 / 3 from
      sample_amount_zero (1 / 3) (by norm_num) (by norm_num),
    show twoFifthsSample.val.amount (0 : Fin 2) = 2 / 5 from
      sample_amount_zero (2 / 5) (by norm_num) (by norm_num)] at ha
  norm_num at ha

/-- The whole-record codec recovers the correlated uncertainty set exactly, including the
state/amount pairing of both records. -/
theorem decodeSet_encodeSet_correlated :
    UncertainSample.decodeSet shape indexing
        (UncertainSample.encodeSet shape indexing correlatedUncertainty) =
      correlatedUncertainty :=
  UncertainSample.decodeSet_encodeSet shape indexing correlatedUncertainty

/-- After the round trip every member is exactly one of the two original whole samples, so the
two distinct states and their amount correlations are not collapsed or marginalized. -/
theorem mem_decodeSet_encodeSet_correlated_iff
    (s : HeterogeneousSample (Fin 2) shape) :
    s ∈ UncertainSample.decodeSet shape indexing
        (UncertainSample.encodeSet shape indexing correlatedUncertainty) ↔
      s = thirdSample ∨ s = twoFifthsSample := by
  rw [decodeSet_encodeSet_correlated]
  simp [correlatedUncertainty]

end ActualSample

end

end OrganicStereoQualitativeMixtureRealization
end OneCenter
end TetraStereo
