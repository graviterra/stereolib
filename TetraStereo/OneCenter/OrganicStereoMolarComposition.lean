/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.P93GeneralConfiguration
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

/-!
# Finite molar compositions for organic stereochemistry

This module supplies a representation layer for molar composition data.  It is deliberately
independent of conformational probability distributions: a composition records nonnegative
real mole amounts, while an uncertain composition is a *set* of complete joint records.  No
probability, free energy, or desired stereochemical output is introduced.

The central definitions are:

* `MolarComposition.Composition` -- a finite family of components, each retaining its own
  arbitrary species/physical-state datum and carrying a nonnegative real mole amount, with a
  positive total amount.  The map `species : Component → Species` need not be injective, so
  two components may depict different molecules, conformers, or the same species.
* `MolarComposition.Composition.fraction` -- the normalized mole fraction
  `amount i / total`; nonnegativity, the sum-to-one law, the `[0,1]` range, positive scaling
  invariance, and reindexing invariance are proved below.
* `MolarComposition.Composition.ofP93BinaryMixture` -- an exact embedding of a valid
  `P93GeneralConfiguration.BinaryMixture` with rational mole fraction `f` as the two
  component amounts `f` and `1 - f`.  The embedding does not specialise the arbitrary pair to
  enantiomers: `IsRacemate` is only a predicate, and it explicitly requires distinct
  mirror-related species.
* `MolarComposition.UncertainComposition` -- `Set` of complete joint composition records.
  Its qualitative equimolar and non-equimolar subsets are filters on amount comparisons; no
  numerical fraction is invented.  `Consistent` records the nonemptiness obligation that keeps
  the possibility set from being silently vacuous.

The aggregation section proves the generic finite regrouping identity and constructs the
amount-aggregated composition over species, showing that amount-weighted observables are
preserved.
-/

namespace TetraStereo.OneCenter

namespace MolarComposition

open scoped BigOperators

/-! ## Core compositions and strong normalization -/

/-- A finite molar composition over an arbitrary component index type.

Each component carries its own `Species` datum (which may contain molecule, isotope,
physical-state, or other descriptive data); the map `species` is not required to be injective.
All mole amounts are nonnegative real numbers and the total amount is positive. -/
structure Composition (Component : Type*) (Species : Type*) [Fintype Component] where
  /-- The species/physical-state datum retained by each component. -/
  species : Component → Species
  /-- The (unrestricted real) mole amount of each component. -/
  amount : Component → ℝ
  amount_nonneg : ∀ i, 0 ≤ amount i
  total_pos : 0 < ∑ i, amount i

namespace Composition

variable {Component : Type*} {Species : Type*} [Fintype Component]

/-- The total mole amount of a finite composition. -/
def total (c : Composition Component Species) : ℝ := ∑ i, c.amount i

@[simp] theorem total_eq_sum (c : Composition Component Species) :
    c.total = ∑ i, c.amount i := rfl

theorem total_pos' (c : Composition Component Species) : 0 < c.total := c.total_pos

theorem total_ne_zero (c : Composition Component Species) : c.total ≠ 0 :=
  ne_of_gt c.total_pos

/-- The normalized mole fraction of a component. -/
noncomputable def fraction (c : Composition Component Species) (i : Component) : ℝ :=
  c.amount i / c.total

@[simp] theorem fraction_eq_div (c : Composition Component Species) (i : Component) :
    c.fraction i = c.amount i / c.total := rfl

theorem fraction_nonneg (c : Composition Component Species) (i : Component) :
    0 ≤ c.fraction i :=
  div_nonneg (c.amount_nonneg i) (le_of_lt c.total_pos)

theorem fraction_pos (c : Composition Component Species) {i : Component}
    (h : 0 < c.amount i) : 0 < c.fraction i :=
  div_pos h c.total_pos

/-- Every component amount is at most the total amount. -/
theorem amount_le_total (c : Composition Component Species) (i : Component) :
    c.amount i ≤ c.total := by
  rw [total]
  exact Finset.single_le_sum (fun j _ => c.amount_nonneg j) (Finset.mem_univ i)

theorem fraction_le_one (c : Composition Component Species) (i : Component) :
    c.fraction i ≤ 1 := by
  rw [fraction]
  change c.amount i / (∑ j, c.amount j) ≤ 1
  rw [div_le_one c.total_pos]
  exact amount_le_total c i

/-- Strong normalization: normalized mole fractions sum to one. -/
theorem sum_fraction_eq_one (c : Composition Component Species) :
    ∑ i, c.fraction i = 1 := by
  simp only [fraction, total]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt c.total_pos)

/-! ### Positive scaling invariance -/

/-- Multiply every component amount by a positive real scale factor. -/
def scale (r : ℝ) (hr : 0 < r) (c : Composition Component Species) :
    Composition Component Species where
  species := c.species
  amount i := r * c.amount i
  amount_nonneg i := mul_nonneg (le_of_lt hr) (c.amount_nonneg i)
  total_pos := by
    show 0 < ∑ i, r * c.amount i
    rw [← Finset.mul_sum]
    exact mul_pos hr c.total_pos

@[simp] theorem scale_species (r : ℝ) (hr : 0 < r) (c : Composition Component Species)
    (i : Component) : (scale r hr c).species i = c.species i := rfl

@[simp] theorem scale_amount (r : ℝ) (hr : 0 < r) (c : Composition Component Species)
    (i : Component) : (scale r hr c).amount i = r * c.amount i := rfl

@[simp] theorem total_scale (r : ℝ) (hr : 0 < r) (c : Composition Component Species) :
    (scale r hr c).total = r * c.total := by
  simp only [total]
  change (∑ i, r * c.amount i) = r * ∑ i, c.amount i
  rw [Finset.mul_sum]

/-- Positive rescaling leaves every normalized mole fraction unchanged. -/
theorem fraction_scale (r : ℝ) (hr : 0 < r) (c : Composition Component Species)
    (i : Component) : (scale r hr c).fraction i = c.fraction i := by
  rw [fraction, fraction, scale_amount, total_scale]
  exact mul_div_mul_left (c.amount i) c.total (ne_of_gt hr)

/-! ### Reindexing -/

/-- Transport a composition along an equivalence of component index types.  Component data
(species and amount) is carried pointwise, so total amount and normalized fractions agree at
corresponding components. -/
def reindex {Component' : Type*} [Fintype Component'] (e : Component ≃ Component')
    (c : Composition Component Species) : Composition Component' Species where
  species j := c.species (e.symm j)
  amount j := c.amount (e.symm j)
  amount_nonneg j := c.amount_nonneg (e.symm j)
  total_pos := by
    change 0 < ∑ j : Component', c.amount (e.symm j)
    rw [Equiv.sum_comp e.symm (fun i => c.amount i)]
    exact c.total_pos

@[simp] theorem reindex_species {Component' : Type*} [Fintype Component']
    (e : Component ≃ Component') (c : Composition Component Species) (j : Component') :
    (reindex e c).species j = c.species (e.symm j) := rfl

@[simp] theorem reindex_amount {Component' : Type*} [Fintype Component']
    (e : Component ≃ Component') (c : Composition Component Species) (j : Component') :
    (reindex e c).amount j = c.amount (e.symm j) := rfl

@[simp] theorem total_reindex {Component' : Type*} [Fintype Component']
    (e : Component ≃ Component') (c : Composition Component Species) :
    (reindex e c).total = c.total := by
  simp only [total, reindex_amount]
  exact Equiv.sum_comp e.symm (fun i => c.amount i)

/-- Reindexing preserves the normalized fraction at the corresponding component. -/
@[simp] theorem fraction_reindex {Component' : Type*} [Fintype Component']
    (e : Component ≃ Component') (c : Composition Component Species) (i : Component) :
    (reindex e c).fraction (e i) = c.fraction i := by
  simp only [fraction, reindex_amount, total_reindex, Equiv.symm_apply_apply]

/-! ## Binary compositions and the P-93 embedding -/

/-- The species map of the canonical two-component composition. -/
def binarySpecies (first second : Species) : Fin 2 → Species :=
  Fin.cases first (fun _ => second)

/-- The amount map of the canonical two-component composition. -/
def binaryAmount (a b : ℝ) : Fin 2 → ℝ :=
  Fin.cases a (fun _ => b)

/-- A two-component composition with explicit amounts and species data.  Distinct components
with equal species are retained as distinct components; no identification is forced. -/
def binary (first second : Species) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : 0 < a + b) : Composition (Fin 2) Species where
  species := binarySpecies first second
  amount := binaryAmount a b
  amount_nonneg := Fin.cases ha (fun _ => hb)
  total_pos := by
    show (0 : ℝ) < ∑ i : Fin 2, binaryAmount a b i
    rw [Fin.sum_univ_two]
    rw [← Fin.succ_zero_eq_one]
    simp only [binaryAmount, Fin.cases_zero, Fin.cases_succ]
    simpa using h

@[simp] theorem binary_species_zero (first second : Species) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a + b) :
    (binary first second a b ha hb h).species (0 : Fin 2) = first := by
  show binarySpecies first second (0 : Fin 2) = first
  simp only [binarySpecies, Fin.cases_zero]

@[simp] theorem binary_species_one (first second : Species) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a + b) :
    (binary first second a b ha hb h).species (1 : Fin 2) = second := by
  show binarySpecies first second (1 : Fin 2) = second
  rw [← Fin.succ_zero_eq_one]
  simp only [binarySpecies, Fin.cases_succ]

@[simp] theorem binary_amount_zero (first second : Species) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a + b) :
    (binary first second a b ha hb h).amount (0 : Fin 2) = a := by
  show binaryAmount a b (0 : Fin 2) = a
  simp only [binaryAmount, Fin.cases_zero]

@[simp] theorem binary_amount_one (first second : Species) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a + b) :
    (binary first second a b ha hb h).amount (1 : Fin 2) = b := by
  show binaryAmount a b (1 : Fin 2) = b
  rw [← Fin.succ_zero_eq_one]
  simp only [binaryAmount, Fin.cases_succ]

@[simp] theorem binary_total (first second : Species) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a + b) :
    (binary first second a b ha hb h).total = a + b := by
  simp only [total]
  change (∑ i : Fin 2, binaryAmount a b i) = a + b
  rw [Fin.sum_univ_two, ← Fin.succ_zero_eq_one]
  simp only [binaryAmount, Fin.cases_zero, Fin.cases_succ]

theorem binary_fraction_zero (first second : Species) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a + b) :
    (binary first second a b ha hb h).fraction (0 : Fin 2) = a / (a + b) := by
  simp only [fraction, binary_amount_zero, binary_total]

theorem binary_fraction_one (first second : Species) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a + b) :
    (binary first second a b ha hb h).fraction (1 : Fin 2) = b / (a + b) := by
  simp only [fraction, binary_amount_one, binary_total]

/-! ### Embedding `P93GeneralConfiguration.BinaryMixture`

The P-93 binary mixture is an arbitrary pair of species together with a rational first
fraction.  Valid means `0 < f < 1`.  The embedding uses the *unrestricted real* amounts
`f` and `1 - f`; it neither identifies the two species nor restricts them to be enantiomers. -/

/-- The existing P-93 binary mixture type, re-exported only for readability. -/
abbrev P93BinaryMixture (Species : Type*) : Type _ :=
  BlueBookP93.GeneralConfiguration.BinaryMixture Species

/-- Embed a valid P-93 binary mixture using component amounts `f` and `1 - f`.

The first component keeps `m.first` and amount `(m.firstFraction : ℝ)`, the second keeps
`m.second` and amount `((1 - m.firstFraction : ℚ) : ℝ)`.  No graph identity between the two
species is assumed. -/
def ofP93BinaryMixture (m : P93BinaryMixture Species) (valid : m.Valid) :
    Composition (Fin 2) Species :=
  binary m.first m.second (m.firstFraction : ℝ) ((1 - m.firstFraction : ℚ) : ℝ)
    (le_of_lt (Rat.cast_pos (K := ℝ).mpr valid.1))
    (le_of_lt (Rat.cast_pos (K := ℝ).mpr (sub_pos.mpr valid.2)))
    (by
      have hq : m.firstFraction + (1 - m.firstFraction) = (1 : ℚ) := by ring
      have hr : (m.firstFraction : ℝ) + ((1 - m.firstFraction : ℚ) : ℝ) = 1 := by
        rw [← Rat.cast_add, hq, Rat.cast_one]
      rw [hr]
      norm_num)

/-- Exact species preservation: the first component is `m.first`. -/
@[simp] theorem ofP93BinaryMixture_species_zero (m : P93BinaryMixture Species)
    (valid : m.Valid) :
    (ofP93BinaryMixture m valid).species (0 : Fin 2) = m.first := by
  simp only [ofP93BinaryMixture, binary_species_zero]

/-- Exact species preservation: the second component is `m.second`. -/
@[simp] theorem ofP93BinaryMixture_species_one (m : P93BinaryMixture Species)
    (valid : m.Valid) :
    (ofP93BinaryMixture m valid).species (1 : Fin 2) = m.second := by
  simp only [ofP93BinaryMixture, binary_species_one]

/-- Exact fraction preservation: the normalized first fraction equals the rational input. -/
theorem ofP93BinaryMixture_fraction_zero (m : P93BinaryMixture Species) (valid : m.Valid) :
    (ofP93BinaryMixture m valid).fraction (0 : Fin 2) = (m.firstFraction : ℝ) := by
  simp only [ofP93BinaryMixture]
  rw [binary_fraction_zero]
  have hq : m.firstFraction + (1 - m.firstFraction) = (1 : ℚ) := by ring
  have hr : (m.firstFraction : ℝ) + ((1 - m.firstFraction : ℚ) : ℝ) = 1 := by
    rw [← Rat.cast_add, hq, Rat.cast_one]
  rw [hr, div_one]

/-- Exact fraction preservation for the second component: its normalized fraction is the real
cast of `1 - f`. -/
theorem ofP93BinaryMixture_fraction_one (m : P93BinaryMixture Species) (valid : m.Valid) :
    (ofP93BinaryMixture m valid).fraction (1 : Fin 2) =
      ((1 - m.firstFraction : ℚ) : ℝ) := by
  simp only [ofP93BinaryMixture]
  rw [binary_fraction_one]
  have hq : m.firstFraction + (1 - m.firstFraction) = (1 : ℚ) := by ring
  have hr : (m.firstFraction : ℝ) + ((1 - m.firstFraction : ℚ) : ℝ) = 1 := by
    rw [← Rat.cast_add, hq, Rat.cast_one]
  rw [hr, div_one]

/-- The embedded P-93 binary composition has total amount exactly one. -/
@[simp] theorem ofP93BinaryMixture_total (m : P93BinaryMixture Species) (valid : m.Valid) :
    (ofP93BinaryMixture m valid).total = 1 := by
  simp only [ofP93BinaryMixture]
  rw [binary_total]
  have hq : m.firstFraction + (1 - m.firstFraction) = (1 : ℚ) := by ring
  have hr : (m.firstFraction : ℝ) + ((1 - m.firstFraction : ℚ) : ℝ) = 1 := by
    rw [← Rat.cast_add, hq, Rat.cast_one]
  exact hr

/-! ## Amount-weighted observables and racemate/excess statements -/

/-- The raw amount-weighted sum of a species observable.  This is an unnormalized finite sum,
not an average, expectation, or probability-weighted mean: amounts are molar quantities, and the
value scales with the total amount.  Divide by `total` explicitly if a normalized average is
wanted. -/
def amountWeighted (c : Composition Component Species) (obs : Species → ℝ) : ℝ :=
  ∑ i, c.amount i * obs (c.species i)

/-- Signed amount excess between the two components of a binary composition. -/
def binaryExcess (c : Composition (Fin 2) Species) : ℝ := c.amount 0 - c.amount 1

/-- A racemate predicate for a binary composition.

The type of the two species is explicit (`first`, `second`), and the predicate *requires*
`first ≠ second` and `mirror first = second`.  Equal amounts alone are not enough.

The function `mirror : Species → Species` is supplied by the caller.  This predicate is therefore
*relative to that explicitly given function*: it records that the supplied data names a pair
related by `mirror`, not that `mirror` is a certified physical mirror operation on `Species`, nor
that a physical sample is a racemate.  Establishing those facts is outside the scope of this
purely compositional predicate. -/
def IsRacemate (mirror : Species → Species) (first second : Species)
    (c : Composition (Fin 2) Species) : Prop :=
  c.species (0 : Fin 2) = first ∧
  c.species (1 : Fin 2) = second ∧
  first ≠ second ∧
  mirror first = second ∧
  c.amount (0 : Fin 2) = c.amount (1 : Fin 2)

/-- Constructor for the racemate predicate from explicitly supplied data. -/
theorem isRacemate_of_data {mirror : Species → Species} {first second : Species}
    {c : Composition (Fin 2) Species}
    (h0 : c.species (0 : Fin 2) = first)
    (h1 : c.species (1 : Fin 2) = second)
    (hne : first ≠ second) (hmirror : mirror first = second)
    (heq : c.amount (0 : Fin 2) = c.amount (1 : Fin 2)) :
    IsRacemate mirror first second c :=
  ⟨h0, h1, hne, hmirror, heq⟩

theorem isRacemate_distinct {mirror : Species → Species} {first second : Species}
    {c : Composition (Fin 2) Species} (race : IsRacemate mirror first second c) :
    first ≠ second :=
  race.2.2.1

theorem isRacemate_mirror {mirror : Species → Species} {first second : Species}
    {c : Composition (Fin 2) Species} (race : IsRacemate mirror first second c) :
    mirror first = second :=
  race.2.2.2.1

theorem isRacemate_equal_amounts {mirror : Species → Species} {first second : Species}
    {c : Composition (Fin 2) Species} (race : IsRacemate mirror first second c) :
    c.amount (0 : Fin 2) = c.amount (1 : Fin 2) :=
  race.2.2.2.2

/-- A racemate has zero amount excess. -/
theorem isRacemate_excess_eq_zero {mirror : Species → Species} {first second : Species}
    {c : Composition (Fin 2) Species} (race : IsRacemate mirror first second c) :
    binaryExcess c = 0 := by
  rw [binaryExcess, sub_eq_zero]
  exact isRacemate_equal_amounts race

/-- Zero excess is equivalent to equality of the two component amounts. -/
@[simp] theorem binaryExcess_eq_zero_iff (c : Composition (Fin 2) Species) :
    binaryExcess c = 0 ↔ c.amount (0 : Fin 2) = c.amount (1 : Fin 2) := by
  rw [binaryExcess, sub_eq_zero]

/-- **Racemate cancellation** (requires the explicit distinct mirror-related species in
`IsRacemate`).  If the observable is odd on the mirror pair, an equimolar binary composition
of that pair has zero amount-weighted response. -/
theorem racemate_amountWeighted_eq_zero {mirror : Species → Species} {first second : Species}
    {c : Composition (Fin 2) Species} (race : IsRacemate mirror first second c)
    (obs : Species → ℝ) (odd : obs second = -obs first) :
    amountWeighted c obs = 0 := by
  rcases race with ⟨h0, h1, _hne, _hmirror, heq⟩
  rw [amountWeighted, Fin.sum_univ_two, h0, h1, heq, odd]
  ring

/-- For a binary composition whose second species is the mirror image of the first, the
amount-weighted response of a mirror-odd observable is the amount excess times the first
response. -/
theorem binary_amountWeighted_eq_excess_mul {mirror : Species → Species}
    (c : Composition (Fin 2) Species)
    (hmirror : c.species (1 : Fin 2) = mirror (c.species (0 : Fin 2)))
    (obs : Species → ℝ)
    (odd : obs (mirror (c.species (0 : Fin 2))) = -obs (c.species (0 : Fin 2))) :
    amountWeighted c obs = binaryExcess c * obs (c.species (0 : Fin 2)) := by
  rw [amountWeighted, binaryExcess, Fin.sum_univ_two, hmirror, odd]
  ring

/-- **Zero excess alone does not make a racemate.**  Even with equal amounts and the two
species explicitly named, the absence of the mirror relation rules out `IsRacemate`. -/
theorem zeroExcess_not_racemate_without_mirror {mirror : Species → Species}
    {first second : Species} {c : Composition (Fin 2) Species}
    (h0 : c.species (0 : Fin 2) = first)
    (h1 : c.species (1 : Fin 2) = second)
    (_heq : c.amount (0 : Fin 2) = c.amount (1 : Fin 2))
    (hnotMirror : c.species (1 : Fin 2) ≠ mirror (c.species (0 : Fin 2))) :
    ¬IsRacemate mirror first second c := by
  intro race
  apply hnotMirror
  rw [h1, h0]
  exact (isRacemate_mirror race).symm

/-! ## Generic finite regrouping and species aggregation -/

/-- Generic finite regrouping core.  Summing `amount i * obsOf (key i)` and then grouping by
the value of `key` preserves the total: the group amount is the sum of the amounts in the
fiber, and the observable only depends on the group. -/
theorem sum_amount_mul_regroup {Component Class : Type*} [Fintype Component]
    [DecidableEq Class] (key : Component → Class) (amount : Component → ℝ)
    (obsOf : Class → ℝ) :
    (∑ i, amount i * obsOf (key i)) =
      ∑ k ∈ (Finset.univ : Finset Component).image key,
        (∑ i ∈ (Finset.univ : Finset Component).filter (fun i => key i = k), amount i) *
          obsOf k := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset Component))
    (t := (Finset.univ : Finset Component).image key)
    (g := key)
    (h := fun i _ => Finset.mem_image_of_mem key (Finset.mem_univ i))
    (f := fun i => amount i * obsOf (key i))]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- The total mole amount assigned to a species datum, summing every component that carries
that datum.  This is the aggregation of identical species. -/
def aggregatedAmount {Component Species : Type*} [Fintype Component] [DecidableEq Species]
    (c : Composition Component Species) (s : Species) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset Component).filter (fun i => c.species i = s), c.amount i

theorem aggregatedAmount_nonneg {Component Species : Type*} [Fintype Component]
    [DecidableEq Species] (c : Composition Component Species) (s : Species) :
    0 ≤ aggregatedAmount c s :=
  Finset.sum_nonneg (fun i _ => c.amount_nonneg i)

/-- Aggregation of identical species preserves the amount-weighted observable.  This is the
specialization of the generic regrouping identity to the species map of a composition. -/
theorem amountWeighted_eq_regrouped {Component Species : Type*} [Fintype Component]
    [DecidableEq Species] (c : Composition Component Species) (obs : Species → ℝ) :
    amountWeighted c obs =
      ∑ s ∈ (Finset.univ : Finset Component).image c.species,
        aggregatedAmount c s * obs s := by
  simpa only [amountWeighted, aggregatedAmount] using
    (sum_amount_mul_regroup (key := c.species) (amount := c.amount) (obsOf := obs))

/-- The composition obtained by merging components with the same species datum.

This convenience definition asks for `[Fintype Species]`, so it is stated for a finite species
carrier (for example a finite subtype of the occurring species).  The underlying generic
regrouping identity `amountWeighted_eq_regrouped` and the identity `sum_amount_mul_regroup` work
for an arbitrary `Species` as long as `[DecidableEq Species]` is available; only this packaged
`Composition Species Species` carrier needs the global finiteness assumption. -/
def aggregateBySpecies {Component Species : Type*} [Fintype Component] [Fintype Species]
    [DecidableEq Species] (c : Composition Component Species) :
    Composition Species Species where
  species s := s
  amount s := aggregatedAmount c s
  amount_nonneg s := aggregatedAmount_nonneg c s
  total_pos := by
    have h := Finset.sum_fiberwise (s := (Finset.univ : Finset Component))
      (g := c.species) (f := c.amount)
    simp only [aggregatedAmount]
    rw [h]
    exact c.total_pos

@[simp] theorem total_aggregateBySpecies {Component Species : Type*} [Fintype Component]
    [Fintype Species] [DecidableEq Species] (c : Composition Component Species) :
    (aggregateBySpecies c).total = c.total := by
  simp only [total, aggregateBySpecies, aggregatedAmount]
  exact Finset.sum_fiberwise (s := (Finset.univ : Finset Component))
    (g := c.species) (f := c.amount)

/-- Aggregating identical species preserves every amount-weighted observable whose value
depends only on the species datum. -/
theorem amountWeighted_aggregateBySpecies {Component Species : Type*} [Fintype Component]
    [Fintype Species] [DecidableEq Species] (c : Composition Component Species)
    (obs : Species → ℝ) :
    amountWeighted c obs = amountWeighted (aggregateBySpecies c) obs := by
  rw [amountWeighted_eq_regrouped c obs, amountWeighted]
  change (∑ s ∈ (Finset.univ : Finset Component).image c.species,
      (∑ i ∈ (Finset.univ : Finset Component).filter (fun i => c.species i = s),
        c.amount i) * obs s)
    = ∑ s, (∑ i ∈ (Finset.univ : Finset Component).filter (fun i => c.species i = s),
        c.amount i) * obs s
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro s _ hs
  have hempty : (Finset.univ : Finset Component).filter (fun i => c.species i = s) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _ h
    exact hs (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h⟩)
  simp [hempty]

/-! ### Aggregation on the finite occurring support -/

/-- The finite set of species data that actually occur in a composition. -/
def occurringSpecies {Component Species : Type*} [Fintype Component] [DecidableEq Species]
    (c : Composition Component Species) : Finset Species :=
  (Finset.univ : Finset Component).image c.species

/-- The finite type of species data occurring in a composition.  This is a subtype of an
explicit finset, so it exists even when `Species` itself is not globally finite. -/
abbrev OccurringSpecies {Component Species : Type*} [Fintype Component] [DecidableEq Species]
    (c : Composition Component Species) : Type _ :=
  {s : Species // s ∈ occurringSpecies c}

/-- Merge components with the same species datum, indexed by the finite occurring support.
Unlike `aggregateBySpecies`, this definition does not require a global `[Fintype Species]`. -/
def aggregateOnSupport {Component Species : Type*} [Fintype Component] [DecidableEq Species]
    (c : Composition Component Species) : Composition (OccurringSpecies c) Species where
  species s := s.1
  amount s := aggregatedAmount c s.1
  amount_nonneg s := aggregatedAmount_nonneg c s.1
  total_pos := by
    show 0 < ∑ s : OccurringSpecies c, aggregatedAmount c s.1
    have hfw := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset Component))
      (t := occurringSpecies c)
      (g := c.species)
      (h := fun i _ => Finset.mem_image_of_mem c.species (Finset.mem_univ i))
      (f := c.amount)
    rw [← Finset.sum_subtype (occurringSpecies c) (fun x => Iff.rfl)
      (fun s => aggregatedAmount c s)]
    simp only [aggregatedAmount]
    rw [hfw]
    exact c.total_pos

/-- Merging on the occurring support preserves the total amount. -/
@[simp] theorem total_aggregateOnSupport {Component Species : Type*} [Fintype Component]
    [DecidableEq Species] (c : Composition Component Species) :
    (aggregateOnSupport c).total = c.total := by
  simp only [total]
  change (∑ s : OccurringSpecies c, aggregatedAmount c s.1) = c.total
  rw [← Finset.sum_subtype (occurringSpecies c) (fun x => Iff.rfl)
    (fun s => aggregatedAmount c s)]
  simp only [aggregatedAmount]
  exact Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset Component))
    (t := occurringSpecies c)
    (g := c.species)
    (h := fun i _ => Finset.mem_image_of_mem c.species (Finset.mem_univ i))
    (f := c.amount)

/-- Merging on the occurring support preserves every amount-weighted observable on `Species`,
without requiring a global `[Fintype Species]`. -/
theorem amountWeighted_aggregateOnSupport {Component Species : Type*} [Fintype Component]
    [DecidableEq Species] (c : Composition Component Species) (obs : Species → ℝ) :
    amountWeighted c obs = amountWeighted (aggregateOnSupport c) obs := by
  rw [amountWeighted_eq_regrouped c obs, amountWeighted]
  change (∑ s ∈ occurringSpecies c, aggregatedAmount c s * obs s) =
    ∑ s : OccurringSpecies c, aggregatedAmount c s.1 * obs s.1
  rw [← Finset.sum_subtype (occurringSpecies c) (fun x => Iff.rfl)
    (fun s => aggregatedAmount c s * obs s)]

end Composition

/-! ## Uncertain compositions as sets of complete joint records -/

/-- A complete joint composition record.  The configuration datum of each component is kept
jointly with the amount of the same component, so amount/configuration correlations are not
marginalized away. -/
structure JointCompositionRecord (Component : Type*) (Species : Type*)
    (Configuration : Type*) [Fintype Component] where
  /-- The complete molar composition common to all components of the record. -/
  composition : Composition Component Species
  /-- Per-component configuration datum, indexed jointly with species and amount. -/
  configuration : Component → Configuration

namespace JointCompositionRecord

variable {Component : Type*} {Species : Type*} {Configuration : Type*} [Fintype Component]

/-- Qualitative equimolarity: all components carry the same mole amount.  No numerical
fraction is introduced. -/
def IsEquimolar (r : JointCompositionRecord Component Species Configuration) : Prop :=
  ∀ i j : Component, r.composition.amount i = r.composition.amount j

/-- Qualitative non-equimolarity: some two components carry different mole amounts. -/
def IsNonEquimolar (r : JointCompositionRecord Component Species Configuration) : Prop :=
  ∃ i j : Component, r.composition.amount i ≠ r.composition.amount j

theorem equimolar_or_nonEquimolar (r : JointCompositionRecord Component Species Configuration) :
    r.IsEquimolar ∨ r.IsNonEquimolar := by
  by_cases h : r.IsEquimolar
  · exact Or.inl h
  · obtain ⟨i, hi⟩ := not_forall.mp h
    obtain ⟨j, hj⟩ := not_forall.mp hi
    exact Or.inr ⟨i, j, hj⟩

theorem not_equimolar_and_nonEquimolar
    (r : JointCompositionRecord Component Species Configuration) :
    ¬(r.IsEquimolar ∧ r.IsNonEquimolar) := by
  rintro ⟨he, i, j, hne⟩
  exact hne (he i j)

end JointCompositionRecord

/-- An uncertain composition is a `Set` of complete joint records.

It is *not* a conformational probability distribution: membership records possibility, the
records carry no probabilities or energies, and no stereochemical output is selected.  A
consumer must separately supply any quantitative confidence or physical model. -/
abbrev UncertainComposition (Component Species Configuration : Type*) [Fintype Component] :=
  Set (JointCompositionRecord Component Species Configuration)

/-- Consistency obligation for an uncertain composition: at least one complete joint record.
Without this, subset conclusions would be vacuous. -/
def Consistent {Component Species Configuration : Type*} [Fintype Component]
    (U : UncertainComposition Component Species Configuration) : Prop :=
  U.Nonempty

theorem consistent_iff_nonempty {Component Species Configuration : Type*} [Fintype Component]
    (U : UncertainComposition Component Species Configuration) :
    Consistent U ↔ U.Nonempty := Iff.rfl

theorem consistent_of_mem {Component Species Configuration : Type*} [Fintype Component]
    {U : UncertainComposition Component Species Configuration}
    {r : JointCompositionRecord Component Species Configuration} (hr : r ∈ U) :
    Consistent U :=
  ⟨r, hr⟩

theorem not_consistent_empty {Component Species Configuration : Type*} [Fintype Component] :
    ¬Consistent (∅ : UncertainComposition Component Species Configuration) := by
  simp [Consistent]

/-- The qualitative equimolar subset of an uncertain composition. -/
def equimolarSubset {Component Species Configuration : Type*} [Fintype Component]
    (U : UncertainComposition Component Species Configuration) :
    Set (JointCompositionRecord Component Species Configuration) :=
  {r | r ∈ U ∧ r.IsEquimolar}

/-- The qualitative non-equimolar subset of an uncertain composition. -/
def nonEquimolarSubset {Component Species Configuration : Type*} [Fintype Component]
    (U : UncertainComposition Component Species Configuration) :
    Set (JointCompositionRecord Component Species Configuration) :=
  {r | r ∈ U ∧ r.IsNonEquimolar}

theorem equimolarSubset_subset {Component Species Configuration : Type*} [Fintype Component]
    (U : UncertainComposition Component Species Configuration) :
    equimolarSubset U ⊆ U := by
  intro r hr
  exact hr.1

theorem nonEquimolarSubset_subset {Component Species Configuration : Type*}
    [Fintype Component] (U : UncertainComposition Component Species Configuration) :
    nonEquimolarSubset U ⊆ U := by
  intro r hr
  exact hr.1

/-- The qualitative equimolar and non-equimolar subsets are disjoint. -/
theorem equimolarSubset_disjoint_nonEquimolarSubset {Component Species Configuration : Type*}
    [Fintype Component] (U : UncertainComposition Component Species Configuration) :
    Disjoint (equimolarSubset U) (nonEquimolarSubset U) := by
  rw [Set.disjoint_left]
  intro r he hn
  exact r.not_equimolar_and_nonEquimolar ⟨he.2, hn.2⟩

/-- The two qualitative subsets cover the uncertainty set: every complete record is either
equimolar or non-equimolar. -/
theorem equimolarSubset_union_nonEquimolarSubset {Component Species Configuration : Type*}
    [Fintype Component] (U : UncertainComposition Component Species Configuration) :
    equimolarSubset U ∪ nonEquimolarSubset U = U := by
  ext r
  constructor
  · rintro (⟨hr, _⟩ | ⟨hr, _⟩)
    · exact hr
    · exact hr
  · intro hr
    rcases r.equimolar_or_nonEquimolar with he | hne
    · exact Or.inl ⟨hr, he⟩
    · exact Or.inr ⟨hr, hne⟩

end MolarComposition

end TetraStereo.OneCenter
