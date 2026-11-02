/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly
import TetraStereo.OneCenter.OrganicStereoMolarComposition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sigma.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
























































namespace TetraStereo.OneCenter
namespace OrganicStereoJointAuthorityCellMixtures

noncomputable section

open scoped BigOperators

open OrganicStereoJointAuthorityCellAssembly
open OrganicStereoSpatialSupportMolecularAssembly
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoAuthorityMixedSourceAssembly
open OrganicStereoAllAuthorityEntries
open OccurrenceSpatialSupportExperiment

/-! ## The parameter types of the joint record -/

/-- The ten auxiliary source types of `JointRequest`/`JointRepresentation`, packaged so that the
whole-mixture definitions take one parameter instead of ten.  This is a signature convenience
only: every use below is the dependency's actual `JointRequest` at these types. -/
structure JointParameterTypes where
  /-- The ligand identifier type. -/
  ligandId : Type
  /-- The ligand kind type. -/
  ligandKind : Type
  /-- The fragment identifier type. -/
  fragmentId : Type
  /-- The fragment kind type. -/
  fragmentKind : Type
  /-- The state type. -/
  state : Type
  /-- The framework type. -/
  framework : Type
  /-- The base-name type. -/
  baseName : Type
  /-- The numbering type. -/
  numbering : Type
  /-- The locant type. -/
  locant : Type
  /-- The prefix type. -/
  «prefix» : Type

/-! ## The varying-shape joint case -/

/-- The dependency's concrete request, at a data-determined atom-label count `n`. -/
abbrev JointCaseType (P : JointParameterTypes) (n : ℕ) : Type _ :=
  JointRequest (Fin n) P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state P.framework
    P.baseName P.numbering P.locant P.prefix

/-- The dependency's concrete representation, at a data-determined atom-label count `n`. -/
abbrev NativeJointCaseType (P : JointParameterTypes) (n : ℕ) : Type _ :=
  JointRepresentation (Fin n) P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
    P.framework P.baseName P.numbering P.locant P.prefix

/-- A joint case with a data-determined number of atom labels.  The number `n` is the atom-label
count of the dependency's concrete request over `Fin n`.  The path and band channels inside each
core are independent data: the atom-label count does not determine their sizes. -/
abbrev JointCase (P : JointParameterTypes) : Type _ := Σ n : ℕ, JointCaseType P n

/-- The native image of a joint case, with the same data-determined atom-label count. -/
abbrev NativeJointCase (P : JointParameterTypes) : Type _ := Σ n : ℕ, NativeJointCaseType P n

/-- Assemble a joint case through the dependency's concrete assembly.  The atom-label count is
retained as data. -/
def assembleJointCase (P : JointParameterTypes) (c : JointCase P) : NativeJointCase P :=
  ⟨c.1, assembleJoint c.2⟩

/-- Decode a native joint case through the dependency's concrete decoder.  The atom-label count is
retained as data. -/
def decodeJointCase (P : JointParameterTypes) (c : NativeJointCase P) : JointCase P :=
  ⟨c.1, decodeJoint c.2⟩

@[simp] theorem assembleJointCase_fst (P : JointParameterTypes) (c : JointCase P) :
    (assembleJointCase P c).1 = c.1 := rfl

@[simp] theorem assembleJointCase_snd (P : JointParameterTypes) (c : JointCase P) :
    (assembleJointCase P c).2 = assembleJoint c.2 := rfl

@[simp] theorem decodeJointCase_fst (P : JointParameterTypes) (c : NativeJointCase P) :
    (decodeJointCase P c).1 = c.1 := rfl

@[simp] theorem decodeJointCase_snd (P : JointParameterTypes) (c : NativeJointCase P) :
    (decodeJointCase P c).2 = decodeJoint c.2 := rfl

/-- Decoding the assembled image of a joint case returns exactly that case, including the
atom-label count and the complete dependency request. -/
theorem decodeJointCase_assembleJointCase (P : JointParameterTypes) (c : JointCase P) :
    decodeJointCase P (assembleJointCase P c) = c := by
  obtain ⟨n, request⟩ := c
  simp [assembleJointCase, decodeJointCase, decodeJoint_assembleJoint]

/-- Assembly is injective on the whole joint case, because decoding is a left inverse. -/
theorem assembleJointCase_injective (P : JointParameterTypes) :
    Function.Injective (assembleJointCase P) := by
  intro first second equal
  rw [← decodeJointCase_assembleJointCase P first,
    ← decodeJointCase_assembleJointCase P second, equal]

/-- The image of an arbitrary set of joint cases under assembly.  The whole set is mapped as a
set; it is never replaced by a product of marginals. -/
def assembleJointCaseSet (P : JointParameterTypes) (cases : Set (JointCase P)) :
    Set (NativeJointCase P) :=
  assembleJointCase P '' cases

/-- The image of an arbitrary set of native joint cases under decoding. -/
def decodeJointCaseSet (P : JointParameterTypes) (cases : Set (NativeJointCase P)) :
    Set (JointCase P) :=
  decodeJointCase P '' cases

@[simp] theorem mem_assembleJointCaseSet_iff {P : JointParameterTypes}
    {cases : Set (JointCase P)} {native : NativeJointCase P} :
    native ∈ assembleJointCaseSet P cases ↔ ∃ c ∈ cases, assembleJointCase P c = native :=
  Iff.rfl

@[simp] theorem mem_decodeJointCaseSet_iff {P : JointParameterTypes}
    {cases : Set (NativeJointCase P)} {c : JointCase P} :
    c ∈ decodeJointCaseSet P cases ↔ ∃ native ∈ cases, decodeJointCase P native = c :=
  Iff.rfl

/-- Exact membership recovery for a single joint case. -/
theorem mem_assembleJointCaseSet_image_iff (P : JointParameterTypes)
    (cases : Set (JointCase P)) (c : JointCase P) :
    assembleJointCase P c ∈ assembleJointCaseSet P cases ↔ c ∈ cases := by
  constructor
  · rintro ⟨other, otherMem, equal⟩
    have same : other = c := assembleJointCase_injective P equal
    simpa [same] using otherMem
  · intro member
    exact ⟨c, member, rfl⟩

/-- Decoding the assembled image of an arbitrary set of joint cases recovers that set exactly. -/
theorem decodeJointCaseSet_assembleJointCaseSet (P : JointParameterTypes)
    (cases : Set (JointCase P)) :
    decodeJointCaseSet P (assembleJointCaseSet P cases) = cases := by
  rw [decodeJointCaseSet, assembleJointCaseSet, Set.image_image]
  have identity : (fun c => decodeJointCase P (assembleJointCase P c)) = id := by
    funext c
    exact decodeJointCase_assembleJointCase P c
  rw [identity, Set.image_id]

/-! ## Complete mixture samples -/

/-- One complete mixture sample.

* `k` is the number of constituents and every occurrence is indexed by `Fin k`.
* `cases` is the **actual** whole joint case of each occurrence: the raw chemical authority, the
  physical core and the continuous multicenter cells of that constituent.
* `amounts` are unrestricted real mole amounts, nonnegative with positive total.
* `possible` is the optional per-constituent whole-record possibility set, and `possible_mem`
  records that the supplied actual case belongs to it.

The record preserves every occurrence: two constituents with equal `cases` remain distinct because
they are indexed by distinct `Fin k` points. -/
structure MixtureSample (P : JointParameterTypes) where
  /-- The number of constituents. -/
  k : ℕ
  /-- The actual joint case of every occurrence. -/
  cases : Fin k → JointCase P
  /-- The unrestricted real mole amount of every occurrence. -/
  amounts : Fin k → ℝ
  /-- Every amount is nonnegative. -/
  amount_nonneg : ∀ i, 0 ≤ amounts i
  /-- The total mole amount is strictly positive. -/
  total_pos : 0 < ∑ i, amounts i
  /-- The supplied per-constituent whole-record possibility set. -/
  possible : Fin k → Set (JointCase P)
  /-- The actual case of every occurrence belongs to its own possibility set. -/
  possible_mem : ∀ i, cases i ∈ possible i

/-- Extensionality for complete mixture samples.  All data channels are compared, and the
proposition-valued fields are identified by proof irrelevance. -/
theorem MixtureSample.extEq (P : JointParameterTypes) {first second : MixtureSample P}
    (k : first.k = second.k)
    (cases : HEq first.cases second.cases)
    (amounts : HEq first.amounts second.amounts)
    (possible : HEq first.possible second.possible) : first = second := by
  obtain ⟨firstK, firstCases, firstAmounts, firstNonneg, firstTotal, firstPossible,
    firstMem⟩ := first
  obtain ⟨secondK, secondCases, secondAmounts, secondNonneg, secondTotal, secondPossible,
    secondMem⟩ := second
  dsimp only at k cases amounts possible
  cases k
  have casesEq : firstCases = secondCases := eq_of_heq cases
  have amountsEq : firstAmounts = secondAmounts := eq_of_heq amounts
  have possibleEq : firstPossible = secondPossible := eq_of_heq possible
  cases casesEq
  cases amountsEq
  cases possibleEq
  have nonnegEq : firstNonneg = secondNonneg := Subsingleton.elim _ _
  have totalEq : firstTotal = secondTotal := Subsingleton.elim _ _
  have memEq : firstMem = secondMem := Subsingleton.elim _ _
  cases nonnegEq
  cases totalEq
  cases memEq
  rfl

/-- The actual species datum of one occurrence: the occurrence index retained together with the
whole joint case.  Retaining the index is what prevents deduplication of equal cases. -/
abbrev IndexedCase {P : JointParameterTypes} (s : MixtureSample P) : Type _ :=
  Σ i : Fin s.k, JointCase P

/-- The faithful species composition of a mixture sample.  The species of occurrence `i` is the
pair `⟨i, cases i⟩`, so occurrence identity is part of the species datum; the amount is the actual
mole amount.  This is exactly a `MolarComposition.Composition`. -/
def indexedComposition (P : JointParameterTypes) (s : MixtureSample P) :
    MolarComposition.Composition (Fin s.k) (IndexedCase s) where
  species i := ⟨i, s.cases i⟩
  amount := s.amounts
  amount_nonneg := s.amount_nonneg
  total_pos := s.total_pos

@[simp] theorem indexedComposition_amount (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) : (indexedComposition P s).amount i = s.amounts i := rfl

@[simp] theorem indexedComposition_species (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) : (indexedComposition P s).species i = ⟨i, s.cases i⟩ := rfl

@[simp] theorem indexedComposition_total (P : JointParameterTypes) (s : MixtureSample P) :
    (indexedComposition P s).total = ∑ i, s.amounts i := rfl

/-- The total mole amount of a mixture sample, via the existing molar composition. -/
def total (P : JointParameterTypes) (s : MixtureSample P) : ℝ :=
  (indexedComposition P s).total

@[simp] theorem total_eq_sum (P : JointParameterTypes) (s : MixtureSample P) :
    total P s = ∑ i, s.amounts i := rfl

theorem total_pos' (P : JointParameterTypes) (s : MixtureSample P) : 0 < total P s :=
  s.total_pos

theorem total_ne_zero (P : JointParameterTypes) (s : MixtureSample P) : total P s ≠ 0 :=
  ne_of_gt s.total_pos

/-- The normalized mole fraction of one occurrence. -/
def fraction (P : JointParameterTypes) (s : MixtureSample P) (i : Fin s.k) : ℝ :=
  (indexedComposition P s).fraction i

theorem fraction_nonneg (P : JointParameterTypes) (s : MixtureSample P) (i : Fin s.k) :
    0 ≤ fraction P s i :=
  (indexedComposition P s).fraction_nonneg i

theorem sum_fraction_eq_one (P : JointParameterTypes) (s : MixtureSample P) :
    ∑ i, fraction P s i = 1 :=
  (indexedComposition P s).sum_fraction_eq_one

/-- The amount-weighted observable over the faithful species carrier.  Every occurrence
contributes its actual amount times the observable evaluated at the pair (occurrence, whole joint
case), so identical cases at different occurrences are neither merged nor reordered. -/
def speciesWeighted (P : JointParameterTypes) (s : MixtureSample P)
    (observable : IndexedCase s → ℝ) : ℝ :=
  MolarComposition.Composition.amountWeighted (indexedComposition P s) observable

theorem speciesWeighted_eq_sum (P : JointParameterTypes) (s : MixtureSample P)
    (observable : IndexedCase s → ℝ) :
    speciesWeighted P s observable = ∑ i, s.amounts i * observable ⟨i, s.cases i⟩ := rfl

/-- Occurrence indicator over the faithful species carrier.  It reads exactly one occurrence,
even when two occurrences carry equal joint cases. -/
def occurrenceIndicator {P : JointParameterTypes} (s : MixtureSample P) (i0 : Fin s.k) :
    IndexedCase s → ℝ :=
  fun p => if p.1 = i0 then 1 else 0

/-- Exact recovery of every occurrence amount: the indicator observable reads the actual amount of
that occurrence, with no deduplication of equal cases. -/
theorem speciesWeighted_occurrenceIndicator (P : JointParameterTypes) (s : MixtureSample P)
    (i0 : Fin s.k) :
    speciesWeighted P s (occurrenceIndicator s i0) = s.amounts i0 := by
  rw [speciesWeighted_eq_sum]
  rw [Finset.sum_eq_single i0]
  · simp [occurrenceIndicator]
  · intro i _ different
    simp [occurrenceIndicator, different]
  · intro absent
    exact absurd (Finset.mem_univ i0) absent

/-- The constant observable returns the unrestricted total mole amount. -/
theorem speciesWeighted_one (P : JointParameterTypes) (s : MixtureSample P) :
    speciesWeighted P s (fun _ => 1) = ∑ i, s.amounts i := by
  rw [speciesWeighted_eq_sum]
  simp

/-! ## Native mixture samples -/

/-- One complete native mixture sample.  It contains **no** source `JointCase` and no source
`JointRequest`: every constituent is stored in the dependency's concrete native representation,
and the possibility sets are sets of native cases.  Amounts are preserved literally. -/
structure NativeMixtureSample (P : JointParameterTypes) where
  /-- The number of constituents. -/
  k : ℕ
  /-- The native joint case of every occurrence. -/
  cases : Fin k → NativeJointCase P
  /-- The unrestricted real mole amount of every occurrence. -/
  amounts : Fin k → ℝ
  /-- Every amount is nonnegative. -/
  amount_nonneg : ∀ i, 0 ≤ amounts i
  /-- The total mole amount is strictly positive. -/
  total_pos : 0 < ∑ i, amounts i
  /-- The encoded per-constituent whole-record possibility set. -/
  possible : Fin k → Set (NativeJointCase P)
  /-- The native actual case of every occurrence belongs to its own possibility set. -/
  possible_mem : ∀ i, cases i ∈ possible i

/-! ### The optional possible-set channel

The per-constituent possible-set channel is optional in the concrete sense used by the existing
mixed-source samples: when no restriction is supplied, the full set of all whole joint cases is
used.  This is a legitimate value of the same channel, not a coarse projection. -/

/-- The unrestricted possible-set channel: every whole joint case is admitted at every
occurrence. -/
def fullPossible {P : JointParameterTypes} {k : ℕ} : Fin k → Set (JointCase P) :=
  fun _ => Set.univ

/-- Every actual case belongs to the unrestricted possible-set channel. -/
theorem fullPossible_admissible {P : JointParameterTypes} {k : ℕ} (cases : Fin k → JointCase P) :
    ∀ i, cases i ∈ (fullPossible : Fin k → Set (JointCase P)) i :=
  fun _ => Set.mem_univ _

/-- Sample data with no supplied possible-set restriction. -/
def ofCases {P : JointParameterTypes} {k : ℕ} (cases : Fin k → JointCase P)
    (amounts : Fin k → ℝ) (amount_nonneg : ∀ i, 0 ≤ amounts i)
    (total_pos : 0 < ∑ i, amounts i) : MixtureSample P where
  k := k
  cases := cases
  amounts := amounts
  amount_nonneg := amount_nonneg
  total_pos := total_pos
  possible := fullPossible
  possible_mem := fullPossible_admissible cases

@[simp] theorem ofCases_k {P : JointParameterTypes} {k : ℕ} (cases : Fin k → JointCase P)
    (amounts : Fin k → ℝ) (amount_nonneg : ∀ i, 0 ≤ amounts i)
    (total_pos : 0 < ∑ i, amounts i) :
    (ofCases cases amounts amount_nonneg total_pos).k = k := rfl

@[simp] theorem ofCases_cases {P : JointParameterTypes} {k : ℕ} (cases : Fin k → JointCase P)
    (amounts : Fin k → ℝ) (amount_nonneg : ∀ i, 0 ≤ amounts i)
    (total_pos : 0 < ∑ i, amounts i) :
    (ofCases cases amounts amount_nonneg total_pos).cases = cases := rfl

@[simp] theorem ofCases_possible {P : JointParameterTypes} {k : ℕ}
    (cases : Fin k → JointCase P) (amounts : Fin k → ℝ)
    (amount_nonneg : ∀ i, 0 ≤ amounts i) (total_pos : 0 < ∑ i, amounts i) :
    (ofCases cases amounts amount_nonneg total_pos).possible = fullPossible := rfl

/-- Decoding the unrestricted native possible-set channel is again the unrestricted channel:
decoding is surjective because assembly is a section. -/
theorem decodeJointCaseSet_univ (P : JointParameterTypes) :
    decodeJointCaseSet P (Set.univ : Set (NativeJointCase P)) = Set.univ := by
  apply Set.ext
  intro c
  constructor
  · intro _
    exact Set.mem_univ c
  · intro _
    exact ⟨assembleJointCase P c, Set.mem_univ _, decodeJointCase_assembleJointCase P c⟩

/-- Extensionality for native mixture samples. -/
theorem NativeMixtureSample.extEq (P : JointParameterTypes) {first second : NativeMixtureSample P}
    (k : first.k = second.k)
    (cases : HEq first.cases second.cases)
    (amounts : HEq first.amounts second.amounts)
    (possible : HEq first.possible second.possible) : first = second := by
  obtain ⟨firstK, firstCases, firstAmounts, firstNonneg, firstTotal, firstPossible,
    firstMem⟩ := first
  obtain ⟨secondK, secondCases, secondAmounts, secondNonneg, secondTotal, secondPossible,
    secondMem⟩ := second
  dsimp only at k cases amounts possible
  cases k
  have casesEq : firstCases = secondCases := eq_of_heq cases
  have amountsEq : firstAmounts = secondAmounts := eq_of_heq amounts
  have possibleEq : firstPossible = secondPossible := eq_of_heq possible
  cases casesEq
  cases amountsEq
  cases possibleEq
  have nonnegEq : firstNonneg = secondNonneg := Subsingleton.elim _ _
  have totalEq : firstTotal = secondTotal := Subsingleton.elim _ _
  have memEq : firstMem = secondMem := Subsingleton.elim _ _
  cases nonnegEq
  cases totalEq
  cases memEq
  rfl

/-- The faithful native species composition; the occurrence index is retained exactly as in
`indexedComposition`. -/
abbrev NativeIndexedCase {P : JointParameterTypes} (s : NativeMixtureSample P) : Type _ :=
  Σ i : Fin s.k, NativeJointCase P

/-- The native faithful species composition. -/
def nativeIndexedComposition (P : JointParameterTypes) (s : NativeMixtureSample P) :
    MolarComposition.Composition (Fin s.k) (NativeIndexedCase s) where
  species i := ⟨i, s.cases i⟩
  amount := s.amounts
  amount_nonneg := s.amount_nonneg
  total_pos := s.total_pos

/-! ## Encoding and decoding complete mixtures -/

/-- Encode a complete mixture sample: every constituent's whole joint case is assembled, the
amounts are preserved literally, and every whole-record possibility set is mapped as a whole
set. -/
def encodeSample (P : JointParameterTypes) (s : MixtureSample P) : NativeMixtureSample P where
  k := s.k
  cases i := assembleJointCase P (s.cases i)
  amounts := s.amounts
  amount_nonneg := s.amount_nonneg
  total_pos := s.total_pos
  possible i := assembleJointCaseSet P (s.possible i)
  possible_mem i := ⟨s.cases i, s.possible_mem i, rfl⟩

/-- Decode a complete native mixture sample: every native constituent case is decoded through the
dependency's concrete decoder, and every native possibility set is decoded as a whole set.  No
original source record is consulted. -/
def decodeSample (P : JointParameterTypes) (s : NativeMixtureSample P) : MixtureSample P where
  k := s.k
  cases i := decodeJointCase P (s.cases i)
  amounts := s.amounts
  amount_nonneg := s.amount_nonneg
  total_pos := s.total_pos
  possible i := decodeJointCaseSet P (s.possible i)
  possible_mem i := ⟨s.cases i, s.possible_mem i, rfl⟩

@[simp] theorem encodeSample_k (P : JointParameterTypes) (s : MixtureSample P) :
    (encodeSample P s).k = s.k := rfl

/-- Encoding preserves the atom-label count `n` of every occurrence.  Two samples with different
`n` remain different after encoding and can therefore coexist in one outer set; the path and band
channels are separate data, not a function of `n`. -/
@[simp] theorem encodeSample_case_nat (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) : ((encodeSample P s).cases i).1 = (s.cases i).1 := rfl

/-- Decoding preserves the atom-label count `n` of every native occurrence. -/
@[simp] theorem decodeSample_case_nat (P : JointParameterTypes) (s : NativeMixtureSample P)
    (i : Fin s.k) : ((decodeSample P s).cases i).1 = (s.cases i).1 := rfl

@[simp] theorem encodeSample_cases (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) :
    (encodeSample P s).cases i = assembleJointCase P (s.cases i) := rfl

@[simp] theorem encodeSample_amounts (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) : (encodeSample P s).amounts i = s.amounts i := rfl

@[simp] theorem encodeSample_possible (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) :
    (encodeSample P s).possible i = assembleJointCaseSet P (s.possible i) := rfl

@[simp] theorem decodeSample_k (P : JointParameterTypes) (s : NativeMixtureSample P) :
    (decodeSample P s).k = s.k := rfl

@[simp] theorem decodeSample_cases (P : JointParameterTypes) (s : NativeMixtureSample P)
    (i : Fin s.k) : (decodeSample P s).cases i = decodeJointCase P (s.cases i) := rfl

@[simp] theorem decodeSample_amounts (P : JointParameterTypes) (s : NativeMixtureSample P)
    (i : Fin s.k) : (decodeSample P s).amounts i = s.amounts i := rfl

@[simp] theorem decodeSample_possible (P : JointParameterTypes) (s : NativeMixtureSample P)
    (i : Fin s.k) :
    (decodeSample P s).possible i = decodeJointCaseSet P (s.possible i) := rfl

/-- The decoded quantities are computed solely from the native sample: no source record is
consulted. -/
theorem decodeSample_from_native (P : JointParameterTypes) (s : NativeMixtureSample P) :
    ((decodeSample P s).cases = fun i => decodeJointCase P (s.cases i)) ∧
      ((decodeSample P s).amounts = s.amounts) ∧
      ((decodeSample P s).possible = fun i => decodeJointCaseSet P (s.possible i)) :=
  ⟨rfl, rfl, rfl⟩

/-- A no-restriction sample stays no-restriction on the source side after encoding: its encoded
possible-set channel is the image of the full channel.  (The image of `Set.univ` is not claimed to
be `Set.univ`; only the left inverse is part of the dependency contract.) -/
@[simp] theorem encodeSample_ofCases_possible {P : JointParameterTypes} {k : ℕ}
    (cases : Fin k → JointCase P) (amounts : Fin k → ℝ)
    (amount_nonneg : ∀ i, 0 ≤ amounts i) (total_pos : 0 < ∑ i, amounts i) (i : Fin k) :
    (encodeSample P (ofCases cases amounts amount_nonneg total_pos)).possible i =
      assembleJointCaseSet P (Set.univ : Set (JointCase P)) := rfl

/-- **Whole-mixture inverse.**  Decoding the encoded image of a complete mixture sample recovers
the entire original sample: every occurrence's actual whole joint case, every amount, every
per-constituent whole-record possibility set and the constituent count. -/
theorem decodeSample_encodeSample (P : JointParameterTypes) (s : MixtureSample P) :
    decodeSample P (encodeSample P s) = s := by
  refine MixtureSample.extEq P (first := decodeSample P (encodeSample P s)) (second := s)
    (k := rfl) ?_ ?_ ?_
  · apply heq_of_eq
    funext i
    exact decodeJointCase_assembleJointCase P (s.cases i)
  · apply heq_of_eq
    rfl
  · apply heq_of_eq
    funext i
    exact decodeJointCaseSet_assembleJointCaseSet P (s.possible i)

/-- Encoding is injective on complete mixture samples, because decoding is a left inverse. -/
theorem encodeSample_injective (P : JointParameterTypes) :
    Function.Injective (encodeSample P) := by
  intro first second equal
  rw [← decodeSample_encodeSample P first, ← decodeSample_encodeSample P second, equal]

/-- An equality of encoded samples is exactly an equality of source samples. -/
theorem encodeSample_eq_iff (P : JointParameterTypes) (first second : MixtureSample P) :
    encodeSample P first = encodeSample P second ↔ first = second :=
  ⟨fun equal => encodeSample_injective P equal, fun equal => congrArg (encodeSample P) equal⟩

/-- Encoding preserves every amount. -/
theorem encodeSample_amounts_eq (P : JointParameterTypes) (s : MixtureSample P) :
    (encodeSample P s).amounts = s.amounts := rfl

/-- Encoding preserves the total mole amount. -/
theorem encodeSample_total (P : JointParameterTypes) (s : MixtureSample P) :
    (∑ i, (encodeSample P s).amounts i) = ∑ i, s.amounts i := rfl

/-! ### Preservation of the full source core, including the path and band channels

The whole-mixture inverse recovers the dependency's complete source record, so every internal
channel of the core — graph, conformation, ordered role ledger, optional coordinates, optional
path family and optional band attachment — is recovered exactly. -/

/-- The decoded core of every occurrence is exactly the supplied core. -/
theorem decodeSample_encodeSample_core (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) :
    (decodeJoint (assembleJoint (s.cases i).2)).spatial.core = (s.cases i).2.spatial.core :=
  decodeJoint_assembleJoint_core _

/-- The decoded optional rational-coordinate channel is exactly the supplied channel. -/
theorem decodeSample_encodeSample_rationalPositions? (P : JointParameterTypes)
    (s : MixtureSample P) (i : Fin s.k) :
    (decodeJoint (assembleJoint (s.cases i).2)).spatial.core.rationalPositions? =
      (s.cases i).2.spatial.core.rationalPositions? :=
  decodeJoint_assembleJoint_rationalPositions? _

/-- The decoded optional path family is exactly the supplied family; in particular every path
count inside the core is preserved. -/
theorem decodeSample_encodeSample_paths? (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) :
    (decodeJoint (assembleJoint (s.cases i).2)).spatial.core.paths? =
      (s.cases i).2.spatial.core.paths? :=
  decodeJoint_assembleJoint_paths? _

/-- The decoded optional band attachment is exactly the supplied attachment; in particular every
band count inside the core is preserved. -/
theorem decodeSample_encodeSample_bands? (P : JointParameterTypes) (s : MixtureSample P)
    (i : Fin s.k) :
    (decodeJoint (assembleJoint (s.cases i).2)).spatial.core.bands? =
      (s.cases i).2.spatial.core.bands? :=
  decodeJoint_assembleJoint_bands? _

/-! ## Outer sets of complete samples -/

/-- The image of an arbitrary outer set of complete mixture samples.  Membership is joint: the
whole sample, including the cross-constituent and state/amount correlations it carries, is mapped
as one record. -/
def encodeMixtureSet (P : JointParameterTypes) (samples : Set (MixtureSample P)) :
    Set (NativeMixtureSample P) :=
  encodeSample P '' samples

/-- The image of an arbitrary outer set of native mixture samples under decoding. -/
def decodeMixtureSet (P : JointParameterTypes) (samples : Set (NativeMixtureSample P)) :
    Set (MixtureSample P) :=
  decodeSample P '' samples

@[simp] theorem mem_encodeMixtureSet_iff {P : JointParameterTypes}
    {samples : Set (MixtureSample P)} {native : NativeMixtureSample P} :
    native ∈ encodeMixtureSet P samples ↔ ∃ s ∈ samples, encodeSample P s = native :=
  Iff.rfl

@[simp] theorem mem_decodeMixtureSet_iff {P : JointParameterTypes}
    {samples : Set (NativeMixtureSample P)} {s : MixtureSample P} :
    s ∈ decodeMixtureSet P samples ↔ ∃ native ∈ samples, decodeSample P native = s :=
  Iff.rfl

/-- Exact membership recovery at the level of one complete sample.  A sample's encoded image lies
in the encoded outer set exactly when the sample lies in the original outer set.  This is an exact
joint statement, not a product of per-constituent marginals. -/
theorem mem_encodeMixtureSet_image_iff (P : JointParameterTypes)
    (samples : Set (MixtureSample P)) (s : MixtureSample P) :
    encodeSample P s ∈ encodeMixtureSet P samples ↔ s ∈ samples := by
  constructor
  · rintro ⟨other, otherMem, equal⟩
    have same : other = s := encodeSample_injective P equal
    simpa [same] using otherMem
  · intro member
    exact ⟨s, member, rfl⟩

/-- Decoding the image of an arbitrary outer set of complete mixture samples recovers that set
exactly.  Cross-constituent correlations, unequal constituent counts and unequal atom-label counts
are all recovered because each complete sample is encoded as one record. -/
theorem decodeMixtureSet_encodeMixtureSet (P : JointParameterTypes)
    (samples : Set (MixtureSample P)) :
    decodeMixtureSet P (encodeMixtureSet P samples) = samples := by
  rw [decodeMixtureSet, encodeMixtureSet, Set.image_image]
  have identity : (fun s => decodeSample P (encodeSample P s)) = id := by
    funext s
    exact decodeSample_encodeSample P s
  rw [identity, Set.image_id]

/-- The outer-set encoding is injective: two outer sets with the same encoded image are equal. -/
theorem encodeMixtureSet_injective (P : JointParameterTypes) :
    Function.Injective (encodeMixtureSet P) := by
  intro first second equal
  rw [← decodeMixtureSet_encodeMixtureSet P first,
    ← decodeMixtureSet_encodeMixtureSet P second, equal]

/-- Consistency (nonemptiness) is preserved and reflected by the outer-set encoding. -/
@[simp] theorem nonempty_encodeMixtureSet_iff (P : JointParameterTypes)
    (samples : Set (MixtureSample P)) :
    (encodeMixtureSet P samples).Nonempty ↔ samples.Nonempty :=
  ⟨fun ⟨_, s, member, _⟩ => ⟨s, member⟩,
    fun ⟨s, member⟩ => ⟨encodeSample P s, s, member, rfl⟩⟩

/-! ### Varying constituent and atom-label counts in one outer set

The outer set is a set of complete samples, so samples of different constituent count `k` and
different atom-label counts `n` coexist in it without any common-shape restriction. -/

/-- The constituent count of a sample. -/
def constituentCount (P : JointParameterTypes) (s : MixtureSample P) : ℕ := s.k

/-- The set of atom-label counts occurring in a sample.  This is the `n`-shape of the sample; the
path and band channels inside each core are part of the recovered whole request. -/
def caseCounts (P : JointParameterTypes) (s : MixtureSample P) : Set ℕ :=
  Set.range fun i => (s.cases i).1

/-- The native constituent count. -/
def nativeConstituentCount (P : JointParameterTypes) (s : NativeMixtureSample P) : ℕ := s.k

/-- The native atom-label-count shape. -/
def nativeCaseCounts (P : JointParameterTypes) (s : NativeMixtureSample P) : Set ℕ :=
  Set.range fun i => (s.cases i).1

@[simp] theorem encodeSample_constituentCount (P : JointParameterTypes) (s : MixtureSample P) :
    (encodeSample P s).k = constituentCount P s := rfl

@[simp] theorem encodeSample_caseCounts (P : JointParameterTypes) (s : MixtureSample P) :
    nativeCaseCounts P (encodeSample P s) = caseCounts P s := by
  apply Set.ext
  intro n
  constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, hi⟩

@[simp] theorem decodeSample_constituentCount (P : JointParameterTypes)
    (s : NativeMixtureSample P) :
    (decodeSample P s).k = nativeConstituentCount P s := rfl

@[simp] theorem decodeSample_caseCounts (P : JointParameterTypes)
    (s : NativeMixtureSample P) :
    caseCounts P (decodeSample P s) = nativeCaseCounts P s := by
  apply Set.ext
  intro n
  constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, hi⟩

/-- Two members of one outer set with different `k` or different `n`-shape remain distinct after
encoding and both are present in the encoded outer set.  This is the same-outer-set varying-shape
statement; no common constituent count or atom-label count is imposed. -/
theorem encoded_members_distinct_of_shape_ne (P : JointParameterTypes)
    (samples : Set (MixtureSample P)) {s t : MixtureSample P}
    (sMem : s ∈ samples) (tMem : t ∈ samples)
    (different : s.k ≠ t.k ∨ caseCounts P s ≠ caseCounts P t) :
    encodeSample P s ∈ encodeMixtureSet P samples ∧
      encodeSample P t ∈ encodeMixtureSet P samples ∧ encodeSample P s ≠ encodeSample P t := by
  refine ⟨⟨s, sMem, rfl⟩, ⟨t, tMem, rfl⟩, ?_⟩
  intro equal
  have same : s = t := encodeSample_injective P equal
  cases same
  rcases different with different | different
  · exact different rfl
  · exact different rfl

/-- A single complete sample, as an outer uncertainty set. -/
def singletonUncertainty (P : JointParameterTypes) (s : MixtureSample P) :
    Set (MixtureSample P) :=
  {s}

theorem mem_singletonUncertainty (P : JointParameterTypes) (s : MixtureSample P) :
    s ∈ singletonUncertainty P s := by
  simp [singletonUncertainty]










/-- The two constituent cases of a two-constituent sample. -/
def pairCases {P : JointParameterTypes} (a b : JointCase P) : Fin 2 → JointCase P :=
  Fin.cons a fun _ => b

@[simp] theorem pairCases_zero {P : JointParameterTypes} (a b : JointCase P) :
    pairCases a b 0 = a :=
  Fin.cons_zero _ _

@[simp] theorem pairCases_one {P : JointParameterTypes} (a b : JointCase P) :
    pairCases a b (1 : Fin 2) = b := by
  simpa [pairCases] using Fin.cons_succ a (fun _ : Fin 1 => b) 0

/-- The two constituent amounts of a two-constituent sample. -/
def pairAmounts (amount0 amount1 : ℝ) : Fin 2 → ℝ :=
  Fin.cons amount0 fun _ => amount1

@[simp] theorem pairAmounts_zero (amount0 amount1 : ℝ) :
    pairAmounts amount0 amount1 0 = amount0 :=
  Fin.cons_zero _ _

@[simp] theorem pairAmounts_one (amount0 amount1 : ℝ) :
    pairAmounts amount0 amount1 (1 : Fin 2) = amount1 := by
  simpa [pairAmounts] using Fin.cons_succ amount0 (fun _ : Fin 1 => amount1) 0

/-- A two-constituent mixture sample with equal unit amounts.  Both occurrences have the same
constant whole-record possibility set `support`; the actual cases are `a` and `b`. -/
def pairSample (P : JointParameterTypes) (support : Set (JointCase P)) (a b : JointCase P)
    (aMem : a ∈ support) (bMem : b ∈ support) : MixtureSample P where
  k := 2
  cases := pairCases a b
  amounts := fun _ => 1
  amount_nonneg := fun _ => by norm_num
  total_pos := by
    rw [Fin.sum_univ_two]
    norm_num
  possible := fun _ => support
  possible_mem := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [pairCases] using aMem
    · intro j
      simpa [pairCases] using bMem

@[simp] theorem pairSample_k (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) :
    (pairSample P support a b aMem bMem).k = 2 := rfl

@[simp] theorem pairSample_cases_zero (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) :
    (pairSample P support a b aMem bMem).cases (0 : Fin 2) = a := rfl

@[simp] theorem pairSample_cases_one (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) :
    (pairSample P support a b aMem bMem).cases (1 : Fin 2) = b := by
  simpa [pairSample] using pairCases_one a b

@[simp] theorem pairSample_amounts (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) (i : Fin 2) :
    (pairSample P support a b aMem bMem).amounts i = 1 := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem pairSample_possible (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) (i : Fin 2) :
    (pairSample P support a b aMem bMem).possible i = support := rfl

/-- A two-constituent mixture sample with arbitrary real amounts.  Occurrence identity is
retained: the amount of occurrence `0` and the amount of occurrence `1` are stored
independently. -/
def pairSampleWithAmounts (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support)
    (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0) (amount1_nonneg : 0 ≤ amount1)
    (totalAmount_pos : 0 < amount0 + amount1) : MixtureSample P where
  k := 2
  cases := pairCases a b
  amounts := pairAmounts amount0 amount1
  amount_nonneg := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [pairAmounts] using amount0_nonneg
    · intro j
      simpa [pairAmounts] using amount1_nonneg
  total_pos := by
    rw [Fin.sum_univ_two, pairAmounts_zero, pairAmounts_one]
    exact totalAmount_pos
  possible := fun _ => support
  possible_mem := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [pairCases] using aMem
    · intro j
      simpa [pairCases] using bMem

@[simp] theorem pairSampleWithAmounts_cases_zero (P : JointParameterTypes)
    (support : Set (JointCase P)) (a b : JointCase P) (aMem : a ∈ support)
    (bMem : b ∈ support) (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0)
    (amount1_nonneg : 0 ≤ amount1) (totalAmount_pos : 0 < amount0 + amount1) :
    (pairSampleWithAmounts P support a b aMem bMem amount0 amount1 amount0_nonneg
      amount1_nonneg totalAmount_pos).cases (0 : Fin 2) = a := rfl

@[simp] theorem pairSampleWithAmounts_cases_one (P : JointParameterTypes)
    (support : Set (JointCase P)) (a b : JointCase P) (aMem : a ∈ support)
    (bMem : b ∈ support) (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0)
    (amount1_nonneg : 0 ≤ amount1) (totalAmount_pos : 0 < amount0 + amount1) :
    (pairSampleWithAmounts P support a b aMem bMem amount0 amount1 amount0_nonneg
      amount1_nonneg totalAmount_pos).cases (1 : Fin 2) = b := by
  simpa [pairSampleWithAmounts] using pairCases_one a b

@[simp] theorem pairSampleWithAmounts_possible (P : JointParameterTypes)
    (support : Set (JointCase P)) (a b : JointCase P) (aMem : a ∈ support)
    (bMem : b ∈ support) (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0)
    (amount1_nonneg : 0 ≤ amount1) (totalAmount_pos : 0 < amount0 + amount1)
    (i : Fin 2) :
    (pairSampleWithAmounts P support a b aMem bMem amount0 amount1 amount0_nonneg
      amount1_nonneg totalAmount_pos).possible i = support := rfl

@[simp] theorem pairSampleWithAmounts_k (P : JointParameterTypes)
    (support : Set (JointCase P)) (a b : JointCase P) (aMem : a ∈ support)
    (bMem : b ∈ support) (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0)
    (amount1_nonneg : 0 ≤ amount1) (totalAmount_pos : 0 < amount0 + amount1) :
    (pairSampleWithAmounts P support a b aMem bMem amount0 amount1 amount0_nonneg
      amount1_nonneg totalAmount_pos).k = 2 := rfl

@[simp] theorem pairSampleWithAmounts_amounts_zero (P : JointParameterTypes)
    (support : Set (JointCase P)) (a b : JointCase P) (aMem : a ∈ support)
    (bMem : b ∈ support) (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0)
    (amount1_nonneg : 0 ≤ amount1) (totalAmount_pos : 0 < amount0 + amount1) :
    (pairSampleWithAmounts P support a b aMem bMem amount0 amount1 amount0_nonneg
      amount1_nonneg totalAmount_pos).amounts (0 : Fin 2) = amount0 := rfl

@[simp] theorem pairSampleWithAmounts_amounts_one (P : JointParameterTypes)
    (support : Set (JointCase P)) (a b : JointCase P) (aMem : a ∈ support)
    (bMem : b ∈ support) (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0)
    (amount1_nonneg : 0 ≤ amount1) (totalAmount_pos : 0 < amount0 + amount1) :
    (pairSampleWithAmounts P support a b aMem bMem amount0 amount1 amount0_nonneg
      amount1_nonneg totalAmount_pos).amounts (1 : Fin 2) = amount1 := by
  simpa [pairSampleWithAmounts] using pairAmounts_one amount0 amount1

/-- The diagonal outer uncertainty set: both constituents always carry the same case. -/
def diagonalUncertainty (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    Set (MixtureSample P) :=
  {pairSample P support f0 f0 f0Mem f0Mem, pairSample P support f1 f1 f1Mem f1Mem}

/-- The antidiagonal outer uncertainty set: the two constituents always carry opposite cases. -/
def antidiagonalUncertainty (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    Set (MixtureSample P) :=
  {pairSample P support f0 f1 f0Mem f1Mem, pairSample P support f1 f0 f1Mem f0Mem}

theorem diagonal_f0_f0_mem (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    pairSample P support f0 f0 f0Mem f0Mem ∈
      diagonalUncertainty P support f0 f1 f0Mem f1Mem := by
  simp [diagonalUncertainty]

theorem diagonal_f1_f1_mem (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    pairSample P support f1 f1 f1Mem f1Mem ∈
      diagonalUncertainty P support f0 f1 f0Mem f1Mem := by
  simp [diagonalUncertainty]

theorem antidiagonal_f0_f1_mem (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    pairSample P support f0 f1 f0Mem f1Mem ∈
      antidiagonalUncertainty P support f0 f1 f0Mem f1Mem := by
  simp [antidiagonalUncertainty]

theorem antidiagonal_f1_f0_mem (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    pairSample P support f1 f0 f1Mem f0Mem ∈
      antidiagonalUncertainty P support f0 f1 f0Mem f1Mem := by
  simp [antidiagonalUncertainty]

/-- The non-dependent first-constituent observation. -/
def caseAtZero (P : JointParameterTypes) (s : MixtureSample P) : Option (JointCase P) :=
  if h : 0 < s.k then some (s.cases ⟨0, h⟩) else none

/-- The non-dependent second-constituent observation. -/
def caseAtOne (P : JointParameterTypes) (s : MixtureSample P) : Option (JointCase P) :=
  if h : 1 < s.k then some (s.cases ⟨1, h⟩) else none

/-- The non-dependent occurrence-zero amount observation. -/
def amountAtZero (P : JointParameterTypes) (s : MixtureSample P) : Option ℝ :=
  if h : 0 < s.k then some (s.amounts ⟨0, h⟩) else none

/-- The non-dependent occurrence-one amount observation. -/
def amountAtOne (P : JointParameterTypes) (s : MixtureSample P) : Option ℝ :=
  if h : 1 < s.k then some (s.amounts ⟨1, h⟩) else none

/-- The native occurrence-zero amount observation. -/
def nativeAmountAtZero (P : JointParameterTypes) (s : NativeMixtureSample P) : Option ℝ :=
  if h : 0 < s.k then some (s.amounts ⟨0, h⟩) else none

/-- The native occurrence-one amount observation. -/
def nativeAmountAtOne (P : JointParameterTypes) (s : NativeMixtureSample P) : Option ℝ :=
  if h : 1 < s.k then some (s.amounts ⟨1, h⟩) else none

@[simp] theorem nativeAmountAtZero_encodeSample (P : JointParameterTypes)
    (s : MixtureSample P) :
    nativeAmountAtZero P (encodeSample P s) = amountAtZero P s := by
  unfold nativeAmountAtZero amountAtZero
  rfl

@[simp] theorem nativeAmountAtOne_encodeSample (P : JointParameterTypes)
    (s : MixtureSample P) :
    nativeAmountAtOne P (encodeSample P s) = amountAtOne P s := by
  unfold nativeAmountAtOne amountAtOne
  rfl

@[simp] theorem caseAtZero_pairSample (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) :
    caseAtZero P (pairSample P support a b aMem bMem) = some a := by
  simp [caseAtZero, pairSample]

@[simp] theorem caseAtOne_pairSample (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) :
    caseAtOne P (pairSample P support a b aMem bMem) = some b := by
  simp [caseAtOne, pairSample]

@[simp] theorem amountAtZero_pairSample (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) :
    amountAtZero P (pairSample P support a b aMem bMem) = some 1 := by
  simp [amountAtZero, pairSample]

@[simp] theorem amountAtOne_pairSample (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) :
    amountAtOne P (pairSample P support a b aMem bMem) = some 1 := by
  simp [amountAtOne, pairSample]

@[simp] theorem amountAtZero_pairSampleWithAmounts (P : JointParameterTypes)
    (support : Set (JointCase P)) (a b : JointCase P) (aMem : a ∈ support)
    (bMem : b ∈ support) (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0)
    (amount1_nonneg : 0 ≤ amount1) (totalAmount_pos : 0 < amount0 + amount1) :
    amountAtZero P (pairSampleWithAmounts P support a b aMem bMem amount0 amount1 amount0_nonneg
      amount1_nonneg totalAmount_pos) = some amount0 := by
  simp [amountAtZero, pairSampleWithAmounts]

@[simp] theorem amountAtOne_pairSampleWithAmounts (P : JointParameterTypes)
    (support : Set (JointCase P)) (a b : JointCase P) (aMem : a ∈ support)
    (bMem : b ∈ support) (amount0 amount1 : ℝ) (amount0_nonneg : 0 ≤ amount0)
    (amount1_nonneg : 0 ≤ amount1) (totalAmount_pos : 0 < amount0 + amount1) :
    amountAtOne P (pairSampleWithAmounts P support a b aMem bMem amount0 amount1 amount0_nonneg
      amount1_nonneg totalAmount_pos) = some amount1 := by
  simp [amountAtOne, pairSampleWithAmounts]

/-- The first-constituent marginal of an outer set of complete samples.  It is the set of actual
cases appearing at occurrence `0`; it is a projection of the outer set, not a product factor. -/
def firstMargin (P : JointParameterTypes) (samples : Set (MixtureSample P)) :
    Set (JointCase P) :=
  {c | ∃ s ∈ samples, caseAtZero P s = some c}

/-- The second-constituent marginal of an outer set of complete samples. -/
def secondMargin (P : JointParameterTypes) (samples : Set (MixtureSample P)) :
    Set (JointCase P) :=
  {c | ∃ s ∈ samples, caseAtOne P s = some c}

theorem firstMargin_diagonal (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    firstMargin P (diagonalUncertainty P support f0 f1 f0Mem f1Mem) = {f0, f1} := by
  apply Set.ext
  intro c
  constructor
  · rintro ⟨s, sMem, sValue⟩
    simp only [diagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at sMem
    rcases sMem with rfl | rfl
    · rw [caseAtZero_pairSample] at sValue
      have : c = f0 := (Option.some.injEq _ _).mp sValue.symm
      simp [this]
    · rw [caseAtZero_pairSample] at sValue
      have : c = f1 := (Option.some.injEq _ _).mp sValue.symm
      simp [this]
  · intro cMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at cMem
    rcases cMem with hc | hc
    · rw [hc]
      exact ⟨pairSample P support f0 f0 f0Mem f0Mem,
        diagonal_f0_f0_mem P support f0 f1 f0Mem f1Mem, by simp [caseAtZero, pairSample]⟩
    · rw [hc]
      exact ⟨pairSample P support f1 f1 f1Mem f1Mem,
        diagonal_f1_f1_mem P support f0 f1 f0Mem f1Mem, by simp [caseAtZero, pairSample]⟩

theorem firstMargin_antidiagonal (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    firstMargin P (antidiagonalUncertainty P support f0 f1 f0Mem f1Mem) = {f0, f1} := by
  apply Set.ext
  intro c
  constructor
  · rintro ⟨s, sMem, sValue⟩
    simp only [antidiagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at sMem
    rcases sMem with rfl | rfl
    · rw [caseAtZero_pairSample] at sValue
      have : c = f0 := (Option.some.injEq _ _).mp sValue.symm
      simp [this]
    · rw [caseAtZero_pairSample] at sValue
      have : c = f1 := (Option.some.injEq _ _).mp sValue.symm
      simp [this]
  · intro cMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at cMem
    rcases cMem with hc | hc
    · rw [hc]
      exact ⟨pairSample P support f0 f1 f0Mem f1Mem,
        antidiagonal_f0_f1_mem P support f0 f1 f0Mem f1Mem, by simp [caseAtZero, pairSample]⟩
    · rw [hc]
      exact ⟨pairSample P support f1 f0 f1Mem f0Mem,
        antidiagonal_f1_f0_mem P support f0 f1 f0Mem f1Mem, by simp [caseAtZero, pairSample]⟩

theorem secondMargin_diagonal (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    secondMargin P (diagonalUncertainty P support f0 f1 f0Mem f1Mem) = {f0, f1} := by
  apply Set.ext
  intro c
  constructor
  · rintro ⟨s, sMem, sValue⟩
    simp only [diagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at sMem
    rcases sMem with rfl | rfl
    · rw [caseAtOne_pairSample] at sValue
      have : c = f0 := (Option.some.injEq _ _).mp sValue.symm
      simp [this]
    · rw [caseAtOne_pairSample] at sValue
      have : c = f1 := (Option.some.injEq _ _).mp sValue.symm
      simp [this]
  · intro cMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at cMem
    rcases cMem with hc | hc
    · rw [hc]
      exact ⟨pairSample P support f0 f0 f0Mem f0Mem,
        diagonal_f0_f0_mem P support f0 f1 f0Mem f1Mem, by simp [caseAtOne, pairSample]⟩
    · rw [hc]
      exact ⟨pairSample P support f1 f1 f1Mem f1Mem,
        diagonal_f1_f1_mem P support f0 f1 f0Mem f1Mem, by simp [caseAtOne, pairSample]⟩

theorem secondMargin_antidiagonal (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    secondMargin P (antidiagonalUncertainty P support f0 f1 f0Mem f1Mem) = {f0, f1} := by
  apply Set.ext
  intro c
  constructor
  · rintro ⟨s, sMem, sValue⟩
    simp only [antidiagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at sMem
    rcases sMem with rfl | rfl
    · rw [caseAtOne_pairSample] at sValue
      have : c = f1 := (Option.some.injEq _ _).mp sValue.symm
      simp [this]
    · rw [caseAtOne_pairSample] at sValue
      have : c = f0 := (Option.some.injEq _ _).mp sValue.symm
      simp [this]
  · intro cMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at cMem
    rcases cMem with hc | hc
    · rw [hc]
      exact ⟨pairSample P support f1 f0 f1Mem f0Mem,
        antidiagonal_f1_f0_mem P support f0 f1 f0Mem f1Mem, by simp [caseAtOne, pairSample]⟩
    · rw [hc]
      exact ⟨pairSample P support f0 f1 f0Mem f1Mem,
        antidiagonal_f0_f1_mem P support f0 f1 f0Mem f1Mem, by simp [caseAtOne, pairSample]⟩

/-- **Same constituent marginals.**  The first-coordinate marginals of the diagonal and
antidiagonal outer sets are literally equal. -/
theorem diagonal_antidiagonal_same_firstMargin (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    firstMargin P (diagonalUncertainty P support f0 f1 f0Mem f1Mem) =
      firstMargin P (antidiagonalUncertainty P support f0 f1 f0Mem f1Mem) := by
  rw [firstMargin_diagonal, firstMargin_antidiagonal]

/-- **Same constituent marginals.**  The second-coordinate marginals are also literally equal. -/
theorem diagonal_antidiagonal_same_secondMargin (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    secondMargin P (diagonalUncertainty P support f0 f1 f0Mem f1Mem) =
      secondMargin P (antidiagonalUncertainty P support f0 f1 f0Mem f1Mem) := by
  rw [secondMargin_diagonal, secondMargin_antidiagonal]

/-- **Different joint sets.**  Even though the two marginals agree, the diagonal and antidiagonal
outer sets are different whenever the two cases are different. -/
theorem diagonal_ne_antidiagonal (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) (different : f0 ≠ f1) :
    diagonalUncertainty P support f0 f1 f0Mem f1Mem ≠
      antidiagonalUncertainty P support f0 f1 f0Mem f1Mem := by
  intro equal
  have member : pairSample P support f0 f1 f0Mem f1Mem ∈
      diagonalUncertainty P support f0 f1 f0Mem f1Mem := by
    rw [equal]
    exact antidiagonal_f0_f1_mem P support f0 f1 f0Mem f1Mem
  simp only [diagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with same | same
  · have observed := congrArg (caseAtOne P) same
    rw [caseAtOne_pairSample, caseAtOne_pairSample] at observed
    exact different ((Option.some.injEq _ _).mp observed).symm
  · have observed := congrArg (caseAtZero P) same
    rw [caseAtZero_pairSample, caseAtZero_pairSample] at observed
    exact different ((Option.some.injEq _ _).mp observed)

/-- **The inner channel does not encode cross-constituent correlation.**  Every sample of both
outer sets has the *same* constant per-constituent possibility channel `fun _ => support`.
Consequently no per-constituent possibility set can distinguish the diagonal from the
antidiagonal; the distinction lives only in the outer set. -/
theorem diagonal_antidiagonal_same_inner_possible (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    (∀ s ∈ diagonalUncertainty P support f0 f1 f0Mem f1Mem, s.possible = fun _ => support) ∧
      (∀ s ∈ antidiagonalUncertainty P support f0 f1 f0Mem f1Mem,
        s.possible = fun _ => support) := by
  constructor
  · intro s sMem
    simp only [diagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at sMem
    rcases sMem with rfl | rfl <;> funext i <;> rfl
  · intro s sMem
    simp only [antidiagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at sMem
    rcases sMem with rfl | rfl <;> funext i <;> rfl

/-- All four fixture samples have equal positive unit amounts. -/
theorem diagonal_antidiagonal_unit_amounts (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    (∀ s ∈ diagonalUncertainty P support f0 f1 f0Mem f1Mem, ∀ i, s.amounts i = 1) ∧
      (∀ s ∈ antidiagonalUncertainty P support f0 f1 f0Mem f1Mem, ∀ i, s.amounts i = 1) := by
  constructor
  · intro s sMem
    simp only [diagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at sMem
    rcases sMem with rfl | rfl <;> intro i <;> simp
  · intro s sMem
    simp only [antidiagonalUncertainty, Set.mem_insert_iff, Set.mem_singleton_iff] at sMem
    rcases sMem with rfl | rfl <;> intro i <;> simp

/-- **Encoded outer sets remain distinct and decode exactly.**  The encoded diagonal and
antidiagonal uncertainty sets are different, and each is recovered exactly by decoding. -/
theorem diagonal_antidiagonal_encoded_distinct_and_decodes (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) (different : f0 ≠ f1) :
    encodeMixtureSet P (diagonalUncertainty P support f0 f1 f0Mem f1Mem) ≠
        encodeMixtureSet P (antidiagonalUncertainty P support f0 f1 f0Mem f1Mem) ∧
      decodeMixtureSet P (encodeMixtureSet P
        (diagonalUncertainty P support f0 f1 f0Mem f1Mem)) =
        diagonalUncertainty P support f0 f1 f0Mem f1Mem ∧
      decodeMixtureSet P (encodeMixtureSet P
        (antidiagonalUncertainty P support f0 f1 f0Mem f1Mem)) =
        antidiagonalUncertainty P support f0 f1 f0Mem f1Mem := by
  refine ⟨?_, decodeMixtureSet_encodeMixtureSet P _, decodeMixtureSet_encodeMixtureSet P _⟩
  intro equal
  exact diagonal_ne_antidiagonal P support f0 f1 f0Mem f1Mem different
    (encodeMixtureSet_injective P equal)

/-- The two-constituent `n`-shape of the pair sample: every occurrence carries a case with the
same atom-label count. -/
theorem pairSample_caseCounts (P : JointParameterTypes) (support : Set (JointCase P))
    (a b : JointCase P) (aMem : a ∈ support) (bMem : b ∈ support) (n : ℕ)
    (ha : a.1 = n) (hb : b.1 = n) :
    caseCounts P (pairSample P support a b aMem bMem) = {n} := by
  apply Set.ext
  intro m
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ ?_ i
    · intro hi
      simpa using hi.symm.trans ha
    · intro j hi
      simpa using hi.symm.trans hb
  · intro hm
    have hm' : m = n := by simpa using hm
    refine ⟨⟨0, by simp [pairSample]⟩, ?_⟩
    exact ha.trans hm'.symm

/-! ### Varying amounts correlated with states, with occurrence identity retained -/



def correlatedForward (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    MixtureSample P :=
  pairSampleWithAmounts P support f0 f1 f0Mem f1Mem 1 3 (by norm_num) (by norm_num)
    (by norm_num)

/-- The swapped configuration: the same two states and the same two amounts, but the occurrences
(and hence the state/amount pairing by index) are swapped. -/
def correlatedSwapped (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    MixtureSample P :=
  pairSampleWithAmounts P support f1 f0 f1Mem f0Mem 3 1 (by norm_num) (by norm_num)
    (by norm_num)

/-- An outer uncertainty set whose two complete samples have the same multiset of states and the
same multiset of amounts, but different state/amount correlation over the occurrence indices. -/
def amountCorrelatedUncertainty (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    Set (MixtureSample P) :=
  {correlatedForward P support f0 f1 f0Mem f1Mem,
    correlatedSwapped P support f0 f1 f0Mem f1Mem}

@[simp] theorem amountAtZero_correlatedForward (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    amountAtZero P (correlatedForward P support f0 f1 f0Mem f1Mem) = some 1 := by
  simp [correlatedForward]

@[simp] theorem amountAtOne_correlatedForward (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    amountAtOne P (correlatedForward P support f0 f1 f0Mem f1Mem) = some 3 := by
  simp [correlatedForward]

@[simp] theorem amountAtZero_correlatedSwapped (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    amountAtZero P (correlatedSwapped P support f0 f1 f0Mem f1Mem) = some 3 := by
  simp [correlatedSwapped]

@[simp] theorem amountAtOne_correlatedSwapped (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    amountAtOne P (correlatedSwapped P support f0 f1 f0Mem f1Mem) = some 1 := by
  simp [correlatedSwapped]



theorem amount_correlated_with_state (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    (correlatedForward P support f0 f1 f0Mem f1Mem).cases (0 : Fin 2) = f0 ∧
      (correlatedForward P support f0 f1 f0Mem f1Mem).amounts (0 : Fin 2) = 1 ∧
      (correlatedForward P support f0 f1 f0Mem f1Mem).cases (1 : Fin 2) = f1 ∧
      (correlatedForward P support f0 f1 f0Mem f1Mem).amounts (1 : Fin 2) = 3 ∧
      (correlatedSwapped P support f0 f1 f0Mem f1Mem).cases (0 : Fin 2) = f1 ∧
      (correlatedSwapped P support f0 f1 f0Mem f1Mem).amounts (0 : Fin 2) = 3 ∧
      (correlatedSwapped P support f0 f1 f0Mem f1Mem).cases (1 : Fin 2) = f0 ∧
        (correlatedSwapped P support f0 f1 f0Mem f1Mem).amounts (1 : Fin 2) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [correlatedForward, correlatedSwapped]

/-- The two amount-correlated samples are different after encoding: their occurrence-one amounts
are `3` and `1` respectively. -/
theorem amountCorrelated_members_distinct (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    encodeSample P (correlatedForward P support f0 f1 f0Mem f1Mem) ≠
      encodeSample P (correlatedSwapped P support f0 f1 f0Mem f1Mem) := by
  intro equal
  have observed := congrArg (nativeAmountAtOne P) equal
  rw [nativeAmountAtOne_encodeSample, nativeAmountAtOne_encodeSample,
    amountAtOne_correlatedForward, amountAtOne_correlatedSwapped] at observed
  have numeric : (3 : ℝ) = 1 := (Option.some.injEq _ _).mp observed
  norm_num at numeric

/-- The amount-correlated outer set is recovered exactly by the whole-set round trip. -/
theorem amountCorrelated_decode_exact (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    decodeMixtureSet P (encodeMixtureSet P
      (amountCorrelatedUncertainty P support f0 f1 f0Mem f1Mem)) =
      amountCorrelatedUncertainty P support f0 f1 f0Mem f1Mem :=
  decodeMixtureSet_encodeMixtureSet P
    (amountCorrelatedUncertainty P support f0 f1 f0Mem f1Mem)

/-- Both amount-correlated samples are present in the outer set. -/
theorem amountCorrelated_both_mem (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    correlatedForward P support f0 f1 f0Mem f1Mem ∈
        amountCorrelatedUncertainty P support f0 f1 f0Mem f1Mem ∧
      correlatedSwapped P support f0 f1 f0Mem f1Mem ∈
        amountCorrelatedUncertainty P support f0 f1 f0Mem f1Mem := by
  simp [amountCorrelatedUncertainty]

/-! ### Equal cases at two occurrences are not deduplicated -/



def repeatedCaseSample (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    MixtureSample P :=
  pairSampleWithAmounts P support f0 f0 f0Mem f0Mem 1 3 (by norm_num) (by norm_num)
    (by norm_num)

theorem repeatedCaseSample_cases_equal (P : JointParameterTypes) (support : Set (JointCase P))
    (f0 f1 : JointCase P) (f0Mem : f0 ∈ support) (f1Mem : f1 ∈ support) :
    (repeatedCaseSample P support f0 f1 f0Mem f1Mem).cases (0 : Fin 2) =
      (repeatedCaseSample P support f0 f1 f0Mem f1Mem).cases (1 : Fin 2) := by
  simp [repeatedCaseSample]

theorem repeatedCaseSample_encoded_cases_equal (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    (encodeSample P (repeatedCaseSample P support f0 f1 f0Mem f1Mem)).cases (0 : Fin 2) =
      (encodeSample P (repeatedCaseSample P support f0 f1 f0Mem f1Mem)).cases (1 : Fin 2) := by
  change assembleJointCase P
      ((repeatedCaseSample P support f0 f1 f0Mem f1Mem).cases (0 : Fin 2)) =
    assembleJointCase P
      ((repeatedCaseSample P support f0 f1 f0Mem f1Mem).cases (1 : Fin 2))
  rw [repeatedCaseSample_cases_equal]

theorem repeatedCaseSample_amounts_differ (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    (repeatedCaseSample P support f0 f1 f0Mem f1Mem).amounts (0 : Fin 2) = 1 ∧
      (repeatedCaseSample P support f0 f1 f0Mem f1Mem).amounts (1 : Fin 2) = 3 := by
  simp [repeatedCaseSample]

/-- Occurrence identity is retained: the occurrence indicator reads the amount of occurrence `0`
exactly, even though both occurrences carry the same case. -/
theorem repeatedCaseSample_occurrence_zero (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    speciesWeighted P (repeatedCaseSample P support f0 f1 f0Mem f1Mem)
      (occurrenceIndicator (repeatedCaseSample P support f0 f1 f0Mem f1Mem) (0 : Fin 2)) =
      1 := by
  rw [speciesWeighted_occurrenceIndicator]
  simp [repeatedCaseSample]

/-- The occurrence indicator reads the amount of occurrence `1` exactly. -/
theorem repeatedCaseSample_occurrence_one (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    speciesWeighted P (repeatedCaseSample P support f0 f1 f0Mem f1Mem)
      (occurrenceIndicator (repeatedCaseSample P support f0 f1 f0Mem f1Mem) (1 : Fin 2)) =
      3 := by
  rw [speciesWeighted_occurrenceIndicator]
  simp [repeatedCaseSample]

/-- Encoding also retains both occurrence amounts, so decoding cannot merge the two equal
cases. -/
theorem repeatedCaseSample_encoded_amounts_differ (P : JointParameterTypes)
    (support : Set (JointCase P)) (f0 f1 : JointCase P) (f0Mem : f0 ∈ support)
    (f1Mem : f1 ∈ support) :
    (encodeSample P (repeatedCaseSample P support f0 f1 f0Mem f1Mem)).amounts (0 : Fin 2) = 1 ∧
      (encodeSample P (repeatedCaseSample P support f0 f1 f0Mem f1Mem)).amounts (1 : Fin 2) =
        3 := by
  change (repeatedCaseSample P support f0 f1 f0Mem f1Mem).amounts (0 : Fin 2) = 1 ∧
    (repeatedCaseSample P support f0 f1 f0Mem f1Mem).amounts (1 : Fin 2) = 3
  simp [repeatedCaseSample]

/-! ### A generic one-constituent sample

This constructor is used by the varying-shape fixture in the fixtures module; it is kept in the
generic core because it accepts an arbitrary joint case and an arbitrary possible set. -/

/-- A one-constituent sample. -/
def singleCaseSample (P : JointParameterTypes) (c : JointCase P)
    (possible : Set (JointCase P)) (mem : c ∈ possible) : MixtureSample P where
  k := 1
  cases := fun _ => c
  amounts := fun _ => 1
  amount_nonneg := fun _ => by norm_num
  total_pos := by
    rw [Fin.sum_univ_one]
    norm_num
  possible := fun _ => possible
  possible_mem := fun _ => mem

@[simp] theorem singleCaseSample_k (P : JointParameterTypes) (c : JointCase P)
    (possible : Set (JointCase P)) (mem : c ∈ possible) :
    (singleCaseSample P c possible mem).k = 1 := rfl

@[simp] theorem singleCaseSample_cases (P : JointParameterTypes) (c : JointCase P)
    (possible : Set (JointCase P)) (mem : c ∈ possible) (i : Fin 1) :
    (singleCaseSample P c possible mem).cases i = c := rfl

@[simp] theorem singleCaseSample_amounts (P : JointParameterTypes) (c : JointCase P)
    (possible : Set (JointCase P)) (mem : c ∈ possible) (i : Fin 1) :
    (singleCaseSample P c possible mem).amounts i = 1 := rfl

theorem singleCaseSample_caseCounts (P : JointParameterTypes) (c : JointCase P)
    (possible : Set (JointCase P)) (mem : c ∈ possible) :
    caseCounts P (singleCaseSample P c possible mem) = {c.1} := by
  apply Set.ext
  intro m
  constructor
  · rintro ⟨i, hi⟩
    simpa [singleCaseSample] using hi.symm
  · intro hm
    have hm' : m = c.1 := by simpa using hm
    exact ⟨⟨0, by simp [singleCaseSample]⟩, hm'.symm⟩

end

end OrganicStereoJointAuthorityCellMixtures
end TetraStereo.OneCenter
