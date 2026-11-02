import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.CIPRule2MassDataGenerated

set_option autoImplicit false

namespace TetraStereo.OneCenter.CIPRule2MassData

/-!
# Frozen exact mass data for CIP Sequence Rule 2

The two data classes used here must not be conflated:

* ordinary-element values come from the IUPAC periodic table dated 4 May 2022, based on the CIAAW
  2021 standard-atomic-weight report;
* explicit nuclides use CIAAW's 17 March 2021 CSV of AME records through AME-2020.

Both inputs are byte-verified by `tools/generate_cip_rule2_mass_data.py`.  Decimal source values are
represented exactly as integers scaled by `10^12`; no floating-point arithmetic or secondary
rounding occurs in Lean.  Ordinary H, CIAAW monoisotopic elements, and bracketed radioactive
elements use the exact AME mass of their reference nuclide.  This realizes the explicit P-92.3
identity `H = ¹H` and prevents rounding from distinguishing an ordinary monoisotopic element from
the same explicitly labelled nuclide.
-/

abbrev MassPico := Nat

def scale : Nat := Generated.picoDaltonScale

structure FrozenMassSource where
  title : String
  url : String
  sha256 : String
  recordCount : Nat
  deriving DecidableEq, Repr

def periodicTable2022 : FrozenMassSource where
  title := "IUPAC Periodic Table of the Elements, 4 May 2022"
  url :=
    "https://iupac.org/wp-content/uploads/2022/07/" ++
      "IUPAC_Periodic_Table-04May22_CRA.pdf"
  sha256 := Generated.periodicTable2022Sha256
  recordCount := Generated.ordinaryWeightRecordCount

def isotopeMasses2020 : FrozenMassSource where
  title := "CIAAW AME-recommended nuclide masses, latest records through AME-2020"
  url := "https://ciaaw.org/data/IUPAC-atomic-masses.csv"
  sha256 := Generated.isotopeMasses2020CsvSha256
  recordCount := Generated.isotopeMassRecordCount

/-- Atomic numbers 1 through 118, in source order. -/
def currentAtomicNumbers : List Nat := (List.range 118).map Nat.succ

/-- Structurally recursive mass-number lookup in one element's sorted frozen table. -/
def lookupMassNumber? : List (Nat × MassPico) → Nat → Option MassPico
  | [], _ => none
  | record :: rest, massNumber =>
      if record.1 = massNumber then some record.2
      else lookupMassNumber? rest massNumber

def isotopeAtomicMassPico? (atomicNumber massNumber : Nat) : Option MassPico :=
  lookupMassNumber? (Generated.isotopeMassesPico atomicNumber) massNumber

/-- Rule-2 value of an ordinary atom.  Exact-nuclide references override the displayed abridged
value; genuinely multi-isotopic ordinary elements use the displayed conventional value. -/
def ordinaryAtomicMassPico? (atomicNumber : Nat) : Option MassPico :=
  match Generated.ordinaryNuclideReferenceMassNumber? atomicNumber with
  | some massNumber => isotopeAtomicMassPico? atomicNumber massNumber
  | none => Generated.ordinaryAtomicWeightPico? atomicNumber

/-- Total source lookup for a semantic atom spelling.  `none` means ordinary unlabelled isotopic
composition; `some A` means the explicitly labelled nuclide of mass number `A`. -/
def rule2MassPico? (atomicNumber : Nat) : Option Nat → Option MassPico
  | none => ordinaryAtomicMassPico? atomicNumber
  | some massNumber => isotopeAtomicMassPico? atomicNumber massNumber

/-- All frozen nuclide keys, paired with atomic number. -/
def supportedNuclides : List (Nat × Nat) :=
  currentAtomicNumbers.flatMap fun atomicNumber =>
    (Generated.isotopeMassesPico atomicNumber).map fun record =>
      (atomicNumber, record.1)

/-- Source-order validity: mass numbers and exact masses both increase strictly within one
element, and every stored exact mass is positive. -/
def ValidIsotopeMassList (records : List (Nat × MassPico)) : Prop :=
  records.Pairwise fun left right => left.1 < right.1 ∧ left.2 < right.2

def validIsotopeMassList? : List (Nat × MassPico) → Bool
  | [] => true
  | first :: rest =>
      rest.all (fun second => decide (first.1 < second.1) && decide (first.2 < second.2)) &&
        validIsotopeMassList? rest

@[simp] theorem validIsotopeMassList?_eq_true_iff (records : List (Nat × MassPico)) :
    validIsotopeMassList? records = true ↔ ValidIsotopeMassList records := by
  induction records with
  | nil => simp [validIsotopeMassList?, ValidIsotopeMassList]
  | cons first rest inductionHypothesis =>
      simp [validIsotopeMassList?, ValidIsotopeMassList, inductionHypothesis]

theorem currentAtomicNumbers_exact :
    currentAtomicNumbers = List.range' 1 118 := by
  decide

theorem all_current_atomic_numbers_have_an_ordinary_value :
    currentAtomicNumbers.all
      (fun atomicNumber => (ordinaryAtomicMassPico? atomicNumber).isSome) = true := by
  decide

theorem every_current_atomic_number_has_an_ordinary_value
    (atomicNumber : Nat) (membership : atomicNumber ∈ currentAtomicNumbers) :
    ∃ mass, ordinaryAtomicMassPico? atomicNumber = some mass := by
  have present := (List.all_eq_true.mp
    all_current_atomic_numbers_have_an_ordinary_value) atomicNumber membership
  exact Option.isSome_iff_exists.mp present

theorem all_current_atomic_numbers_have_isotope_data :
    currentAtomicNumbers.all
      (fun atomicNumber => !(Generated.isotopeMassesPico atomicNumber).isEmpty) = true := by
  decide

theorem every_current_atomic_number_has_isotope_data
    (atomicNumber : Nat) (membership : atomicNumber ∈ currentAtomicNumbers) :
    Generated.isotopeMassesPico atomicNumber ≠ [] := by
  have present := (List.all_eq_true.mp
    all_current_atomic_numbers_have_isotope_data) atomicNumber membership
  simpa using present

theorem all_isotope_mass_lists_are_valid :
    currentAtomicNumbers.all
      (fun atomicNumber =>
        validIsotopeMassList? (Generated.isotopeMassesPico atomicNumber)) = true := by
  decide

theorem every_isotope_mass_list_is_valid
    (atomicNumber : Nat) (membership : atomicNumber ∈ currentAtomicNumbers) :
    ValidIsotopeMassList (Generated.isotopeMassesPico atomicNumber) := by
  have valid := (List.all_eq_true.mp all_isotope_mass_lists_are_valid)
    atomicNumber membership
  exact (validIsotopeMassList?_eq_true_iff _).mp valid

/-- A small structural aggregate used to compose the global 3,557-record count without asking
the kernel to normalize the entire flattened table in one recursion chain. -/
private def isotopeChunkCount (start count : Nat) : Nat :=
  ((List.range' start count).map fun atomicNumber =>
    (Generated.isotopeMassesPico atomicNumber).length).sum

private theorem isotopeChunkCount_1_10 : isotopeChunkCount 1 10 = 143 := by decide
private theorem isotopeChunkCount_11_20 : isotopeChunkCount 11 10 = 250 := by decide
private theorem isotopeChunkCount_21_30 : isotopeChunkCount 21 10 = 313 := by decide
private theorem isotopeChunkCount_31_40 : isotopeChunkCount 31 10 = 342 := by decide
private theorem isotopeChunkCount_41_50 : isotopeChunkCount 41 10 = 409 := by decide
private theorem isotopeChunkCount_51_60 : isotopeChunkCount 51 10 = 416 := by decide
private theorem isotopeChunkCount_61_70 : isotopeChunkCount 61 10 = 396 := by decide
private theorem isotopeChunkCount_71_80 : isotopeChunkCount 71 10 = 419 := by decide
private theorem isotopeChunkCount_81_90 : isotopeChunkCount 81 10 = 384 := by decide
private theorem isotopeChunkCount_91_100 : isotopeChunkCount 91 10 = 245 := by decide
private theorem isotopeChunkCount_101_110 : isotopeChunkCount 101 10 = 173 := by decide
private theorem isotopeChunkCount_111_118 : isotopeChunkCount 111 8 = 67 := by decide

theorem supportedNuclides_count :
    supportedNuclides.length = Generated.isotopeMassRecordCount := by
  rw [supportedNuclides, List.length_flatMap]
  simp only [List.length_map]
  rw [currentAtomicNumbers_exact]
  change isotopeChunkCount 1 118 = Generated.isotopeMassRecordCount
  unfold isotopeChunkCount
  rw [show 118 = 10 + 108 by omega, ← List.range'_append_1]
  rw [show 108 = 10 + 98 by omega, ← List.range'_append_1]
  rw [show 98 = 10 + 88 by omega, ← List.range'_append_1]
  rw [show 88 = 10 + 78 by omega, ← List.range'_append_1]
  rw [show 78 = 10 + 68 by omega, ← List.range'_append_1]
  rw [show 68 = 10 + 58 by omega, ← List.range'_append_1]
  rw [show 58 = 10 + 48 by omega, ← List.range'_append_1]
  rw [show 48 = 10 + 38 by omega, ← List.range'_append_1]
  rw [show 38 = 10 + 28 by omega, ← List.range'_append_1]
  rw [show 28 = 10 + 18 by omega, ← List.range'_append_1]
  rw [show 18 = 10 + 8 by omega, ← List.range'_append_1]
  simp only [List.map_append, List.sum_append]
  change isotopeChunkCount 1 10 + isotopeChunkCount 11 10 +
    isotopeChunkCount 21 10 + isotopeChunkCount 31 10 +
    isotopeChunkCount 41 10 + isotopeChunkCount 51 10 +
    isotopeChunkCount 61 10 + isotopeChunkCount 71 10 +
    isotopeChunkCount 81 10 + isotopeChunkCount 91 10 +
    isotopeChunkCount 101 10 + isotopeChunkCount 111 8 =
      Generated.isotopeMassRecordCount
  rw [isotopeChunkCount_1_10, isotopeChunkCount_11_20,
    isotopeChunkCount_21_30, isotopeChunkCount_31_40,
    isotopeChunkCount_41_50, isotopeChunkCount_51_60,
    isotopeChunkCount_61_70, isotopeChunkCount_71_80,
    isotopeChunkCount_81_90, isotopeChunkCount_91_100,
    isotopeChunkCount_101_110, isotopeChunkCount_111_118]
  rfl

theorem supportedNuclides_nodup : supportedNuclides.Nodup := by
  rw [supportedNuclides, List.nodup_flatMap]
  constructor
  · intro atomicNumber atomicPresent
    have valid := every_isotope_mass_list_is_valid atomicNumber atomicPresent
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact valid.imp fun {left right} ordered equality => by
      have massNumberEquality := congrArg Prod.snd equality
      exact (Nat.ne_of_lt ordered.1) massNumberEquality
  · have atomicNumbersNodup : currentAtomicNumbers.Nodup := by
      rw [currentAtomicNumbers_exact]
      exact List.nodup_range'
    apply atomicNumbersNodup.imp
    intro left right distinct
    change List.Disjoint
      ((Generated.isotopeMassesPico left).map fun record => (left, record.1))
      ((Generated.isotopeMassesPico right).map fun record => (right, record.1))
    rw [List.disjoint_left]
    intro nuclide leftPresent rightPresent
    rw [List.mem_map] at leftPresent rightPresent
    obtain ⟨leftRecord, _leftRecordPresent, leftIdentity⟩ := leftPresent
    obtain ⟨rightRecord, _rightRecordPresent, rightIdentity⟩ := rightPresent
    rw [← leftIdentity] at rightIdentity
    exact distinct (congrArg Prod.fst rightIdentity).symm

theorem every_supported_nuclide_has_current_atomic_number :
    ∀ nuclide, nuclide ∈ supportedNuclides →
      0 < nuclide.1 ∧ nuclide.1 ≤ 118 := by
  intro nuclide present
  rw [supportedNuclides, List.mem_flatMap] at present
  obtain ⟨atomicNumber, atomicPresent, recordPresent⟩ := present
  rw [List.mem_map] at recordPresent
  obtain ⟨record, _recordPresent, identity⟩ := recordPresent
  subst nuclide
  rw [currentAtomicNumbers_exact, List.mem_range'] at atomicPresent
  omega

@[simp] theorem rule2MassPico?_explicit (atomicNumber massNumber : Nat) :
    rule2MassPico? atomicNumber (some massNumber) =
      isotopeAtomicMassPico? atomicNumber massNumber := rfl

@[simp] theorem rule2MassPico?_ordinary (atomicNumber : Nat) :
    rule2MassPico? atomicNumber none = ordinaryAtomicMassPico? atomicNumber := rfl

/-- The Blue Book's explicit `¹H (or H)` identity is exact in the encoded datum. -/
@[simp] theorem ordinary_hydrogen_eq_protium :
    rule2MassPico? 1 none = rule2MassPico? 1 (some 1) := by
  decide

/-- Deuterium has a strictly larger Rule-2 datum than ordinary/protium hydrogen. -/
theorem ordinary_hydrogen_lt_deuterium :
    (rule2MassPico? 1 none).getD 0 < (rule2MassPico? 1 (some 2)).getD 0 := by
  decide

/-- Monoisotopic iodine is not spuriously separated by the abridged periodic-table rounding. -/
@[simp] theorem ordinary_iodine_eq_iodine127 :
    rule2MassPico? 53 none = rule2MassPico? 53 (some 127) := by
  decide

/-- The P-92.3 bromine example is reproduced by exact AME and ordinary values. -/
theorem bromine81_gt_ordinary_gt_bromine79 :
    (rule2MassPico? 35 (some 79)).getD 0 < (rule2MassPico? 35 none).getD 0 ∧
      (rule2MassPico? 35 none).getD 0 < (rule2MassPico? 35 (some 81)).getD 0 := by
  decide

/-- Natural oxygen is slightly heavier than oxygen-16; picodalton scale preserves this close
ordering without the previous microdalton rounding boundary. -/
theorem oxygen16_lt_ordinary_oxygen :
    (rule2MassPico? 8 (some 16)).getD 0 < (rule2MassPico? 8 none).getD 0 := by
  decide

/-- An arbitrary syntactic isotope label absent from the frozen physical nuclide table is refused. -/
@[simp] theorem carbon999_is_unknown : rule2MassPico? 6 (some 999) = none := by
  decide

end TetraStereo.OneCenter.CIPRule2MassData
