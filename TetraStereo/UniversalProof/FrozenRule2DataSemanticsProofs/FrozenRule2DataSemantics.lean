import TetraStereo.OneCenter.CIPRule2MassData
import TetraStereo.OneCenter.CIAAWStandardAtomicWeights2021Generated
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 4096





























namespace TetraStereo.UniversalProof.FrozenRule2DataSemanticsProofs.FrozenRule2DataSemantics

open TetraStereo.OneCenter.CIPRule2MassData

open TetraStereo.OneCenter

/-! ## Primitive record families -/

/-- One row of the frozen ordinary periodic table: a listed atomic number paired with its displayed
abridged standard-atomic-weight value scaled exactly by `10^12`. -/
structure PeriodicElementRecord where
  atomicNumber : Nat
  ordinaryWeightPico : MassPico
  deriving DecidableEq, Repr

/-- One exact nuclide record: atomic number, mass number and the AME-2020 mass scaled by `10^12`. -/
structure IsotopeMassRecord where
  atomicNumber : Nat
  massNumber : Nat
  exactMassPico : MassPico
  deriving DecidableEq, Repr

/-- A source decimal written as an integer part, a fractional part and the number of fractional
digits actually written.  The bound is the exact-precision budget of the picodalton scale. -/
structure DecimalPico where
  whole : Nat
  fraction : Nat
  fractionalDigits : Nat
  digitsBound : fractionalDigits ≤ 12
  fractionBound : fraction < 10 ^ fractionalDigits

namespace DecimalPico

/-- Exact base-10 scaling of the written decimal by `10^12`; no truncation or floating rounding is
performed. -/
def value (decimal : DecimalPico) : Nat :=
  decimal.whole * Generated.picoDaltonScale +
    decimal.fraction * 10 ^ (12 - decimal.fractionalDigits)

end DecimalPico

/-- The no-floating-rounding judgement: the stored integer is exactly the base-10 scaling of a
witnessed source decimal of at most twelve fractional digits.  The witness must also carry the
fractional-width invariant. This arithmetic judgment alone does not bind external source bytes. -/
def ExactDecimalScale (stored : Nat) (decimal : DecimalPico) : Prop := stored = decimal.value

/-- Independent source-level judgement: the frozen 4 May 2022 IUPAC table lists an element with this
atomic number.  This is the mathematical range relation, not a lookup into the generated function. -/
def PeriodicTableAdmits (atomicNumber : Nat) : Prop := 1 ≤ atomicNumber ∧ atomicNumber ≤ 118

/-! ## Frozen record lists extracted from the validated generated table -/

/-- The frozen ordinary-table rows: exactly those current atomic numbers the generated
ordinary-weight lookup answers. -/
def periodicTableRecords : List PeriodicElementRecord :=
  currentAtomicNumbers.filterMap fun atomicNumber =>
    (Generated.ordinaryAtomicWeightPico? atomicNumber).map fun weight =>
      ⟨atomicNumber, weight⟩




def standardWeightRecords : List (Nat × CIAAWStandardAtomicWeights2021.Entry) :=
  [
    (1, (.interval 1007840000000 1008110000000)),
    (2, (.value 4002602000000 2000000)),
    (3, (.interval 6938000000000 6997000000000)),
    (4, (.value 9012183100000 500000)),
    (5, (.interval 10806000000000 10821000000000)),
    (6, (.interval 12009600000000 12011600000000)),
    (7, (.interval 14006430000000 14007280000000)),
    (8, (.interval 15999030000000 15999770000000)),
    (9, (.value 18998403162000 5000)),
    (10, (.value 20179700000000 600000000)),
    (11, (.value 22989769280000 20000)),
    (12, (.interval 24304000000000 24307000000000)),
    (13, (.value 26981538400000 300000)),
    (14, (.interval 28084000000000 28086000000000)),
    (15, (.value 30973761998000 5000)),
    (16, (.interval 32059000000000 32076000000000)),
    (17, (.interval 35446000000000 35457000000000)),
    (18, (.interval 39792000000000 39963000000000)),
    (19, (.value 39098300000000 100000000)),
    (20, (.value 40078000000000 4000000000)),
    (21, (.value 44955907000000 4000000)),
    (22, (.value 47867000000000 1000000000)),
    (23, (.value 50941500000000 100000000)),
    (24, (.value 51996100000000 600000000)),
    (25, (.value 54938043000000 2000000)),
    (26, (.value 55845000000000 2000000000)),
    (27, (.value 58933194000000 3000000)),
    (28, (.value 58693400000000 400000000)),
    (29, (.value 63546000000000 3000000000)),
    (30, (.value 65380000000000 20000000000)),
    (31, (.value 69723000000000 1000000000)),
    (32, (.value 72630000000000 8000000000)),
    (33, (.value 74921595000000 6000000)),
    (34, (.value 78971000000000 8000000000)),
    (35, (.interval 79901000000000 79907000000000)),
    (36, (.value 83798000000000 2000000000)),
    (37, (.value 85467800000000 300000000)),
    (38, (.value 87620000000000 10000000000)),
    (39, (.value 88905838000000 2000000)),
    (40, (.value 91224000000000 2000000000)),
    (41, (.value 92906370000000 10000000)),
    (42, (.value 95950000000000 10000000000)),
    (43, .noStandardWeight),
    (44, (.value 101070000000000 20000000000)),
    (45, (.value 102905490000000 20000000)),
    (46, (.value 106420000000000 10000000000)),
    (47, (.value 107868200000000 200000000)),
    (48, (.value 112414000000000 4000000000)),
    (49, (.value 114818000000000 1000000000)),
    (50, (.value 118710000000000 7000000000)),
    (51, (.value 121760000000000 1000000000)),
    (52, (.value 127600000000000 30000000000)),
    (53, (.value 126904470000000 30000000)),
    (54, (.value 131293000000000 6000000000)),
    (55, (.value 132905451960000 60000)),
    (56, (.value 137327000000000 7000000000)),
    (57, (.value 138905470000000 70000000)),
    (58, (.value 140116000000000 1000000000)),
    (59, (.value 140907660000000 10000000)),
    (60, (.value 144242000000000 3000000000)),
    (61, .noStandardWeight),
    (62, (.value 150360000000000 20000000000)),
    (63, (.value 151964000000000 1000000000)),
    (64, (.value 157250000000000 30000000000)),
    (65, (.value 158925354000000 7000000)),
    (66, (.value 162500000000000 1000000000)),
    (67, (.value 164930329000000 5000000)),
    (68, (.value 167259000000000 3000000000)),
    (69, (.value 168934219000000 5000000)),
    (70, (.value 173045000000000 10000000000)),
    (71, (.value 174966800000000 100000000)),
    (72, (.value 178486000000000 6000000000)),
    (73, (.value 180947880000000 20000000)),
    (74, (.value 183840000000000 10000000000)),
    (75, (.value 186207000000000 1000000000)),
    (76, (.value 190230000000000 30000000000)),
    (77, (.value 192217000000000 2000000000)),
    (78, (.value 195084000000000 9000000000)),
    (79, (.value 196966570000000 4000000)),
    (80, (.value 200592000000000 3000000000)),
    (81, (.interval 204382000000000 204385000000000)),
    (82, (.interval 206140000000000 207940000000000)),
    (83, (.value 208980400000000 10000000)),
    (84, .noStandardWeight),
    (85, .noStandardWeight),
    (86, .noStandardWeight),
    (87, .noStandardWeight),
    (88, .noStandardWeight),
    (89, .noStandardWeight),
    (90, (.value 232037700000000 400000000)),
    (91, (.value 231035880000000 10000000)),
    (92, (.value 238028910000000 30000000)),
    (93, .noStandardWeight),
    (94, .noStandardWeight),
    (95, .noStandardWeight),
    (96, .noStandardWeight),
    (97, .noStandardWeight),
    (98, .noStandardWeight),
    (99, .noStandardWeight),
    (100, .noStandardWeight),
    (101, .noStandardWeight),
    (102, .noStandardWeight),
    (103, .noStandardWeight),
    (104, .noStandardWeight),
    (105, .noStandardWeight),
    (106, .noStandardWeight),
    (107, .noStandardWeight),
    (108, .noStandardWeight),
    (109, .noStandardWeight),
    (110, .noStandardWeight),
    (111, .noStandardWeight),
    (112, .noStandardWeight),
    (113, .noStandardWeight),
    (114, .noStandardWeight),
    (115, .noStandardWeight),
    (116, .noStandardWeight),
    (117, .noStandardWeight),
    (118, .noStandardWeight)]

/-- Independent literal abridged periodic-table records used only by the separate Rule-2 policy. -/
def ordinaryDisplayWeightRecords : List (Nat × Nat) :=
  [
    (1, 1008000000000), (2, 4002600000000), (3, 6940000000000), (4, 9012200000000),
    (5, 10810000000000), (6, 12011000000000), (7, 14007000000000), (8, 15999000000000),
    (9, 18998000000000), (10, 20180000000000), (11, 22990000000000), (12, 24305000000000),
    (13, 26982000000000), (14, 28085000000000), (15, 30974000000000), (16, 32060000000000),
    (17, 35450000000000), (18, 39950000000000), (19, 39098000000000), (20, 40078000000000),
    (21, 44956000000000), (22, 47867000000000), (23, 50942000000000), (24, 51996000000000),
    (25, 54938000000000), (26, 55845000000000), (27, 58933000000000), (28, 58693000000000),
    (29, 63546000000000), (30, 65380000000000), (31, 69723000000000), (32, 72630000000000),
    (33, 74922000000000), (34, 78971000000000), (35, 79904000000000), (36, 83798000000000),
    (37, 85468000000000), (38, 87620000000000), (39, 88906000000000), (40, 91224000000000),
    (41, 92906000000000), (42, 95950000000000), (43, 97000000000000), (44, 101070000000000),
    (45, 102910000000000), (46, 106420000000000), (47, 107870000000000), (48, 112410000000000),
    (49, 114820000000000), (50, 118710000000000), (51, 121760000000000), (52, 127600000000000),
    (53, 126900000000000), (54, 131290000000000), (55, 132910000000000), (56, 137330000000000),
    (57, 138910000000000), (58, 140120000000000), (59, 140910000000000), (60, 144240000000000),
    (61, 145000000000000), (62, 150360000000000), (63, 151960000000000), (64, 157250000000000),
    (65, 158930000000000), (66, 162500000000000), (67, 164930000000000), (68, 167260000000000),
    (69, 168930000000000), (70, 173050000000000), (71, 174970000000000), (72, 178490000000000),
    (73, 180950000000000), (74, 183840000000000), (75, 186210000000000), (76, 190230000000000),
    (77, 192220000000000), (78, 195080000000000), (79, 196970000000000), (80, 200590000000000),
    (81, 204380000000000), (82, 207200000000000), (83, 208980000000000), (84, 209000000000000),
    (85, 210000000000000), (86, 222000000000000), (87, 223000000000000), (88, 226000000000000),
    (89, 227000000000000), (90, 232040000000000), (91, 231040000000000), (92, 238030000000000),
    (93, 237000000000000), (94, 244000000000000), (95, 243000000000000), (96, 247000000000000),
    (97, 247000000000000), (98, 251000000000000), (99, 252000000000000), (100, 257000000000000),
    (101, 258000000000000), (102, 259000000000000), (103, 262000000000000), (104, 267000000000000),
    (105, 268000000000000), (106, 269000000000000), (107, 270000000000000), (108, 269000000000000),
    (109, 277000000000000), (110, 281000000000000), (111, 282000000000000), (112, 285000000000000),
    (113, 286000000000000), (114, 290000000000000), (115, 290000000000000), (116, 293000000000000),
    (117, 294000000000000), (118, 294000000000000)]

/-- The frozen exact-nuclide rows: the graph of the generated per-element mass tables, flattened in
current-atomic-number order.  This is the unique-key nuclide table. -/
def isotopeRecords : List IsotopeMassRecord :=
  currentAtomicNumbers.flatMap fun atomicNumber =>
    (Generated.isotopeMassesPico atomicNumber).map fun record =>
      ⟨atomicNumber, record.1, record.2⟩

/-- Independent literal reference policy: ordinary H, monoisotopic elements and bracketed
radioactive reference nuclides. It is a Rule-2 policy list, not the CIAAW standard-weight report. -/
def ordinaryReferenceRecords : List (Nat × Nat) :=
  [
    (1, 1), (4, 9), (9, 19), (11, 23),
    (13, 27), (15, 31), (21, 45), (25, 55),
    (27, 59), (33, 75), (39, 89), (41, 93),
    (43, 97), (45, 103), (53, 127), (55, 133),
    (59, 141), (61, 145), (65, 159), (67, 165),
    (69, 169), (79, 197), (83, 209), (84, 209),
    (85, 210), (86, 222), (87, 223), (88, 226),
    (89, 227), (91, 231), (93, 237), (94, 244),
    (95, 243), (96, 247), (97, 247), (98, 251),
    (99, 252), (100, 257), (101, 258), (102, 259),
    (103, 262), (104, 267), (105, 268), (106, 269),
    (107, 270), (108, 269), (109, 277), (110, 281),
    (111, 282), (112, 285), (113, 286), (114, 290),
    (115, 290), (116, 293), (117, 294), (118, 294)]

/-! ## Lookup characterisation of a sorted unique-key table

`lookupMassNumber?` is a linear search returning the first record whose mass number matches.  On a
table whose mass numbers are pairwise distinct it returns the unique matching record.  Both
directions are proved structurally; uniqueness is supplied by the already-validated
`ValidIsotopeMassList`. -/

theorem lookupMassNumber?_some_mem {records : List (Nat × MassPico)} {a : Nat} {m : MassPico}
    (lookup : lookupMassNumber? records a = some m) : (a, m) ∈ records := by
  induction records with
  | nil => simp [lookupMassNumber?] at lookup
  | cons head tail inductionHypothesis =>
      obtain ⟨k, v⟩ := head
      by_cases hka : k = a
      · have hv : v = m := by simpa [lookupMassNumber?, hka] using lookup
        simp only [List.mem_cons]
        exact Or.inl (by rw [hv, hka])
      · have htail : lookupMassNumber? tail a = some m := by
          simpa [lookupMassNumber?, hka] using lookup
        simp only [List.mem_cons]
        exact Or.inr (inductionHypothesis htail)

theorem lookupMassNumber?_eq_some_of_mem {records : List (Nat × MassPico)}
    (nodup : (records.map Prod.fst).Nodup) {a : Nat} {m : MassPico}
    (member : (a, m) ∈ records) : lookupMassNumber? records a = some m := by
  induction records with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      obtain ⟨k, v⟩ := head
      simp only [List.map_cons, List.nodup_cons] at nodup
      obtain ⟨kNotMember, tailNodup⟩ := nodup
      simp only [List.mem_cons] at member
      rcases member with heq | memberTail
      · cases heq
        simp [lookupMassNumber?]
      · have hne : ¬ k = a := by
          intro hka
          apply kNotMember
          rw [hka]
          exact List.mem_map_of_mem (f := Prod.fst) memberTail
        have htail := inductionHypothesis tailNodup memberTail
        simpa [lookupMassNumber?, hne] using htail

/-- Exact lookup iff for a unique-key table: the search returns `m` at `a` exactly when `(a, m)` is a
source record. -/
theorem lookupMassNumber?_eq_some_iff_of_nodup (records : List (Nat × MassPico))
    (nodup : (records.map Prod.fst).Nodup) (a m : Nat) :
    lookupMassNumber? records a = some m ↔ (a, m) ∈ records :=
  ⟨fun lookup => lookupMassNumber?_some_mem lookup,
    fun member => lookupMassNumber?_eq_some_of_mem nodup member⟩

/-- Uniqueness of mass numbers inside one element's frozen table, from the validated monotonicity. -/
theorem validIsotopeMassList_fst_nodup {records : List (Nat × MassPico)}
    (valid : ValidIsotopeMassList records) : (records.map Prod.fst).Nodup := by
  induction records with
  | nil => simp
  | cons head tail inductionHypothesis =>
      obtain ⟨k, v⟩ := head
      rw [ValidIsotopeMassList, List.pairwise_cons] at valid
      obtain ⟨headRelation, tailRelation⟩ := valid
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, inductionHypothesis tailRelation⟩
      rw [List.mem_map]
      rintro ⟨pair, pairMember, pairEq⟩
      have hk : pair.1 = k := pairEq
      have ordered := headRelation pair pairMember
      rw [hk] at ordered
      exact Nat.lt_irrefl k ordered.1

/-! ## Provision 1: periodicAtomicNumbers -/

/-- The independent range judgement is exactly membership in the generated current-atomic-number
list. -/
theorem mem_currentAtomicNumbers_iff_admits (atomicNumber : Nat) :
    atomicNumber ∈ currentAtomicNumbers ↔ PeriodicTableAdmits atomicNumber := by
  unfold PeriodicTableAdmits
  constructor
  · intro member
    rw [currentAtomicNumbers_exact, List.mem_range'] at member
    obtain ⟨offset, bound, indexEq⟩ := member
    exact ⟨by omega, by omega⟩
  · rintro ⟨lower, upper⟩
    rw [currentAtomicNumbers_exact, List.mem_range']
    exact ⟨atomicNumber - 1, by omega, by omega⟩

/-- Exact record-membership iff for the frozen ordinary periodic table. -/
theorem mem_periodicTableRecords_iff (record : PeriodicElementRecord) :
    record ∈ periodicTableRecords ↔
      PeriodicTableAdmits record.atomicNumber ∧
        Generated.ordinaryAtomicWeightPico? record.atomicNumber = some record.ordinaryWeightPico := by
  rw [periodicTableRecords, List.mem_filterMap]
  constructor
  · rintro ⟨z, hz, hmap⟩
    rw [Option.map_eq_some_iff] at hmap
    obtain ⟨weight, hweight, heq⟩ := hmap
    subst heq
    exact ⟨(mem_currentAtomicNumbers_iff_admits z).mp hz, hweight⟩
  · rintro ⟨admitted, lookup⟩
    refine ⟨record.atomicNumber, (mem_currentAtomicNumbers_iff_admits _).mpr admitted, ?_⟩
    exact Option.map_eq_some_iff.mpr ⟨record.ordinaryWeightPico, lookup, rfl⟩

/-- Kernel-meaningful record count: the frozen table length equals the generated count. -/
theorem periodicTableRecords_count :
    periodicTableRecords.length = Generated.ordinaryWeightRecordCount := by decide

/-! ## Provision 3: isotopeAtomicMasses -/

/-- Exact record-membership iff for the unique-key nuclide table. -/
theorem mem_isotopeRecords_iff (record : IsotopeMassRecord) :
    record ∈ isotopeRecords ↔
      record.atomicNumber ∈ currentAtomicNumbers ∧
        (record.massNumber, record.exactMassPico) ∈
          Generated.isotopeMassesPico record.atomicNumber := by
  rw [isotopeRecords, List.mem_flatMap]
  constructor
  · rintro ⟨z, hz, hmem⟩
    rw [List.mem_map] at hmem
    obtain ⟨pair, hpair, heq⟩ := hmem
    subst heq
    exact ⟨hz, hpair⟩
  · rintro ⟨hz, hmem⟩
    exact ⟨record.atomicNumber, hz,
      List.mem_map.mpr ⟨(record.massNumber, record.exactMassPico), hmem, rfl⟩⟩

/-- Explicit source-record uniqueness: the `(atomic number, mass number)` key of every frozen nuclide
row is distinct.  Derived from the already-validated `supportedNuclides_nodup`. -/
theorem isotopeRecords_key_nodup :
    (isotopeRecords.map fun record => (record.atomicNumber, record.massNumber)).Nodup := by
  have equal : (isotopeRecords.map fun record => (record.atomicNumber, record.massNumber))
      = supportedNuclides := by
    simp only [isotopeRecords, supportedNuclides, List.map_flatMap, List.map_map,
      Function.comp_def]
  rw [equal]
  exact supportedNuclides_nodup

/-- Exact nuclide lookup iff on the current atomic-number domain: the generated lookup returns `m`
at `(atomicNumber, massNumber)` exactly when that source record exists.  The domain hypothesis is
explicit and visible. -/
theorem isotopeAtomicMassPico?_eq_some_iff_of_current (atomicNumber massNumber mass : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers) :
    isotopeAtomicMassPico? atomicNumber massNumber = some mass ↔
      (massNumber, mass) ∈ Generated.isotopeMassesPico atomicNumber := by
  unfold isotopeAtomicMassPico?
  exact lookupMassNumber?_eq_some_iff_of_nodup (Generated.isotopeMassesPico atomicNumber)
    (validIsotopeMassList_fst_nodup (every_isotope_mass_list_is_valid atomicNumber current))
    massNumber mass

/-- Unknown-nuclide refusal: a labelled mass number absent from the frozen table is not silently
accepted. -/
theorem isotopeAtomicMassPico?_eq_none_of_not_mem (atomicNumber massNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers)
    (absent : ∀ mass, (massNumber, mass) ∉ Generated.isotopeMassesPico atomicNumber) :
    isotopeAtomicMassPico? atomicNumber massNumber = none := by
  cases observed : isotopeAtomicMassPico? atomicNumber massNumber with
  | none => rfl
  | some mass =>
      exact absurd ((isotopeAtomicMassPico?_eq_some_iff_of_current
        atomicNumber massNumber mass current).mp observed) (absent mass)

/-- The Rule-2 datum of an explicitly labelled unknown nuclide refuses: no value is fabricated. -/
theorem rule2MassPico?_unknown_nuclide_is_none (atomicNumber massNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers)
    (absent : ∀ mass, (massNumber, mass) ∉ Generated.isotopeMassesPico atomicNumber) :
    rule2MassPico? atomicNumber (some massNumber) = none := by
  rw [rule2MassPico?_explicit]
  exact isotopeAtomicMassPico?_eq_none_of_not_mem atomicNumber massNumber current absent

/-- Kernel-meaningful record count for the nuclide table, reusing the validated chunked count. -/
theorem isotopeRecords_count :
    isotopeRecords.length = Generated.isotopeMassRecordCount := by
  have equal : isotopeRecords.length = supportedNuclides.length := by
    simp only [isotopeRecords, supportedNuclides, List.length_flatMap, List.length_map]
  rw [equal, supportedNuclides_count]

/-! ## Provision 2: genuine CIAAW Standard Atomic Weights 2021 -/

/-- Structural search over independent three-variant CIAAW records. -/
def lookupStandardWeight? : List (Nat × CIAAWStandardAtomicWeights2021.Entry) → Nat → Option CIAAWStandardAtomicWeights2021.Entry
  | [], _ => none
  | record :: rest, atomicNumber =>
      if record.1 = atomicNumber then some record.2
      else lookupStandardWeight? rest atomicNumber

theorem lookupStandardWeight?_some_mem {records : List (Nat × CIAAWStandardAtomicWeights2021.Entry)} {a : Nat} {m : CIAAWStandardAtomicWeights2021.Entry}
    (lookup : lookupStandardWeight? records a = some m) : (a, m) ∈ records := by
  induction records with
  | nil => simp [lookupStandardWeight?] at lookup
  | cons head tail inductionHypothesis =>
      obtain ⟨k, v⟩ := head
      by_cases hka : k = a
      · have hv : v = m := by simpa [lookupStandardWeight?, hka] using lookup
        simp only [List.mem_cons]
        exact Or.inl (by rw [hv, hka])
      · have htail : lookupStandardWeight? tail a = some m := by
          simpa [lookupStandardWeight?, hka] using lookup
        simp only [List.mem_cons]
        exact Or.inr (inductionHypothesis htail)

theorem lookupStandardWeight?_eq_some_of_mem {records : List (Nat × CIAAWStandardAtomicWeights2021.Entry)}
    (nodup : (records.map Prod.fst).Nodup) {a : Nat} {m : CIAAWStandardAtomicWeights2021.Entry}
    (member : (a, m) ∈ records) : lookupStandardWeight? records a = some m := by
  induction records with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      obtain ⟨k, v⟩ := head
      simp only [List.map_cons, List.nodup_cons] at nodup
      obtain ⟨kNotMember, tailNodup⟩ := nodup
      simp only [List.mem_cons] at member
      rcases member with heq | memberTail
      · cases heq
        simp [lookupStandardWeight?]
      · have hne : ¬ k = a := by
          intro hka
          apply kNotMember
          rw [hka]
          exact List.mem_map_of_mem (f := Prod.fst) memberTail
        have htail := inductionHypothesis tailNodup memberTail
        simpa [lookupStandardWeight?, hne] using htail

/-- Exact lookup iff for a unique-key table: the search returns `m` at `a` exactly when `(a, m)` is a
source record. -/
theorem lookupStandardWeight?_eq_some_iff_of_nodup (records : List (Nat × CIAAWStandardAtomicWeights2021.Entry))
    (nodup : (records.map Prod.fst).Nodup) (a : Nat) (m : CIAAWStandardAtomicWeights2021.Entry) :
    lookupStandardWeight? records a = some m ↔ (a, m) ∈ records :=
  ⟨fun lookup => lookupStandardWeight?_some_mem lookup,
    fun member => lookupStandardWeight?_eq_some_of_mem nodup member⟩


private theorem standardWeightLookup_checked :
    currentAtomicNumbers.all (fun z => decide
      (CIAAWStandardAtomicWeights2021.entry? z = lookupStandardWeight? standardWeightRecords z)) = true := by decide

private theorem standardWeightRecords_key_nodup :
    (standardWeightRecords.map Prod.fst).Nodup := by decide

/-- On the frozen current domain, the production CIAAW lookup returns an entry exactly when that
three-variant entry is an independently listed authority record. -/
theorem standardAtomicWeight_lookup_iff (z : Nat) (entry : CIAAWStandardAtomicWeights2021.Entry)
    (current : z ∈ currentAtomicNumbers) :
    CIAAWStandardAtomicWeights2021.entry? z = some entry ↔ (z, entry) ∈ standardWeightRecords := by
  have checked := (List.all_eq_true.mp standardWeightLookup_checked) z current
  have equal : CIAAWStandardAtomicWeights2021.entry? z = lookupStandardWeight? standardWeightRecords z :=
    of_decide_eq_true checked
  rw [equal]
  exact lookupStandardWeight?_eq_some_iff_of_nodup standardWeightRecords
    standardWeightRecords_key_nodup z entry

/-- Counts preserve the source's distinction between intervals, values with uncertainty, and
explicitly unavailable standard weights. -/
theorem standardWeightRecords_variant_counts :
    standardWeightRecords.length = 118 ∧
      (standardWeightRecords.filter fun r => match r.2 with
        | .interval _ _ => true | _ => false).length = 14 ∧
      (standardWeightRecords.filter fun r => match r.2 with
        | .value _ _ => true | _ => false).length = 70 ∧
      (standardWeightRecords.filter fun r => match r.2 with
        | .noStandardWeight => true | _ => false).length = 34 := by decide

/-- Concrete authority entries exhibit all three variants, and retain hydrogen's interval instead
of substituting the ordinary Rule-2 protium mass. -/
theorem standardWeightRecords_three_variants :
    (1, CIAAWStandardAtomicWeights2021.Entry.interval 1007840000000 1008110000000) ∈ standardWeightRecords ∧
      (2, CIAAWStandardAtomicWeights2021.Entry.value 4002602000000 2000000) ∈ standardWeightRecords ∧
      (43, CIAAWStandardAtomicWeights2021.Entry.noStandardWeight) ∈ standardWeightRecords := by decide

/-! ## Separate composition: ordinary Rule-2 mass policy -/

private theorem ordinaryReferenceLookup_checked :
    currentAtomicNumbers.all (fun z => decide
      (Generated.ordinaryNuclideReferenceMassNumber? z =
        lookupMassNumber? ordinaryReferenceRecords z)) = true := by decide

private theorem ordinaryDisplayLookup_checked :
    currentAtomicNumbers.all (fun z => decide
      (Generated.ordinaryAtomicWeightPico? z =
        lookupMassNumber? ordinaryDisplayWeightRecords z)) = true := by decide

private theorem ordinaryReferenceRecords_key_nodup :
    (ordinaryReferenceRecords.map Prod.fst).Nodup := by decide

private theorem ordinaryDisplayWeightRecords_key_nodup :
    (ordinaryDisplayWeightRecords.map Prod.fst).Nodup := by decide

theorem ordinary_reference_lookup_iff (z massNumber : Nat)
    (current : z ∈ currentAtomicNumbers) :
    Generated.ordinaryNuclideReferenceMassNumber? z = some massNumber ↔
      (z, massNumber) ∈ ordinaryReferenceRecords := by
  have checked := (List.all_eq_true.mp ordinaryReferenceLookup_checked) z current
  have equal : Generated.ordinaryNuclideReferenceMassNumber? z =
      lookupMassNumber? ordinaryReferenceRecords z := of_decide_eq_true checked
  rw [equal]
  exact lookupMassNumber?_eq_some_iff_of_nodup ordinaryReferenceRecords
    ordinaryReferenceRecords_key_nodup z massNumber

theorem ordinary_display_lookup_iff (z mass : Nat)
    (current : z ∈ currentAtomicNumbers) :
    Generated.ordinaryAtomicWeightPico? z = some mass ↔
      (z, mass) ∈ ordinaryDisplayWeightRecords := by
  have checked := (List.all_eq_true.mp ordinaryDisplayLookup_checked) z current
  have equal : Generated.ordinaryAtomicWeightPico? z =
      lookupMassNumber? ordinaryDisplayWeightRecords z := of_decide_eq_true checked
  rw [equal]
  exact lookupMassNumber?_eq_some_iff_of_nodup ordinaryDisplayWeightRecords
    ordinaryDisplayWeightRecords_key_nodup z mass

theorem isotope_record_iff_lookup (z massNumber mass : Nat)
    (current : z ∈ currentAtomicNumbers) :
    (⟨z, massNumber, mass⟩ : IsotopeMassRecord) ∈ isotopeRecords ↔
      isotopeAtomicMassPico? z massNumber = some mass := by
  rw [mem_isotopeRecords_iff]
  exact ⟨fun h => (isotopeAtomicMassPico?_eq_some_iff_of_current
      z massNumber mass current).mpr h.2,
    fun h => ⟨current, (isotopeAtomicMassPico?_eq_some_iff_of_current
      z massNumber mass current).mp h⟩⟩

/-- Independent record semantics for the separate ordinary Rule-2 composition: a declared reference
selects its genuine AME record; absence of any reference selects the abridged periodic-table record.
No lookup equality appears in this judgment. -/
def OrdinaryRule2Mass (z mass : Nat) : Prop :=
  (∃ massNumber, (z, massNumber) ∈ ordinaryReferenceRecords ∧
    (⟨z, massNumber, mass⟩ : IsotopeMassRecord) ∈ isotopeRecords) ∨
  ((∀ massNumber, (z, massNumber) ∉ ordinaryReferenceRecords) ∧
    (z, mass) ∈ ordinaryDisplayWeightRecords)

/-- Exact bridge from the composed ordinary lookup to independent record membership. It is separate
from, and does not alter, the CIAAW standard-weight authority meaning. -/
theorem ordinaryAtomicMassPico?_eq_some_iff (z mass : Nat)
    (current : z ∈ currentAtomicNumbers) :
    ordinaryAtomicMassPico? z = some mass ↔ OrdinaryRule2Mass z mass := by
  unfold OrdinaryRule2Mass
  simp_rw [← ordinary_reference_lookup_iff z _ current,
    isotope_record_iff_lookup z _ _ current, ← ordinary_display_lookup_iff z _ current]
  unfold ordinaryAtomicMassPico?
  cases observed : Generated.ordinaryNuclideReferenceMassNumber? z with
  | none => simp
  | some massNumber => simp

/-- Every literal ordinary reference selects a supported frozen AME nuclide. -/
theorem ordinaryReferenceRecords_are_supported :
    ordinaryReferenceRecords.all (fun record =>
      (isotopeAtomicMassPico? record.1 record.2).isSome) = true := by decide

/-- Reference-branch provenance yields an independently listed nuclide mass, without assuming a
successful mass lookup or an expected value as a premise. -/
theorem ordinary_reference_mass_is_supported (z massNumber : Nat)
    (current : z ∈ currentAtomicNumbers)
    (reference : (z, massNumber) ∈ ordinaryReferenceRecords) :
    ∃ mass, ordinaryAtomicMassPico? z = some mass ∧
      (⟨z, massNumber, mass⟩ : IsotopeMassRecord) ∈ isotopeRecords := by
  have supported := (List.all_eq_true.mp ordinaryReferenceRecords_are_supported)
    (z, massNumber) reference
  obtain ⟨mass, lookup⟩ := Option.isSome_iff_exists.mp supported
  have refLookup := (ordinary_reference_lookup_iff z massNumber current).mpr reference
  refine ⟨mass, ?_, (isotope_record_iff_lookup z massNumber mass current).mpr lookup⟩
  simpa [ordinaryAtomicMassPico?, refLookup] using lookup

/-- The P-92.3 hydrogen identity follows from the literal reference record and the structural bridge. -/
theorem ordinary_hydrogen_reflects_protium :
    ordinaryAtomicMassPico? 1 = isotopeAtomicMassPico? 1 1 := by
  have current : 1 ∈ currentAtomicNumbers := by decide
  have reference : (1, 1) ∈ ordinaryReferenceRecords := by decide
  have lookup := (ordinary_reference_lookup_iff 1 1 current).mpr reference
  simp [ordinaryAtomicMassPico?, lookup]

/-! ## No-floating-rounding witnesses

The stored integers are exactly base-10 scalings of written source decimals with at most twelve
fractional digits.  Ordinary hydrogen is the displayed `1.008`; protium is the AME value
`1.007825031898`.  Both are kernel-checked exact conversions, not rounded floating values. -/

/-- The displayed ordinary hydrogen weight `1.008`, written with three fractional digits. -/
def ordinaryHydrogenDecimal : DecimalPico := ⟨1, 8, 3, by decide, by decide⟩

/-- The AME-2020 protium mass `1.007825031898`, written with twelve fractional digits. -/
def protiumDecimal : DecimalPico := ⟨1, 7825031898, 12, by decide, by decide⟩

theorem hydrogen_ordinary_weight_exact_decimal :
    Generated.ordinaryAtomicWeightPico? 1 = some ordinaryHydrogenDecimal.value ∧
      ExactDecimalScale ordinaryHydrogenDecimal.value ordinaryHydrogenDecimal :=
  ⟨by decide, rfl⟩

theorem protium_isotope_mass_exact_decimal :
    isotopeAtomicMassPico? 1 1 = some protiumDecimal.value ∧
      ExactDecimalScale protiumDecimal.value protiumDecimal :=
  ⟨by decide, rfl⟩

/-! ## Candidate normative data coverage mapping

The three candidate authority record lists have the frozen source counts. The ordinary Rule-2
reference policy is separate and contributes no standard-weight authority coverage. These counts
alone do not justify changing the absent partition; actual manifest/adapter integration remains open. -/

theorem candidate_coverage :
    periodicTableRecords.length = 118 ∧
      standardWeightRecords.length = 118 ∧
        isotopeRecords.length = 3557 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · exact isotopeRecords_count

/-! ## Kernel metadata vs external generation receipt -/

/-- Metadata of the actual CIAAW 2021 standard-weight report. The digest field is copied from the
existing frozen CIAAW module and does not prove equality with any externally supplied bytes. -/
def standardAtomicWeights2021 : FrozenMassSource where
  title := "CIAAW Standard Atomic Weights 2021"
  url := "https://doi.org/10.1515/pac-2019-0603"
  sha256 := CIAAWStandardAtomicWeights2021.sourceSha256
  recordCount := CIAAWStandardAtomicWeights2021.recordCount

/-- Kernel metadata pin for the separate CIAAW source, preserving its actual 2021-report digest.
It is not the periodic-table or AME digest and makes no publication-byte verification claim. -/
theorem standardAtomicWeights2021_metadata_exact :
    standardAtomicWeights2021.sha256 =
      "4aba4ddd55523e64039aee076295fe0f9b1bb16576a0bae6111c43dbd0e97318" ∧
      standardWeightRecords.length = standardAtomicWeights2021.recordCount := by
  constructor
  · rfl
  · decide

/-- The kernel merely *carries* the pinned digest strings verbatim; it proves no byte-level claim
about them.  Only the record counts are kernel-meaningful and are checked in `candidate_coverage`. -/
theorem source_digest_fields_carried :
    periodicTable2022.sha256 = Generated.periodicTable2022Sha256 ∧
      isotopeMasses2020.sha256 = Generated.isotopeMasses2020CsvSha256 :=
  ⟨rfl, rfl⟩

end TetraStereo.UniversalProof.FrozenRule2DataSemanticsProofs.FrozenRule2DataSemantics
