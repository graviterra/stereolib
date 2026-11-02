import TetraStereo.OneCenter.AuthoritativeMainGroupLewisEndpointElectronicInventory
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Frozen IUPAC periodic-group to main-group valence conformance

The generated table is extracted from horizontal cell placement in the byte-frozen IUPAC
periodic-table PDF.  This module separately states the mathematical group-to-valence relation and
proves that the lookup used by the Lewis endpoint ledger is exactly that relation.  In particular,
helium has two valence electrons rather than inheriting the octet value of the remaining Group 18
elements.
-/

namespace IUPACPeriodicGroupData

structure FrozenPeriodicGroupSource where
  title : String
  url : String
  sha256 : String
  groupedElementRecordCount : Nat
  deriving DecidableEq, Repr

def periodicTable2022 : FrozenPeriodicGroupSource where
  title := Generated.periodicTableTitle
  url := Generated.periodicTableUrl
  sha256 := Generated.periodicTableSha256
  groupedElementRecordCount := Generated.groupedElementRecordCount

/-- Independent mathematical reading of main-group valence count from an IUPAC group number.
The Group 18 exception is exactly helium's closed `1s²` shell. -/
def MainGroupValenceElectronCountByGroup
    (atomicNumber group valenceElectrons : ℕ) : Prop :=
  (group = 1 ∧ valenceElectrons = 1) ∨
  (group = 2 ∧ valenceElectrons = 2) ∨
  (group = 13 ∧ valenceElectrons = 3) ∨
  (group = 14 ∧ valenceElectrons = 4) ∨
  (group = 15 ∧ valenceElectrons = 5) ∨
  (group = 16 ∧ valenceElectrons = 6) ∨
  (group = 17 ∧ valenceElectrons = 7) ∨
  (group = 18 ∧
    ((atomicNumber = 2 ∧ valenceElectrons = 2) ∨
      (atomicNumber ≠ 2 ∧ valenceElectrons = 8)))

/-- Independent source-level meaning: the frozen IUPAC table puts the element in a numbered group,
and the main-group valence count follows the preceding group relation. -/
def IUPACMainGroupValenceElectronCount
    (element : PeriodicElement) (valenceElectrons : ℕ) : Prop :=
  ∃ group,
    Generated.groupNumber? element.atomicNumber = some group ∧
      MainGroupValenceElectronCountByGroup
        element.atomicNumber group valenceElectrons

theorem mainGroupValenceElectronCountFromIUPACGroup?_eq_some_iff
    (atomicNumber group valenceElectrons : ℕ) :
    AuthoritativeChemicalInput.mainGroupValenceElectronCountFromIUPACGroup?
        atomicNumber (some group) = some valenceElectrons ↔
      MainGroupValenceElectronCountByGroup atomicNumber group valenceElectrons := by
  unfold AuthoritativeChemicalInput.mainGroupValenceElectronCountFromIUPACGroup?
  unfold MainGroupValenceElectronCountByGroup
  split <;> simp_all [eq_comm]
  split <;> simp_all

/-- The lookup consumed by the Lewis ledger is exactly the independently stated IUPAC-group
relation. -/
theorem mainGroupValenceElectronCount?_eq_some_iff_iupacGroup
    (element : PeriodicElement) (valenceElectrons : ℕ) :
    AuthoritativeChemicalInput.mainGroupValenceElectronCount? element =
        some valenceElectrons ↔
      IUPACMainGroupValenceElectronCount element valenceElectrons := by
  unfold AuthoritativeChemicalInput.mainGroupValenceElectronCount?
  unfold IUPACMainGroupValenceElectronCount
  cases observed : Generated.groupNumber? element.atomicNumber with
  | none =>
      simp [AuthoritativeChemicalInput.mainGroupValenceElectronCountFromIUPACGroup?]
  | some group =>
      simp only [Option.some.injEq, exists_eq_left']
      exact mainGroupValenceElectronCountFromIUPACGroup?_eq_some_iff
        element.atomicNumber group valenceElectrons

/-- Lookup failure is exactly absence of any group-derived main-group valence value. -/
theorem mainGroupValenceElectronCount?_eq_none_iff_not_iupacGroup
    (element : PeriodicElement) :
    AuthoritativeChemicalInput.mainGroupValenceElectronCount? element = none ↔
      ¬ ∃ valenceElectrons,
        IUPACMainGroupValenceElectronCount element valenceElectrons := by
  constructor
  · intro absent
    rintro ⟨valenceElectrons, authoritative⟩
    have present :=
      (mainGroupValenceElectronCount?_eq_some_iff_iupacGroup
        element valenceElectrons).mpr authoritative
    rw [absent] at present
    contradiction
  · intro unsupported
    cases observed :
        AuthoritativeChemicalInput.mainGroupValenceElectronCount? element with
    | none => rfl
    | some valenceElectrons =>
        exact False.elim (unsupported ⟨valenceElectrons,
          (mainGroupValenceElectronCount?_eq_some_iff_iupacGroup
            element valenceElectrons).mp observed⟩)

/-- The group transcription and the existing Rule-2 mass transcription name the identical frozen
IUPAC PDF byte sequence. -/
theorem periodicTable2022_sha256_agrees_with_rule2_source :
    periodicTable2022.sha256 = CIPRule2MassData.periodicTable2022.sha256 := by
  rfl

theorem groupedElementRecordCount_exact :
    periodicTable2022.groupedElementRecordCount = 88 := by
  rfl

theorem helium_group_exact : Generated.groupNumber? 2 = some 18 := by
  rfl

theorem helium_valence_electron_count_exact :
    AuthoritativeChemicalInput.mainGroupValenceElectronCount?
      ⟨2, by omega, by omega⟩ = some 2 := by
  rfl

theorem neon_valence_electron_count_exact :
    AuthoritativeChemicalInput.mainGroupValenceElectronCount?
      ⟨10, by omega, by omega⟩ = some 8 := by
  rfl

end IUPACPeriodicGroupData
end TetraStereo.OneCenter
