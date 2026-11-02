import TetraStereo.OneCenter.AuthoritativeChemicalInputAtomElectronicStateValidation
import TetraStereo.OneCenter.IUPACPeriodicGroupDataGenerated

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Main-group Lewis derivation of endpoint electronic inventories

For a localized main-group covalent endpoint, the formal-charge form of the Lewis electron ledger
is

`valence electrons - formal charge = represented bond order + implicit H + 2·lone pairs + radicals`.

Together with the independent two-position endpoint accounting equation, this determines the
implicit-protium and lone-pair counts uniquely.  This module states that ledger independently of
the inventory lookup implementation, proves uniqueness, and implements an exact finite search.
Vacancies are excluded from this closed-valence derivation; radical positions remain tied to the
semantic atom's explicit unpaired-electron count and are therefore derived rather than erased.
-/

/-- Main-group valence-electron count derived from one IUPAC numbered group.  Helium is the
closed-`1s²` exception to the otherwise octet-valued Group 18 column. -/
def mainGroupValenceElectronCountFromIUPACGroup?
    (atomicNumber : ℕ) : Option ℕ → Option ℕ
  | some 1 => some 1
  | some 2 => some 2
  | some 13 => some 3
  | some 14 => some 4
  | some 15 => some 5
  | some 16 => some 6
  | some 17 => some 7
  | some 18 => if atomicNumber = 2 then some 2 else some 8
  | _ => none

/-- Main-group valence-electron count for all currently named s- and p-block elements.  The group
number is extracted from the byte-frozen 4 May 2022 IUPAC periodic table.  Transition,
lanthanide, and actinide electron accounting requires a coordination/electronic-state model and is
deliberately outside this localized covalent ledger. -/
def mainGroupValenceElectronCount? (element : PeriodicElement) : Option ℕ :=
  mainGroupValenceElectronCountFromIUPACGroup? element.atomicNumber
    (IUPACPeriodicGroupData.Generated.groupNumber? element.atomicNumber)

/-- Sum of represented localized bond orders incident at an endpoint. -/
noncomputable def aromaticCanonicalRepresentedBondOrderSum
    (source : AuthoritativeChemicalInput)
    (endpoint : source.AromaticCanonicalAtom) : ℕ :=
  (source.aromaticCanonicalNeighborFinset endpoint).sum fun neighbor =>
    source.molecule.aromaticCanonicalBondOrder endpoint.val neighbor.val

/-- The independent Lewis formal-charge equation for one proposed inventory. -/
def MainGroupLewisElectronBalance
    (source : AuthoritativeChemicalInput)
    (endpoint : source.AromaticCanonicalAtom)
    (valenceElectrons : ℕ)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  (valenceElectrons : ℤ) - (source.molecule.atoms.get endpoint).formalCharge =
    (source.aromaticCanonicalRepresentedBondOrderSum endpoint : ℤ) +
      inventory.implicitProtia + 2 * inventory.lonePairs +
        inventory.unpairedElectronPositions

/-- Closed-valence main-group meaning of an endpoint inventory. -/
def MainGroupClosedValenceLewisEndpointInventory
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
      endpoint partner inventory ∧
    inventory.vacancies = 0 ∧
    ∃ valenceElectrons,
      mainGroupValenceElectronCount? (source.molecule.atoms.get endpoint).element =
          some valenceElectrons ∧
        source.MainGroupLewisElectronBalance endpoint valenceElectrons inventory

noncomputable instance (source : AuthoritativeChemicalInput)
    (endpoint : source.AromaticCanonicalAtom)
    (valenceElectrons : ℕ)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    Decidable (source.MainGroupLewisElectronBalance endpoint valenceElectrons inventory) := by
  unfold MainGroupLewisElectronBalance
  infer_instance

/-- The position equation and Lewis electron equation together make the derived inventory
functional. -/
theorem mainGroupClosedValenceLewisEndpointInventory_subsingleton
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    {left right : AromaticCanonicalRule3EndpointElectronicInventory}
    (leftLewis : source.MainGroupClosedValenceLewisEndpointInventory
      endpoint partner left)
    (rightLewis : source.MainGroupClosedValenceLewisEndpointInventory
      endpoint partner right) :
    left = right := by
  rcases leftLewis with ⟨leftCanonical, leftNoVacancy,
    leftValence, leftElement, leftBalance⟩
  rcases rightLewis with ⟨rightCanonical, rightNoVacancy,
    rightValence, rightElement, rightBalance⟩
  have valenceEqual : leftValence = rightValence := by
    rw [leftElement] at rightElement
    exact Option.some.inj rightElement
  subst rightValence
  unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory at leftCanonical rightCanonical
  unfold AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions at leftCanonical rightCanonical
  unfold MainGroupLewisElectronBalance at leftBalance rightBalance
  rcases left with ⟨leftImplicit, leftLonePairs, leftVacancies, leftRadicals⟩
  rcases right with ⟨rightImplicit, rightLonePairs, rightVacancies, rightRadicals⟩
  simp only at leftNoVacancy rightNoVacancy
  simp only at leftCanonical rightCanonical leftBalance rightBalance
  congr <;> omega

/-- Nine finite H/lone-pair candidates; vacancy is zero and the explicit semantic radical count is
copied literally.  The endpoint position equation filters impossible candidates. -/
def mainGroupClosedValenceEndpointInventoryCandidates
    (unpairedElectrons : ℕ) :
    List AromaticCanonicalRule3EndpointElectronicInventory :=
  (List.range 3).flatMap fun implicitProtia =>
    (List.range 3).map fun lonePairs =>
      { implicitProtia := implicitProtia
        lonePairs := lonePairs
        vacancies := 0
        unpairedElectronPositions := unpairedElectrons }

/-- Every closed-valence Lewis inventory satisfying endpoint accounting occurs in the finite
candidate list. -/
theorem mem_mainGroupClosedValenceEndpointInventoryCandidates_of_lewis
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (lewis : source.MainGroupClosedValenceLewisEndpointInventory
      endpoint partner inventory) :
    inventory ∈ mainGroupClosedValenceEndpointInventoryCandidates
      (source.molecule.atoms.get endpoint).unpairedElectrons := by
  rcases inventory with ⟨implicitProtia, lonePairs, vacancies, radicals⟩
  rcases lewis with ⟨canonical, noVacancy, _electronBalance⟩
  unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory at canonical
  unfold AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions at canonical
  simp only at noVacancy canonical
  apply List.mem_flatMap.mpr
  refine ⟨implicitProtia, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_map.mpr
  refine ⟨lonePairs, List.mem_range.mpr (by omega), ?_⟩
  simp only [noVacancy, canonical.2]

/-- Exact finite inference of the unique main-group closed-valence endpoint inventory. -/
noncomputable def mainGroupClosedValenceLewisEndpointInventory?
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    Option AromaticCanonicalRule3EndpointElectronicInventory := by
  classical
  exact (mainGroupClosedValenceEndpointInventoryCandidates
    (source.molecule.atoms.get endpoint).unpairedElectrons).find? fun inventory =>
      decide (source.MainGroupClosedValenceLewisEndpointInventory
        endpoint partner inventory)

/-- The finite inference succeeds exactly for the independent Lewis-derived inventory relation. -/
@[simp] theorem mainGroupClosedValenceLewisEndpointInventory?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    source.mainGroupClosedValenceLewisEndpointInventory? endpoint partner = some inventory ↔
      source.MainGroupClosedValenceLewisEndpointInventory endpoint partner inventory := by
  classical
  constructor
  · intro computed
    have computedFind :
        (mainGroupClosedValenceEndpointInventoryCandidates
          (source.molecule.atoms.get endpoint).unpairedElectrons).find? (fun inventory =>
            decide (source.MainGroupClosedValenceLewisEndpointInventory
              endpoint partner inventory)) = some inventory := by
      simpa [mainGroupClosedValenceLewisEndpointInventory?] using computed
    exact of_decide_eq_true (List.find?_some
      (p := fun candidate => decide
        (source.MainGroupClosedValenceLewisEndpointInventory endpoint partner candidate))
      computedFind)
  · intro lewis
    cases observed : source.mainGroupClosedValenceLewisEndpointInventory? endpoint partner with
    | none =>
        have observedFind :
            (mainGroupClosedValenceEndpointInventoryCandidates
              (source.molecule.atoms.get endpoint).unpairedElectrons).find? (fun inventory =>
                decide (source.MainGroupClosedValenceLewisEndpointInventory
                  endpoint partner inventory)) = none := by
          simpa [mainGroupClosedValenceLewisEndpointInventory?] using observed
        have rejected := List.find?_eq_none.mp observedFind inventory
          (source.mem_mainGroupClosedValenceEndpointInventoryCandidates_of_lewis
            endpoint partner inventory lewis)
        exact False.elim (rejected (decide_eq_true lewis))
    | some actual =>
        have observedFind :
            (mainGroupClosedValenceEndpointInventoryCandidates
              (source.molecule.atoms.get endpoint).unpairedElectrons).find? (fun inventory =>
                decide (source.MainGroupClosedValenceLewisEndpointInventory
                  endpoint partner inventory)) = some actual := by
          simpa [mainGroupClosedValenceLewisEndpointInventory?] using observed
        have actualLewis : source.MainGroupClosedValenceLewisEndpointInventory
            endpoint partner actual :=
          of_decide_eq_true (List.find?_some
            (p := fun candidate => decide
              (source.MainGroupClosedValenceLewisEndpointInventory endpoint partner candidate))
            observedFind)
        have equal := source.mainGroupClosedValenceLewisEndpointInventory_subsingleton
          endpoint partner actualLewis lewis
        exact congrArg some equal

/-- Exact negative meaning of finite Lewis inference. -/
theorem mainGroupClosedValenceLewisEndpointInventory?_eq_none_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.mainGroupClosedValenceLewisEndpointInventory? endpoint partner = none ↔
      ¬ ∃ inventory,
        source.MainGroupClosedValenceLewisEndpointInventory endpoint partner inventory := by
  constructor
  · intro absent
    rintro ⟨inventory, lewis⟩
    have present :=
      (source.mainGroupClosedValenceLewisEndpointInventory?_eq_some_iff
        endpoint partner inventory).mpr lewis
    rw [absent] at present
    contradiction
  · intro noInventory
    cases observed : source.mainGroupClosedValenceLewisEndpointInventory? endpoint partner with
    | none => rfl
    | some inventory =>
        exact False.elim (noInventory ⟨inventory,
          (source.mainGroupClosedValenceLewisEndpointInventory?_eq_some_iff
            endpoint partner inventory).mp observed⟩)

/-- Positive, exhaustive reasons why the main-group closed-valence ledger cannot derive an
inventory. -/
def MainGroupClosedValenceLewisEndpointRefusal
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) : Prop :=
  mainGroupValenceElectronCount? (source.molecule.atoms.get endpoint).element = none ∨
    (¬ ∃ inventory,
      source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
          endpoint partner inventory ∧ inventory.vacancies = 0) ∨
    (∃ valenceElectrons,
      mainGroupValenceElectronCount? (source.molecule.atoms.get endpoint).element =
          some valenceElectrons ∧
        (∃ inventory,
          source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
              endpoint partner inventory ∧ inventory.vacancies = 0) ∧
        ∀ inventory,
          source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
              endpoint partner inventory →
            inventory.vacancies = 0 →
              ¬ source.MainGroupLewisElectronBalance endpoint valenceElectrons inventory)

/-- Failure of the exact inference procedure is precisely unsupported main-group identity,
impossible closed-valence position accounting, or Lewis electron imbalance for every position-
canonical candidate. -/
theorem mainGroupClosedValenceLewisEndpointInventory?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.mainGroupClosedValenceLewisEndpointInventory? endpoint partner = none ↔
      source.MainGroupClosedValenceLewisEndpointRefusal endpoint partner := by
  rw [source.mainGroupClosedValenceLewisEndpointInventory?_eq_none_iff endpoint partner]
  unfold MainGroupClosedValenceLewisEndpointRefusal
  constructor
  · intro noLewis
    cases elementObserved :
        mainGroupValenceElectronCount? (source.molecule.atoms.get endpoint).element with
    | none => exact Or.inl rfl
    | some valenceElectrons =>
        by_cases canonicalExists : ∃ inventory,
            source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
                endpoint partner inventory ∧ inventory.vacancies = 0
        · right
          right
          refine ⟨valenceElectrons, rfl, canonicalExists, ?_⟩
          intro inventory canonical noVacancy balance
          exact noLewis ⟨inventory, canonical, noVacancy,
            valenceElectrons, elementObserved, balance⟩
        · exact Or.inr (Or.inl canonicalExists)
  · intro refusal
    rintro ⟨inventory, canonical, noVacancy,
      valenceElectrons, elementObserved, balance⟩
    rcases refusal with unsupported | noCanonical | imbalance
    · rw [unsupported] at elementObserved
      contradiction
    · exact noCanonical ⟨inventory, canonical, noVacancy⟩
    · obtain ⟨actualValence, actualElement, _canonicalExists, allImbalanced⟩ := imbalance
      rw [actualElement] at elementObserved
      cases elementObserved
      exact allImbalanced inventory canonical noVacancy balance

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
