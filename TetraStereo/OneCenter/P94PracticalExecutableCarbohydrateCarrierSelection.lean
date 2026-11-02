import TetraStereo.OneCenter.P94CoordinateRingWitnessDiscovery
import TetraStereo.OneCenter.P94ExecutableRingApplicability
import TetraStereo.OneCenter.P94ExecutableRingFamilySelection

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

namespace BlueBookP94.PracticalCarbohydrateCarrierSelection

open CoordinateRing
open ExecutableRingFamilySelection

/-!
# Executable carbohydrate five-ring carrier perception

The existing source-exact carbohydrate twist geometry intentionally required an external
applicability authority.  This module adds a conservative, fully executable structural route for
ordinary oxygen-furanose carriers.  It recognizes a valid five-ring with exactly one ring oxygen
and four ring carbons, an oxygen-bearing carbon adjacent to the ring oxygen, and at least two
oxygenated ring carbons in total.  The explicit predicate is a sufficient machine-perception
boundary, not a claim that constitution alone exhausts every modified carbohydrate covered by
the broader nomenclature authority.
-/

def atomElement? (molecule : RawMolecule) (atom : Nat) : Option Element :=
  molecule.atoms[atom]?.map AtomSpec.element

def ringAtomsOfElement (molecule : RawMolecule) (unit : P94ConformationUnit)
    (element : Element) : List Nat :=
  unit.atoms.filter fun atom => atomElement? molecule atom == some element

def properlySingleBonded? (molecule : RawMolecule) (left right : Nat) : Bool :=
  molecule.bonds.any fun bond =>
    bond.connects left right && P94ConformationUnit.saturatedSingleBondKind? bond.kind

def hasExocyclicOxygen? (molecule : RawMolecule) (unit : P94ConformationUnit)
    (atom : Nat) : Bool :=
  (molecule.incidentAtoms atom).any fun neighbor =>
    !unit.atoms.contains neighbor && atomElement? molecule neighbor == some .O &&
      properlySingleBonded? molecule atom neighbor

def tetrahedralCompatibleCarbon? (molecule : RawMolecule) (atom : Nat) : Bool :=
  match molecule.atoms[atom]? with
  | none => false
  | some spec =>
      spec.element == .C && !spec.aromatic && decide (spec.charge = 0) &&
        decide (3 ≤ molecule.incidentBondOrderSum atom) &&
        decide (molecule.incidentBondOrderSum atom ≤ 4)

def oxygenatedRingCarbons (molecule : RawMolecule)
    (unit : P94ConformationUnit) : List Nat :=
  unit.atoms.filter fun atom =>
    atomElement? molecule atom == some .C && hasExocyclicOxygen? molecule unit atom

def hasRingOxygenNeighbor? (molecule : RawMolecule) (unit : P94ConformationUnit)
    (atom : Nat) : Bool :=
  (molecule.incidentAtoms atom).any fun neighbor =>
    unit.atoms.contains neighbor && atomElement? molecule neighbor == some .O

def anomericCarrierCandidates (molecule : RawMolecule)
    (unit : P94ConformationUnit) : List Nat :=
  (oxygenatedRingCarbons molecule unit).filter fun atom =>
    hasRingOxygenNeighbor? molecule unit atom &&
      tetrahedralCompatibleCarbon? molecule atom

/-- Declarative finite structural meaning accepted by the practical carbohydrate route. -/
def PerceivedCarbohydrateFiveRingCarrier (molecule : RawMolecule)
    (unit : P94ConformationUnit) : Prop :=
  unit.kind = .fiveMemberedRing ∧
    unit.ValidFor molecule ∧
    unit.SaturatedCyclic molecule ∧
    (ringAtomsOfElement molecule unit .O).length = 1 ∧
    (ringAtomsOfElement molecule unit .C).length = 4 ∧
    2 ≤ (oxygenatedRingCarbons molecule unit).length ∧
    0 < (anomericCarrierCandidates molecule unit).length

/-- Executable reflection of the conservative oxygen-furanose carrier meaning. -/
def carbohydrateFiveRingCarrier? (molecule : RawMolecule)
    (unit : P94ConformationUnit) : Bool :=
  decide (unit.kind = .fiveMemberedRing) &&
    unit.ringValidFor? molecule &&
    unit.saturatedCyclic? molecule &&
    decide ((ringAtomsOfElement molecule unit .O).length = 1) &&
    decide ((ringAtomsOfElement molecule unit .C).length = 4) &&
    decide (2 ≤ (oxygenatedRingCarbons molecule unit).length) &&
    decide (0 < (anomericCarrierCandidates molecule unit).length)

@[simp] theorem carbohydrateFiveRingCarrier?_eq_true_iff
    (molecule : RawMolecule) (unit : P94ConformationUnit) :
    carbohydrateFiveRingCarrier? molecule unit = true ↔
      PerceivedCarbohydrateFiveRingCarrier molecule unit := by
  by_cases kind : unit.kind = .fiveMemberedRing
  · simp [carbohydrateFiveRingCarrier?, PerceivedCarbohydrateFiveRingCarrier,
      kind, P94ConformationUnit.SupportedCoordinateRingKind]
    tauto
  · simp [carbohydrateFiveRingCarrier?, PerceivedCarbohydrateFiveRingCarrier, kind]

/-- One retained offset, plane, and exact five-ring side ledger. -/
structure SelectedCarbohydrateTwist where
  offset : Nat
  plane : ExactPlane
  sides : List PlaneSide
  deriving DecidableEq, Repr

def CarbohydrateTwistSelectionJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (offset : Nat) (plane : ExactPlane) (output : SelectedCarbohydrateTwist) : Prop :=
  PerceivedCarbohydrateFiveRingCarrier molecule unit ∧
    ∃ sides,
      RingSidesOfPlane spatial (unit.atoms.rotate offset) plane sides ∧
      IsCarbohydrateFiveRingTwist sides ∧
      output = { offset := offset, plane := plane, sides := sides }

def selectCarbohydrateTwistAtWitness? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (offset : Nat) (plane : ExactPlane) : Option SelectedCarbohydrateTwist :=
  if carbohydrateFiveRingCarrier? molecule unit then do
    let sides ← executableRingSidesOfPlane? spatial (unit.atoms.rotate offset) plane
    if isCarbohydrateFiveRingTwist? sides then
      some { offset := offset, plane := plane, sides := sides }
    else
      none
  else
    none

theorem selectCarbohydrateTwistAtWitness?_eq_some_iff
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : Nat) (plane : ExactPlane)
    (output : SelectedCarbohydrateTwist) :
    selectCarbohydrateTwistAtWitness? molecule spatial unit offset plane = some output ↔
      CarbohydrateTwistSelectionJudgment molecule spatial unit offset plane output := by
  by_cases carrier : carbohydrateFiveRingCarrier? molecule unit = true
  · have carrierMeaning :=
      (carbohydrateFiveRingCarrier?_eq_true_iff molecule unit).mp carrier
    cases sidesComputed : executableRingSidesOfPlane?
        spatial (unit.atoms.rotate offset) plane with
    | none =>
        constructor
        · simp [selectCarbohydrateTwistAtWitness?, carrier, sidesComputed]
        · rintro ⟨_, sides, sidesJudged, _, _⟩
          have someComputed := (executableRingSidesOfPlane?_eq_some_iff
            spatial (unit.atoms.rotate offset) plane sides).mpr sidesJudged
          rw [sidesComputed] at someComputed
          contradiction
    | some sides =>
        by_cases twist : isCarbohydrateFiveRingTwist? sides = true
        · have twistMeaning :=
            (isCarbohydrateFiveRingTwist?_eq_true_iff sides).mp twist
          constructor
          · intro computed
            have outputEqual :
                SelectedCarbohydrateTwist.mk offset plane sides = output := by
              simpa [selectCarbohydrateTwistAtWitness?, carrier, sidesComputed, twist]
                using computed
            exact ⟨carrierMeaning, sides,
              (executableRingSidesOfPlane?_eq_some_iff
                spatial (unit.atoms.rotate offset) plane sides).mp sidesComputed,
              twistMeaning, outputEqual.symm⟩
          · rintro ⟨_, otherSides, otherSidesJudged, otherTwist, outputEqual⟩
            have otherSidesComputed := (executableRingSidesOfPlane?_eq_some_iff
              spatial (unit.atoms.rotate offset) plane otherSides).mpr otherSidesJudged
            rw [sidesComputed] at otherSidesComputed
            have sidesEqual : sides = otherSides := Option.some.inj otherSidesComputed
            subst otherSides
            subst output
            simp [selectCarbohydrateTwistAtWitness?, carrier, sidesComputed, twist]
        · have twistFalse : isCarbohydrateFiveRingTwist? sides = false :=
            Bool.eq_false_of_not_eq_true twist
          constructor
          · simp [selectCarbohydrateTwistAtWitness?, carrier, sidesComputed, twistFalse]
          · rintro ⟨_, otherSides, otherSidesJudged, otherTwist, _⟩
            have otherSidesComputed := (executableRingSidesOfPlane?_eq_some_iff
              spatial (unit.atoms.rotate offset) plane otherSides).mpr otherSidesJudged
            rw [sidesComputed] at otherSidesComputed
            have sidesEqual : sides = otherSides := Option.some.inj otherSidesComputed
            subst otherSides
            exact False.elim (twist
              ((isCarbohydrateFiveRingTwist?_eq_true_iff sides).mpr otherTwist))
  · have carrierFalse : carbohydrateFiveRingCarrier? molecule unit = false :=
      Bool.eq_false_of_not_eq_true carrier
    constructor
    · simp [selectCarbohydrateTwistAtWitness?, carrierFalse]
    · rintro ⟨carrierMeaning, _⟩
      exact False.elim (carrier
        ((carbohydrateFiveRingCarrier?_eq_true_iff molecule unit).mpr carrierMeaning))

def CanonicalCarbohydrateTwistOffsetSelectionJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (offset : Nat) (output : SelectedCarbohydrateTwist) : Prop :=
  CanonicalRingSearchJudgment spatial (unit.atoms.rotate offset) candidatePlanes
    (CarbohydrateTwistSelectionJudgment molecule spatial unit offset) output

def AutomaticCarbohydrateTwistSelectionJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : SelectedCarbohydrateTwist) : Prop :=
  CanonicalFirst
    (CanonicalCarbohydrateTwistOffsetSelectionJudgment molecule spatial unit)
    (List.range unit.atoms.length) output

def automaticCarbohydrateTwistSelection? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    Option SelectedCarbohydrateTwist :=
  firstSuccess?
    (fun offset =>
      canonicalRingSearch? spatial (unit.atoms.rotate offset) candidatePlanes
        (selectCarbohydrateTwistAtWitness? molecule spatial unit offset))
    (List.range unit.atoms.length)

theorem automaticCarbohydrateTwistSelection?_eq_some_iff
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (output : SelectedCarbohydrateTwist) :
    automaticCarbohydrateTwistSelection? molecule spatial unit = some output ↔
      AutomaticCarbohydrateTwistSelectionJudgment molecule spatial unit output :=
  firstSuccess?_eq_some_iff
    (fun offset => canonicalRingSearch? spatial (unit.atoms.rotate offset) candidatePlanes
      (selectCarbohydrateTwistAtWitness? molecule spatial unit offset))
    (CanonicalCarbohydrateTwistOffsetSelectionJudgment molecule spatial unit)
    (fun offset selected => canonicalRingSearch?_eq_some_iff spatial
      (unit.atoms.rotate offset) candidatePlanes
      (selectCarbohydrateTwistAtWitness? molecule spatial unit offset)
      (CarbohydrateTwistSelectionJudgment molecule spatial unit offset)
      (fun plane candidate => selectCarbohydrateTwistAtWitness?_eq_some_iff
        molecule spatial unit offset plane candidate)
      selected)
    (List.range unit.atoms.length) output

theorem automaticCarbohydrateTwistSelection?_eq_none_iff
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) :
    automaticCarbohydrateTwistSelection? molecule spatial unit = none ↔
      ¬∃ output, AutomaticCarbohydrateTwistSelectionJudgment
        molecule spatial unit output := by
  constructor
  · intro computed ⟨output, judged⟩
    have someComputed := (automaticCarbohydrateTwistSelection?_eq_some_iff
      molecule spatial unit output).mpr judged
    rw [computed] at someComputed
    contradiction
  · intro absent
    cases computed : automaticCarbohydrateTwistSelection? molecule spatial unit with
    | none => rfl
    | some output =>
        exact False.elim (absent ⟨output,
          (automaticCarbohydrateTwistSelection?_eq_some_iff
            molecule spatial unit output).mp computed⟩)

def SelectedCarbohydrateTwist.toEvidence (molecule : RawMolecule)
    (unit : P94ConformationUnit) (selected : SelectedCarbohydrateTwist) :
    P94ConformationEvidence Unit Unit :=
  .ringPlane
    { unit := unit
      sides := selected.sides
      saturatedCyclic := False
      symmetricallyEquivalent := False
      carbohydrateFiveRing := PerceivedCarbohydrateFiveRingCarrier molecule unit }

theorem carbohydrateTwistSelectionJudgment_independent (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (offset : Nat) (plane : ExactPlane) (selected : SelectedCarbohydrateTwist)
    (judged : CarbohydrateTwistSelectionJudgment
      molecule spatial unit offset plane selected) :
    IndependentP94ConformationAssignment molecule [selected.toEvidence molecule unit]
      { unit := unit, descriptor := .twist } := by
  rcases judged with ⟨carrier, sides, sidesJudged, twist, rfl⟩
  refine ⟨(SelectedCarbohydrateTwist.toEvidence molecule unit
      (SelectedCarbohydrateTwist.mk offset plane sides) :
      P94ConformationEvidence Unit Unit), by simp, rfl, carrier.2.1, ?_, ?_⟩
  · simp [SelectedCarbohydrateTwist.toEvidence,
      P94ConformationEvidence.MolecularRolesValid, carrier.1]
  · exact ⟨carrier.1, by simpa using sidesJudged.length_eq, carrier, twist⟩

def automaticCarbohydrateTwistAssignment? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    Option P94ConformationAssignment :=
  (automaticCarbohydrateTwistSelection? molecule spatial unit).map fun _ =>
    { unit := unit, descriptor := .twist }

theorem automaticCarbohydrateTwistAssignment?_some_independent
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (assignment : P94ConformationAssignment)
    (computed : automaticCarbohydrateTwistAssignment? molecule spatial unit =
      some assignment) :
    ∃ evidence : P94ConformationEvidence Unit Unit,
      IndependentP94ConformationAssignment molecule [evidence] assignment := by
  cases selectedComputed : automaticCarbohydrateTwistSelection? molecule spatial unit with
  | none => simp [automaticCarbohydrateTwistAssignment?, selectedComputed] at computed
  | some selected =>
      have assignmentEqual :
          ({ unit := unit, descriptor := .twist } : P94ConformationAssignment) =
            assignment := by
        simpa [automaticCarbohydrateTwistAssignment?, selectedComputed] using computed
      have selectedJudged := (automaticCarbohydrateTwistSelection?_eq_some_iff
        molecule spatial unit selected).mp selectedComputed
      rcases selectedJudged.witness with ⟨offset, offsetPresent, offsetJudged⟩
      rcases offsetJudged with ⟨points, pointsJudged, firstPlane⟩
      rcases firstPlane.witness with ⟨plane, planePresent, planeJudged⟩
      refine ⟨selected.toEvidence molecule unit, ?_⟩
      rw [← assignmentEqual]
      exact carbohydrateTwistSelectionJudgment_independent
        molecule spatial unit offset plane selected planeJudged

end BlueBookP94.PracticalCarbohydrateCarrierSelection

end TetraStereo.OneCenter
