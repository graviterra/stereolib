import TetraStereo.OneCenter.P94CoordinateRingWitnessDiscovery
import TetraStereo.OneCenter.P94ExecutableRingApplicability
import TetraStereo.OneCenter.P94ExecutableRingFamilySelection

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

namespace BlueBookP94.PracticalHalfChairSelection

open CoordinateRing
open ExecutableRingFamilySelection

/-!
# Practical executable P-94 half-chair selection

This module composes the molecular six-ring validity check, exact monounsaturation, discovery of
the unique cyclic double-bond offset, exact rational plane construction, and the P-94 half-chair
side pattern.  The public selector therefore needs only a molecule, a ring traversal, and indexed
exact coordinates.
-/

/-- The complete finite witness retained by an accepted half-chair computation. -/
structure SelectedHalfChair where
  offset : Nat
  plane : ExactPlane
  sides : List PlaneSide
  firstRemoteSide : PlaneSide
  secondRemoteSide : PlaneSide
  deriving DecidableEq, Repr

/-- Independent literal meaning of the half-chair side and double-bond pattern at one offset. -/
def HalfChairPatternMeaning (molecule : RawMolecule) (unit : P94ConformationUnit)
    (offset : Nat) (sides : List PlaneSide)
    (firstRemote secondRemote : PlaneSide) : Prop :=
  ∃ firstBondAtom secondBondAtom,
    (unit.atoms.rotate offset)[0]? = some firstBondAtom ∧
      (unit.atoms.rotate offset)[1]? = some secondBondAtom ∧
      molecule.bondOrder firstBondAtom secondBondAtom = 2 ∧
      sides = [.onPlane, .onPlane, .onPlane, firstRemote, secondRemote, .onPlane] ∧
      OppositeSides firstRemote secondRemote

/-- Extract the remote-atom sides only when the exact double-bond and plane pattern holds. -/
def halfChairRemoteSides? (molecule : RawMolecule) (unit : P94ConformationUnit)
    (offset : Nat) (sides : List PlaneSide) : Option (PlaneSide × PlaneSide) :=
  match (unit.atoms.rotate offset)[0]?, (unit.atoms.rotate offset)[1]?, sides with
  | some firstBondAtom, some secondBondAtom,
      [.onPlane, .onPlane, .onPlane, firstRemote, secondRemote, .onPlane] =>
      if molecule.bondOrder firstBondAtom secondBondAtom == 2 &&
          oppositeSides? firstRemote secondRemote then
        some (firstRemote, secondRemote)
      else
        none
  | _, _, _ => none

@[simp] theorem halfChairRemoteSides?_eq_some_iff
    (molecule : RawMolecule) (unit : P94ConformationUnit)
    (offset : Nat) (sides : List PlaneSide) (firstRemote secondRemote : PlaneSide) :
    halfChairRemoteSides? molecule unit offset sides = some (firstRemote, secondRemote) ↔
      HalfChairPatternMeaning molecule unit offset sides firstRemote secondRemote := by
  simp only [halfChairRemoteSides?, HalfChairPatternMeaning]
  split <;> simp_all
  aesop

/-- Executable molecular admission for the half-chair family. -/
def halfChairCarrier? (molecule : RawMolecule) (unit : P94ConformationUnit) : Bool :=
  decide (unit.kind = .sixMemberedRing) &&
    unit.ringValidFor? molecule && unit.monounsaturatedCyclic? molecule

@[simp] theorem halfChairCarrier?_eq_true_iff
    (molecule : RawMolecule) (unit : P94ConformationUnit) :
    halfChairCarrier? molecule unit = true ↔
      unit.kind = .sixMemberedRing ∧
        unit.ValidFor molecule ∧ unit.MonounsaturatedCyclic molecule := by
  by_cases kind : unit.kind = .sixMemberedRing
  · simp [halfChairCarrier?, kind, P94ConformationUnit.SupportedCoordinateRingKind]
  · simp [halfChairCarrier?, kind]

/-- Independent meaning of one accepted explicit offset-and-plane witness. -/
def HalfChairSelectionJudgment (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : Nat) (plane : ExactPlane)
    (output : SelectedHalfChair) : Prop :=
  unit.kind = .sixMemberedRing ∧
    unit.ValidFor molecule ∧
    unit.MonounsaturatedCyclic molecule ∧
    ∃ sides firstRemote secondRemote,
      RingSidesOfPlane spatial (unit.atoms.rotate offset) plane sides ∧
      HalfChairPatternMeaning molecule unit offset sides firstRemote secondRemote ∧
      output =
        { offset := offset
          plane := plane
          sides := sides
          firstRemoteSide := firstRemote
          secondRemoteSide := secondRemote }

/-- Execute the complete molecular/coordinate half-chair test at one explicit witness. -/
def selectHalfChairAtWitness? (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : Nat) (plane : ExactPlane) :
    Option SelectedHalfChair :=
  if halfChairCarrier? molecule unit then do
    let sides ← executableRingSidesOfPlane? spatial (unit.atoms.rotate offset) plane
    let remote ← halfChairRemoteSides? molecule unit offset sides
    some
      { offset := offset
        plane := plane
        sides := sides
        firstRemoteSide := remote.1
        secondRemoteSide := remote.2 }
  else
    none

/-- Exact positive characterization of explicit-witness execution. -/
theorem selectHalfChairAtWitness?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (offset : Nat) (plane : ExactPlane) (output : SelectedHalfChair) :
    selectHalfChairAtWitness? molecule spatial unit offset plane = some output ↔
      HalfChairSelectionJudgment molecule spatial unit offset plane output := by
  by_cases carrier : halfChairCarrier? molecule unit = true
  · have carrierMeaning := (halfChairCarrier?_eq_true_iff molecule unit).mp carrier
    cases sidesComputed : executableRingSidesOfPlane?
        spatial (unit.atoms.rotate offset) plane with
    | none =>
        constructor
        · simp [selectHalfChairAtWitness?, carrier, sidesComputed]
        · rintro ⟨_, _, _, sides, firstRemote, secondRemote,
              sidesJudged, _, _⟩
          have someComputed := (executableRingSidesOfPlane?_eq_some_iff
            spatial (unit.atoms.rotate offset) plane sides).mpr sidesJudged
          rw [sidesComputed] at someComputed
          contradiction
    | some sides =>
        cases remoteComputed : halfChairRemoteSides? molecule unit offset sides with
        | none =>
            constructor
            · simp [selectHalfChairAtWitness?, carrier, sidesComputed, remoteComputed]
            · rintro ⟨_, _, _, otherSides, firstRemote, secondRemote,
                  sidesJudged, pattern, _⟩
              have otherSidesComputed := (executableRingSidesOfPlane?_eq_some_iff
                spatial (unit.atoms.rotate offset) plane otherSides).mpr sidesJudged
              rw [sidesComputed] at otherSidesComputed
              have sidesEqual : sides = otherSides := Option.some.inj otherSidesComputed
              subst otherSides
              have someComputed := (halfChairRemoteSides?_eq_some_iff
                molecule unit offset sides firstRemote secondRemote).mpr pattern
              rw [remoteComputed] at someComputed
              contradiction
        | some remote =>
            rcases remote with ⟨firstRemote, secondRemote⟩
            have sidesJudged := (executableRingSidesOfPlane?_eq_some_iff
              spatial (unit.atoms.rotate offset) plane sides).mp sidesComputed
            have pattern := (halfChairRemoteSides?_eq_some_iff
              molecule unit offset sides firstRemote secondRemote).mp remoteComputed
            constructor
            · intro computed
              have outputEqual :
                  SelectedHalfChair.mk offset plane sides firstRemote secondRemote = output := by
                simpa [selectHalfChairAtWitness?, carrier, sidesComputed, remoteComputed]
                  using computed
              exact ⟨carrierMeaning.1, carrierMeaning.2.1, carrierMeaning.2.2,
                sides, firstRemote, secondRemote, sidesJudged, pattern, outputEqual.symm⟩
            · rintro ⟨_, _, _, otherSides, otherFirst, otherSecond,
                  otherSidesJudged, otherPattern, outputEqual⟩
              have otherSidesComputed := (executableRingSidesOfPlane?_eq_some_iff
                spatial (unit.atoms.rotate offset) plane otherSides).mpr otherSidesJudged
              rw [sidesComputed] at otherSidesComputed
              have sidesEqual : sides = otherSides := Option.some.inj otherSidesComputed
              subst otherSides
              have otherRemoteComputed := (halfChairRemoteSides?_eq_some_iff
                molecule unit offset sides otherFirst otherSecond).mpr otherPattern
              rw [remoteComputed] at otherRemoteComputed
              have remoteEqual : (firstRemote, secondRemote) = (otherFirst, otherSecond) :=
                Option.some.inj otherRemoteComputed
              cases remoteEqual
              subst output
              simp [selectHalfChairAtWitness?, carrier, sidesComputed, remoteComputed]
  · constructor
    · have carrierFalse : halfChairCarrier? molecule unit = false :=
        Bool.eq_false_of_not_eq_true carrier
      simp [selectHalfChairAtWitness?, carrierFalse]
    · rintro ⟨kind, valid, monounsaturated, _⟩
      have accepted := (halfChairCarrier?_eq_true_iff molecule unit).mpr
        ⟨kind, valid, monounsaturated⟩
      exact False.elim (carrier accepted)

/-- First-success semantics over all cyclic offsets and all ring-supported exact planes. -/
def CanonicalHalfChairOffsetSelectionJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (offset : Nat) (output : SelectedHalfChair) : Prop :=
  CanonicalRingSearchJudgment spatial (unit.atoms.rotate offset) candidatePlanes
    (HalfChairSelectionJudgment molecule spatial unit offset) output

def AutomaticHalfChairSelectionJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : SelectedHalfChair) : Prop :=
  CanonicalFirst
    (CanonicalHalfChairOffsetSelectionJudgment molecule spatial unit)
    (List.range unit.atoms.length) output

/-- Plane- and offset-free executable half-chair selector. -/
def automaticHalfChairSelection? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    Option SelectedHalfChair :=
  firstSuccess?
    (fun offset =>
      canonicalRingSearch? spatial (unit.atoms.rotate offset) candidatePlanes
        (selectHalfChairAtWitness? molecule spatial unit offset))
    (List.range unit.atoms.length)

theorem automaticHalfChairSelection?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : SelectedHalfChair) :
    automaticHalfChairSelection? molecule spatial unit = some output ↔
      AutomaticHalfChairSelectionJudgment molecule spatial unit output :=
  firstSuccess?_eq_some_iff
    (fun offset => canonicalRingSearch? spatial (unit.atoms.rotate offset) candidatePlanes
      (selectHalfChairAtWitness? molecule spatial unit offset))
    (CanonicalHalfChairOffsetSelectionJudgment molecule spatial unit)
    (fun offset selected => canonicalRingSearch?_eq_some_iff spatial
      (unit.atoms.rotate offset) candidatePlanes
      (selectHalfChairAtWitness? molecule spatial unit offset)
      (HalfChairSelectionJudgment molecule spatial unit offset)
      (fun plane candidate => selectHalfChairAtWitness?_eq_some_iff
        molecule spatial unit offset plane candidate)
      selected)
    (List.range unit.atoms.length) output

theorem automaticHalfChairSelection?_eq_none_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    automaticHalfChairSelection? molecule spatial unit = none ↔
      ¬∃ output, AutomaticHalfChairSelectionJudgment molecule spatial unit output := by
  constructor
  · intro computed ⟨output, judged⟩
    have someComputed := (automaticHalfChairSelection?_eq_some_iff
      molecule spatial unit output).mpr judged
    rw [computed] at someComputed
    contradiction
  · intro absent
    cases computed : automaticHalfChairSelection? molecule spatial unit with
    | none => rfl
    | some output =>
        exact False.elim (absent ⟨output,
          (automaticHalfChairSelection?_eq_some_iff
            molecule spatial unit output).mp computed⟩)

/-! ## Public assignment and kernel-checkable independent evidence -/

def SelectedHalfChair.toEvidence (molecule : RawMolecule) (unit : P94ConformationUnit)
    (selected : SelectedHalfChair) : P94ConformationEvidence Unit Unit :=
  .halfChair
    { unit := unit
      observation :=
        { ringSize := unit.atoms.length
          doubleBondCount := unit.CycleDoubleBondCount molecule
          firstRemoteSide := selected.firstRemoteSide
          secondRemoteSide := selected.secondRemoteSide } }

theorem halfChairSelectionJudgment_independent (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (offset : Nat) (plane : ExactPlane) (selected : SelectedHalfChair)
    (judged : HalfChairSelectionJudgment molecule spatial unit offset plane selected) :
    IndependentP94ConformationAssignment molecule [selected.toEvidence molecule unit]
      { unit := unit, descriptor := .halfChair } := by
  rcases judged with
    ⟨kind, valid, monounsaturated, sides, firstRemote, secondRemote,
      sidesJudged, pattern, rfl⟩
  rcases pattern with ⟨firstBond, secondBond, firstAt, secondAt,
    doubleAt, sidesEqual, opposite⟩
  have lengthSix : unit.atoms.length = 6 := by
    unfold P94ConformationUnit.ValidFor at valid
    rw [kind] at valid
    exact valid.2.2.2.1
  refine ⟨(SelectedHalfChair.toEvidence molecule unit
      (SelectedHalfChair.mk offset plane sides firstRemote secondRemote) :
      P94ConformationEvidence Unit Unit),
    by simp, rfl, valid, ?_, ?_⟩
  · exact ⟨rfl, monounsaturated⟩
  · exact ⟨kind, lengthSix, monounsaturated.1, opposite⟩

def automaticHalfChairAssignment? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    Option P94ConformationAssignment :=
  (automaticHalfChairSelection? molecule spatial unit).map fun _ =>
    { unit := unit, descriptor := .halfChair }

theorem automaticHalfChairAssignment?_some_independent (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (assignment : P94ConformationAssignment)
    (computed : automaticHalfChairAssignment? molecule spatial unit = some assignment) :
    ∃ evidence : P94ConformationEvidence Unit Unit,
      IndependentP94ConformationAssignment molecule [evidence] assignment := by
  cases selectedComputed : automaticHalfChairSelection? molecule spatial unit with
  | none => simp [automaticHalfChairAssignment?, selectedComputed] at computed
  | some selected =>
      have assignmentEqual :
          ({ unit := unit, descriptor := .halfChair } : P94ConformationAssignment) =
            assignment := by
        simpa [automaticHalfChairAssignment?, selectedComputed] using computed
      have selectedJudged := (automaticHalfChairSelection?_eq_some_iff
        molecule spatial unit selected).mp selectedComputed
      rcases selectedJudged.witness with ⟨offset, offsetPresent, offsetJudged⟩
      rcases offsetJudged with ⟨points, pointsJudged, firstPlane⟩
      rcases firstPlane.witness with ⟨plane, planePresent, planeJudged⟩
      refine ⟨selected.toEvidence molecule unit, ?_⟩
      rw [← assignmentEqual]
      exact halfChairSelectionJudgment_independent
        molecule spatial unit offset plane selected planeJudged

end BlueBookP94.PracticalHalfChairSelection

end TetraStereo.OneCenter
