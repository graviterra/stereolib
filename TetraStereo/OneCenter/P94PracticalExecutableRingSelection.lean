import TetraStereo.OneCenter.P94CoordinateRingWitnessDiscovery
import TetraStereo.OneCenter.P94ExecutableRingApplicability
import TetraStereo.OneCenter.P94ExecutableRingFamilySelection

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

namespace BlueBookP94.PracticalRingSelection

open CoordinateRing
open ExecutableRingFamilySelection

/-!
# Practical executable P-94 ring selection

This module composes finite molecular admission, exact rational plane geometry, literal
envelope/chair/boat classification, and exhaustive candidate-plane search.  Its automatic entry
point needs only a molecular ring unit and indexed exact coordinates: the reference plane is
selected canonically from ordered triples of actual ring points.

The current selector covers the source-defined envelope, chair, boat, and tub plane families.
Crown symmetry, carbohydrate twist carrier identification, and half-chair unsaturation retain
their separate stronger algorithms until their executable reflections are composed downstream.
-/

/-- One accepted exact plane, its derived side ledger, and the selected P-94 descriptor. -/
structure SelectedRingPlane where
  plane : ExactPlane
  sides : List PlaneSide
  descriptor : P94ConformationDescriptor
  deriving DecidableEq, Repr

/-- Independent descriptor meaning for the currently executable plane families. -/
def DescriptorMatchesSides (kind : P94ConformationUnitKind)
    (sides : List PlaneSide) (descriptor : P94ConformationDescriptor) : Prop :=
  match kind, descriptor with
  | .fiveMemberedRing, .envelope => IsEnvelope sides
  | .sixMemberedRing, .chair => IsChair sides
  | .sixMemberedRing, .boat => IsBoat sides
  | .eightMemberedTubRing, .tub => IsTub sides
  | _, _ => False

/-- Deterministic executable selector for the represented plane-side descriptor relation. -/
def descriptorForSides? (kind : P94ConformationUnitKind) (sides : List PlaneSide) :
    Option P94ConformationDescriptor :=
  match kind with
  | .fiveMemberedRing => executableEnvelopeDescriptor? sides
  | .sixMemberedRing => executableSixRingDescriptor? sides
  | .eightMemberedTubRing => executableTubDescriptor? sides
  | _ => none

@[simp] theorem descriptorForSides?_eq_some_iff
    (kind : P94ConformationUnitKind) (sides : List PlaneSide)
    (descriptor : P94ConformationDescriptor) :
    descriptorForSides? kind sides = some descriptor ↔
      DescriptorMatchesSides kind sides descriptor := by
  cases kind with
  | fiveMemberedRing =>
      cases descriptor <;>
        simp [descriptorForSides?, DescriptorMatchesSides,
          executableEnvelopeDescriptor?]
  | sixMemberedRing =>
      by_cases chair : IsChair sides
      · have chairTrue : isChair? sides = true := (isChair?_eq_true_iff sides).mpr chair
        have notBoat : ¬IsBoat sides := chair_not_boat sides chair
        cases descriptor <;>
          simp [descriptorForSides?, DescriptorMatchesSides,
            executableSixRingDescriptor?, chair, notBoat, chairTrue]
      · have chairFalse : isChair? sides = false := Bool.eq_false_of_not_eq_true
          (fun accepted => chair ((isChair?_eq_true_iff sides).mp accepted))
        by_cases boat : IsBoat sides
        · have boatTrue : isBoat? sides = true := (isBoat?_eq_true_iff sides).mpr boat
          cases descriptor <;>
            simp [descriptorForSides?, DescriptorMatchesSides,
              executableSixRingDescriptor?, chair, boat, chairFalse, boatTrue]
        · have boatFalse : isBoat? sides = false := Bool.eq_false_of_not_eq_true
            (fun accepted => boat ((isBoat?_eq_true_iff sides).mp accepted))
          cases descriptor <;>
            simp [descriptorForSides?, DescriptorMatchesSides,
              executableSixRingDescriptor?, chair, boat, chairFalse, boatFalse]
  | eightMemberedTubRing =>
      cases descriptor <;>
        simp [descriptorForSides?, DescriptorMatchesSides, executableTubDescriptor?]
  | _ =>
      cases descriptor <;> simp [descriptorForSides?, DescriptorMatchesSides]

/-- Independent meaning of one molecularly admitted selection at an explicit witness plane. -/
def PlaneSelectionJudgment (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (plane : ExactPlane) (output : SelectedRingPlane) : Prop :=
  unit.ValidFor molecule ∧
    ∃ sides descriptor,
      RingSidesOfPlane spatial unit.atoms plane sides ∧
      DescriptorMatchesSides unit.kind sides descriptor ∧
      output = { plane := plane, sides := sides, descriptor := descriptor }

/-- Execute molecular admission, exact side extraction, and family classification at one plane. -/
def selectAtPlane? (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (plane : ExactPlane) : Option SelectedRingPlane :=
  if unit.ringValidFor? molecule then do
    let sides ← executableRingSidesOfPlane? spatial unit.atoms plane
    let descriptor ← descriptorForSides? unit.kind sides
    some { plane := plane, sides := sides, descriptor := descriptor }
  else
    none

/-- Exact positive characterization of explicit-plane execution. -/
theorem selectAtPlane?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (plane : ExactPlane) (output : SelectedRingPlane) :
    selectAtPlane? molecule spatial unit plane = some output ↔
      PlaneSelectionJudgment molecule spatial unit plane output := by
  by_cases admitted : unit.ringValidFor? molecule = true
  · have validSupported :=
      (P94ConformationUnit.ringValidFor?_eq_true_iff unit molecule).mp admitted
    cases sidesComputed : executableRingSidesOfPlane? spatial unit.atoms plane with
    | none =>
        constructor
        · intro computed
          simp [selectAtPlane?, admitted, sidesComputed] at computed
        · rintro ⟨_, sides, _, sidesJudged, _, _⟩
          have someComputed := (executableRingSidesOfPlane?_eq_some_iff
            spatial unit.atoms plane sides).mpr sidesJudged
          rw [sidesComputed] at someComputed
          contradiction
    | some sides =>
        cases descriptorComputed : descriptorForSides? unit.kind sides with
        | none =>
            constructor
            · intro computed
              simp [selectAtPlane?, admitted, sidesComputed, descriptorComputed] at computed
            · rintro ⟨_, otherSides, descriptor, sidesJudged, descriptorJudged, _⟩
              have otherSidesComputed := (executableRingSidesOfPlane?_eq_some_iff
                spatial unit.atoms plane otherSides).mpr sidesJudged
              rw [sidesComputed] at otherSidesComputed
              have sidesEqual : sides = otherSides := Option.some.inj otherSidesComputed
              subst otherSides
              have someComputed := (descriptorForSides?_eq_some_iff
                unit.kind sides descriptor).mpr descriptorJudged
              rw [descriptorComputed] at someComputed
              contradiction
        | some descriptor =>
            constructor
            · intro computed
              have outputEqual :
                  ({ plane := plane, sides := sides, descriptor := descriptor } :
                    SelectedRingPlane) = output := by
                simpa [selectAtPlane?, admitted, sidesComputed, descriptorComputed]
                  using computed
              exact ⟨validSupported.1, sides, descriptor,
                (executableRingSidesOfPlane?_eq_some_iff
                  spatial unit.atoms plane sides).mp sidesComputed,
                (descriptorForSides?_eq_some_iff
                  unit.kind sides descriptor).mp descriptorComputed,
                outputEqual.symm⟩
            · rintro ⟨_, otherSides, otherDescriptor,
                sidesJudged, descriptorJudged, outputEqual⟩
              have otherSidesComputed := (executableRingSidesOfPlane?_eq_some_iff
                spatial unit.atoms plane otherSides).mpr sidesJudged
              rw [sidesComputed] at otherSidesComputed
              have sidesEqual : sides = otherSides := Option.some.inj otherSidesComputed
              subst otherSides
              have otherDescriptorComputed := (descriptorForSides?_eq_some_iff
                unit.kind sides otherDescriptor).mpr descriptorJudged
              rw [descriptorComputed] at otherDescriptorComputed
              have descriptorEqual : descriptor = otherDescriptor :=
                Option.some.inj otherDescriptorComputed
              subst otherDescriptor
              subst output
              simp [selectAtPlane?, admitted, sidesComputed, descriptorComputed]
  · constructor
    · intro computed
      simp [selectAtPlane?, admitted] at computed
    · rintro ⟨valid, _, descriptor, _, descriptorJudged, _⟩
      have supported : P94ConformationUnit.SupportedCoordinateRingKind unit.kind := by
        cases kind : unit.kind <;> cases descriptor <;>
          simp [DescriptorMatchesSides, P94ConformationUnit.SupportedCoordinateRingKind,
            kind] at descriptorJudged ⊢
      have accepted :=
        (P94ConformationUnit.ringValidFor?_eq_true_iff unit molecule).mpr
          ⟨valid, supported⟩
      exact False.elim (admitted accepted)

/-- The exhaustive first-success judgment over all exact noncollinear ring-supported planes. -/
def AutomaticRingSelectionJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : SelectedRingPlane) : Prop :=
  CanonicalRingSearchJudgment spatial unit.atoms candidatePlanes
    (PlaneSelectionJudgment molecule spatial unit) output

/-- Practical plane-free selector for envelope, chair, boat, and tub geometries. -/
def automaticRingSelection? (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) : Option SelectedRingPlane :=
  canonicalRingSearch? spatial unit.atoms candidatePlanes
    (selectAtPlane? molecule spatial unit)

/-- Exact canonical-success theorem for the practical automatic selector. -/
theorem automaticRingSelection?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : SelectedRingPlane) :
    automaticRingSelection? molecule spatial unit = some output ↔
      AutomaticRingSelectionJudgment molecule spatial unit output :=
  canonicalRingSearch?_eq_some_iff spatial unit.atoms candidatePlanes
    (selectAtPlane? molecule spatial unit)
    (PlaneSelectionJudgment molecule spatial unit)
    (fun plane candidate => selectAtPlane?_eq_some_iff molecule spatial unit plane candidate)
    output

/-- Exhaustive refusal: no indexed coordinate packet and candidate plane satisfies the exact
molecular and geometric judgment. -/
theorem automaticRingSelection?_eq_none_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    automaticRingSelection? molecule spatial unit = none ↔
      ¬∃ output, AutomaticRingSelectionJudgment molecule spatial unit output := by
  constructor
  · intro computed ⟨output, judged⟩
    have selected := (automaticRingSelection?_eq_some_iff
      molecule spatial unit output).mpr judged
    rw [computed] at selected
    contradiction
  · intro absent
    cases computed : automaticRingSelection? molecule spatial unit with
    | none => rfl
    | some output =>
        exact False.elim (absent ⟨output,
          (automaticRingSelection?_eq_some_iff molecule spatial unit output).mp computed⟩)

/-! ## Executable public assignment adapter -/

/-- Package a selected plane ledger as the existing public P-94 evidence type.  The selected
families do not use crown saturation or carbohydrate applicability fields. -/
def SelectedRingPlane.toEvidence (selected : SelectedRingPlane)
    (unit : P94ConformationUnit) : P94ConformationEvidence Unit Unit :=
  .ringPlane
    { unit := unit
      sides := selected.sides
      saturatedCyclic := False
      symmetricallyEquivalent := False }

/-- Every explicit-plane judgment yields a valid singleton independent P-94 assignment. -/
theorem planeSelectionJudgment_independent (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (plane : ExactPlane) (selected : SelectedRingPlane)
    (judged : PlaneSelectionJudgment molecule spatial unit plane selected) :
    IndependentP94ConformationAssignment molecule [selected.toEvidence unit]
      { unit := unit, descriptor := selected.descriptor } := by
  rcases judged with
    ⟨valid, sides, descriptor, sidesJudged, descriptorJudged, selectedEqual⟩
  subst selected
  have sidesLength : sides.length = unit.atoms.length := sidesJudged.length_eq
  refine ⟨({ plane := plane, sides := sides, descriptor := descriptor } :
      SelectedRingPlane).toEvidence unit, by simp, rfl, valid, ?_, ?_⟩
  · cases kind : unit.kind <;> cases descriptor <;>
      simp [SelectedRingPlane.toEvidence, P94ConformationEvidence.MolecularRolesValid,
        DescriptorMatchesSides, kind] at descriptorJudged ⊢
  · cases kind : unit.kind <;> cases descriptor <;>
      simp [SelectedRingPlane.toEvidence, P94ConformationEvidence.Supports,
        DescriptorMatchesSides, kind, sidesLength] at descriptorJudged ⊢
    all_goals assumption

/-- Direct executable assignment output, avoiding the older noncomputable exhaustive report
filter when one canonical coordinate-ring result is requested. -/
def automaticRingAssignment? (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) : Option P94ConformationAssignment :=
  (automaticRingSelection? molecule spatial unit).map fun selected =>
    { unit := unit, descriptor := selected.descriptor }

/-- Exact positive meaning of the executable assignment adapter. -/
theorem automaticRingAssignment?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (assignment : P94ConformationAssignment) :
    automaticRingAssignment? molecule spatial unit = some assignment ↔
      ∃ selected,
        AutomaticRingSelectionJudgment molecule spatial unit selected ∧
        assignment = { unit := unit, descriptor := selected.descriptor } := by
  cases selectedComputed : automaticRingSelection? molecule spatial unit with
  | none =>
      constructor
      · intro computed
        simp [automaticRingAssignment?, selectedComputed] at computed
      · rintro ⟨selected, judged, _⟩
        have someComputed := (automaticRingSelection?_eq_some_iff
          molecule spatial unit selected).mpr judged
        rw [selectedComputed] at someComputed
        contradiction
  | some selected =>
      have selectedJudged := (automaticRingSelection?_eq_some_iff
        molecule spatial unit selected).mp selectedComputed
      constructor
      · intro computed
        have assignmentEqual :
            ({ unit := unit, descriptor := selected.descriptor } :
              P94ConformationAssignment) = assignment := by
          simpa [automaticRingAssignment?, selectedComputed] using computed
        exact ⟨selected, selectedJudged, assignmentEqual.symm⟩
      · rintro ⟨other, otherJudged, assignmentEqual⟩
        have otherComputed := (automaticRingSelection?_eq_some_iff
          molecule spatial unit other).mpr otherJudged
        rw [selectedComputed] at otherComputed
        have selectedEqual : selected = other := Option.some.inj otherComputed
        subst other
        subst assignment
        simp [automaticRingAssignment?, selectedComputed]

/-- Every emitted executable assignment carries a concrete singleton witness for the existing
independent P-94 transaction relation. -/
theorem automaticRingAssignment?_some_independent (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (assignment : P94ConformationAssignment)
    (computed : automaticRingAssignment? molecule spatial unit = some assignment) :
    ∃ evidence : P94ConformationEvidence Unit Unit,
      IndependentP94ConformationAssignment molecule [evidence] assignment := by
  rcases (automaticRingAssignment?_eq_some_iff
    molecule spatial unit assignment).mp computed with
    ⟨selected, selectedJudged, assignmentEqual⟩
  rcases selectedJudged with ⟨points, pointsJudged, firstJudged⟩
  rcases firstJudged.witness with ⟨plane, _, planeJudged⟩
  refine ⟨selected.toEvidence unit, ?_⟩
  rw [assignmentEqual]
  exact planeSelectionJudgment_independent molecule spatial unit plane selected planeJudged

end BlueBookP94.PracticalRingSelection

end TetraStereo.OneCenter
