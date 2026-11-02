import TetraStereo.OneCenter.ConstitutionAutomorphismSemantics
import TetraStereo.OneCenter.P94CoordinateCrownSymmetry
import TetraStereo.OneCenter.P94MolecularRingCarrier

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

/-!
# Molecule- and coordinate-derived P-94 ring conformations

This module composes exact rational plane geometry, actual molecular ring bond orders, and the
independent P-94.3.2 relations.  Plane-side ledgers, crown saturation, crown symmetry, and the
half-chair double-bond count are derived or validated here; none is accepted as an unconnected
caller assertion.

The source phrase “symmetrically equivalent” for a crown is treated as both spatial and chemical:
the cyclic shift must preserve every pairwise squared distance and extend to a full
constitution/label-preserving molecular automorphism.  This is an explicit finite mathematical
completion of the source phrase, not a claim that IUPAC prints this particular search algorithm.
-/

namespace BlueBookP94.CoordinateRing

abbrev CoordinateRingEvidence := P94ConformationEvidence Unit Unit

/-! ## A reusable exact specification selector -/

private noncomputable def specificationChoice? {Alpha : Type*}
    (predicate : Alpha → Prop) : Option Alpha := by
  classical
  exact if present : ∃ value, predicate value then
    some (Classical.choose present)
  else
    none

private theorem specificationChoice?_eq_some_iff {Alpha : Type*}
    (predicate : Alpha → Prop)
    (functional : ∀ left right, predicate left → predicate right → left = right)
    (value : Alpha) :
    specificationChoice? predicate = some value ↔ predicate value := by
  classical
  by_cases present : ∃ candidate, predicate candidate
  · have chosen : predicate (Classical.choose present) := Classical.choose_spec present
    constructor
    · intro computed
      have equal : Classical.choose present = value := by
        simpa [specificationChoice?, present] using computed
      simpa [← equal] using chosen
    · intro judged
      have equal := functional (Classical.choose present) value chosen judged
      simp [specificationChoice?, present, equal]
  · constructor
    · intro computed
      simp [specificationChoice?, present] at computed
    · intro judged
      exact False.elim (present ⟨value, judged⟩)

private theorem specificationChoice?_eq_none_iff {Alpha : Type*}
    (predicate : Alpha → Prop) :
    specificationChoice? predicate = none ↔ ¬∃ value, predicate value := by
  classical
  by_cases present : ∃ value, predicate value <;>
    simp [specificationChoice?, present]

/-! ## Exact molecular meaning of crown equivalence -/

/-- The one-step cyclic shift of the ring traversal extends to a full constitutional automorphism
of the finite molecule.  Atom labels, isotopes, charges, and all bond/nonbond classes are thereby
preserved, not merely the ring polygon's distances. -/
def CyclicRingConstitutionallyEquivalent (molecule : RawMolecule)
    (unit : P94ConformationUnit) : Prop :=
  molecule.HasSeededConstitutionAutomorphism molecule.localizedMancudeEdges
    (List.range molecule.atomCount)
    (unit.atoms.zip (unit.atoms.rotate 1))

private def ordinaryRingRecord (unit : P94ConformationUnit)
    (sides : List PlaneSide) : CoordinateRingEvidence :=
  .ringPlane
    { unit := unit
      sides := sides
      saturatedCyclic := False
      symmetricallyEquivalent := False }

private def crownRingRecord (molecule : RawMolecule) (unit : P94ConformationUnit)
    (points : List CartesianPoint3) (sides : List PlaneSide) : CoordinateRingEvidence :=
  .ringPlane
    { unit := unit
      sides := sides
      saturatedCyclic := unit.SaturatedCyclic molecule
      symmetricallyEquivalent :=
        CyclicallySymmetricallyEquivalent points ∧
          CyclicRingConstitutionallyEquivalent molecule unit }

private def halfChairRecord (molecule : RawMolecule) (unit : P94ConformationUnit)
    (firstRemote secondRemote : PlaneSide) : CoordinateRingEvidence :=
  .halfChair
    { unit := unit
      observation :=
        { ringSize := unit.atoms.length
          doubleBondCount := unit.CycleDoubleBondCount molecule
          firstRemoteSide := firstRemote
          secondRemoteSide := secondRemote } }

/-! ## Envelope, chair/boat, and tub exactness -/

def CoordinateEnvelopeEvidenceJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane)
    (output : CoordinateRingEvidence) : Prop :=
  unit.kind = .fiveMemberedRing ∧
    unit.ValidFor molecule ∧
    ∃ sides,
      RingSidesOfPlane spatial unit.atoms plane sides ∧
      IsEnvelope sides ∧
      output = ordinaryRingRecord unit sides

private theorem coordinateEnvelopeEvidenceJudgment_functional
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (plane : ExactPlane) :
    ∀ left right,
      CoordinateEnvelopeEvidenceJudgment molecule spatial unit plane left →
      CoordinateEnvelopeEvidenceJudgment molecule spatial unit plane right →
      left = right := by
  rintro left right ⟨_, _, leftSides, leftJudged, _, rfl⟩
    ⟨_, _, rightSides, rightJudged, _, rfl⟩
  have equal := RingSidesOfPlane.unique spatial unit.atoms plane leftJudged rightJudged
  subst rightSides
  rfl

noncomputable def coordinateEnvelopeEvidence? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane) :
    Option CoordinateRingEvidence :=
  specificationChoice? (CoordinateEnvelopeEvidenceJudgment molecule spatial unit plane)

theorem coordinateEnvelopeEvidence?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane)
    (output : CoordinateRingEvidence) :
    coordinateEnvelopeEvidence? molecule spatial unit plane = some output ↔
      CoordinateEnvelopeEvidenceJudgment molecule spatial unit plane output :=
  specificationChoice?_eq_some_iff _
    (coordinateEnvelopeEvidenceJudgment_functional molecule spatial unit plane) output

def CoordinateSixRingEvidenceJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane)
    (output : CoordinateRingEvidence) : Prop :=
  unit.kind = .sixMemberedRing ∧
    unit.ValidFor molecule ∧
    ∃ sides,
      RingSidesOfPlane spatial unit.atoms plane sides ∧
      (IsChair sides ∨ IsBoat sides) ∧
      output = ordinaryRingRecord unit sides

private theorem coordinateSixRingEvidenceJudgment_functional
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (plane : ExactPlane) :
    ∀ left right,
      CoordinateSixRingEvidenceJudgment molecule spatial unit plane left →
      CoordinateSixRingEvidenceJudgment molecule spatial unit plane right →
      left = right := by
  rintro left right ⟨_, _, leftSides, leftJudged, _, rfl⟩
    ⟨_, _, rightSides, rightJudged, _, rfl⟩
  have equal := RingSidesOfPlane.unique spatial unit.atoms plane leftJudged rightJudged
  subst rightSides
  rfl

noncomputable def coordinateSixRingEvidence? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane) :
    Option CoordinateRingEvidence :=
  specificationChoice? (CoordinateSixRingEvidenceJudgment molecule spatial unit plane)

theorem coordinateSixRingEvidence?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane)
    (output : CoordinateRingEvidence) :
    coordinateSixRingEvidence? molecule spatial unit plane = some output ↔
      CoordinateSixRingEvidenceJudgment molecule spatial unit plane output :=
  specificationChoice?_eq_some_iff _
    (coordinateSixRingEvidenceJudgment_functional molecule spatial unit plane) output

def CoordinateTubEvidenceJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane)
    (output : CoordinateRingEvidence) : Prop :=
  unit.kind = .eightMemberedTubRing ∧
    unit.ValidFor molecule ∧
    ∃ sides,
      RingSidesOfPlane spatial unit.atoms plane sides ∧
      IsTub sides ∧
      output = ordinaryRingRecord unit sides

private theorem coordinateTubEvidenceJudgment_functional
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (plane : ExactPlane) :
    ∀ left right,
      CoordinateTubEvidenceJudgment molecule spatial unit plane left →
      CoordinateTubEvidenceJudgment molecule spatial unit plane right →
      left = right := by
  rintro left right ⟨_, _, leftSides, leftJudged, _, rfl⟩
    ⟨_, _, rightSides, rightJudged, _, rfl⟩
  have equal := RingSidesOfPlane.unique spatial unit.atoms plane leftJudged rightJudged
  subst rightSides
  rfl

noncomputable def coordinateTubEvidence? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane) :
    Option CoordinateRingEvidence :=
  specificationChoice? (CoordinateTubEvidenceJudgment molecule spatial unit plane)

theorem coordinateTubEvidence?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) (plane : ExactPlane)
    (output : CoordinateRingEvidence) :
    coordinateTubEvidence? molecule spatial unit plane = some output ↔
      CoordinateTubEvidenceJudgment molecule spatial unit plane output :=
  specificationChoice?_eq_some_iff _
    (coordinateTubEvidenceJudgment_functional molecule spatial unit plane) output

/-! ## Exact half-chair geometry and molecular unsaturation -/

/-- After rotating the ring so its unique double bond is positions `0-1`, positions `5,0,1,2`
lie in the reference plane and the two atoms remote from the double bond, positions `3,4`, lie on
opposite sides. -/
def HalfChairCoordinateGeometry (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (doubleBondOffset : ℕ) (plane : ExactPlane)
    (firstRemote secondRemote : PlaneSide) : Prop :=
  let atoms := unit.atoms.rotate doubleBondOffset
  ∃ sides firstBondAtom secondBondAtom,
    RingSidesOfPlane spatial atoms plane sides ∧
    atoms[0]? = some firstBondAtom ∧
    atoms[1]? = some secondBondAtom ∧
    molecule.bondOrder firstBondAtom secondBondAtom = 2 ∧
    sides[5]? = some .onPlane ∧
    sides[0]? = some .onPlane ∧
    sides[1]? = some .onPlane ∧
    sides[2]? = some .onPlane ∧
    sides[3]? = some firstRemote ∧
    sides[4]? = some secondRemote ∧
    OppositeSides firstRemote secondRemote

def CoordinateHalfChairEvidenceJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (doubleBondOffset : ℕ) (plane : ExactPlane) (output : CoordinateRingEvidence) : Prop :=
  unit.kind = .sixMemberedRing ∧
    unit.ValidFor molecule ∧
    unit.MonounsaturatedCyclic molecule ∧
    ∃ firstRemote secondRemote,
      HalfChairCoordinateGeometry molecule spatial unit doubleBondOffset plane
        firstRemote secondRemote ∧
      output = halfChairRecord molecule unit firstRemote secondRemote

private theorem coordinateHalfChairEvidenceJudgment_functional
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (doubleBondOffset : ℕ) (plane : ExactPlane) :
    ∀ left right,
      CoordinateHalfChairEvidenceJudgment molecule spatial unit doubleBondOffset plane left →
      CoordinateHalfChairEvidenceJudgment molecule spatial unit doubleBondOffset plane right →
      left = right := by
  rintro left right
    ⟨_, _, _, leftFirst, leftSecond, leftGeometry, rfl⟩
    ⟨_, _, _, rightFirst, rightSecond, rightGeometry, rfl⟩
  dsimp [HalfChairCoordinateGeometry] at leftGeometry rightGeometry
  rcases leftGeometry with
    ⟨leftSides, leftBondFirst, leftBondSecond, leftSidesJudged, _, _, _, _, _, _, _,
      leftFirstAt, leftSecondAt, _⟩
  rcases rightGeometry with
    ⟨rightSides, rightBondFirst, rightBondSecond, rightSidesJudged, _, _, _, _, _, _, _,
      rightFirstAt, rightSecondAt, _⟩
  have sidesEqual := RingSidesOfPlane.unique spatial
    (unit.atoms.rotate doubleBondOffset) plane leftSidesJudged rightSidesJudged
  subst rightSides
  have firstEqual : leftFirst = rightFirst := by simpa [leftFirstAt] using rightFirstAt
  have secondEqual : leftSecond = rightSecond := by simpa [leftSecondAt] using rightSecondAt
  subst rightFirst
  subst rightSecond
  rfl

noncomputable def coordinateHalfChairEvidence? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (doubleBondOffset : ℕ) (plane : ExactPlane) : Option CoordinateRingEvidence :=
  specificationChoice?
    (CoordinateHalfChairEvidenceJudgment molecule spatial unit doubleBondOffset plane)

theorem coordinateHalfChairEvidence?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (doubleBondOffset : ℕ) (plane : ExactPlane) (output : CoordinateRingEvidence) :
    coordinateHalfChairEvidence? molecule spatial unit doubleBondOffset plane = some output ↔
      CoordinateHalfChairEvidenceJudgment molecule spatial unit doubleBondOffset plane output :=
  specificationChoice?_eq_some_iff _
    (coordinateHalfChairEvidenceJudgment_functional
      molecule spatial unit doubleBondOffset plane) output

/-! ## Exact crown geometry, saturation, and labeled symmetry -/

def CoordinateCrownEvidenceJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : CoordinateRingEvidence) : Prop :=
  unit.kind = .crownRing ∧
    unit.ValidFor molecule ∧
    unit.SaturatedCyclic molecule ∧
    CyclicRingConstitutionallyEquivalent molecule unit ∧
    ∃ points sides,
      SpatialPointsAt spatial unit.atoms points ∧
      CoordinateCrownSides points sides ∧
      output = crownRingRecord molecule unit points sides

private theorem coordinateCrownEvidenceJudgment_functional
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) :
    ∀ left right,
      CoordinateCrownEvidenceJudgment molecule spatial unit left →
      CoordinateCrownEvidenceJudgment molecule spatial unit right →
      left = right := by
  rintro left right
    ⟨_, _, _, _, leftPoints, leftSides, leftPointsJudged, leftSidesJudged, rfl⟩
    ⟨_, _, _, _, rightPoints, rightSides, rightPointsJudged, rightSidesJudged, rfl⟩
  have leftPointsEq :=
    (spatialPointsAt?_eq_some_iff spatial unit.atoms leftPoints).mpr leftPointsJudged
  have rightPointsEq :=
    (spatialPointsAt?_eq_some_iff spatial unit.atoms rightPoints).mpr rightPointsJudged
  rw [leftPointsEq] at rightPointsEq
  have pointsEqual : leftPoints = rightPoints := Option.some.inj rightPointsEq
  subst rightPoints
  have leftSidesEq :=
    (coordinateCrownSides?_eq_some_iff leftPoints leftSides).mpr leftSidesJudged
  have rightSidesEq :=
    (coordinateCrownSides?_eq_some_iff leftPoints rightSides).mpr rightSidesJudged
  rw [leftSidesEq] at rightSidesEq
  have sidesEqual : leftSides = rightSides := Option.some.inj rightSidesEq
  subst rightSides
  rfl

noncomputable def coordinateCrownEvidence? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    Option CoordinateRingEvidence :=
  specificationChoice? (CoordinateCrownEvidenceJudgment molecule spatial unit)

theorem coordinateCrownEvidence?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : CoordinateRingEvidence) :
    coordinateCrownEvidence? molecule spatial unit = some output ↔
      CoordinateCrownEvidenceJudgment molecule spatial unit output :=
  specificationChoice?_eq_some_iff _
    (coordinateCrownEvidenceJudgment_functional molecule spatial unit) output

/-! ## Unified coordinate-ring analyzer and public exact-once output -/

inductive CoordinateRingInput where
  | envelope (unit : P94ConformationUnit) (plane : ExactPlane)
  | sixRing (unit : P94ConformationUnit) (plane : ExactPlane)
  | halfChair (unit : P94ConformationUnit) (doubleBondOffset : ℕ) (plane : ExactPlane)
  | crown (unit : P94ConformationUnit)
  | tub (unit : P94ConformationUnit) (plane : ExactPlane)
  deriving DecidableEq, Repr

def CoordinateRingEvidenceJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) : CoordinateRingInput → CoordinateRingEvidence → Prop
  | .envelope unit plane => CoordinateEnvelopeEvidenceJudgment molecule spatial unit plane
  | .sixRing unit plane => CoordinateSixRingEvidenceJudgment molecule spatial unit plane
  | .halfChair unit offset plane =>
      CoordinateHalfChairEvidenceJudgment molecule spatial unit offset plane
  | .crown unit => CoordinateCrownEvidenceJudgment molecule spatial unit
  | .tub unit plane => CoordinateTubEvidenceJudgment molecule spatial unit plane

noncomputable def coordinateRingEvidence? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) : CoordinateRingInput → Option CoordinateRingEvidence
  | .envelope unit plane => coordinateEnvelopeEvidence? molecule spatial unit plane
  | .sixRing unit plane => coordinateSixRingEvidence? molecule spatial unit plane
  | .halfChair unit offset plane =>
      coordinateHalfChairEvidence? molecule spatial unit offset plane
  | .crown unit => coordinateCrownEvidence? molecule spatial unit
  | .tub unit plane => coordinateTubEvidence? molecule spatial unit plane

theorem coordinateRingEvidence?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (input : CoordinateRingInput)
    (output : CoordinateRingEvidence) :
    coordinateRingEvidence? molecule spatial input = some output ↔
      CoordinateRingEvidenceJudgment molecule spatial input output := by
  cases input with
  | envelope unit plane => exact coordinateEnvelopeEvidence?_eq_some_iff _ _ _ _ _
  | sixRing unit plane => exact coordinateSixRingEvidence?_eq_some_iff _ _ _ _ _
  | halfChair unit offset plane => exact coordinateHalfChairEvidence?_eq_some_iff _ _ _ _ _ _
  | crown unit => exact coordinateCrownEvidence?_eq_some_iff _ _ _ _
  | tub unit plane => exact coordinateTubEvidence?_eq_some_iff _ _ _ _ _

theorem coordinateRingEvidence?_eq_none_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (input : CoordinateRingInput) :
    coordinateRingEvidence? molecule spatial input = none ↔
      ¬∃ output, CoordinateRingEvidenceJudgment molecule spatial input output := by
  constructor
  · intro computed ⟨output, judged⟩
    have some := (coordinateRingEvidence?_eq_some_iff molecule spatial input output).mpr judged
    rw [computed] at some
    contradiction
  · intro absent
    cases computed : coordinateRingEvidence? molecule spatial input with
    | none => rfl
    | some output =>
        exact False.elim (absent ⟨output,
          (coordinateRingEvidence?_eq_some_iff molecule spatial input output).mp computed⟩)

/-- Every coordinate judgment already contains enough geometry and molecular information to
construct at least one independently supported P-94 descriptor. -/
theorem coordinateRingEvidenceJudgment_supports
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : CoordinateRingInput) (output : CoordinateRingEvidence)
    (judged : CoordinateRingEvidenceJudgment molecule spatial input output) :
    output.unit.ValidFor molecule ∧
      output.MolecularRolesValid molecule ∧
      ∃ descriptor, output.Supports descriptor := by
  cases input with
  | envelope unit plane =>
      rcases judged with ⟨kind, valid, sides, sidesJudged, envelope, rfl⟩
      refine ⟨valid, ?_, .envelope, ?_⟩
      · simp [ordinaryRingRecord, P94ConformationEvidence.MolecularRolesValid, kind]
      · exact ⟨kind, sidesJudged.length_eq, envelope⟩
  | sixRing unit plane =>
      rcases judged with ⟨kind, valid, sides, sidesJudged, shape, rfl⟩
      refine ⟨valid, ?_, ?_⟩
      · simp [ordinaryRingRecord, P94ConformationEvidence.MolecularRolesValid, kind]
      · rcases shape with chair | boat
        · exact ⟨.chair, kind, sidesJudged.length_eq, chair⟩
        · exact ⟨.boat, kind, sidesJudged.length_eq, boat⟩
  | halfChair unit offset plane =>
      rcases judged with
        ⟨kind, valid, monounsaturated, firstRemote, secondRemote, geometry, rfl⟩
      have lengthSix : unit.atoms.length = 6 := by
        unfold P94ConformationUnit.ValidFor at valid
        rw [kind] at valid
        exact valid.2.2.2.1
      dsimp [HalfChairCoordinateGeometry] at geometry
      rcases geometry with
        ⟨sides, firstBond, secondBond, sidesJudged, firstAt, secondAt, doubleAt,
          side5, side0, side1, side2, firstRemoteAt, secondRemoteAt, opposite⟩
      refine ⟨valid, ?_, .halfChair, ?_⟩
      · exact ⟨rfl, monounsaturated⟩
      · exact ⟨kind, lengthSix, monounsaturated.1, opposite⟩
  | crown unit =>
      rcases judged with
        ⟨kind, valid, saturated, constitutional, points, sides,
          pointsJudged, crownJudged, rfl⟩
      have sidesLength : sides.length = unit.atoms.length :=
        crownJudged.length_eq.trans pointsJudged.length_eq
      have spatialSymmetry : CyclicallySymmetricallyEquivalent points :=
        crownJudged.1.2.2.2
      have crown : IsCrown sides
          (CyclicallySymmetricallyEquivalent points ∧
            CyclicRingConstitutionallyEquivalent molecule unit) :=
        crownJudged.isCrown_of_symmetricallyEquivalent _
          ⟨spatialSymmetry, constitutional⟩
      refine ⟨valid, ?_, .crown, ?_⟩
      · simpa [crownRingRecord, P94ConformationEvidence.MolecularRolesValid, kind]
          using saturated
      · exact ⟨kind, sidesLength, saturated, crown⟩
  | tub unit plane =>
      rcases judged with ⟨kind, valid, sides, sidesJudged, tub, rfl⟩
      refine ⟨valid, ?_, .tub, ?_⟩
      · simp [ordinaryRingRecord, P94ConformationEvidence.MolecularRolesValid, kind]
      · exact ⟨kind, sidesJudged.length_eq, tub⟩

noncomputable def coordinateRingAssignments
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : CoordinateRingInput) : List P94ConformationAssignment :=
  match coordinateRingEvidence? certified.result.parsed spatial input with
  | none => []
  | some output => certified.analyzeP94Conformation [output]

theorem coordinateRingAssignments_mem_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : CoordinateRingInput) (assignment : P94ConformationAssignment) :
    assignment ∈ coordinateRingAssignments certified spatial input ↔
      ∃ output,
        CoordinateRingEvidenceJudgment certified.result.parsed spatial input output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  cases computed : coordinateRingEvidence? certified.result.parsed spatial input with
  | none =>
      constructor
      · intro present
        unfold coordinateRingAssignments at present
        rw [computed] at present
        simp at present
      · rintro ⟨output, judged, _⟩
        have some := (coordinateRingEvidence?_eq_some_iff
          certified.result.parsed spatial input output).mpr judged
        rw [computed] at some
        contradiction
  | some output =>
      constructor
      · intro present
        have analyzedPresent : assignment ∈ certified.analyzeP94Conformation [output] := by
          unfold coordinateRingAssignments at present
          rw [computed] at present
          exact present
        have independent := (mem_analyzeP94Conformation_iff_independent
          certified [output] assignment).mp analyzedPresent
        exact ⟨output,
          (coordinateRingEvidence?_eq_some_iff
            certified.result.parsed spatial input output).mp computed,
          independent⟩
      · rintro ⟨other, judged, independent⟩
        have otherComputed := (coordinateRingEvidence?_eq_some_iff
          certified.result.parsed spatial input other).mpr judged
        rw [computed] at otherComputed
        have equal : output = other := Option.some.inj otherComputed
        subst other
        have analyzedPresent := (mem_analyzeP94Conformation_iff_independent
          certified [output] assignment).mpr independent
        unfold coordinateRingAssignments
        rw [computed]
        exact analyzedPresent

theorem coordinateRingAssignments_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : CoordinateRingInput) :
    (coordinateRingAssignments certified spatial input).Nodup := by
  classical
  cases computed : coordinateRingEvidence? certified.result.parsed spatial input with
  | none =>
      unfold coordinateRingAssignments
      rw [computed]
      simp
  | some output =>
      unfold coordinateRingAssignments
      rw [computed]
      exact analyzeP94Conformation_nodup certified [output]

theorem coordinateRingAssignment_count_eq_one_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : CoordinateRingInput) (assignment : P94ConformationAssignment) :
    List.count assignment (coordinateRingAssignments certified spatial input) = 1 ↔
      ∃ output,
        CoordinateRingEvidenceJudgment certified.result.parsed spatial input output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  rw [← coordinateRingAssignments_mem_iff]
  constructor
  · intro countOne
    by_contra absent
    have countZero : List.count assignment
        (coordinateRingAssignments certified spatial input) = 0 :=
      List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem
      (coordinateRingAssignments_nodup certified spatial input)

/-- Every successful coordinate derivation reaches the public P-94 report exactly once for at
least one descriptor, with both molecular-role and independent-support obligations discharged. -/
theorem coordinateRingEvidence_success_emits_descriptor_exactly_once
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : CoordinateRingInput) (output : CoordinateRingEvidence)
    (computed : coordinateRingEvidence? certified.result.parsed spatial input = some output) :
    ∃ descriptor,
      List.count
        ({ unit := output.unit, descriptor := descriptor } : P94ConformationAssignment)
        (coordinateRingAssignments certified spatial input) = 1 := by
  have judged := (coordinateRingEvidence?_eq_some_iff
    certified.result.parsed spatial input output).mp computed
  rcases coordinateRingEvidenceJudgment_supports
    certified.result.parsed spatial input output judged with
    ⟨valid, roles, descriptor, support⟩
  refine ⟨descriptor,
    (coordinateRingAssignment_count_eq_one_iff certified spatial input _).mpr ?_⟩
  refine ⟨output, judged, output, by simp, rfl, valid, roles, support⟩

end BlueBookP94.CoordinateRing
end TetraStereo.OneCenter
