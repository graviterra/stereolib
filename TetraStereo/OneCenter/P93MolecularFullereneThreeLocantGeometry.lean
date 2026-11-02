import TetraStereo.OneCenter.P93MolecularFullereneSymmetry
import TetraStereo.OneCenter.LocalizedRule3Spatial

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

open P94MolecularRingCycleScheduler

/-!
# Molecular fullerene three-locant geometry

P-93.5.6 assigns `f,xC` or `f,xA` by viewing the polygon in which numbering starts
from outside the cage and following C-1 to C-2 to C-3.  This module binds that rule to
an explicit numbering and exact rational molecular coordinates.

The supplied numbering is checked to be a bijection onto the molecular cage and to begin with
three consecutive atoms of one named cage face.  Selection of that numbering under the complete
systematic or trivial fullerene-numbering rules remains an upstream nomenclature authority; the
present module does not confuse a finite bijection with a proof that it is the preferred numbering.

For geometry, the plane through C-1, C-2, and C-3 must support the whole cage: every cage atom is
on its interior side or in the plane, and at least one cage atom is strictly inside.  This makes
the exterior viewing side exact, rejects aligned/degenerate evidence, and determines clockwise
versus anticlockwise without a floating-point tolerance or a caller-supplied turn Boolean.
-/

/-- Explicit atom numbering and the polygon in which that numbering starts. -/
structure MolecularFullereneNumberingEvidence where
  numberingKind : FullereneNumberingKind
  atomsByLocant : List ℕ
  startingFace : List ℕ

/-- The numbering is a duplicate-free bijection onto the cage, and locants 1, 2, and 3 are
consecutive atoms of the declared starting polygon. -/
def MolecularFullereneNumberingEvidenceJudgment
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence) : Prop :=
  evidence.atomsByLocant.Nodup ∧
    evidence.atomsByLocant.toFinset = input.carrier ∧
    evidence.startingFace ∈ input.faces ∧
    ∃ first second third,
      evidence.atomsByLocant[0]? = some first ∧
        evidence.atomsByLocant[1]? = some second ∧
        evidence.atomsByLocant[2]? = some third ∧
        first ≠ second ∧
        second ≠ third ∧
        first ≠ third ∧
        IsNamedCycleEdge evidence.startingFace first second ∧
        IsNamedCycleEdge evidence.startingFace second third

noncomputable instance molecularFullereneNumberingEvidenceJudgmentDecidable
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence) :
    Decidable (MolecularFullereneNumberingEvidenceJudgment input evidence) :=
  Classical.propDecidable _

/-- Deterministic atom lookup for a zero-based locant offset.  Valid numbering evidence proves
that offsets `0`, `1`, and `2` never use the fallback. -/
def molecularFullereneNumberedAtom
    (evidence : MolecularFullereneNumberingEvidence) (offset : ℕ) : ℕ :=
  evidence.atomsByLocant[offset]?.getD 0

/-- A harmless coordinate fallback used only to keep the geometric measure total.  The spatial
completeness conjunct below proves that no cage atom uses it. -/
def molecularFullereneFallbackPoint : CartesianPoint3 :=
  { x := 0, y := 0, z := 0 }

/-- Total coordinate lookup for one atom. -/
def molecularFullerenePointAt
    (spatial : SpatialConfiguration) (atom : ℕ) : CartesianPoint3 :=
  spatial.positions[atom]?.getD molecularFullereneFallbackPoint

/-- Every atom of this cage has exact spatial coordinates. -/
def MolecularFullereneCarrierSpatiallyComplete
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput) : Prop :=
  ∀ atom ∈ input.carrier,
    ∃ point, spatial.positions[atom]? = some point

noncomputable instance molecularFullereneCarrierSpatiallyCompleteDecidable
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput) :
    Decidable (MolecularFullereneCarrierSpatiallyComplete spatial input) :=
  Classical.propDecidable _

/-- Signed side of `point` relative to the directed C-1/C-2/C-3 plane. -/
def fullereneThreeLocantPlaneMeasure
    (first second third point : CartesianPoint3) : ℚ :=
  RationalVector3.dot
    (RationalVector3.cross
      (CartesianPoint3.displacement first second)
      (CartesianPoint3.displacement first third))
    (CartesianPoint3.displacement first point)

/-- Signed side of one cage atom relative to the numbered C-1/C-2/C-3 plane. -/
def molecularFullereneThreeLocantAtomMeasure
    (spatial : SpatialConfiguration)
    (evidence : MolecularFullereneNumberingEvidence)
    (atom : ℕ) : ℚ :=
  fullereneThreeLocantPlaneMeasure
    (molecularFullerenePointAt spatial
      (molecularFullereneNumberedAtom evidence 0))
    (molecularFullerenePointAt spatial
      (molecularFullereneNumberedAtom evidence 1))
    (molecularFullerenePointAt spatial
      (molecularFullereneNumberedAtom evidence 2))
    (molecularFullerenePointAt spatial atom)

/-- Exact exterior-view convention.  If the cage interior is on the positive side of the directed
C-1/C-2/C-3 plane, the exterior normal is negative and the viewed path is clockwise.  If the
interior is on the negative side, the exterior normal is positive and the path is anticlockwise.
The strict witness excludes a collinear triple or a wholly coplanar cage. -/
def MolecularFullereneThreeLocantInteriorSideJudgment
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence) : ThreeLocantTurn → Prop
  | .clockwise =>
      (∀ atom ∈ input.carrier,
        0 ≤ molecularFullereneThreeLocantAtomMeasure spatial evidence atom) ∧
      ∃ atom ∈ input.carrier,
        0 < molecularFullereneThreeLocantAtomMeasure spatial evidence atom
  | .anticlockwise =>
      (∀ atom ∈ input.carrier,
        molecularFullereneThreeLocantAtomMeasure spatial evidence atom ≤ 0) ∧
      ∃ atom ∈ input.carrier,
        molecularFullereneThreeLocantAtomMeasure spatial evidence atom < 0

noncomputable instance molecularFullereneThreeLocantInteriorSideJudgmentDecidable
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (turn : ThreeLocantTurn) :
    Decidable (MolecularFullereneThreeLocantInteriorSideJudgment
      spatial input evidence turn) :=
  Classical.propDecidable _

/-- Independent exact meaning of the numbered three-locant turn. -/
def MolecularFullereneThreeLocantTurnJudgment
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (turn : ThreeLocantTurn) : Prop :=
  MolecularFullereneNumberingEvidenceJudgment input evidence ∧
    MolecularFullereneCarrierSpatiallyComplete spatial input ∧
    MolecularFullereneThreeLocantInteriorSideJudgment spatial input evidence turn

noncomputable instance molecularFullereneThreeLocantTurnJudgmentDecidable
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (turn : ThreeLocantTurn) :
    Decidable (MolecularFullereneThreeLocantTurnJudgment
      spatial input evidence turn) :=
  Classical.propDecidable _

/-- Exact supporting-side evidence cannot assign both clockwise and anticlockwise to the same
numbering and conformation. -/
theorem molecularFullereneThreeLocantTurnJudgment_functional
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (first second : ThreeLocantTurn)
    (firstJudged : MolecularFullereneThreeLocantTurnJudgment
      spatial input evidence first)
    (secondJudged : MolecularFullereneThreeLocantTurnJudgment
      spatial input evidence second) :
    first = second := by
  cases first <;> cases second
  · rfl
  · exfalso
    have clockwiseSide := firstJudged.2.2
    have anticlockwiseSide := secondJudged.2.2
    rcases clockwiseSide.2 with ⟨atom, atomPresent, positive⟩
    exact (not_lt_of_ge (anticlockwiseSide.1 atom atomPresent)) positive
  · exfalso
    have anticlockwiseSide := firstJudged.2.2
    have clockwiseSide := secondJudged.2.2
    rcases anticlockwiseSide.2 with ⟨atom, atomPresent, negative⟩
    exact (not_lt_of_ge (clockwiseSide.1 atom atomPresent)) negative
  · rfl

/-- Derive the P-93.5.6 turn from exact numbering and supporting-face coordinate evidence. -/
noncomputable def molecularFullereneThreeLocantTurn?
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence) : Option ThreeLocantTurn :=
  if MolecularFullereneThreeLocantTurnJudgment
      spatial input evidence .clockwise then
    some .clockwise
  else if MolecularFullereneThreeLocantTurnJudgment
      spatial input evidence .anticlockwise then
    some .anticlockwise
  else
    none

/-- Turn derivation succeeds exactly for the independent numbered exterior-view judgment. -/
@[simp] theorem molecularFullereneThreeLocantTurn?_eq_some_iff
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (turn : ThreeLocantTurn) :
    molecularFullereneThreeLocantTurn? spatial input evidence = some turn ↔
      MolecularFullereneThreeLocantTurnJudgment spatial input evidence turn := by
  by_cases clockwise : MolecularFullereneThreeLocantTurnJudgment
      spatial input evidence .clockwise
  · have notAnticlockwise : ¬MolecularFullereneThreeLocantTurnJudgment
        spatial input evidence .anticlockwise := by
      intro anticlockwise
      cases molecularFullereneThreeLocantTurnJudgment_functional
        spatial input evidence .clockwise .anticlockwise clockwise anticlockwise
    cases turn <;>
      simp [molecularFullereneThreeLocantTurn?, clockwise, notAnticlockwise]
  · by_cases anticlockwise : MolecularFullereneThreeLocantTurnJudgment
        spatial input evidence .anticlockwise
    · cases turn <;>
        simp [molecularFullereneThreeLocantTurn?, clockwise, anticlockwise]
    · cases turn <;>
        simp [molecularFullereneThreeLocantTurn?, clockwise, anticlockwise]

/-- Refusal is exact: neither orientation satisfies the independent numbered geometry. -/
@[simp] theorem molecularFullereneThreeLocantTurn?_eq_none_iff
    (spatial : SpatialConfiguration)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence) :
    molecularFullereneThreeLocantTurn? spatial input evidence = none ↔
      ¬∃ turn,
        MolecularFullereneThreeLocantTurnJudgment spatial input evidence turn := by
  constructor
  · intro computed
    rintro ⟨turn, judged⟩
    have success :=
      (molecularFullereneThreeLocantTurn?_eq_some_iff
        spatial input evidence turn).mpr judged
    rw [computed] at success
    cases success
  · intro noTurn
    cases computed : molecularFullereneThreeLocantTurn? spatial input evidence with
    | none => rfl
    | some turn =>
        have judged :=
          (molecularFullereneThreeLocantTurn?_eq_some_iff
            spatial input evidence turn).mp computed
        exact False.elim (noTurn ⟨turn, judged⟩)

/-- Strict source record that adds exact numbering and spatial turn evidence to the oriented
symmetry-derived fullerene record. -/
structure SpatiallyDerivedMolecularFullereneConfigurationInput where
  symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput
  numberingEvidence : MolecularFullereneNumberingEvidence

/-- The oriented cage and substitution test are valid, the numbered turn follows from exact
coordinates, and the legacy descriptor evidence contains precisely that numbering kind and turn. -/
def SpatiallyDerivedMolecularFullereneConfigurationInputJudgment
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput) : Prop :=
  SymmetryDerivedMolecularFullereneConfigurationInputJudgment
      molecule input.symmetryInput ∧
    ∃ turn,
      MolecularFullereneThreeLocantTurnJudgment spatial input.symmetryInput.cage
          input.numberingEvidence turn ∧
        input.symmetryInput.cage.descriptorEvidence.cageNumberingKind =
          some input.numberingEvidence.numberingKind ∧
        input.symmetryInput.cage.descriptorEvidence.cageTurn = some turn

noncomputable instance spatiallyDerivedMolecularFullereneConfigurationInputJudgmentDecidable
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput) :
    Decidable (SpatiallyDerivedMolecularFullereneConfigurationInputJudgment
      molecule spatial input) :=
  Classical.propDecidable _

/-- Admit a strict fullerene record only when its numbering-tagged turn is exactly coordinate
derived. -/
noncomputable def spatiallyDerivedMolecularFullereneConfigurationInput?
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput) :
    Option SymmetryDerivedMolecularFullereneConfigurationInput :=
  if SpatiallyDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input then
    some input.symmetryInput
  else
    none

@[simp] theorem spatiallyDerivedMolecularFullereneConfigurationInput?_eq_some_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput) :
    spatiallyDerivedMolecularFullereneConfigurationInput? molecule spatial input =
        some symmetryInput ↔
      SpatiallyDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input ∧
        symmetryInput = input.symmetryInput := by
  by_cases valid :
      SpatiallyDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input
  · simp [spatiallyDerivedMolecularFullereneConfigurationInput?, valid, eq_comm]
  · simp [spatiallyDerivedMolecularFullereneConfigurationInput?, valid]

@[simp] theorem spatiallyDerivedMolecularFullereneConfigurationInput?_eq_none_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput) :
    spatiallyDerivedMolecularFullereneConfigurationInput? molecule spatial input = none ↔
      ¬SpatiallyDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input := by
  by_cases valid :
      SpatiallyDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input
  · simp [spatiallyDerivedMolecularFullereneConfigurationInput?, valid]
  · simp [spatiallyDerivedMolecularFullereneConfigurationInput?, valid]

/-- All and only strict records whose numbering-tagged cage turn is derived from exact spatial
evidence. -/
noncomputable def validatedSpatiallyDerivedMolecularFullereneConfigurationInputs
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput) :
    List SymmetryDerivedMolecularFullereneConfigurationInput :=
  inputs.filterMap
    (spatiallyDerivedMolecularFullereneConfigurationInput? molecule spatial)

/-- Exact finite-family membership at the numbered geometry boundary. -/
theorem mem_validatedSpatiallyDerivedMolecularFullereneConfigurationInputs_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput) :
    symmetryInput ∈
        validatedSpatiallyDerivedMolecularFullereneConfigurationInputs
          molecule spatial inputs ↔
      ∃ input ∈ inputs,
        SpatiallyDerivedMolecularFullereneConfigurationInputJudgment
            molecule spatial input ∧
          symmetryInput = input.symmetryInput := by
  simp [validatedSpatiallyDerivedMolecularFullereneConfigurationInputs,
    spatiallyDerivedMolecularFullereneConfigurationInput?_eq_some_iff]

/-- Independent complete meaning of an emitted assignment sourced from exact numbered geometry.
The witness remains the original spatial record, while same-cage agreement ranges over the family
surviving spatial, symmetry, and molecular-cage validation. -/
def SpatiallyDerivedMolecularFullereneConfigurationAssignmentJudgment
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs,
    SpatiallyDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input ∧
      FullereneConfigurationAssignmentJudgment
        input.symmetryInput.cage.toFullereneConfigurationInput assignment ∧
      FullereneConfigurationAssignmentAgreement
        (validatedMolecularFullereneConfigurationInputs molecule
          (validatedSymmetryDerivedMolecularFullereneConfigurationInputs molecule
            (validatedSpatiallyDerivedMolecularFullereneConfigurationInputs
              molecule spatial inputs)))
        assignment

/-- The spatial source judgment is exactly the symmetry-backed assignment judgment over records
admitted by the numbered geometry boundary. -/
theorem spatiallyDerivedMolecularFullereneConfigurationAssignmentJudgment_iff_symmetry
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    SpatiallyDerivedMolecularFullereneConfigurationAssignmentJudgment
        molecule spatial inputs assignment ↔
      SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment molecule
        (validatedSpatiallyDerivedMolecularFullereneConfigurationInputs
          molecule spatial inputs)
        assignment := by
  unfold SpatiallyDerivedMolecularFullereneConfigurationAssignmentJudgment
  unfold SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
  constructor
  · rintro ⟨input, inputPresent, spatialJudged, localJudged, agreement⟩
    exact ⟨input.symmetryInput,
      (mem_validatedSpatiallyDerivedMolecularFullereneConfigurationInputs_iff
        molecule spatial inputs input.symmetryInput).mpr
          ⟨input, inputPresent, spatialJudged, rfl⟩,
      spatialJudged.1, localJudged, agreement⟩
  · rintro ⟨symmetryInput, symmetryPresent, _symmetryJudged, localJudged, agreement⟩
    rcases (mem_validatedSpatiallyDerivedMolecularFullereneConfigurationInputs_iff
      molecule spatial inputs symmetryInput).mp symmetryPresent with
      ⟨input, inputPresent, spatialJudged, symmetryEq⟩
    subst symmetryInput
    exact ⟨input, inputPresent, spatialJudged, localJudged, agreement⟩

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
