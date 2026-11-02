import TetraStereo.OneCenter.P94CoordinateRingConformation
import TetraStereo.OneCenter.P94ExecutableCoordinateRingGeometry
import TetraStereo.OneCenter.P94GeneralCrownSymmetry

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

/-!
# Finite exact witness discovery for P-94 ring conformations

The coordinate conformation layer accepts an exact reference plane, and its half-chair branch
also accepts the cyclic position of the unique double bond.  This module removes both caller
witnesses for the currently represented P-94 ring families.

For a ring coordinate list, every ordered triple of actual ring points is enumerated and the
degenerate triples are discarded by exact rational noncollinearity.  The remaining finite list
is searched in list order.  Half-chair discovery searches every offset in
`List.range unit.atoms.length`, then every such plane.  A declarative `CanonicalFirst` relation
specifies the first-success policy independently of the recursive evaluator.

There is deliberately no approximate equality or tolerance in this layer.
-/

namespace BlueBookP94.CoordinateRing

/-! ## A proved finite first-success selector -/

/-- Select the first successful value in a finite candidate list. -/
def firstSuccess? {Alpha Beta : Type*} (evaluate : Alpha → Option Beta) :
    List Alpha → Option Beta
  | [] => none
  | candidate :: candidates =>
      match evaluate candidate with
      | some output => some output
      | none => firstSuccess? evaluate candidates

/-- Independent declarative meaning of the first successful candidate. -/
inductive CanonicalFirst {Alpha Beta : Type*} (judgment : Alpha → Beta → Prop) :
    List Alpha → Beta → Prop
  | head {candidate : Alpha} {candidates : List Alpha} {output : Beta}
      (judged : judgment candidate output) :
      CanonicalFirst judgment (candidate :: candidates) output
  | tail {candidate : Alpha} {candidates : List Alpha} {output : Beta}
      (refused : ¬∃ candidateOutput, judgment candidate candidateOutput)
      (next : CanonicalFirst judgment candidates output) :
      CanonicalFirst judgment (candidate :: candidates) output

theorem firstSuccess?_eq_some_iff {Alpha Beta : Type*}
    (evaluate : Alpha → Option Beta) (judgment : Alpha → Beta → Prop)
    (exact : ∀ candidate output, evaluate candidate = some output ↔
      judgment candidate output) (candidates : List Alpha) (output : Beta) :
    firstSuccess? evaluate candidates = some output ↔
      CanonicalFirst judgment candidates output := by
  induction candidates with
  | nil =>
      constructor
      · intro computed
        simp [firstSuccess?] at computed
      · intro judged
        cases judged
  | cons candidate candidates inductionHypothesis =>
      cases candidateComputed : evaluate candidate with
      | none =>
          have refused : ¬∃ candidateOutput, judgment candidate candidateOutput := by
            rintro ⟨candidateOutput, candidateJudged⟩
            have someComputed := (exact candidate candidateOutput).mpr candidateJudged
            rw [candidateComputed] at someComputed
            contradiction
          constructor
          · intro computed
            have tailComputed : firstSuccess? evaluate candidates = some output := by
              simpa [firstSuccess?, candidateComputed] using computed
            exact .tail refused (inductionHypothesis.mp tailComputed)
          · intro judged
            cases judged with
            | head candidateJudged =>
                have someComputed := (exact candidate output).mpr candidateJudged
                rw [candidateComputed] at someComputed
                contradiction
            | tail _ next =>
                simpa [firstSuccess?, candidateComputed] using
                  inductionHypothesis.mpr next
      | some selected =>
          have selectedJudged : judgment candidate selected :=
            (exact candidate selected).mp candidateComputed
          constructor
          · intro computed
            have someEqual : some selected = some output := by
              simpa [firstSuccess?, candidateComputed] using computed
            have equal : selected = output := Option.some.inj someEqual
            subst output
            exact .head selectedJudged
          · intro judged
            cases judged with
            | head candidateJudged =>
                have outputComputed := (exact candidate output).mpr candidateJudged
                rw [candidateComputed] at outputComputed
                have equal : selected = output := Option.some.inj outputComputed
                simp [firstSuccess?, candidateComputed, equal]
            | tail refused _ =>
                exact False.elim (refused ⟨selected, selectedJudged⟩)

theorem CanonicalFirst.witness {Alpha Beta : Type*}
    {judgment : Alpha → Beta → Prop} {candidates : List Alpha} {output : Beta}
    (judged : CanonicalFirst judgment candidates output) :
    ∃ candidate, candidate ∈ candidates ∧ judgment candidate output := by
  induction judged with
  | head candidateJudged => exact ⟨_, by simp, candidateJudged⟩
  | tail _ _ inductionHypothesis =>
      rcases inductionHypothesis with ⟨candidate, present, candidateJudged⟩
      exact ⟨candidate, by simp [present], candidateJudged⟩

theorem CanonicalFirst.exists_iff {Alpha Beta : Type*}
    (judgment : Alpha → Beta → Prop) (candidates : List Alpha) :
    (∃ output, CanonicalFirst judgment candidates output) ↔
      ∃ candidate, candidate ∈ candidates ∧ ∃ output, judgment candidate output := by
  induction candidates with
  | nil =>
      constructor
      · rintro ⟨_, judged⟩
        cases judged
      · simp
  | cons candidate candidates inductionHypothesis =>
      by_cases present : ∃ output, judgment candidate output
      · rcases present with ⟨output, judged⟩
        constructor
        · intro _
          exact ⟨candidate, by simp, output, judged⟩
        · intro _
          exact ⟨output, .head judged⟩
      · constructor
        · rintro ⟨output, judged⟩
          cases judged with
          | head candidateJudged =>
              exact False.elim (present ⟨output, candidateJudged⟩)
          | tail _ next =>
              rcases inductionHypothesis.mp ⟨output, next⟩ with
                ⟨later, laterPresent, laterOutput, laterJudged⟩
              exact ⟨later, by simp [laterPresent], laterOutput, laterJudged⟩
        · rintro ⟨found, foundPresent, output, foundJudged⟩
          have foundCases : found = candidate ∨ found ∈ candidates := by
            simpa using foundPresent
          rcases foundCases with rfl | laterPresent
          · exact False.elim (present ⟨output, foundJudged⟩)
          · rcases inductionHypothesis.mpr
              ⟨found, laterPresent, output, foundJudged⟩ with
              ⟨selected, selectedJudged⟩
            exact ⟨selected, .tail present selectedJudged⟩

theorem CanonicalFirst.functional {Alpha Beta : Type*}
    {judgment : Alpha → Beta → Prop}
    (pointwise : ∀ candidate left right,
      judgment candidate left → judgment candidate right → left = right)
    {candidates : List Alpha} {left right : Beta}
    (leftJudged : CanonicalFirst judgment candidates left)
    (rightJudged : CanonicalFirst judgment candidates right) : left = right := by
  induction candidates generalizing left right with
  | nil => cases leftJudged
  | cons candidate candidates inductionHypothesis =>
      cases leftJudged with
      | head leftAtHead =>
          cases rightJudged with
          | head rightAtHead =>
              exact pointwise candidate left right leftAtHead rightAtHead
          | tail refused _ =>
              exact False.elim (refused ⟨left, leftAtHead⟩)
      | tail refused leftNext =>
          cases rightJudged with
          | head rightAtHead =>
              exact False.elim (refused ⟨right, rightAtHead⟩)
          | tail _ rightNext =>
              exact inductionHypothesis leftNext rightNext

/-! ## Exhaustive exact plane and offset candidates -/

/-- Every ordered triple drawn from the ring coordinate list. -/
def allRingPointPlanes (points : List CartesianPoint3) : List ExactPlane :=
  points.flatMap fun first =>
    points.flatMap fun second =>
      points.map fun third => { first := first, second := second, third := third }

/-- Exactly the noncollinear ordered triples of actual ring coordinates.  The determinant test
is a Boolean so this finite candidate list is code-generatable. -/
def candidatePlanes (points : List CartesianPoint3) : List ExactPlane :=
  (allRingPointPlanes points).filter ExactPlane.nondegenerate?

theorem allRingPointPlanes_mem_iff (points : List CartesianPoint3) (plane : ExactPlane) :
    plane ∈ allRingPointPlanes points ↔
      plane.first ∈ points ∧ plane.second ∈ points ∧ plane.third ∈ points := by
  cases plane with
  | mk first second third => simp [allRingPointPlanes]

/-- Candidate membership is precisely actual-ring support plus exact noncollinearity. -/
theorem candidatePlanes_mem_iff (points : List CartesianPoint3) (plane : ExactPlane) :
    plane ∈ candidatePlanes points ↔
      plane.Nondegenerate ∧ plane.SpannedByRingPoints points := by
  simp [candidatePlanes, allRingPointPlanes_mem_iff,
    ExactPlane.SpannedByRingPoints, and_assoc, and_comm]

theorem ringSidesOfPlane_has_candidate (spatial : SpatialConfiguration)
    (atoms : List ℕ) (plane : ExactPlane) (sides : List PlaneSide)
    (judged : RingSidesOfPlane spatial atoms plane sides) :
    ∃ points,
      SpatialPointsAt spatial atoms points ∧ plane ∈ candidatePlanes points := by
  rcases judged with
    ⟨nondegenerate, points, pointsJudged, _, planeSpanned, _⟩
  exact ⟨points, pointsJudged,
    (candidatePlanes_mem_iff points plane).mpr ⟨nondegenerate, planeSpanned⟩⟩

/-- One finite half-chair search key: a canonical cyclic offset and an exact plane. -/
structure HalfChairWitnessCandidate where
  offset : ℕ
  plane : ExactPlane
  deriving DecidableEq, Repr

/-- All canonical cyclic offsets, each paired with every exact ring-supported plane. -/
def halfChairWitnessCandidates (unit : P94ConformationUnit)
    (points : List CartesianPoint3) : List HalfChairWitnessCandidate :=
  (List.range unit.atoms.length).flatMap fun offset =>
    (candidatePlanes points).map fun plane => { offset := offset, plane := plane }

theorem halfChairWitnessCandidates_mem_iff (unit : P94ConformationUnit)
    (points : List CartesianPoint3) (candidate : HalfChairWitnessCandidate) :
    candidate ∈ halfChairWitnessCandidates unit points ↔
      candidate.offset < unit.atoms.length ∧ candidate.plane ∈ candidatePlanes points := by
  classical
  cases candidate with
  | mk offset plane => simp [halfChairWitnessCandidates]

/-! ## Coordinate lookup followed by canonical finite search -/

def CanonicalRingSearchJudgment {Alpha Beta : Type*}
    (spatial : SpatialConfiguration) (atoms : List ℕ)
    (candidates : List CartesianPoint3 → List Alpha)
    (judgment : Alpha → Beta → Prop) (output : Beta) : Prop :=
  ∃ points,
    SpatialPointsAt spatial atoms points ∧
    CanonicalFirst judgment (candidates points) output

def canonicalRingSearch? {Alpha Beta : Type*}
    (spatial : SpatialConfiguration) (atoms : List ℕ)
    (candidates : List CartesianPoint3 → List Alpha)
    (evaluate : Alpha → Option Beta) : Option Beta :=
  match spatialPointsAt? spatial atoms with
  | none => none
  | some points => firstSuccess? evaluate (candidates points)

theorem canonicalRingSearch?_eq_some_iff {Alpha Beta : Type*}
    (spatial : SpatialConfiguration) (atoms : List ℕ)
    (candidates : List CartesianPoint3 → List Alpha)
    (evaluate : Alpha → Option Beta) (judgment : Alpha → Beta → Prop)
    (exact : ∀ candidate output, evaluate candidate = some output ↔
      judgment candidate output) (output : Beta) :
    canonicalRingSearch? spatial atoms candidates evaluate = some output ↔
      CanonicalRingSearchJudgment spatial atoms candidates judgment output := by
  cases pointsComputed : spatialPointsAt? spatial atoms with
  | none =>
      constructor
      · intro computed
        simp [canonicalRingSearch?, pointsComputed] at computed
      · rintro ⟨points, pointsJudged, _⟩
        have someComputed :=
          (spatialPointsAt?_eq_some_iff spatial atoms points).mpr pointsJudged
        rw [pointsComputed] at someComputed
        contradiction
  | some selectedPoints =>
      have selectedPointsJudged : SpatialPointsAt spatial atoms selectedPoints :=
        (spatialPointsAt?_eq_some_iff spatial atoms selectedPoints).mp pointsComputed
      constructor
      · intro computed
        have selected := (firstSuccess?_eq_some_iff evaluate judgment exact
          (candidates selectedPoints) output).mp (by
            simpa [canonicalRingSearch?, pointsComputed] using computed)
        exact ⟨selectedPoints, selectedPointsJudged, selected⟩
      · rintro ⟨points, pointsJudged, selected⟩
        have pointsComputed' :=
          (spatialPointsAt?_eq_some_iff spatial atoms points).mpr pointsJudged
        rw [pointsComputed] at pointsComputed'
        have equal : selectedPoints = points := Option.some.inj pointsComputed'
        subst points
        simpa [canonicalRingSearch?, pointsComputed] using
          (firstSuccess?_eq_some_iff evaluate judgment exact
            (candidates selectedPoints) output).mpr selected

theorem CanonicalRingSearchJudgment.exists_iff {Alpha Beta : Type*}
    (spatial : SpatialConfiguration) (atoms : List ℕ)
    (candidates : List CartesianPoint3 → List Alpha)
    (judgment : Alpha → Beta → Prop) :
    (∃ output, CanonicalRingSearchJudgment spatial atoms candidates judgment output) ↔
      ∃ points,
        SpatialPointsAt spatial atoms points ∧
        ∃ candidate, candidate ∈ candidates points ∧
          ∃ output, judgment candidate output := by
  constructor
  · rintro ⟨output, points, pointsJudged, selected⟩
    rcases selected.witness with ⟨candidate, present, candidateJudged⟩
    exact ⟨points, pointsJudged, candidate, present, output, candidateJudged⟩
  · rintro ⟨points, pointsJudged, candidate, present, output, candidateJudged⟩
    rcases (CanonicalFirst.exists_iff judgment (candidates points)).mpr
      ⟨candidate, present, output, candidateJudged⟩ with ⟨selected, selectedJudged⟩
    exact ⟨selected, points, pointsJudged, selectedJudged⟩

/-- Independent meaning of applying an exact family judgment to the uniquely collected ring
coordinate packet. -/
def CoordinatePacketJudgment {Beta : Type*}
    (spatial : SpatialConfiguration) (atoms : List ℕ)
    (judgment : List CartesianPoint3 → Beta → Prop) (output : Beta) : Prop :=
  ∃ points, SpatialPointsAt spatial atoms points ∧ judgment points output

def coordinatePacketEvidence? {Beta : Type*}
    (spatial : SpatialConfiguration) (atoms : List ℕ)
    (evaluate : List CartesianPoint3 → Option Beta) : Option Beta :=
  match spatialPointsAt? spatial atoms with
  | none => none
  | some points => evaluate points

theorem coordinatePacketEvidence?_eq_some_iff {Beta : Type*}
    (spatial : SpatialConfiguration) (atoms : List ℕ)
    (evaluate : List CartesianPoint3 → Option Beta)
    (judgment : List CartesianPoint3 → Beta → Prop)
    (exact : ∀ points output, evaluate points = some output ↔ judgment points output)
    (output : Beta) :
    coordinatePacketEvidence? spatial atoms evaluate = some output ↔
      CoordinatePacketJudgment spatial atoms judgment output := by
  cases pointsComputed : spatialPointsAt? spatial atoms with
  | none =>
      constructor
      · intro computed
        simp [coordinatePacketEvidence?, pointsComputed] at computed
      · rintro ⟨points, pointsJudged, _⟩
        have someComputed :=
          (spatialPointsAt?_eq_some_iff spatial atoms points).mpr pointsJudged
        rw [pointsComputed] at someComputed
        contradiction
  | some selectedPoints =>
      have selectedPointsJudged : SpatialPointsAt spatial atoms selectedPoints :=
        (spatialPointsAt?_eq_some_iff spatial atoms selectedPoints).mp pointsComputed
      constructor
      · intro computed
        have evaluated : evaluate selectedPoints = some output := by
          simpa [coordinatePacketEvidence?, pointsComputed] using computed
        exact ⟨selectedPoints, selectedPointsJudged,
          (exact selectedPoints output).mp evaluated⟩
      · rintro ⟨points, pointsJudged, judged⟩
        have pointsComputed' :=
          (spatialPointsAt?_eq_some_iff spatial atoms points).mpr pointsJudged
        rw [pointsComputed] at pointsComputed'
        have equal : selectedPoints = points := Option.some.inj pointsComputed'
        subst points
        simpa [coordinatePacketEvidence?, pointsComputed] using
          (exact selectedPoints output).mpr judged

/-! ## Witness-free family interface -/

/-- A P-94 coordinate request with neither a plane nor a half-chair rotation supplied. -/
inductive AutomaticCoordinateRingInput where
  | envelope (unit : P94ConformationUnit)
  | sixRing (unit : P94ConformationUnit)
  | halfChair (unit : P94ConformationUnit)
  | crown (unit : P94ConformationUnit)
  | tub (unit : P94ConformationUnit)
  deriving DecidableEq, Repr

/-- The exact plane search performed at one canonical half-chair offset. -/
def CanonicalHalfChairOffsetJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (offset : ℕ) (output : CoordinateRingEvidence) : Prop :=
  CanonicalRingSearchJudgment spatial (unit.atoms.rotate offset) candidatePlanes
    (CoordinateHalfChairEvidenceJudgment molecule spatial unit offset) output

/-- Independent canonical meaning of the witness-free analyzer's selected evidence. -/
def AutomaticCoordinateRingEvidenceJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) :
    AutomaticCoordinateRingInput → CoordinateRingEvidence → Prop
  | .envelope unit, output =>
      CanonicalRingSearchJudgment spatial unit.atoms candidatePlanes
        (CoordinateEnvelopeEvidenceJudgment molecule spatial unit) output
  | .sixRing unit, output =>
      CanonicalRingSearchJudgment spatial unit.atoms candidatePlanes
        (CoordinateSixRingEvidenceJudgment molecule spatial unit) output
  | .halfChair unit, output =>
      CanonicalFirst (CanonicalHalfChairOffsetJudgment molecule spatial unit)
        (List.range unit.atoms.length) output
  | .crown unit, output =>
      CoordinatePacketJudgment spatial unit.atoms
        (GeneralCrownEvidenceJudgment molecule unit) output
  | .tub unit, output =>
      CanonicalRingSearchJudgment spatial unit.atoms candidatePlanes
        (CoordinateTubEvidenceJudgment molecule spatial unit) output

/-- Existence of some finite candidate accepted by an existing independent family judgment. -/
def AutomaticCoordinateRingWitness (molecule : RawMolecule)
    (spatial : SpatialConfiguration) : AutomaticCoordinateRingInput → Prop
  | .envelope unit =>
      ∃ points,
        SpatialPointsAt spatial unit.atoms points ∧
        ∃ plane, plane ∈ candidatePlanes points ∧
          ∃ output, CoordinateEnvelopeEvidenceJudgment molecule spatial unit plane output
  | .sixRing unit =>
      ∃ points,
        SpatialPointsAt spatial unit.atoms points ∧
        ∃ plane, plane ∈ candidatePlanes points ∧
          ∃ output, CoordinateSixRingEvidenceJudgment molecule spatial unit plane output
  | .halfChair unit =>
      ∃ offset,
        offset < unit.atoms.length ∧
        ∃ points,
          SpatialPointsAt spatial (unit.atoms.rotate offset) points ∧
          ∃ plane, plane ∈ candidatePlanes points ∧
            ∃ output, CoordinateHalfChairEvidenceJudgment molecule spatial unit
              offset plane output
  | .crown unit =>
      ∃ points,
        SpatialPointsAt spatial unit.atoms points ∧
        ∃ output, GeneralCrownEvidenceJudgment molecule unit points output
  | .tub unit =>
      ∃ points,
        SpatialPointsAt spatial unit.atoms points ∧
        ∃ plane, plane ∈ candidatePlanes points ∧
          ∃ output, CoordinateTubEvidenceJudgment molecule spatial unit plane output

/-- The existential surface of the former API, before planes and offsets became internal. -/
def PriorCoordinateRingFamilyWitness (molecule : RawMolecule)
    (spatial : SpatialConfiguration) : AutomaticCoordinateRingInput → Prop
  | .envelope unit =>
      ∃ plane output, CoordinateEnvelopeEvidenceJudgment molecule spatial unit plane output
  | .sixRing unit =>
      ∃ plane output, CoordinateSixRingEvidenceJudgment molecule spatial unit plane output
  | .halfChair unit =>
      ∃ offset plane output,
        CoordinateHalfChairEvidenceJudgment molecule spatial unit offset plane output
  | .crown unit =>
      ∃ points,
        SpatialPointsAt spatial unit.atoms points ∧
        ∃ output, GeneralCrownEvidenceJudgment molecule unit points output
  | .tub unit =>
      ∃ plane output, CoordinateTubEvidenceJudgment molecule spatial unit plane output

/-- Output-specific soundness statement, retaining the accepted finite witness. -/
def AutomaticCoordinateRingOutputWitness (molecule : RawMolecule)
    (spatial : SpatialConfiguration) :
    AutomaticCoordinateRingInput → CoordinateRingEvidence → Prop
  | .envelope unit, output =>
      ∃ points, SpatialPointsAt spatial unit.atoms points ∧
        ∃ plane, plane ∈ candidatePlanes points ∧
          CoordinateEnvelopeEvidenceJudgment molecule spatial unit plane output
  | .sixRing unit, output =>
      ∃ points, SpatialPointsAt spatial unit.atoms points ∧
        ∃ plane, plane ∈ candidatePlanes points ∧
          CoordinateSixRingEvidenceJudgment molecule spatial unit plane output
  | .halfChair unit, output =>
      ∃ offset,
        offset < unit.atoms.length ∧
        ∃ points, SpatialPointsAt spatial (unit.atoms.rotate offset) points ∧
          ∃ plane, plane ∈ candidatePlanes points ∧
            CoordinateHalfChairEvidenceJudgment molecule spatial unit offset plane output
  | .crown unit, output =>
      ∃ points,
        SpatialPointsAt spatial unit.atoms points ∧
        GeneralCrownEvidenceJudgment molecule unit points output
  | .tub unit, output =>
      ∃ points, SpatialPointsAt spatial unit.atoms points ∧
        ∃ plane, plane ∈ candidatePlanes points ∧
          CoordinateTubEvidenceJudgment molecule spatial unit plane output

/-! ## Completeness relative to the former arbitrary-offset half-chair API -/

/-- Half-chair geometry is periodic in the caller's offset, exactly as `List.rotate` is. -/
theorem coordinateHalfChairEvidenceJudgment_rotate_mod_iff
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : ℕ) (plane : ExactPlane)
    (output : CoordinateRingEvidence) :
    CoordinateHalfChairEvidenceJudgment molecule spatial unit
        (offset % unit.atoms.length) plane output ↔
      CoordinateHalfChairEvidenceJudgment molecule spatial unit offset plane output := by
  simp only [CoordinateHalfChairEvidenceJudgment, HalfChairCoordinateGeometry,
    List.rotate_mod]

/-- Searching `0 .. ringLength-1` loses no success admitted by the former API at an arbitrary
natural-number offset.  A successful six-ring judgment proves nonemptiness, and `rotate_mod`
places its exact geometry at the enumerated remainder. -/
theorem automaticHalfChairWitness_iff_exists_coordinateHalfChairEvidenceJudgment
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) :
    AutomaticCoordinateRingWitness molecule spatial (.halfChair unit) ↔
      ∃ offset plane output,
        CoordinateHalfChairEvidenceJudgment molecule spatial unit offset plane output := by
  constructor
  · rintro ⟨offset, _, _, _, plane, _, output, judged⟩
    exact ⟨offset, plane, output, judged⟩
  · rintro ⟨offset, plane, output, judged⟩
    rcases judged with
      ⟨kind, valid, monounsaturated, firstRemote, secondRemote, geometry, outputEq⟩
    have lengthSix : unit.atoms.length = 6 := by
      unfold P94ConformationUnit.ValidFor at valid
      rw [kind] at valid
      exact valid.2.2.2.1
    have lengthPositive : 0 < unit.atoms.length := by omega
    have reducedJudged : CoordinateHalfChairEvidenceJudgment molecule spatial unit
        (offset % unit.atoms.length) plane output :=
      (coordinateHalfChairEvidenceJudgment_rotate_mod_iff
        molecule spatial unit offset plane output).mpr
        ⟨kind, valid, monounsaturated, firstRemote, secondRemote, geometry, outputEq⟩
    have reducedJudgedCopy := reducedJudged
    rcases reducedJudged with
      ⟨reducedKind, reducedValid, reducedMonounsaturated,
        reducedFirstRemote, reducedSecondRemote, reducedGeometry, reducedOutputEq⟩
    dsimp [HalfChairCoordinateGeometry] at reducedGeometry
    rcases reducedGeometry with
      ⟨sides, firstBondAtom, secondBondAtom, sidesJudged,
        firstAt, secondAt, doubleAt, side5, side0, side1, side2,
        firstRemoteAt, secondRemoteAt, opposite⟩
    rcases sidesJudged with
      ⟨nondegenerate, points, pointsJudged, pointsNodup, planeSpanned, sideRelations⟩
    have planePresent : plane ∈ candidatePlanes points :=
      (candidatePlanes_mem_iff points plane).mpr ⟨nondegenerate, planeSpanned⟩
    refine ⟨offset % unit.atoms.length, Nat.mod_lt offset lengthPositive,
      points, pointsJudged, plane, planePresent, output, ?_⟩
    exact reducedJudgedCopy

/-- The finite candidate domains are complete for every formerly caller-witnessed represented
family, not merely complete relative to their own definition. -/
theorem automaticCoordinateRingWitness_iff_prior_family_witness
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) :
    AutomaticCoordinateRingWitness molecule spatial input ↔
      PriorCoordinateRingFamilyWitness molecule spatial input := by
  cases input with
  | envelope unit =>
      constructor
      · rintro ⟨_, _, plane, _, output, judged⟩
        exact ⟨plane, output, judged⟩
      · rintro ⟨plane, output, judged⟩
        have judgedCopy := judged
        rcases judged with ⟨_, _, sides, sidesJudged, _, _⟩
        rcases ringSidesOfPlane_has_candidate spatial unit.atoms plane sides sidesJudged with
          ⟨points, pointsJudged, planePresent⟩
        exact ⟨points, pointsJudged, plane, planePresent, output, judgedCopy⟩
  | sixRing unit =>
      constructor
      · rintro ⟨_, _, plane, _, output, judged⟩
        exact ⟨plane, output, judged⟩
      · rintro ⟨plane, output, judged⟩
        have judgedCopy := judged
        rcases judged with ⟨_, _, sides, sidesJudged, _, _⟩
        rcases ringSidesOfPlane_has_candidate spatial unit.atoms plane sides sidesJudged with
          ⟨points, pointsJudged, planePresent⟩
        exact ⟨points, pointsJudged, plane, planePresent, output, judgedCopy⟩
  | halfChair unit =>
      exact automaticHalfChairWitness_iff_exists_coordinateHalfChairEvidenceJudgment
        molecule spatial unit
  | crown unit => rfl
  | tub unit =>
      constructor
      · rintro ⟨_, _, plane, _, output, judged⟩
        exact ⟨plane, output, judged⟩
      · rintro ⟨plane, output, judged⟩
        have judgedCopy := judged
        rcases judged with ⟨_, _, sides, sidesJudged, _, _⟩
        rcases ringSidesOfPlane_has_candidate spatial unit.atoms plane sides sidesJudged with
          ⟨points, pointsJudged, planePresent⟩
        exact ⟨points, pointsJudged, plane, planePresent, output, judgedCopy⟩

noncomputable def automaticCoordinateRingEvidence? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) :
    AutomaticCoordinateRingInput → Option CoordinateRingEvidence
  | .envelope unit =>
      canonicalRingSearch? spatial unit.atoms candidatePlanes
        (coordinateEnvelopeEvidence? molecule spatial unit)
  | .sixRing unit =>
      canonicalRingSearch? spatial unit.atoms candidatePlanes
        (coordinateSixRingEvidence? molecule spatial unit)
  | .halfChair unit =>
      firstSuccess?
        (fun offset => canonicalRingSearch? spatial (unit.atoms.rotate offset) candidatePlanes
          (coordinateHalfChairEvidence? molecule spatial unit offset))
        (List.range unit.atoms.length)
  | .crown unit =>
      coordinatePacketEvidence? spatial unit.atoms (generalCrownEvidence? molecule unit)
  | .tub unit =>
      canonicalRingSearch? spatial unit.atoms candidatePlanes
        (coordinateTubEvidence? molecule spatial unit)

/-- Exact canonical-output theorem for automatic finite witness discovery. -/
theorem automaticCoordinateRingEvidence?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (input : AutomaticCoordinateRingInput)
    (output : CoordinateRingEvidence) :
    automaticCoordinateRingEvidence? molecule spatial input = some output ↔
      AutomaticCoordinateRingEvidenceJudgment molecule spatial input output := by
  cases input with
  | envelope unit =>
      exact canonicalRingSearch?_eq_some_iff spatial unit.atoms candidatePlanes
        (coordinateEnvelopeEvidence? molecule spatial unit)
        (CoordinateEnvelopeEvidenceJudgment molecule spatial unit)
        (fun plane candidate =>
          coordinateEnvelopeEvidence?_eq_some_iff molecule spatial unit plane candidate)
        output
  | sixRing unit =>
      exact canonicalRingSearch?_eq_some_iff spatial unit.atoms candidatePlanes
        (coordinateSixRingEvidence? molecule spatial unit)
        (CoordinateSixRingEvidenceJudgment molecule spatial unit)
        (fun plane candidate =>
          coordinateSixRingEvidence?_eq_some_iff molecule spatial unit plane candidate)
        output
  | halfChair unit =>
      exact firstSuccess?_eq_some_iff
        (fun offset => canonicalRingSearch? spatial (unit.atoms.rotate offset) candidatePlanes
          (coordinateHalfChairEvidence? molecule spatial unit offset))
        (CanonicalHalfChairOffsetJudgment molecule spatial unit)
        (fun offset result => canonicalRingSearch?_eq_some_iff spatial
          (unit.atoms.rotate offset) candidatePlanes
          (coordinateHalfChairEvidence? molecule spatial unit offset)
          (CoordinateHalfChairEvidenceJudgment molecule spatial unit offset)
          (fun plane candidate => coordinateHalfChairEvidence?_eq_some_iff molecule spatial unit
            offset plane candidate)
          result)
        (List.range unit.atoms.length) output
  | crown unit =>
      exact coordinatePacketEvidence?_eq_some_iff spatial unit.atoms
        (generalCrownEvidence? molecule unit)
        (GeneralCrownEvidenceJudgment molecule unit)
        (fun points candidate =>
          generalCrownEvidence?_eq_some_iff molecule unit points candidate)
        output
  | tub unit =>
      exact canonicalRingSearch?_eq_some_iff spatial unit.atoms candidatePlanes
        (coordinateTubEvidence? molecule spatial unit)
        (CoordinateTubEvidenceJudgment molecule spatial unit)
        (fun plane candidate =>
          coordinateTubEvidence?_eq_some_iff molecule spatial unit plane candidate)
        output

theorem automaticCoordinateRingEvidenceJudgment_exists_iff_witness
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) :
    (∃ output, AutomaticCoordinateRingEvidenceJudgment molecule spatial input output) ↔
      AutomaticCoordinateRingWitness molecule spatial input := by
  cases input with
  | envelope unit =>
      exact CanonicalRingSearchJudgment.exists_iff spatial unit.atoms candidatePlanes
        (CoordinateEnvelopeEvidenceJudgment molecule spatial unit)
  | sixRing unit =>
      exact CanonicalRingSearchJudgment.exists_iff spatial unit.atoms candidatePlanes
        (CoordinateSixRingEvidenceJudgment molecule spatial unit)
  | halfChair unit =>
      constructor
      · rintro ⟨output, selected⟩
        rcases selected.witness with ⟨offset, offsetPresent, offsetJudged⟩
        rcases offsetJudged with ⟨points, pointsJudged, planeSelected⟩
        rcases planeSelected.witness with ⟨plane, planePresent, planeJudged⟩
        exact ⟨offset, List.mem_range.mp offsetPresent, points, pointsJudged,
          plane, planePresent, output, planeJudged⟩
      · rintro ⟨offset, offsetLt, points, pointsJudged,
          plane, planePresent, output, planeJudged⟩
        rcases (CanonicalFirst.exists_iff
          (CoordinateHalfChairEvidenceJudgment molecule spatial unit offset)
          (candidatePlanes points)).mpr
          ⟨plane, planePresent, output, planeJudged⟩ with
          ⟨planeOutput, planeSelected⟩
        have offsetJudged : CanonicalHalfChairOffsetJudgment molecule spatial unit
            offset planeOutput := ⟨points, pointsJudged, planeSelected⟩
        rcases (CanonicalFirst.exists_iff
          (CanonicalHalfChairOffsetJudgment molecule spatial unit)
          (List.range unit.atoms.length)).mpr
          ⟨offset, List.mem_range.mpr offsetLt, planeOutput, offsetJudged⟩ with
          ⟨selectedOutput, selected⟩
        exact ⟨selectedOutput, selected⟩
  | crown unit =>
      constructor
      · rintro ⟨output, points, pointsJudged, crownJudged⟩
        exact ⟨points, pointsJudged, output, crownJudged⟩
      · rintro ⟨points, pointsJudged, output, crownJudged⟩
        exact ⟨output, points, pointsJudged, crownJudged⟩
  | tub unit =>
      exact CanonicalRingSearchJudgment.exists_iff spatial unit.atoms candidatePlanes
        (CoordinateTubEvidenceJudgment molecule spatial unit)

/-- Exhaustive refusal: `none` means that no finite exact family witness exists. -/
theorem automaticCoordinateRingEvidence?_eq_none_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (input : AutomaticCoordinateRingInput) :
    automaticCoordinateRingEvidence? molecule spatial input = none ↔
      ¬AutomaticCoordinateRingWitness molecule spatial input := by
  constructor
  · intro computed witness
    rcases (automaticCoordinateRingEvidenceJudgment_exists_iff_witness
      molecule spatial input).mpr witness with ⟨output, judged⟩
    have someComputed := (automaticCoordinateRingEvidence?_eq_some_iff
      molecule spatial input output).mpr judged
    rw [computed] at someComputed
    contradiction
  · intro absent
    cases computed : automaticCoordinateRingEvidence? molecule spatial input with
    | none => rfl
    | some output =>
        have judged := (automaticCoordinateRingEvidence?_eq_some_iff
          molecule spatial input output).mp computed
        exact False.elim (absent
          ((automaticCoordinateRingEvidenceJudgment_exists_iff_witness
            molecule spatial input).mp ⟨output, judged⟩))

/-- Positive existence is exactly existence of an independent finite family witness. -/
theorem automaticCoordinateRingEvidence?_has_result_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (input : AutomaticCoordinateRingInput) :
    (∃ output, automaticCoordinateRingEvidence? molecule spatial input = some output) ↔
      AutomaticCoordinateRingWitness molecule spatial input := by
  constructor
  · rintro ⟨output, computed⟩
    exact (automaticCoordinateRingEvidenceJudgment_exists_iff_witness
      molecule spatial input).mp
        ⟨output, (automaticCoordinateRingEvidence?_eq_some_iff
          molecule spatial input output).mp computed⟩
  · intro witness
    rcases (automaticCoordinateRingEvidenceJudgment_exists_iff_witness
      molecule spatial input).mpr witness with ⟨output, judged⟩
    exact ⟨output, (automaticCoordinateRingEvidence?_eq_some_iff
      molecule spatial input output).mpr judged⟩

theorem automaticCoordinateRingEvidenceJudgment_outputWitness
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) (output : CoordinateRingEvidence)
    (judged : AutomaticCoordinateRingEvidenceJudgment molecule spatial input output) :
    AutomaticCoordinateRingOutputWitness molecule spatial input output := by
  cases input with
  | envelope unit =>
      rcases judged with ⟨points, pointsJudged, selected⟩
      rcases selected.witness with ⟨plane, present, planeJudged⟩
      exact ⟨points, pointsJudged, plane, present, planeJudged⟩
  | sixRing unit =>
      rcases judged with ⟨points, pointsJudged, selected⟩
      rcases selected.witness with ⟨plane, present, planeJudged⟩
      exact ⟨points, pointsJudged, plane, present, planeJudged⟩
  | halfChair unit =>
      rcases judged.witness with ⟨offset, offsetPresent, offsetJudged⟩
      rcases offsetJudged with ⟨points, pointsJudged, planeSelected⟩
      rcases planeSelected.witness with ⟨plane, planePresent, planeJudged⟩
      exact ⟨offset, List.mem_range.mp offsetPresent, points, pointsJudged,
        plane, planePresent, planeJudged⟩
  | crown unit => exact judged
  | tub unit =>
      rcases judged with ⟨points, pointsJudged, selected⟩
      rcases selected.witness with ⟨plane, present, planeJudged⟩
      exact ⟨points, pointsJudged, plane, present, planeJudged⟩

/-- Every result retains a concrete noncollinear ring triple and, for half-chair, a canonical
offset below the ring length. -/
theorem automaticCoordinateRingEvidence?_some_witness
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) (output : CoordinateRingEvidence)
    (computed : automaticCoordinateRingEvidence? molecule spatial input = some output) :
    AutomaticCoordinateRingOutputWitness molecule spatial input output :=
  automaticCoordinateRingEvidenceJudgment_outputWitness molecule spatial input output
    ((automaticCoordinateRingEvidence?_eq_some_iff molecule spatial input output).mp computed)

/-! ## Sound public descriptor emission -/

theorem automaticCoordinateRingEvidenceJudgment_supports
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) (output : CoordinateRingEvidence)
    (judged : AutomaticCoordinateRingEvidenceJudgment molecule spatial input output) :
    output.unit.ValidFor molecule ∧ output.MolecularRolesValid molecule ∧
      ∃ descriptor, output.Supports descriptor := by
  have witnessed := automaticCoordinateRingEvidenceJudgment_outputWitness
    molecule spatial input output judged
  cases input with
  | envelope unit =>
      rcases witnessed with ⟨_, _, plane, _, planeJudged⟩
      exact coordinateRingEvidenceJudgment_supports molecule spatial
        (.envelope unit plane) output planeJudged
  | sixRing unit =>
      rcases witnessed with ⟨_, _, plane, _, planeJudged⟩
      exact coordinateRingEvidenceJudgment_supports molecule spatial
        (.sixRing unit plane) output planeJudged
  | halfChair unit =>
      rcases witnessed with ⟨offset, _, _, _, plane, _, planeJudged⟩
      exact coordinateRingEvidenceJudgment_supports molecule spatial
        (.halfChair unit offset plane) output planeJudged
  | crown unit =>
      rcases witnessed with ⟨points, _, crownJudged⟩
      rcases generalCrownEvidenceJudgment_supports crownJudged with
        ⟨valid, roles, support⟩
      exact ⟨valid, roles, .crown, support⟩
  | tub unit =>
      rcases witnessed with ⟨_, _, plane, _, planeJudged⟩
      exact coordinateRingEvidenceJudgment_supports molecule spatial
        (.tub unit plane) output planeJudged

noncomputable def automaticCoordinateRingAssignments
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) : List P94ConformationAssignment :=
  match automaticCoordinateRingEvidence? certified.result.parsed spatial input with
  | none => []
  | some output => certified.analyzeP94Conformation [output]

theorem automaticCoordinateRingAssignments_mem_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) (assignment : P94ConformationAssignment) :
    assignment ∈ automaticCoordinateRingAssignments certified spatial input ↔
      ∃ output,
        AutomaticCoordinateRingEvidenceJudgment certified.result.parsed spatial input output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  cases computed : automaticCoordinateRingEvidence? certified.result.parsed spatial input with
  | none =>
      constructor
      · intro present
        unfold automaticCoordinateRingAssignments at present
        rw [computed] at present
        simp at present
      · rintro ⟨output, judged, _⟩
        have someComputed := (automaticCoordinateRingEvidence?_eq_some_iff
          certified.result.parsed spatial input output).mpr judged
        rw [computed] at someComputed
        contradiction
  | some output =>
      constructor
      · intro present
        have analyzedPresent : assignment ∈ certified.analyzeP94Conformation [output] := by
          unfold automaticCoordinateRingAssignments at present
          rw [computed] at present
          exact present
        exact ⟨output,
          (automaticCoordinateRingEvidence?_eq_some_iff
            certified.result.parsed spatial input output).mp computed,
          (mem_analyzeP94Conformation_iff_independent
            certified [output] assignment).mp analyzedPresent⟩
      · rintro ⟨other, judged, independent⟩
        have otherComputed := (automaticCoordinateRingEvidence?_eq_some_iff
          certified.result.parsed spatial input other).mpr judged
        rw [computed] at otherComputed
        have equal : output = other := Option.some.inj otherComputed
        subst other
        have analyzedPresent := (mem_analyzeP94Conformation_iff_independent
          certified [output] assignment).mpr independent
        unfold automaticCoordinateRingAssignments
        rw [computed]
        exact analyzedPresent

theorem automaticCoordinateRingAssignments_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) :
    (automaticCoordinateRingAssignments certified spatial input).Nodup := by
  classical
  cases computed : automaticCoordinateRingEvidence? certified.result.parsed spatial input with
  | none =>
      unfold automaticCoordinateRingAssignments
      rw [computed]
      simp
  | some output =>
      unfold automaticCoordinateRingAssignments
      rw [computed]
      exact analyzeP94Conformation_nodup certified [output]

theorem automaticCoordinateRingAssignment_count_eq_one_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) (assignment : P94ConformationAssignment) :
    List.count assignment (automaticCoordinateRingAssignments certified spatial input) = 1 ↔
      ∃ output,
        AutomaticCoordinateRingEvidenceJudgment certified.result.parsed spatial input output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  rw [← automaticCoordinateRingAssignments_mem_iff]
  constructor
  · intro countOne
    by_contra absent
    have countZero : List.count assignment
        (automaticCoordinateRingAssignments certified spatial input) = 0 :=
      List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem
      (automaticCoordinateRingAssignments_nodup certified spatial input)

/-- A successful witness-free derivation reaches the public P-94 report exactly once. -/
theorem automaticCoordinateRingEvidence_success_emits_descriptor_exactly_once
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (input : AutomaticCoordinateRingInput) (output : CoordinateRingEvidence)
    (computed : automaticCoordinateRingEvidence? certified.result.parsed spatial input =
      some output) :
    ∃ descriptor,
      List.count
        ({ unit := output.unit, descriptor := descriptor } : P94ConformationAssignment)
        (automaticCoordinateRingAssignments certified spatial input) = 1 := by
  have judged := (automaticCoordinateRingEvidence?_eq_some_iff
    certified.result.parsed spatial input output).mp computed
  rcases automaticCoordinateRingEvidenceJudgment_supports
    certified.result.parsed spatial input output judged with
    ⟨valid, roles, descriptor, support⟩
  refine ⟨descriptor,
    (automaticCoordinateRingAssignment_count_eq_one_iff certified spatial input _).mpr ?_⟩
  refine ⟨output, judged, output, by simp, rfl, valid, roles, support⟩

end BlueBookP94.CoordinateRing
end TetraStereo.OneCenter
