import TetraStereo.OneCenter.CIPObservedDerivedHelicalSpatialCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Sense-free practical axial, planar, and helical spatial perception

The older public geometry records contain a caller-supplied `StereoSense`.  The exact spatial
refinements no longer need that bit, but callers still had to manufacture it to use the API.  This
module removes that residual trust surface.  Candidates carry only molecular roles and physical
applicability data; the descriptor is calculated from exact coordinates.

This closes descriptor perception for a supplied candidate frame.  Exhaustive discovery of every
chemically eligible frame remains a separate constitution/topology problem.
-/

namespace BlueBookP93.PracticalSpatialUnitPerception

/-- Unordered endpoint-reference frame for an axial unit. -/
structure PracticalAxialCandidate where
  axisStart : Nat
  axisEnd : Nat
  startFirst : Nat
  startSecond : Nat
  endFirst : Nat
  endSecond : Nat
  deriving DecidableEq, Repr

def PracticalAxialCandidate.toObservation
    (candidate : PracticalAxialCandidate) (sense : StereoSense) :
    IndexedAxialGeometryObservation :=
  { axisStart := candidate.axisStart
    axisEnd := candidate.axisEnd
    startFirst := candidate.startFirst
    startSecond := candidate.startSecond
    endFirst := candidate.endFirst
    endSecond := candidate.endSecond
    sense := sense }

/-- Ordered chemical helix path and its two terminal references, without a claimed handedness. -/
structure PracticalHelicalCandidate where
  helixPath : List Nat
  frontReference : Nat
  backReference : Nat
  deriving DecidableEq, Repr

def PracticalHelicalCandidate.toObservation
    (candidate : PracticalHelicalCandidate) (sense : StereoSense) :
    IndexedHelicalGeometryObservation :=
  { helixPath := candidate.helixPath
    frontReference := candidate.frontReference
    backReference := candidate.backReference
    sense := sense }

/-- Molecule-backed axial carrier conditions not implied by the coordinate sign calculation. -/
def PracticalAxialMolecularFrameJudgment
    (result : ChemistryNormalizationResult) (candidate : PracticalAxialCandidate) : Prop :=
  candidate.axisStart < result.parsed.atomCount ∧
    candidate.axisEnd < result.parsed.atomCount ∧
    candidate.startFirst < result.parsed.atomCount ∧
    candidate.startSecond < result.parsed.atomCount ∧
    candidate.endFirst < result.parsed.atomCount ∧
    candidate.endSecond < result.parsed.atomCount ∧
    candidate.axisStart ≠ candidate.axisEnd ∧
    candidate.startFirst ≠ candidate.startSecond ∧
    candidate.endFirst ≠ candidate.endSecond ∧
    candidate.startFirst ≠ candidate.axisEnd ∧
    candidate.startSecond ≠ candidate.axisEnd ∧
    candidate.endFirst ≠ candidate.axisStart ∧
    candidate.endSecond ≠ candidate.axisStart ∧
    candidate.startFirst ∈
      result.geometryPriorityState.1.writtenNeighbors candidate.axisStart ∧
    candidate.startSecond ∈
      result.geometryPriorityState.1.writtenNeighbors candidate.axisStart ∧
    candidate.endFirst ∈
      result.geometryPriorityState.1.writtenNeighbors candidate.axisEnd ∧
    candidate.endSecond ∈
      result.geometryPriorityState.1.writtenNeighbors candidate.axisEnd

def practicalAxialMolecularFrameOK? (result : ChemistryNormalizationResult)
    (candidate : PracticalAxialCandidate) : Bool :=
  decide (candidate.axisStart < result.parsed.atomCount) &&
    decide (candidate.axisEnd < result.parsed.atomCount) &&
    decide (candidate.startFirst < result.parsed.atomCount) &&
    decide (candidate.startSecond < result.parsed.atomCount) &&
    decide (candidate.endFirst < result.parsed.atomCount) &&
    decide (candidate.endSecond < result.parsed.atomCount) &&
    decide (candidate.axisStart ≠ candidate.axisEnd) &&
    decide (candidate.startFirst ≠ candidate.startSecond) &&
    decide (candidate.endFirst ≠ candidate.endSecond) &&
    decide (candidate.startFirst ≠ candidate.axisEnd) &&
    decide (candidate.startSecond ≠ candidate.axisEnd) &&
    decide (candidate.endFirst ≠ candidate.axisStart) &&
    decide (candidate.endSecond ≠ candidate.axisStart) &&
    (result.geometryPriorityState.1.writtenNeighbors candidate.axisStart).contains
      candidate.startFirst &&
    (result.geometryPriorityState.1.writtenNeighbors candidate.axisStart).contains
      candidate.startSecond &&
    (result.geometryPriorityState.1.writtenNeighbors candidate.axisEnd).contains
      candidate.endFirst &&
    (result.geometryPriorityState.1.writtenNeighbors candidate.axisEnd).contains
      candidate.endSecond

@[simp] theorem practicalAxialMolecularFrameOK?_eq_true_iff
    (result : ChemistryNormalizationResult) (candidate : PracticalAxialCandidate) :
    practicalAxialMolecularFrameOK? result candidate = true ↔
      PracticalAxialMolecularFrameJudgment result candidate := by
  simp [practicalAxialMolecularFrameOK?, PracticalAxialMolecularFrameJudgment,
    and_assoc]

theorem practicalAxialMolecularFrameOK?_eq_false_of_startFirst_eq_axisEnd
    (result : ChemistryNormalizationResult) (candidate : PracticalAxialCandidate)
    (usedAxisPartner : candidate.startFirst = candidate.axisEnd) :
    practicalAxialMolecularFrameOK? result candidate = false := by
  simp [practicalAxialMolecularFrameOK?, usedAxisPartner]

theorem practicalAxialMolecularFrameOK?_eq_false_of_startSecond_eq_axisEnd
    (result : ChemistryNormalizationResult) (candidate : PracticalAxialCandidate)
    (usedAxisPartner : candidate.startSecond = candidate.axisEnd) :
    practicalAxialMolecularFrameOK? result candidate = false := by
  simp [practicalAxialMolecularFrameOK?, usedAxisPartner]

theorem practicalAxialMolecularFrameOK?_eq_false_of_endFirst_eq_axisStart
    (result : ChemistryNormalizationResult) (candidate : PracticalAxialCandidate)
    (usedAxisPartner : candidate.endFirst = candidate.axisStart) :
    practicalAxialMolecularFrameOK? result candidate = false := by
  simp [practicalAxialMolecularFrameOK?, usedAxisPartner]

theorem practicalAxialMolecularFrameOK?_eq_false_of_endSecond_eq_axisStart
    (result : ChemistryNormalizationResult) (candidate : PracticalAxialCandidate)
    (usedAxisPartner : candidate.endSecond = candidate.axisStart) :
    practicalAxialMolecularFrameOK? result candidate = false := by
  simp [practicalAxialMolecularFrameOK?, usedAxisPartner]

/-- The three source-shaped candidate families handled by the exact coordinate layer. -/
inductive PracticalSpatialCandidate where
  | axial (candidate : PracticalAxialCandidate)
  | planar (candidate : IndexedPlanarDerivedTetrahedronObservation)
  | helical (candidate : PracticalHelicalCandidate)
  deriving DecidableEq, Repr

/-- Derive an axial assignment from official-context endpoint priorities and exact coordinates. -/
def perceiveAxial? (result : ChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (candidate : PracticalAxialCandidate) :
    Option StereoAssignment := do
  if !practicalAxialMolecularFrameOK? result candidate then none else
  let record := candidate.toObservation .positive
  let descriptor ← result.axialObservationSpatialDescriptor? spatial record
  some
    { unit := StereoUnit.axis candidate.axisStart candidate.axisEnd
      outcome := StereoOutcome.axial descriptor }

def PracticalAxialPerceptionJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : PracticalAxialCandidate) (assignment : StereoAssignment) : Prop :=
  PracticalAxialMolecularFrameJudgment result candidate ∧
    ∃ descriptor,
      BlueBookP93.GeometryIngress.RationalAxialObservationJudgment
        result spatial (candidate.toObservation .positive) descriptor ∧
      assignment =
        { unit := StereoUnit.axis candidate.axisStart candidate.axisEnd
          outcome := StereoOutcome.axial descriptor }

theorem perceiveAxial?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : PracticalAxialCandidate) (assignment : StereoAssignment) :
    perceiveAxial? result spatial candidate = some assignment ↔
      PracticalAxialPerceptionJudgment result spatial candidate assignment := by
  constructor
  · intro computed
    unfold perceiveAxial? at computed
    split at computed <;> rename_i frameCheck
    · simp at computed
    · have frameTrue : practicalAxialMolecularFrameOK? result candidate = true := by
        cases observed : practicalAxialMolecularFrameOK? result candidate <;>
          simp [observed] at frameCheck ⊢
      have frame := (practicalAxialMolecularFrameOK?_eq_true_iff
          result candidate).mp frameTrue
      let record := candidate.toObservation .positive
      cases descriptorEq : result.axialObservationSpatialDescriptor? spatial record with
      | none => simp [record, descriptorEq] at computed
      | some descriptor =>
          have judged :=
            (result.axialObservationSpatialDescriptor?_eq_some_iff
              spatial record descriptor).mp descriptorEq
          have assignmentEq : assignment =
              { unit := StereoUnit.axis candidate.axisStart candidate.axisEnd
                outcome := StereoOutcome.axial descriptor } := by
            simpa [record, descriptorEq] using computed.symm
          exact ⟨frame, descriptor, judged, assignmentEq⟩
  · rintro ⟨frame, descriptor, judged, rfl⟩
    have frameCheck :=
      (practicalAxialMolecularFrameOK?_eq_true_iff result candidate).mpr frame
    have descriptorEq :=
      (result.axialObservationSpatialDescriptor?_eq_some_iff
        spatial (candidate.toObservation .positive) descriptor).mpr judged
    simp [perceiveAxial?, frameCheck, descriptorEq]

/-- One total family dispatcher.  The planar and helical branches reuse their already exact
molecule-backed coordinate evaluators; the helical placeholder sense is definitionally ignored. -/
def perceiveSpatialUnit? (result : ChemistryNormalizationResult)
    (spatial : SpatialConfiguration) : PracticalSpatialCandidate → Option StereoAssignment
  | .axial candidate => perceiveAxial? result spatial candidate
  | .planar candidate => result.planarDerivedTetrahedronAssignment? spatial candidate
  | .helical candidate =>
      result.coordinateDerivedHelicalAssignment? spatial
        (candidate.toObservation .positive)

inductive PracticalSpatialPerceptionJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    PracticalSpatialCandidate → StereoAssignment → Prop
  | axial {candidate assignment}
      (judged : PracticalAxialPerceptionJudgment result spatial candidate assignment) :
      PracticalSpatialPerceptionJudgment result spatial (.axial candidate) assignment
  | planar {candidate assignment}
      (judged : BlueBookP93.GeometryIngress.PlanarDerivedObservationAssignmentJudgment
        result spatial candidate assignment) :
      PracticalSpatialPerceptionJudgment result spatial (.planar candidate) assignment
  | helical {candidate assignment}
      (judged : BlueBookP93.GeometryIngress.CoordinateDerivedHelicalAssignmentJudgment
        result spatial (candidate.toObservation .positive) assignment) :
      PracticalSpatialPerceptionJudgment result spatial (.helical candidate) assignment

theorem perceiveSpatialUnit?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : PracticalSpatialCandidate) (assignment : StereoAssignment) :
    perceiveSpatialUnit? result spatial candidate = some assignment ↔
      PracticalSpatialPerceptionJudgment result spatial candidate assignment := by
  cases candidate with
  | axial candidate =>
      rw [show perceiveSpatialUnit? result spatial (.axial candidate) =
        perceiveAxial? result spatial candidate by rfl,
        perceiveAxial?_eq_some_iff]
      exact ⟨PracticalSpatialPerceptionJudgment.axial,
        fun judged => by cases judged with | axial judged => exact judged⟩
  | planar candidate =>
      rw [show perceiveSpatialUnit? result spatial (.planar candidate) =
        result.planarDerivedTetrahedronAssignment? spatial candidate by rfl,
        result.planarDerivedTetrahedronAssignment?_eq_some_iff]
      exact ⟨PracticalSpatialPerceptionJudgment.planar,
        fun judged => by cases judged with | planar judged => exact judged⟩
  | helical candidate =>
      rw [show perceiveSpatialUnit? result spatial (.helical candidate) =
        result.coordinateDerivedHelicalAssignment? spatial
          (candidate.toObservation .positive) by rfl,
        result.coordinateDerivedHelicalAssignment?_eq_some_iff]
      exact ⟨PracticalSpatialPerceptionJudgment.helical,
        fun judged => by cases judged with | helical judged => exact judged⟩

theorem perceiveSpatialUnit?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : PracticalSpatialCandidate) :
    perceiveSpatialUnit? result spatial candidate = none ↔
      ¬∃ assignment,
        PracticalSpatialPerceptionJudgment result spatial candidate assignment := by
  rw [← not_iff_not]
  simp only [not_not, Option.ne_none_iff_isSome, Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    perceiveSpatialUnit?_eq_some_iff result spatial candidate assignment

end BlueBookP93.PracticalSpatialUnitPerception

end TetraStereo.OneCenter
