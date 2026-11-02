import TetraStereo.OneCenter.P93PracticalSpatialUnitPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.PracticalSpatialUnitPerception

/-!
# Conflict-free batch perception of practical P-93 spatial units

The sense-free local dispatcher is exact for one independently identified frame. This module
evaluates a finite mixed family of axial, planar, and helical frames and applies the common public
conflict policy: an assignment is retained precisely when some supplied frame independently
derives it and every other successful frame for the same physical unit agrees on the outcome.
-/

/-- Evaluate every supplied frame, remove conflicting unit assignments, and erase duplicates. -/
def perceiveSpatialUnits (result : ChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (candidates : List PracticalSpatialCandidate) :
    List StereoAssignment :=
  conflictFreeGeometryAssignments
    (candidates.filterMap (perceiveSpatialUnit? result spatial))

/-- Independent meaning of one retained mixed-family batch result. -/
def PracticalSpatialConflictFreeAssignmentJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidates : List PracticalSpatialCandidate) (assignment : StereoAssignment) : Prop :=
  (∃ candidate ∈ candidates,
    PracticalSpatialPerceptionJudgment result spatial candidate assignment) ∧
  ∀ otherCandidate ∈ candidates, ∀ otherAssignment,
    PracticalSpatialPerceptionJudgment result spatial otherCandidate otherAssignment →
    otherAssignment.unit = assignment.unit →
    otherAssignment.outcome = assignment.outcome

/-- Batch membership is exactly independent derivability plus same-unit agreement. -/
theorem mem_perceiveSpatialUnits_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidates : List PracticalSpatialCandidate) (assignment : StereoAssignment) :
    assignment ∈ perceiveSpatialUnits result spatial candidates ↔
      PracticalSpatialConflictFreeAssignmentJudgment
        result spatial candidates assignment := by
  rw [perceiveSpatialUnits, mem_conflictFreeGeometryAssignments_iff]
  constructor
  · rintro ⟨candidatePresent, agrees⟩
    rcases List.mem_filterMap.mp candidatePresent with
      ⟨candidate, candidateInInput, computed⟩
    refine ⟨⟨candidate, candidateInInput,
      (perceiveSpatialUnit?_eq_some_iff
        result spatial candidate assignment).mp computed⟩, ?_⟩
    intro otherCandidate otherCandidateInInput otherAssignment otherJudged sameUnit
    have otherComputed :=
      (perceiveSpatialUnit?_eq_some_iff
        result spatial otherCandidate otherAssignment).mpr otherJudged
    exact agrees otherAssignment
      (List.mem_filterMap.mpr
        ⟨otherCandidate, otherCandidateInInput, otherComputed⟩) sameUnit
  · rintro ⟨⟨candidate, candidateInInput, judged⟩, allAgree⟩
    have computed :=
      (perceiveSpatialUnit?_eq_some_iff
        result spatial candidate assignment).mpr judged
    refine ⟨List.mem_filterMap.mpr
      ⟨candidate, candidateInInput, computed⟩, ?_⟩
    intro otherAssignment otherCandidate sameUnit
    rcases List.mem_filterMap.mp otherCandidate with
      ⟨otherFrame, otherFrameInInput, otherComputed⟩
    exact allAgree otherFrame otherFrameInInput otherAssignment
      ((perceiveSpatialUnit?_eq_some_iff
        result spatial otherFrame otherAssignment).mp otherComputed) sameUnit

/-- The mixed-family public result contains no duplicate assignment. -/
theorem perceiveSpatialUnits_nodup
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidates : List PracticalSpatialCandidate) :
    (perceiveSpatialUnits result spatial candidates).Nodup :=
  conflictFreeGeometryAssignments_nodup _

/-- Public readiness of one supplied frame includes successful independent assignment and
agreement with every other successful frame for that unit. -/
def PracticalSpatialCandidatePublicReady
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidates : List PracticalSpatialCandidate)
    (candidate : PracticalSpatialCandidate) : Prop :=
  candidate ∈ candidates ∧
    ∃ assignment,
      PracticalSpatialPerceptionJudgment result spatial candidate assignment ∧
      PracticalSpatialConflictFreeAssignmentJudgment
        result spatial candidates assignment

/-- Every public-ready supplied frame contributes exactly one independently judged assignment. -/
theorem publicReady_candidate_occurs_exactly_once
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidates : List PracticalSpatialCandidate)
    (candidate : PracticalSpatialCandidate)
    (ready : PracticalSpatialCandidatePublicReady
      result spatial candidates candidate) :
    ∃! assignment,
      assignment ∈ perceiveSpatialUnits result spatial candidates ∧
      PracticalSpatialPerceptionJudgment result spatial candidate assignment := by
  rcases ready with ⟨_, assignment, candidateJudged, publicJudged⟩
  refine ⟨assignment,
    ⟨(mem_perceiveSpatialUnits_iff
      result spatial candidates assignment).mpr publicJudged, candidateJudged⟩, ?_⟩
  intro other otherProperties
  have assignmentComputed :=
    (perceiveSpatialUnit?_eq_some_iff
      result spatial candidate assignment).mpr candidateJudged
  have otherComputed :=
    (perceiveSpatialUnit?_eq_some_iff
      result spatial candidate other).mpr otherProperties.2
  rw [assignmentComputed] at otherComputed
  exact Option.some.inj otherComputed.symm

end BlueBookP93.PracticalSpatialUnitPerception
end TetraStereo.OneCenter
