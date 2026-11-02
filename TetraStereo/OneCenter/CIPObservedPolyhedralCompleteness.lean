import TetraStereo.OneCenter.CIPObservedGeometryAssignmentConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Observation-scoped completeness for IR-9 polyhedral assignments

The existing conformance theorem proves that every successful polyhedral observation exposes the
complete independent IR-9 judgment.  This file proves the converse and then follows the result
through conflict filtering and native-unit precedence.  Thus, for every geometry currently
admitted by the router, success and refusal have exact observation-scoped meanings.
-/

open BlueBookP93.GeometryIngress

/-- The independent IR-9 judgment is sufficient for the executable observation constructor. -/
theorem ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?_complete_judgment
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (judged : PolyhedralObservationAssignmentJudgment result record assignment) :
    result.polyhedralGeometryObservationAssignment? record = some assignment := by
  rcases judged with
    ⟨priorities, memberships, independentRotation?, rotation?, positions, index, absolute,
      recognitionOK, recognitionValid, priorityEq, validFrame, finiteCertificate,
      positionsRecognized, orientationRecognized, rotationEq, guardFalse, indexEq,
      absoluteEq, assignmentEq⟩
  subst rotation?
  have acceptedDistinctness : independentRotation?.isSome = true →
      priorities.eraseDups.length = priorities.length := by
    intro rotationPresent
    have distinctnessFalse :
        (priorities.eraseDups.length != priorities.length) = false := by
      simpa [rotationPresent] using guardFalse
    simpa using distinctnessFalse
  subst assignment
  unfold ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?
  rw [priorityEq, orientationRecognized, positionsRecognized]
  simp [recognitionOK, indexEq, absoluteEq]; exact acceptedDistinctness

/-- Exact local success theorem for every currently executable polyhedral geometry. -/
theorem ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment) :
    result.polyhedralGeometryObservationAssignment? record = some assignment ↔
      PolyhedralObservationAssignmentJudgment result record assignment := by
  constructor
  · exact result.polyhedralGeometryObservationAssignment?_sound_judgment record assignment
  · exact result.polyhedralGeometryObservationAssignment?_complete_judgment record assignment

/-- A supplied polyhedral observation is ready exactly when its complete independent judgment has
some public assignment witness. -/
def PolyhedralObservationReady
    (result : ChemistryNormalizationResult)
    (record : IndexedPolyhedralGeometryObservation) : Prop :=
  ∃ assignment, PolyhedralObservationAssignmentJudgment result record assignment

theorem ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?_isSome_iff_ready
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation) :
    (result.polyhedralGeometryObservationAssignment? record).isSome = true ↔
      PolyhedralObservationReady result record := by
  constructor
  · intro present
    obtain ⟨assignment, produced⟩ := Option.isSome_iff_exists.mp present
    exact ⟨assignment,
      (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
        record assignment).mp produced⟩
  · rintro ⟨assignment, judged⟩
    apply Option.isSome_iff_exists.mpr
    exact ⟨assignment,
      (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
        record assignment).mpr judged⟩

/-- Exact local refusal theorem: failure means that no independently valid assignment exists. -/
theorem ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation) :
    result.polyhedralGeometryObservationAssignment? record = none ↔
      ¬ PolyhedralObservationReady result record := by
  constructor
  · intro absent
    rintro ⟨assignment, judged⟩
    have produced :=
      (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
        record assignment).mpr judged
    rw [absent] at produced
    contradiction
  · intro notReady
    cases produced : result.polyhedralGeometryObservationAssignment? record with
    | none => rfl
    | some assignment =>
        exfalso
        apply notReady
        exact ⟨assignment,
          (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
            record assignment).mp produced⟩

/-- One record has at most one independently valid public assignment. -/
theorem polyhedralObservationAssignmentJudgment_subsingleton
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation)
    (first second : StereoAssignment)
    (firstJudged : PolyhedralObservationAssignmentJudgment result record first)
    (secondJudged : PolyhedralObservationAssignmentJudgment result record second) :
    first = second := by
  have firstProduced :=
    (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
      record first).mpr firstJudged
  have secondProduced :=
    (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
      record second).mpr secondJudged
  exact Option.some.inj (firstProduced.symm.trans secondProduced)

/-- The isolated conflict-filtered polyhedral branch used inside the observed-geometry analyzer. -/
def ChemistryNormalizationResult.polyhedralObservationAssignments
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation) : List StereoAssignment :=
  conflictFreeGeometryAssignments
    (records.filterMap result.polyhedralGeometryObservationAssignment?)

/-- Every independently valid record for the same polyhedral unit agrees with `assignment`. -/
def PolyhedralObservationAssignmentAgreement
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  ∀ otherRecord ∈ records, ∀ otherAssignment,
    PolyhedralObservationAssignmentJudgment result otherRecord otherAssignment →
    otherAssignment.unit = assignment.unit →
    otherAssignment.outcome = assignment.outcome

/-- A concrete independently valid record contradicts `assignment` at the same polyhedral unit. -/
def PolyhedralObservationAssignmentConflict
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  ∃ otherRecord ∈ records, ∃ otherAssignment,
    PolyhedralObservationAssignmentJudgment result otherRecord otherAssignment ∧
    otherAssignment.unit = assignment.unit ∧
    otherAssignment.outcome ≠ assignment.outcome

/-- For one valid source record, the generic conflict judgment is exactly global same-unit
agreement among all valid polyhedral records. -/
theorem polyhedralConflictFreeAssignmentJudgment_iff_agreement
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation) (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PolyhedralObservationAssignmentJudgment result record assignment) :
    ConflictFreeGeometryAssignmentJudgment
        (records.filterMap result.polyhedralGeometryObservationAssignment?) assignment ↔
      PolyhedralObservationAssignmentAgreement result records assignment := by
  have produced :=
    (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
      record assignment).mpr judged
  constructor
  · rintro ⟨sourcePresent, agreement⟩ otherRecord otherPresent otherAssignment
      otherJudged sameUnit
    apply agreement otherAssignment
    · apply List.mem_filterMap.mpr
      exact ⟨otherRecord, otherPresent,
        (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
          otherRecord otherAssignment).mpr otherJudged⟩
    · exact sameUnit
  · intro agreement
    refine ⟨?_, ?_⟩
    · apply List.mem_filterMap.mpr
      exact ⟨record, recordPresent, produced⟩
    · intro other otherPresent sameUnit
      rcases List.mem_filterMap.mp otherPresent with
        ⟨otherRecord, otherRecordPresent, otherProduced⟩
      exact agreement otherRecord otherRecordPresent other
        ((result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
          otherRecord other).mp otherProduced) sameUnit

/-- Observation-scoped exact membership in the conflict-free polyhedral branch. -/
theorem ChemistryNormalizationResult.polyhedralObservationAssignment_mem_iff_agreement
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation) (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PolyhedralObservationAssignmentJudgment result record assignment) :
    assignment ∈ result.polyhedralObservationAssignments records ↔
      PolyhedralObservationAssignmentAgreement result records assignment := by
  unfold ChemistryNormalizationResult.polyhedralObservationAssignments
  rw [mem_conflictFreeGeometryAssignments_iff]
  exact polyhedralConflictFreeAssignmentJudgment_iff_agreement
    result records record assignment recordPresent judged

/-- Agreement failure is constructively equivalent to an explicit contradictory record. -/
theorem not_polyhedralObservationAssignmentAgreement_iff_conflict
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment) :
    ¬ PolyhedralObservationAssignmentAgreement result records assignment ↔
      PolyhedralObservationAssignmentConflict result records assignment := by
  classical
  constructor
  · intro notAgreement
    by_contra noConflict
    apply notAgreement
    intro otherRecord otherPresent otherAssignment otherJudged sameUnit
    by_contra differentOutcome
    exact noConflict ⟨otherRecord, otherPresent, otherAssignment, otherJudged,
      sameUnit, differentOutcome⟩
  · rintro ⟨otherRecord, otherPresent, otherAssignment, otherJudged,
      sameUnit, differentOutcome⟩ agreement
    exact differentOutcome
      (agreement otherRecord otherPresent otherAssignment otherJudged sameUnit)

/-- Exact conflict refusal for one valid source record. -/
theorem ChemistryNormalizationResult.polyhedralObservationAssignment_not_mem_iff_conflict
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation) (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PolyhedralObservationAssignmentJudgment result record assignment) :
    assignment ∉ result.polyhedralObservationAssignments records ↔
      PolyhedralObservationAssignmentConflict result records assignment := by
  rw [← not_polyhedralObservationAssignmentAgreement_iff_conflict]
  exact not_congr (result.polyhedralObservationAssignment_mem_iff_agreement
    records record assignment recordPresent judged)

theorem ChemistryNormalizationResult.polyhedralObservationAssignments_nodup
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation) :
    (result.polyhedralObservationAssignments records).Nodup := by
  unfold ChemistryNormalizationResult.polyhedralObservationAssignments
  exact conflictFreeGeometryAssignments_nodup _

/-- No assignment in an earlier branch owns the same stereogenic unit. -/
def PolyhedralAssignmentHasNoNativeOwner
    (native : List StereoAssignment) (assignment : StereoAssignment) : Prop :=
  ∀ existing ∈ native, existing.unit ≠ assignment.unit

/-- The polyhedral contribution after the analyzer's native-unit precedence policy. -/
def ChemistryNormalizationResult.polyhedralObservedContributions
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (native : List StereoAssignment) : List StereoAssignment :=
  (result.polyhedralObservationAssignments records).filter fun assignment =>
    !(native.any fun existing => existing.unit == assignment.unit)

private theorem native_any_same_unit_eq_false_iff
    (native : List StereoAssignment) (assignment : StereoAssignment) :
    (native.any fun existing => existing.unit == assignment.unit) = false ↔
      PolyhedralAssignmentHasNoNativeOwner native assignment := by
  simp [PolyhedralAssignmentHasNoNativeOwner]

/-- Exact membership after conflict filtering and native-unit precedence. -/
theorem ChemistryNormalizationResult.polyhedralObservedContribution_mem_iff
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (native : List StereoAssignment)
    (record : IndexedPolyhedralGeometryObservation) (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PolyhedralObservationAssignmentJudgment result record assignment) :
    assignment ∈ result.polyhedralObservedContributions records native ↔
      PolyhedralObservationAssignmentAgreement result records assignment ∧
        PolyhedralAssignmentHasNoNativeOwner native assignment := by
  unfold ChemistryNormalizationResult.polyhedralObservedContributions
  rw [List.mem_filter, result.polyhedralObservationAssignment_mem_iff_agreement
    records record assignment recordPresent judged]
  constructor
  · rintro ⟨agreement, accepted⟩
    refine ⟨agreement, (native_any_same_unit_eq_false_iff native assignment).mp ?_⟩
    simpa using accepted
  · rintro ⟨agreement, noOwner⟩
    refine ⟨agreement, ?_⟩
    have rejected := (native_any_same_unit_eq_false_iff native assignment).mpr noOwner
    simpa using rejected

theorem ChemistryNormalizationResult.polyhedralObservedContributions_nodup
    (result : ChemistryNormalizationResult)
    (records : List IndexedPolyhedralGeometryObservation)
    (native : List StereoAssignment) :
    (result.polyhedralObservedContributions records native).Nodup := by
  unfold ChemistryNormalizationResult.polyhedralObservedContributions
  exact (result.polyhedralObservationAssignments_nodup records).filter _

end TetraStereo.OneCenter
