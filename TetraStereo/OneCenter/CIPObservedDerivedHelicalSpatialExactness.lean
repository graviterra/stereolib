import TetraStereo.OneCenter.CIPObservedDerivedHelicalSpatialCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Observation-scoped exactness for coordinate-derived helical `P/M`

The coordinate-derived helical analyzer already has exact local semantics, conflict-free list
membership, public soundness, and exact-once coverage for records satisfying its public-readiness
predicate.  This module proves the missing converses.  For a fixed independently valid record,
the helical branch retains its assignment exactly when all same-helix records agree.  At the public
boundary, the only additional exclusion is ownership of the same physical helix by the earlier
certified planar prefix.  Consequently every exclusion has a concrete conflict-or-owner witness,
and multiplicity is exactly zero or one.
-/

namespace BlueBookP93.GeometryIngress

/-- Every independently valid supplied helix observation for this physical unit agrees with the
fixed assignment. -/
def CoordinateDerivedHelicalAssignmentAgreement
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  ∀ otherRecord ∈ records, ∀ otherAssignment,
    CoordinateDerivedHelicalAssignmentJudgment
      result spatial otherRecord otherAssignment →
    otherAssignment.unit = assignment.unit →
    otherAssignment.outcome = assignment.outcome

/-- A concrete independently valid supplied helix observation contradicts the fixed assignment
on the same physical helix. -/
def CoordinateDerivedHelicalAssignmentConflict
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  ∃ otherRecord ∈ records, ∃ otherAssignment,
    CoordinateDerivedHelicalAssignmentJudgment
      result spatial otherRecord otherAssignment ∧
    otherAssignment.unit = assignment.unit ∧
    otherAssignment.outcome ≠ assignment.outcome

/-- No assignment admitted by the earlier certified planar prefix owns this helix. -/
def CoordinateDerivedHelicalAssignmentHasNoEarlierOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  ∀ existing ∈ derivedPlanarHelicalSpatialBaseAssignments
      certified spatial observations derivedPlanes,
    existing.unit ≠ assignment.unit

/-- A concrete assignment in the earlier certified planar prefix already owns this helix. -/
def CoordinateDerivedHelicalAssignmentHasEarlierOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  ∃ existing ∈ derivedPlanarHelicalSpatialBaseAssignments
      certified spatial observations derivedPlanes,
    existing.unit = assignment.unit

end BlueBookP93.GeometryIngress

open BlueBookP93.GeometryIngress

/-- Once one concrete source record is fixed, conflict-free helical judgment is exactly global
same-unit agreement. -/
theorem coordinateDerivedHelicalConflictFreeAssignmentJudgment_iff_agreement
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : CoordinateDerivedHelicalAssignmentJudgment
      result spatial record assignment) :
    CoordinateDerivedHelicalConflictFreeAssignmentJudgment
        result spatial records assignment ↔
      CoordinateDerivedHelicalAssignmentAgreement
        result spatial records assignment := by
  constructor
  · exact fun conflictFree => conflictFree.2
  · intro agreement
    exact ⟨⟨record, recordPresent, judged⟩, agreement⟩

/-- Failure of helical agreement is equivalent to a concrete contradictory same-unit record. -/
theorem not_coordinateDerivedHelicalAssignmentAgreement_iff_conflict
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) :
    ¬ CoordinateDerivedHelicalAssignmentAgreement
        result spatial records assignment ↔
      CoordinateDerivedHelicalAssignmentConflict
        result spatial records assignment := by
  classical
  constructor
  · intro notAgreement
    by_contra noConflict
    apply notAgreement
    intro otherRecord otherRecordPresent otherAssignment otherJudged sameUnit
    by_contra differentOutcome
    exact noConflict ⟨otherRecord, otherRecordPresent, otherAssignment, otherJudged,
      sameUnit, differentOutcome⟩
  · rintro ⟨otherRecord, otherRecordPresent, otherAssignment, otherJudged,
      sameUnit, differentOutcome⟩ agreement
    exact differentOutcome
      (agreement otherRecord otherRecordPresent otherAssignment otherJudged sameUnit)

/-- Failure of earlier-owner exclusion is equivalent to an explicit earlier owner. -/
theorem not_coordinateDerivedHelicalAssignmentHasNoEarlierOwner_iff_hasEarlierOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) :
    ¬ CoordinateDerivedHelicalAssignmentHasNoEarlierOwner
        certified spatial observations derivedPlanes assignment ↔
      CoordinateDerivedHelicalAssignmentHasEarlierOwner
        certified spatial observations derivedPlanes assignment := by
  classical
  simp [CoordinateDerivedHelicalAssignmentHasNoEarlierOwner,
    CoordinateDerivedHelicalAssignmentHasEarlierOwner]

/-- Observation-scoped exact branch membership for one independently valid helix record. -/
theorem ChemistryNormalizationResult.coordinateDerivedHelicalAssignment_mem_iff_agreement
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : CoordinateDerivedHelicalAssignmentJudgment
      result spatial record assignment) :
    assignment ∈ result.derivedHelicalSpatialAssignments spatial records ↔
      CoordinateDerivedHelicalAssignmentAgreement
        result spatial records assignment := by
  rw [result.mem_derivedHelicalSpatialAssignments_iff]
  exact coordinateDerivedHelicalConflictFreeAssignmentJudgment_iff_agreement
    result spatial records record assignment recordPresent judged

/-- Observation-scoped exact branch refusal for one independently valid helix record. -/
theorem ChemistryNormalizationResult.coordinateDerivedHelicalAssignment_not_mem_iff_conflict
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : CoordinateDerivedHelicalAssignmentJudgment
      result spatial record assignment) :
    assignment ∉ result.derivedHelicalSpatialAssignments spatial records ↔
      CoordinateDerivedHelicalAssignmentConflict
        result spatial records assignment := by
  rw [← not_coordinateDerivedHelicalAssignmentAgreement_iff_conflict]
  exact not_congr (result.coordinateDerivedHelicalAssignment_mem_iff_agreement
    spatial records record assignment recordPresent judged)

/-- With a concrete source record fixed, public-contribution eligibility is exactly agreement and
absence of an earlier owner. -/
theorem coordinateDerivedHelicalPublicContributionJudgment_iff_agreement_and_noEarlierOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : CoordinateDerivedHelicalAssignmentJudgment
      certified.result spatial record assignment) :
    CoordinateDerivedHelicalPublicContributionJudgment
        certified spatial observations derivedPlanes records assignment ↔
      CoordinateDerivedHelicalAssignmentAgreement
          certified.result spatial records assignment ∧
        CoordinateDerivedHelicalAssignmentHasNoEarlierOwner
          certified spatial observations derivedPlanes assignment := by
  unfold CoordinateDerivedHelicalPublicContributionJudgment
  rw [coordinateDerivedHelicalConflictFreeAssignmentJudgment_iff_agreement
    certified.result spatial records record assignment recordPresent judged]
  rfl

/-- Exact final public membership for a fixed independently valid helix observation.  The literal
assignment is present either in the earlier prefix or as an agreeing, unowned helical
contribution. -/
theorem coordinateDerivedHelicalObservationAssignment_mem_public_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : CoordinateDerivedHelicalAssignmentJudgment
      certified.result spatial record assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes records ↔
      assignment ∈ derivedPlanarHelicalSpatialBaseAssignments
          certified spatial observations derivedPlanes ∨
        (CoordinateDerivedHelicalAssignmentAgreement
            certified.result spatial records assignment ∧
          CoordinateDerivedHelicalAssignmentHasNoEarlierOwner
            certified spatial observations derivedPlanes assignment) := by
  rw [mem_analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_iff]
  apply or_congr Iff.rfl
  exact
    coordinateDerivedHelicalPublicContributionJudgment_iff_agreement_and_noEarlierOwner
      certified spatial observations derivedPlanes records record assignment
      recordPresent judged

/-- Exhaustive public refusal for a fixed valid helix observation.  If its literal assignment is
not already in the prefix, absence is caused exactly by a contradictory same-unit record or a
concrete earlier owner. -/
theorem coordinateDerivedHelicalObservationAssignment_not_mem_public_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : CoordinateDerivedHelicalAssignmentJudgment
      certified.result spatial record assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes records ↔
      assignment ∉ derivedPlanarHelicalSpatialBaseAssignments
          certified spatial observations derivedPlanes ∧
        (CoordinateDerivedHelicalAssignmentConflict
            certified.result spatial records assignment ∨
          CoordinateDerivedHelicalAssignmentHasEarlierOwner
            certified spatial observations derivedPlanes assignment) := by
  classical
  rw [← not_coordinateDerivedHelicalAssignmentAgreement_iff_conflict,
    ← not_coordinateDerivedHelicalAssignmentHasNoEarlierOwner_iff_hasEarlierOwner]
  rw [coordinateDerivedHelicalObservationAssignment_mem_public_iff
    certified spatial observations derivedPlanes records record assignment
    recordPresent judged]
  tauto

/-- The public-readiness predicate has a fully observation-scoped normal form. -/
theorem coordinateDerivedHelicalObservationPublicReady_iff_explicit
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation) :
    CoordinateDerivedHelicalObservationPublicReady
        certified spatial observations derivedPlanes records record ↔
      record ∈ records ∧
        ∃ assignment,
          CoordinateDerivedHelicalAssignmentJudgment
              certified.result spatial record assignment ∧
            CoordinateDerivedHelicalAssignmentAgreement
              certified.result spatial records assignment ∧
            CoordinateDerivedHelicalAssignmentHasNoEarlierOwner
              certified spatial observations derivedPlanes assignment := by
  constructor
  · rintro ⟨recordPresent, assignment, judged, publicJudged⟩
    have explicit :=
      (coordinateDerivedHelicalPublicContributionJudgment_iff_agreement_and_noEarlierOwner
        certified spatial observations derivedPlanes records record assignment
        recordPresent judged).mp publicJudged
    exact ⟨recordPresent, assignment, judged, explicit⟩
  · rintro ⟨recordPresent, assignment, judged, agreement, noOwner⟩
    have publicJudged :=
      (coordinateDerivedHelicalPublicContributionJudgment_iff_agreement_and_noEarlierOwner
        certified spatial observations derivedPlanes records record assignment
        recordPresent judged).mpr ⟨agreement, noOwner⟩
    exact ⟨recordPresent, assignment, judged, publicJudged⟩

/-- Literal zero multiplicity for either exhaustive helical exclusion witness. -/
theorem excluded_coordinateDerivedHelicalObservationAssignment_count_eq_zero
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : CoordinateDerivedHelicalAssignmentJudgment
      certified.result spatial record assignment)
    (notInBase : assignment ∉ derivedPlanarHelicalSpatialBaseAssignments
      certified spatial observations derivedPlanes)
    (excluded : CoordinateDerivedHelicalAssignmentConflict
        certified.result spatial records assignment ∨
      CoordinateDerivedHelicalAssignmentHasEarlierOwner
        certified spatial observations derivedPlanes assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes records) = 0 := by
  apply List.count_eq_zero_of_not_mem
  exact (coordinateDerivedHelicalObservationAssignment_not_mem_public_iff
    certified spatial observations derivedPlanes records record assignment
    recordPresent judged).mpr ⟨notInBase, excluded⟩

/-- Away from literal prefix duplication, public multiplicity one is exactly agreement plus
absence of an earlier owner. -/
theorem coordinateDerivedHelicalObservationAssignment_count_eq_one_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : CoordinateDerivedHelicalAssignmentJudgment
      certified.result spatial record assignment)
    (notInBase : assignment ∉ derivedPlanarHelicalSpatialBaseAssignments
      certified spatial observations derivedPlanes) :
    List.count assignment
        (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes records) = 1 ↔
      CoordinateDerivedHelicalAssignmentAgreement
          certified.result spatial records assignment ∧
        CoordinateDerivedHelicalAssignmentHasNoEarlierOwner
          certified spatial observations derivedPlanes assignment := by
  constructor
  · intro countOne
    have present : assignment ∈
        analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes records :=
      List.count_pos_iff.mp (by omega)
    exact (coordinateDerivedHelicalObservationAssignment_mem_public_iff
      certified spatial observations derivedPlanes records record assignment
      recordPresent judged).mp present |>.resolve_left notInBase
  · intro accepted
    have present :=
      (coordinateDerivedHelicalObservationAssignment_mem_public_iff
        certified spatial observations derivedPlanes records record assignment
        recordPresent judged).mpr (.inr accepted)
    exact List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
        certified spatial observations derivedPlanes records) present

/-- Every assignment newly contributed by the coordinate-derived helical branch is literally
`P` or `M`. -/
theorem newlyContributedCoordinateDerivedHelicalAssignment_is_P_or_M
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (present : assignment ∈
      analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes records)
    (notInBase : assignment ∉ derivedPlanarHelicalSpatialBaseAssignments
      certified spatial observations derivedPlanes) :
    assignment.outcome = StereoOutcome.helical HelicalDescriptor.P ∨
      assignment.outcome = StereoOutcome.helical HelicalDescriptor.M := by
  have classified :=
    (mem_analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_iff
      certified spatial observations derivedPlanes records assignment).mp present
  rcases classified with inBase | ⟨⟨⟨record, _, judged⟩, _⟩, _⟩
  · exact False.elim (notInBase inBase)
  · rcases judged with ⟨_, descriptor, _, assignmentEq⟩
    rw [assignmentEq]
    cases descriptor <;> simp

end TetraStereo.OneCenter
