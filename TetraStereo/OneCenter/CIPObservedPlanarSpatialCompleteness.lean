import TetraStereo.OneCenter.CIPObservedPlanarSpatialConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Observation-scoped completeness for planar `Rₚ/Sₚ`

`CIPObservedPlanarSpatialConformance` proves exact evaluator and public-list semantics.  This file
closes the complementary observation-scoped boundary.  Once a supplied record has one valid
independent assignment, it is retained by the planar list exactly when every other valid record
for that plane agrees.  Failure produces an explicit conflicting record.  At the joined public
boundary, the only additional exclusion reason is prior ownership of the same stereogenic unit.
-/

namespace BlueBookP93.GeometryIngress

/-- Every independently valid supplied observation for this plane agrees with `assignment`. -/
def PlanarDerivedAssignmentAgreement
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  ∀ otherRecord ∈ records, ∀ otherAssignment,
    PlanarDerivedObservationAssignmentJudgment
      result spatial otherRecord otherAssignment →
    otherAssignment.unit = assignment.unit →
    otherAssignment.outcome = assignment.outcome

/-- A concrete independently valid supplied observation contradicts `assignment` on the same
stereogenic plane. -/
def PlanarDerivedAssignmentConflict
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  ∃ otherRecord ∈ records, ∃ otherAssignment,
    PlanarDerivedObservationAssignmentJudgment
      result spatial otherRecord otherAssignment ∧
    otherAssignment.unit = assignment.unit ∧
    otherAssignment.outcome ≠ assignment.outcome

/-- No assignment already admitted by an earlier certified branch owns this plane. -/
def PlanarDerivedAssignmentHasNoEarlierOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) : Prop :=
  ∀ existing ∈ derivedPlanarSpatialBaseAssignments certified spatial observations,
    existing.unit ≠ assignment.unit

/-- An earlier certified branch already owns this plane. -/
def PlanarDerivedAssignmentHasEarlierOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) : Prop :=
  ∃ existing ∈ derivedPlanarSpatialBaseAssignments certified spatial observations,
    existing.unit = assignment.unit

end BlueBookP93.GeometryIngress

open BlueBookP93.GeometryIngress

/-- With a concrete source witness fixed, the existential part of the conflict-free judgment is
automatic; its remaining content is exactly global same-plane agreement. -/
theorem planarDerivedConflictFreeAssignmentJudgment_iff_agreement
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PlanarDerivedObservationAssignmentJudgment
      result spatial record assignment) :
    PlanarDerivedConflictFreeAssignmentJudgment result spatial records assignment ↔
      PlanarDerivedAssignmentAgreement result spatial records assignment := by
  constructor
  · exact fun conflictFree => conflictFree.2
  · intro agreement
    exact ⟨⟨record, recordPresent, judged⟩, agreement⟩

/-- Agreement fails exactly when the finite input contains an explicit same-plane contradictory
assignment.  This is the constructive exclusion witness hidden by the conflict filter. -/
theorem not_planarDerivedAssignmentAgreement_iff_conflict
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) :
    ¬ PlanarDerivedAssignmentAgreement result spatial records assignment ↔
      PlanarDerivedAssignmentConflict result spatial records assignment := by
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

/-- Prior-owner absence fails exactly when an earlier certified result supplies a concrete owner
of the same stereogenic plane. -/
theorem not_planarDerivedAssignmentHasNoEarlierOwner_iff_hasEarlierOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) :
    ¬ PlanarDerivedAssignmentHasNoEarlierOwner
        certified spatial observations assignment ↔
      PlanarDerivedAssignmentHasEarlierOwner
        certified spatial observations assignment := by
  classical
  simp [PlanarDerivedAssignmentHasNoEarlierOwner,
    PlanarDerivedAssignmentHasEarlierOwner]

/-- Observation-scoped exact list completeness: a valid supplied record's assignment occurs in
the conflict-free planar branch if and only if every same-plane record agrees with it. -/
theorem ChemistryNormalizationResult.planarDerivedAssignment_mem_iff_agreement
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PlanarDerivedObservationAssignmentJudgment
      result spatial record assignment) :
    assignment ∈ result.derivedPlanarSpatialAssignments spatial records ↔
      PlanarDerivedAssignmentAgreement result spatial records assignment := by
  rw [result.mem_derivedPlanarSpatialAssignments_iff]
  exact planarDerivedConflictFreeAssignmentJudgment_iff_agreement
    result spatial records record assignment recordPresent judged

/-- Observation-scoped exact list refusal: a valid supplied record is removed precisely when a
concrete independently valid record assigns the opposite `Rₚ/Sₚ` outcome to the same plane. -/
theorem ChemistryNormalizationResult.planarDerivedAssignment_not_mem_iff_conflict
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PlanarDerivedObservationAssignmentJudgment
      result spatial record assignment) :
    assignment ∉ result.derivedPlanarSpatialAssignments spatial records ↔
      PlanarDerivedAssignmentConflict result spatial records assignment := by
  rw [← not_planarDerivedAssignmentAgreement_iff_conflict]
  exact not_congr (result.planarDerivedAssignment_mem_iff_agreement
    spatial records record assignment recordPresent judged)

/-- Under a concrete valid source record, public-contribution eligibility is exactly agreement
plus absence of an earlier owner. -/
theorem planarDerivedPublicContributionJudgment_iff_agreement_and_noEarlierOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PlanarDerivedObservationAssignmentJudgment
      certified.result spatial record assignment) :
    PlanarDerivedPublicContributionJudgment
        certified spatial observations records assignment ↔
      PlanarDerivedAssignmentAgreement certified.result spatial records assignment ∧
        PlanarDerivedAssignmentHasNoEarlierOwner
          certified spatial observations assignment := by
  unfold PlanarDerivedPublicContributionJudgment
  rw [planarDerivedConflictFreeAssignmentJudgment_iff_agreement
    certified.result spatial records record assignment recordPresent judged]
  rfl

/-- Exact observation-scoped public membership.  A locally valid result is present either because
the certified prefix already contains that literal assignment, or because the planar records
agree and no prefix assignment owns its plane. -/
theorem planarDerivedObservationAssignment_mem_public_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PlanarDerivedObservationAssignmentJudgment
      certified.result spatial record assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
        certified spatial observations records ↔
      assignment ∈ derivedPlanarSpatialBaseAssignments certified spatial observations ∨
        (PlanarDerivedAssignmentAgreement certified.result spatial records assignment ∧
          PlanarDerivedAssignmentHasNoEarlierOwner
            certified spatial observations assignment) := by
  rw [mem_analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_iff]
  apply or_congr Iff.rfl
  exact planarDerivedPublicContributionJudgment_iff_agreement_and_noEarlierOwner
    certified spatial observations records record assignment recordPresent judged

/-- Exhaustive public refusal for a concrete valid observation.  If its literal assignment is not
already in the prefix, the only possible reasons for absence are an explicit same-plane conflict
or an earlier owner of that plane. -/
theorem planarDerivedObservationAssignment_not_mem_public_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PlanarDerivedObservationAssignmentJudgment
      certified.result spatial record assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
        certified spatial observations records ↔
      assignment ∉ derivedPlanarSpatialBaseAssignments certified spatial observations ∧
        (PlanarDerivedAssignmentConflict certified.result spatial records assignment ∨
          PlanarDerivedAssignmentHasEarlierOwner
            certified spatial observations assignment) := by
  classical
  rw [← not_planarDerivedAssignmentAgreement_iff_conflict,
    ← not_planarDerivedAssignmentHasNoEarlierOwner_iff_hasEarlierOwner]
  rw [planarDerivedObservationAssignment_mem_public_iff
    certified spatial observations records record assignment recordPresent judged]
  tauto

/-- The existing public-readiness predicate has a fully observation-scoped normal form: a source
record is supplied, has its unique valid assignment, all same-plane records agree, and the unit is
not owned by an earlier branch. -/
theorem planarDerivedObservationPublicReady_iff_explicit
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation) :
    PlanarDerivedObservationPublicReady certified spatial observations records record ↔
      record ∈ records ∧
        ∃ assignment,
          PlanarDerivedObservationAssignmentJudgment
              certified.result spatial record assignment ∧
            PlanarDerivedAssignmentAgreement
              certified.result spatial records assignment ∧
            PlanarDerivedAssignmentHasNoEarlierOwner
              certified spatial observations assignment := by
  constructor
  · rintro ⟨recordPresent, assignment, judged, publicJudged⟩
    have explicit :=
      (planarDerivedPublicContributionJudgment_iff_agreement_and_noEarlierOwner
        certified spatial observations records record assignment
        recordPresent judged).mp publicJudged
    exact ⟨recordPresent, assignment, judged, explicit⟩
  · rintro ⟨recordPresent, assignment, judged, agreement, noOwner⟩
    have publicJudged :=
      (planarDerivedPublicContributionJudgment_iff_agreement_and_noEarlierOwner
        certified spatial observations records record assignment
        recordPresent judged).mpr ⟨agreement, noOwner⟩
    exact ⟨recordPresent, assignment, judged, publicJudged⟩

/-- Literal zero-multiplicity form of the exhaustive exclusion theorem. -/
theorem excluded_planarDerivedObservationAssignment_count_eq_zero
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (judged : PlanarDerivedObservationAssignmentJudgment
      certified.result spatial record assignment)
    (notInBase : assignment ∉
      derivedPlanarSpatialBaseAssignments certified spatial observations)
    (excluded : PlanarDerivedAssignmentConflict
        certified.result spatial records assignment ∨
      PlanarDerivedAssignmentHasEarlierOwner
        certified spatial observations assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
          certified spatial observations records) = 0 := by
  apply List.count_eq_zero_of_not_mem
  exact (planarDerivedObservationAssignment_not_mem_public_iff
    certified spatial observations records record assignment recordPresent judged).mpr
      ⟨notInBase, excluded⟩

/-- Every member newly contributed by the derived planar branch is literally an `Rₚ` or `Sₚ`
outcome; no other public descriptor family can escape through this route. -/
theorem newlyContributedDerivedPlanarAssignment_is_Rp_or_Sp
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (present : assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
      certified spatial observations records)
    (notInBase : assignment ∉
      derivedPlanarSpatialBaseAssignments certified spatial observations) :
    assignment.outcome = StereoOutcome.planar PlanarDescriptor.Rp ∨
      assignment.outcome = StereoOutcome.planar PlanarDescriptor.Sp := by
  have classified :=
    (mem_analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_iff
      certified spatial observations records assignment).mp present
  rcases classified with inBase | ⟨⟨⟨record, _, judged⟩, _⟩, _⟩
  · exact False.elim (notInBase inBase)
  · rcases judged with
      ⟨_, _, _, _, _, _, _, descriptor, _, _, _, _, _, _, _, _, _, assignmentEq⟩
    rw [assignmentEq]
    cases descriptor <;> simp

end TetraStereo.OneCenter
