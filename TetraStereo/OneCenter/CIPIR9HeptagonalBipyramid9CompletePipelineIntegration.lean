import TetraStereo.OneCenter.CIPIR9HeptagonalBipyramid9SpatialIntegration
import TetraStereo.OneCenter.CIPObservedPolyhedralCompletePipelineExactness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Complete-pipeline integration for coordinate-derived HBPY-9

This module derives typed IR-9 observations from raw HBPY-9 center/ligand records and exact
coordinates, inserts them into the existing conflict-aware public polyhedral route, and proves the
positive and negative public boundaries.  No geometry label, position list, or `A/C` sense is
accepted from the caller.
-/

open BlueBookP93.GeometryIngress

/-- Derive every exact HBPY-9 observation that can be justified from coordinates and molecular
priorities. -/
def ChemistryNormalizationResult.derivedHeptagonalBipyramid9SpatialRecords
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation) :
    List IndexedPolyhedralGeometryObservation :=
  records.filterMap fun record => record.derivedRecord? result spatial

/-- Exact source-list semantics of HBPY-9 observation derivation. -/
theorem ChemistryNormalizationResult.mem_derivedHeptagonalBipyramid9SpatialRecords_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation) :
    derived ∈ result.derivedHeptagonalBipyramid9SpatialRecords spatial records ↔
      ∃ record ∈ records,
        HeptagonalBipyramid9DerivedRecordJudgment record result spatial derived := by
  unfold ChemistryNormalizationResult.derivedHeptagonalBipyramid9SpatialRecords
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨record, recordPresent, produced⟩
    exact ⟨record, recordPresent,
      (record.derivedRecord?_eq_some_iff result spatial derived).mp produced⟩
  · rintro ⟨record, recordPresent, judged⟩
    exact ⟨record, recordPresent,
      (record.derivedRecord?_eq_some_iff result spatial derived).mpr judged⟩

/-- Add coordinate-derived HBPY-9 records without modifying any other observation family. -/
def IndexedCIPGeometryObservations.withDerivedHeptagonalBipyramid9
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation) :
    IndexedCIPGeometryObservations :=
  { observations with
    polyhedra := observations.polyhedra ++
      result.derivedHeptagonalBipyramid9SpatialRecords spatial records }

/-- A derivable HBPY-9 record is literally present in the augmented polyhedral source list. -/
theorem IndexedCIPGeometryObservations.mem_withDerivedHeptagonalBipyramid9_polyhedra
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation)
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HeptagonalBipyramid9DerivedRecordJudgment record result spatial derived) :
    derived ∈
      (observations.withDerivedHeptagonalBipyramid9 result spatial records).polyhedra := by
  apply List.mem_append.mpr
  exact .inr ((result.mem_derivedHeptagonalBipyramid9SpatialRecords_iff
    spatial records derived).mpr ⟨record, recordPresent, derivedJudged⟩)

/-- The direct HBPY-9 option judgment is exactly the independent IR-9 assignment judgment for
the derived observation. -/
theorem heptagonalBipyramid9SpatialAssignmentJudgment_iff_independent
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (assignment : StereoAssignment) :
    HeptagonalBipyramid9SpatialAssignmentJudgment record result spatial assignment ↔
      ∃ derived,
        HeptagonalBipyramid9DerivedRecordJudgment record result spatial derived ∧
        PolyhedralObservationAssignmentJudgment result derived assignment := by
  constructor
  · rintro ⟨derived, derivedJudged, produced⟩
    exact ⟨derived, derivedJudged,
      (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
        derived assignment).mp produced⟩
  · rintro ⟨derived, derivedJudged, judged⟩
    exact ⟨derived, derivedJudged,
      (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
        derived assignment).mpr judged⟩

/-- Public analyzer with exact-coordinate HBPY-9 observations inserted before the existing
polyhedral conflict and ownership policies are applied. -/
def analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry certified spatial
    (observations.withDerivedHeptagonalBipyramid9 certified.result spatial records)
    derivedPlanes derivedHelices

/-- Exact final membership for one independently valid coordinate-derived HBPY-9 assignment.
The only remaining public policy is agreement of every valid observation for that center. -/
theorem heptagonalBipyramid9SpatialAssignment_mem_completePipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation)
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HeptagonalBipyramid9DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices records ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHeptagonalBipyramid9
          certified.result spatial records).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
  exact polyhedralObservationAssignment_mem_completePipeline_iff_agreement
    certified spatial
    (observations.withDerivedHeptagonalBipyramid9 certified.result spatial records)
    derivedPlanes derivedHelices derived assignment
    (observations.mem_withDerivedHeptagonalBipyramid9_polyhedra certified.result spatial
      records record derived recordPresent derivedJudged)
    assignmentJudged

/-- Exhaustive public refusal for a locally valid HBPY-9 assignment: absence is equivalent to a
concrete contradictory same-center IR-9 observation. -/
theorem heptagonalBipyramid9SpatialAssignment_not_mem_completePipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation)
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HeptagonalBipyramid9DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices records ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withDerivedHeptagonalBipyramid9
          certified.result spatial records).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
  exact polyhedralObservationAssignment_not_mem_completePipeline_iff_conflict
    certified spatial
    (observations.withDerivedHeptagonalBipyramid9 certified.result spatial records)
    derivedPlanes derivedHelices derived assignment
    (observations.mem_withDerivedHeptagonalBipyramid9_polyhedra certified.result spatial
      records record derived recordPresent derivedJudged)
    assignmentJudged

/-- The HBPY-9-augmented complete public output is duplicate-free. -/
theorem analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation) :
    (analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
      certified spatial observations derivedPlanes derivedHelices records).Nodup := by
  unfold analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
  exact analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
    certified spatial
    (observations.withDerivedHeptagonalBipyramid9 certified.result spatial records)
    derivedPlanes derivedHelices

/-- Literal final multiplicity one is exactly same-center observational agreement. -/
theorem heptagonalBipyramid9SpatialAssignment_count_eq_one_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation)
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HeptagonalBipyramid9DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 1 ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHeptagonalBipyramid9
          certified.result spatial records).polyhedra assignment := by
  constructor
  · intro countOne
    have present : assignment ∈
        analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry certified spatial
          observations derivedPlanes derivedHelices records :=
      List.count_pos_iff.mp (by omega)
    exact (heptagonalBipyramid9SpatialAssignment_mem_completePipeline_iff_agreement
      certified spatial observations derivedPlanes derivedHelices records record derived
      assignment recordPresent derivedJudged assignmentJudged).mp present
  · intro agreement
    have present :=
      (heptagonalBipyramid9SpatialAssignment_mem_completePipeline_iff_agreement
        certified spatial observations derivedPlanes derivedHelices records record derived
        assignment recordPresent derivedJudged assignmentJudged).mpr agreement
    exact List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry_nodup
        certified spatial observations derivedPlanes derivedHelices records) present

/-- An explicit contradictory observation forces literal zero multiplicity. -/
theorem excluded_heptagonalBipyramid9SpatialAssignment_count_eq_zero
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation)
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HeptagonalBipyramid9DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment)
    (conflict : PolyhedralObservationAssignmentConflict certified.result
      (observations.withDerivedHeptagonalBipyramid9
        certified.result spatial records).polyhedra assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 0 := by
  apply List.count_eq_zero_of_not_mem
  exact (heptagonalBipyramid9SpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices records record derived assignment
    recordPresent derivedJudged assignmentJudged).mpr conflict

/-- Readiness of one raw HBPY-9 record for the final public list. -/
def HeptagonalBipyramid9SpatialCompletePipelineReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation)
    (record : IndexedHeptagonalBipyramid9SpatialObservation) : Prop :=
  record ∈ records ∧
    ∃ derived assignment,
      HeptagonalBipyramid9DerivedRecordJudgment record certified.result spatial derived ∧
      PolyhedralObservationAssignmentJudgment certified.result derived assignment ∧
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHeptagonalBipyramid9
          certified.result spatial records).polyhedra assignment

/-- Every ready coordinate-derived HBPY-9 record emits one independently judged public
assignment with literal multiplicity one. -/
theorem every_ready_heptagonalBipyramid9SpatialRecord_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHeptagonalBipyramid9SpatialObservation)
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (ready : HeptagonalBipyramid9SpatialCompletePipelineReady
      certified spatial observations records record) :
    ∃ assignment,
      HeptagonalBipyramid9SpatialAssignmentJudgment
        record certified.result spatial assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 1 := by
  rcases ready with
    ⟨recordPresent, derived, assignment, derivedJudged, assignmentJudged, agreement⟩
  refine ⟨assignment, ?_, ?_⟩
  · exact (heptagonalBipyramid9SpatialAssignmentJudgment_iff_independent
      certified.result spatial record assignment).mpr
        ⟨derived, derivedJudged, assignmentJudged⟩
  · exact (heptagonalBipyramid9SpatialAssignment_count_eq_one_iff_agreement
      certified spatial observations derivedPlanes derivedHelices records record derived
      assignment recordPresent derivedJudged assignmentJudged).mpr agreement

end TetraStereo.OneCenter
