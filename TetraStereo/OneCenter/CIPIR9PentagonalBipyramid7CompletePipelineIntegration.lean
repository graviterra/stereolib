import TetraStereo.OneCenter.CIPIR9PentagonalBipyramid7SpatialIntegration
import TetraStereo.OneCenter.CIPObservedPolyhedralCompletePipelineExactness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Complete-pipeline integration for coordinate-derived PBPY-7

This module derives typed IR-9 observations from raw PBPY-7 center/ligand records and exact
coordinates, inserts them into the existing conflict-aware public polyhedral route, and proves the
positive and negative public boundaries.  No geometry label, position list, or `A/C` sense is
accepted from the caller.
-/

open BlueBookP93.GeometryIngress

/-- Derive every exact PBPY-7 observation that can be justified from coordinates and molecular
priorities. -/
def ChemistryNormalizationResult.derivedPentagonalBipyramid7SpatialRecords
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPentagonalBipyramid7SpatialObservation) :
    List IndexedPolyhedralGeometryObservation :=
  records.filterMap fun record => record.derivedRecord? result spatial

/-- Exact source-list semantics of PBPY-7 observation derivation. -/
theorem ChemistryNormalizationResult.mem_derivedPentagonalBipyramid7SpatialRecords_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPentagonalBipyramid7SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation) :
    derived ∈ result.derivedPentagonalBipyramid7SpatialRecords spatial records ↔
      ∃ record ∈ records,
        PentagonalBipyramid7DerivedRecordJudgment record result spatial derived := by
  unfold ChemistryNormalizationResult.derivedPentagonalBipyramid7SpatialRecords
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨record, recordPresent, produced⟩
    exact ⟨record, recordPresent,
      (record.derivedRecord?_eq_some_iff result spatial derived).mp produced⟩
  · rintro ⟨record, recordPresent, judged⟩
    exact ⟨record, recordPresent,
      (record.derivedRecord?_eq_some_iff result spatial derived).mpr judged⟩

/-- Add coordinate-derived PBPY-7 records without modifying any other observation family. -/
def IndexedCIPGeometryObservations.withDerivedPentagonalBipyramid7
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPentagonalBipyramid7SpatialObservation) :
    IndexedCIPGeometryObservations :=
  { observations with
    polyhedra := observations.polyhedra ++
      result.derivedPentagonalBipyramid7SpatialRecords spatial records }

/-- A derivable PBPY-7 record is literally present in the augmented polyhedral source list. -/
theorem IndexedCIPGeometryObservations.mem_withDerivedPentagonalBipyramid7_polyhedra
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPentagonalBipyramid7SpatialObservation)
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (recordPresent : record ∈ records)
    (derivedJudged :
      PentagonalBipyramid7DerivedRecordJudgment record result spatial derived) :
    derived ∈
      (observations.withDerivedPentagonalBipyramid7 result spatial records).polyhedra := by
  apply List.mem_append.mpr
  exact .inr ((result.mem_derivedPentagonalBipyramid7SpatialRecords_iff
    spatial records derived).mpr ⟨record, recordPresent, derivedJudged⟩)

/-- The direct PBPY-7 option judgment is exactly the independent IR-9 assignment judgment for
the derived observation. -/
theorem pentagonalBipyramid7SpatialAssignmentJudgment_iff_independent
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (assignment : StereoAssignment) :
    PentagonalBipyramid7SpatialAssignmentJudgment record result spatial assignment ↔
      ∃ derived,
        PentagonalBipyramid7DerivedRecordJudgment record result spatial derived ∧
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

/-- Public analyzer with exact-coordinate PBPY-7 observations inserted before the existing
polyhedral conflict and ownership policies are applied. -/
def analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedPentagonalBipyramid7SpatialObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry certified spatial
    (observations.withDerivedPentagonalBipyramid7 certified.result spatial records)
    derivedPlanes derivedHelices

/-- Exact final membership for one independently valid coordinate-derived PBPY-7 assignment.
The only remaining public policy is agreement of every valid observation for that center. -/
theorem pentagonalBipyramid7SpatialAssignment_mem_completePipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedPentagonalBipyramid7SpatialObservation)
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      PentagonalBipyramid7DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices records ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedPentagonalBipyramid7
          certified.result spatial records).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
  exact polyhedralObservationAssignment_mem_completePipeline_iff_agreement
    certified spatial
    (observations.withDerivedPentagonalBipyramid7 certified.result spatial records)
    derivedPlanes derivedHelices derived assignment
    (observations.mem_withDerivedPentagonalBipyramid7_polyhedra certified.result spatial
      records record derived recordPresent derivedJudged)
    assignmentJudged

/-- Exhaustive public refusal for a locally valid PBPY-7 assignment: absence is equivalent to a
concrete contradictory same-center IR-9 observation. -/
theorem pentagonalBipyramid7SpatialAssignment_not_mem_completePipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedPentagonalBipyramid7SpatialObservation)
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      PentagonalBipyramid7DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices records ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withDerivedPentagonalBipyramid7
          certified.result spatial records).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
  exact polyhedralObservationAssignment_not_mem_completePipeline_iff_conflict
    certified spatial
    (observations.withDerivedPentagonalBipyramid7 certified.result spatial records)
    derivedPlanes derivedHelices derived assignment
    (observations.mem_withDerivedPentagonalBipyramid7_polyhedra certified.result spatial
      records record derived recordPresent derivedJudged)
    assignmentJudged

/-- The PBPY-7-augmented complete public output is duplicate-free. -/
theorem analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedPentagonalBipyramid7SpatialObservation) :
    (analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
      certified spatial observations derivedPlanes derivedHelices records).Nodup := by
  unfold analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
  exact analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
    certified spatial
    (observations.withDerivedPentagonalBipyramid7 certified.result spatial records)
    derivedPlanes derivedHelices

/-- Literal final multiplicity one is exactly same-center observational agreement. -/
theorem pentagonalBipyramid7SpatialAssignment_count_eq_one_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedPentagonalBipyramid7SpatialObservation)
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      PentagonalBipyramid7DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 1 ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedPentagonalBipyramid7
          certified.result spatial records).polyhedra assignment := by
  constructor
  · intro countOne
    have present : assignment ∈
        analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry certified spatial
          observations derivedPlanes derivedHelices records :=
      List.count_pos_iff.mp (by omega)
    exact (pentagonalBipyramid7SpatialAssignment_mem_completePipeline_iff_agreement
      certified spatial observations derivedPlanes derivedHelices records record derived
      assignment recordPresent derivedJudged assignmentJudged).mp present
  · intro agreement
    have present :=
      (pentagonalBipyramid7SpatialAssignment_mem_completePipeline_iff_agreement
        certified spatial observations derivedPlanes derivedHelices records record derived
        assignment recordPresent derivedJudged assignmentJudged).mpr agreement
    exact List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry_nodup
        certified spatial observations derivedPlanes derivedHelices records) present

/-- An explicit contradictory observation forces literal zero multiplicity. -/
theorem excluded_pentagonalBipyramid7SpatialAssignment_count_eq_zero
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedPentagonalBipyramid7SpatialObservation)
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      PentagonalBipyramid7DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment)
    (conflict : PolyhedralObservationAssignmentConflict certified.result
      (observations.withDerivedPentagonalBipyramid7
        certified.result spatial records).polyhedra assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 0 := by
  apply List.count_eq_zero_of_not_mem
  exact (pentagonalBipyramid7SpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices records record derived assignment
    recordPresent derivedJudged assignmentJudged).mpr conflict

/-- Readiness of one raw PBPY-7 record for the final public list. -/
def PentagonalBipyramid7SpatialCompletePipelineReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPentagonalBipyramid7SpatialObservation)
    (record : IndexedPentagonalBipyramid7SpatialObservation) : Prop :=
  record ∈ records ∧
    ∃ derived assignment,
      PentagonalBipyramid7DerivedRecordJudgment record certified.result spatial derived ∧
      PolyhedralObservationAssignmentJudgment certified.result derived assignment ∧
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedPentagonalBipyramid7
          certified.result spatial records).polyhedra assignment

/-- Every ready coordinate-derived PBPY-7 record emits one independently judged public
assignment with literal multiplicity one. -/
theorem every_ready_pentagonalBipyramid7SpatialRecord_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedPentagonalBipyramid7SpatialObservation)
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (ready : PentagonalBipyramid7SpatialCompletePipelineReady
      certified spatial observations records record) :
    ∃ assignment,
      PentagonalBipyramid7SpatialAssignmentJudgment
        record certified.result spatial assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 1 := by
  rcases ready with
    ⟨recordPresent, derived, assignment, derivedJudged, assignmentJudged, agreement⟩
  refine ⟨assignment, ?_, ?_⟩
  · exact (pentagonalBipyramid7SpatialAssignmentJudgment_iff_independent
      certified.result spatial record assignment).mpr
        ⟨derived, derivedJudged, assignmentJudged⟩
  · exact (pentagonalBipyramid7SpatialAssignment_count_eq_one_iff_agreement
      certified spatial observations derivedPlanes derivedHelices records record derived
      assignment recordPresent derivedJudged assignmentJudged).mpr agreement

end TetraStereo.OneCenter
