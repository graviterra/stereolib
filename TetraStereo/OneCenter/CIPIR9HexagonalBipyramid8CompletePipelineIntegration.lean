import TetraStereo.OneCenter.CIPIR9HexagonalBipyramid8SpatialIntegration
import TetraStereo.OneCenter.CIPObservedPolyhedralCompletePipelineExactness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Complete-pipeline integration for coordinate-derived HBPY-8

This module derives typed IR-9 observations from raw HBPY-8 center/ligand records and exact
coordinates, inserts them into the existing conflict-aware public polyhedral route, and proves the
positive and negative public boundaries.  No geometry label, position list, or `A/C` sense is
accepted from the caller.
-/

open BlueBookP93.GeometryIngress

/-- Derive every exact HBPY-8 observation that can be justified from coordinates and molecular
priorities. -/
def ChemistryNormalizationResult.derivedHexagonalBipyramid8SpatialRecords
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHexagonalBipyramid8SpatialObservation) :
    List IndexedPolyhedralGeometryObservation :=
  records.filterMap fun record => record.derivedRecord? result spatial

/-- Exact source-list semantics of HBPY-8 observation derivation. -/
theorem ChemistryNormalizationResult.mem_derivedHexagonalBipyramid8SpatialRecords_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHexagonalBipyramid8SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation) :
    derived ∈ result.derivedHexagonalBipyramid8SpatialRecords spatial records ↔
      ∃ record ∈ records,
        HexagonalBipyramid8DerivedRecordJudgment record result spatial derived := by
  unfold ChemistryNormalizationResult.derivedHexagonalBipyramid8SpatialRecords
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨record, recordPresent, produced⟩
    exact ⟨record, recordPresent,
      (record.derivedRecord?_eq_some_iff result spatial derived).mp produced⟩
  · rintro ⟨record, recordPresent, judged⟩
    exact ⟨record, recordPresent,
      (record.derivedRecord?_eq_some_iff result spatial derived).mpr judged⟩

/-- Add coordinate-derived HBPY-8 records without modifying any other observation family. -/
def IndexedCIPGeometryObservations.withDerivedHexagonalBipyramid8
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHexagonalBipyramid8SpatialObservation) :
    IndexedCIPGeometryObservations :=
  { observations with
    polyhedra := observations.polyhedra ++
      result.derivedHexagonalBipyramid8SpatialRecords spatial records }

/-- A derivable HBPY-8 record is literally present in the augmented polyhedral source list. -/
theorem IndexedCIPGeometryObservations.mem_withDerivedHexagonalBipyramid8_polyhedra
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHexagonalBipyramid8SpatialObservation)
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HexagonalBipyramid8DerivedRecordJudgment record result spatial derived) :
    derived ∈
      (observations.withDerivedHexagonalBipyramid8 result spatial records).polyhedra := by
  apply List.mem_append.mpr
  exact .inr ((result.mem_derivedHexagonalBipyramid8SpatialRecords_iff
    spatial records derived).mpr ⟨record, recordPresent, derivedJudged⟩)

/-- The direct HBPY-8 option judgment is exactly the independent IR-9 assignment judgment for
the derived observation. -/
theorem hexagonalBipyramid8SpatialAssignmentJudgment_iff_independent
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (assignment : StereoAssignment) :
    HexagonalBipyramid8SpatialAssignmentJudgment record result spatial assignment ↔
      ∃ derived,
        HexagonalBipyramid8DerivedRecordJudgment record result spatial derived ∧
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

/-- Public analyzer with exact-coordinate HBPY-8 observations inserted before the existing
polyhedral conflict and ownership policies are applied. -/
def analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHexagonalBipyramid8SpatialObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry certified spatial
    (observations.withDerivedHexagonalBipyramid8 certified.result spatial records)
    derivedPlanes derivedHelices

/-- Exact final membership for one independently valid coordinate-derived HBPY-8 assignment.
The only remaining public policy is agreement of every valid observation for that center. -/
theorem hexagonalBipyramid8SpatialAssignment_mem_completePipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHexagonalBipyramid8SpatialObservation)
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HexagonalBipyramid8DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices records ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHexagonalBipyramid8
          certified.result spatial records).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
  exact polyhedralObservationAssignment_mem_completePipeline_iff_agreement
    certified spatial
    (observations.withDerivedHexagonalBipyramid8 certified.result spatial records)
    derivedPlanes derivedHelices derived assignment
    (observations.mem_withDerivedHexagonalBipyramid8_polyhedra certified.result spatial
      records record derived recordPresent derivedJudged)
    assignmentJudged

/-- Exhaustive public refusal for a locally valid HBPY-8 assignment: absence is equivalent to a
concrete contradictory same-center IR-9 observation. -/
theorem hexagonalBipyramid8SpatialAssignment_not_mem_completePipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHexagonalBipyramid8SpatialObservation)
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HexagonalBipyramid8DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices records ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withDerivedHexagonalBipyramid8
          certified.result spatial records).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
  exact polyhedralObservationAssignment_not_mem_completePipeline_iff_conflict
    certified spatial
    (observations.withDerivedHexagonalBipyramid8 certified.result spatial records)
    derivedPlanes derivedHelices derived assignment
    (observations.mem_withDerivedHexagonalBipyramid8_polyhedra certified.result spatial
      records record derived recordPresent derivedJudged)
    assignmentJudged

/-- The HBPY-8-augmented complete public output is duplicate-free. -/
theorem analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHexagonalBipyramid8SpatialObservation) :
    (analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
      certified spatial observations derivedPlanes derivedHelices records).Nodup := by
  unfold analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
  exact analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
    certified spatial
    (observations.withDerivedHexagonalBipyramid8 certified.result spatial records)
    derivedPlanes derivedHelices

/-- Literal final multiplicity one is exactly same-center observational agreement. -/
theorem hexagonalBipyramid8SpatialAssignment_count_eq_one_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHexagonalBipyramid8SpatialObservation)
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HexagonalBipyramid8DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 1 ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHexagonalBipyramid8
          certified.result spatial records).polyhedra assignment := by
  constructor
  · intro countOne
    have present : assignment ∈
        analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry certified spatial
          observations derivedPlanes derivedHelices records :=
      List.count_pos_iff.mp (by omega)
    exact (hexagonalBipyramid8SpatialAssignment_mem_completePipeline_iff_agreement
      certified spatial observations derivedPlanes derivedHelices records record derived
      assignment recordPresent derivedJudged assignmentJudged).mp present
  · intro agreement
    have present :=
      (hexagonalBipyramid8SpatialAssignment_mem_completePipeline_iff_agreement
        certified spatial observations derivedPlanes derivedHelices records record derived
        assignment recordPresent derivedJudged assignmentJudged).mpr agreement
    exact List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry_nodup
        certified spatial observations derivedPlanes derivedHelices records) present

/-- An explicit contradictory observation forces literal zero multiplicity. -/
theorem excluded_hexagonalBipyramid8SpatialAssignment_count_eq_zero
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHexagonalBipyramid8SpatialObservation)
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ records)
    (derivedJudged :
      HexagonalBipyramid8DerivedRecordJudgment record certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment)
    (conflict : PolyhedralObservationAssignmentConflict certified.result
      (observations.withDerivedHexagonalBipyramid8
        certified.result spatial records).polyhedra assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 0 := by
  apply List.count_eq_zero_of_not_mem
  exact (hexagonalBipyramid8SpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices records record derived assignment
    recordPresent derivedJudged assignmentJudged).mpr conflict

/-- Readiness of one raw HBPY-8 record for the final public list. -/
def HexagonalBipyramid8SpatialCompletePipelineReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (records : List IndexedHexagonalBipyramid8SpatialObservation)
    (record : IndexedHexagonalBipyramid8SpatialObservation) : Prop :=
  record ∈ records ∧
    ∃ derived assignment,
      HexagonalBipyramid8DerivedRecordJudgment record certified.result spatial derived ∧
      PolyhedralObservationAssignmentJudgment certified.result derived assignment ∧
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHexagonalBipyramid8
          certified.result spatial records).polyhedra assignment

/-- Every ready coordinate-derived HBPY-8 record emits one independently judged public
assignment with literal multiplicity one. -/
theorem every_ready_hexagonalBipyramid8SpatialRecord_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (records : List IndexedHexagonalBipyramid8SpatialObservation)
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (ready : HexagonalBipyramid8SpatialCompletePipelineReady
      certified spatial observations records record) :
    ∃ assignment,
      HexagonalBipyramid8SpatialAssignmentJudgment
        record certified.result spatial assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices records) = 1 := by
  rcases ready with
    ⟨recordPresent, derived, assignment, derivedJudged, assignmentJudged, agreement⟩
  refine ⟨assignment, ?_, ?_⟩
  · exact (hexagonalBipyramid8SpatialAssignmentJudgment_iff_independent
      certified.result spatial record assignment).mpr
        ⟨derived, derivedJudged, assignmentJudged⟩
  · exact (hexagonalBipyramid8SpatialAssignment_count_eq_one_iff_agreement
      certified spatial observations derivedPlanes derivedHelices records record derived
      assignment recordPresent derivedJudged assignmentJudged).mpr agreement

end TetraStereo.OneCenter
