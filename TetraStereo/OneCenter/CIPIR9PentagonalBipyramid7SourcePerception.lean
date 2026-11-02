import TetraStereo.OneCenter.CIPIR9PentagonalBipyramid7CompletePipelineIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Certified molecular source perception for PBPY-7

The coordinate recognizer should not require a caller to enumerate candidate centers or donors.
This module schedules exactly the centers having seven distinct written bonded neighbours in the
certified normalized molecular graph.  Geometry remains a separate exact-coordinate judgment:
seven-coordinate source topology alone is not asserted to imply PBPY-7 shape.
-/

open BlueBookP93.GeometryIngress

/-- Independent source-topology condition for a seven-coordinate candidate center.  The neighbor
list is the canonical exact list constructed from the normalized bond records; its `Nodup`
property is already proved for every raw molecule. -/
def SourcePentagonalBipyramid7Center
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) : Prop :=
  center < certified.result.parsed.atomCount ∧
    (certified.result.parsed.exactWrittenNeighbors center).length = 7

instance (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    Decidable (SourcePentagonalBipyramid7Center certified center) := by
  unfold SourcePentagonalBipyramid7Center
  infer_instance

/-- Canonical raw PBPY-7 candidate record at a molecular center. -/
def CertifiedChemistryNormalizationResult.pentagonalBipyramid7SourceRecordAt
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    IndexedPentagonalBipyramid7SpatialObservation :=
  { center := center
    ligands := certified.result.parsed.exactWrittenNeighbors center }

/-- Exhaustive finite source schedule of seven-coordinate candidate centers. -/
def CertifiedChemistryNormalizationResult.pentagonalBipyramid7SourceRecords
    (certified : CertifiedChemistryNormalizationResult) :
    List IndexedPentagonalBipyramid7SpatialObservation :=
  ((List.range certified.result.parsed.atomCount).filter fun center =>
      (certified.result.parsed.exactWrittenNeighbors center).length == 7).map
    certified.pentagonalBipyramid7SourceRecordAt

/-- Exact membership in the source schedule. -/
theorem CertifiedChemistryNormalizationResult.mem_pentagonalBipyramid7SourceRecords_iff
    (certified : CertifiedChemistryNormalizationResult)
    (record : IndexedPentagonalBipyramid7SpatialObservation) :
    record ∈ certified.pentagonalBipyramid7SourceRecords ↔
      ∃ center,
        SourcePentagonalBipyramid7Center certified center ∧
        record = certified.pentagonalBipyramid7SourceRecordAt center := by
  unfold CertifiedChemistryNormalizationResult.pentagonalBipyramid7SourceRecords
  rw [List.mem_map]
  constructor
  · rintro ⟨center, centerPresent, rfl⟩
    have filtered := List.mem_filter.mp centerPresent
    exact ⟨center,
      ⟨by simpa using (List.mem_range.mp filtered.1), by simpa using filtered.2⟩,
      rfl⟩
  · rintro ⟨center, ⟨centerBound, seven⟩, rfl⟩
    exact ⟨center, List.mem_filter.mpr
      ⟨List.mem_range.mpr centerBound, by simp [seven]⟩, rfl⟩

/-- The canonical record at a given center is scheduled exactly on the independent source
condition. -/
theorem CertifiedChemistryNormalizationResult.pentagonalBipyramid7SourceRecordAt_mem_iff
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    certified.pentagonalBipyramid7SourceRecordAt center ∈
        certified.pentagonalBipyramid7SourceRecords ↔
      SourcePentagonalBipyramid7Center certified center := by
  rw [certified.mem_pentagonalBipyramid7SourceRecords_iff]
  constructor
  · rintro ⟨other, source, same⟩
    have centerEq : center = other := congrArg
      IndexedPentagonalBipyramid7SpatialObservation.center same
    simpa [centerEq] using source
  · intro source
    exact ⟨center, source, rfl⟩

/-- The source schedule contains no duplicate center/ligand record. -/
theorem CertifiedChemistryNormalizationResult.pentagonalBipyramid7SourceRecords_nodup
    (certified : CertifiedChemistryNormalizationResult) :
    certified.pentagonalBipyramid7SourceRecords.Nodup := by
  unfold CertifiedChemistryNormalizationResult.pentagonalBipyramid7SourceRecords
  apply List.Nodup.map
  · intro first second same
    exact congrArg IndexedPentagonalBipyramid7SpatialObservation.center same
  · exact List.nodup_range.filter _

/-- All seven source donors are distinct. -/
theorem SourcePentagonalBipyramid7Center.ligands_nodup
    (certified : CertifiedChemistryNormalizationResult) (center : Nat)
    (_source : SourcePentagonalBipyramid7Center certified center) :
    (certified.pentagonalBipyramid7SourceRecordAt center).ligands.Nodup := by
  exact certified.result.parsed.exactWrittenNeighbors_nodup center

/-- All seven scheduled source donors are in the certified parsed atom range. -/
theorem SourcePentagonalBipyramid7Center.ligands_bounded
    (certified : CertifiedChemistryNormalizationResult) (center ligand : Nat)
    (_source : SourcePentagonalBipyramid7Center certified center)
    (member : ligand ∈
      (certified.pentagonalBipyramid7SourceRecordAt center).ligands) :
    ligand < certified.result.parsed.atomCount := by
  exact certified.result.parsed.exactWrittenNeighbors_bound center ligand member

/-- Exact derived-observation semantics after source scheduling and coordinate perception. -/
theorem CertifiedChemistryNormalizationResult.mem_sourceDerivedPentagonalBipyramid7Records_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    derived ∈ certified.result.derivedPentagonalBipyramid7SpatialRecords spatial
        certified.pentagonalBipyramid7SourceRecords ↔
      ∃ center,
        SourcePentagonalBipyramid7Center certified center ∧
        PentagonalBipyramid7DerivedRecordJudgment
          (certified.pentagonalBipyramid7SourceRecordAt center)
          certified.result spatial derived := by
  rw [certified.result.mem_derivedPentagonalBipyramid7SpatialRecords_iff]
  constructor
  · rintro ⟨record, recordPresent, judged⟩
    rcases (certified.mem_pentagonalBipyramid7SourceRecords_iff record).mp recordPresent with
      ⟨center, source, rfl⟩
    exact ⟨center, source, judged⟩
  · rintro ⟨center, source, judged⟩
    exact ⟨certified.pentagonalBipyramid7SourceRecordAt center,
      (certified.pentagonalBipyramid7SourceRecordAt_mem_iff center).mpr source, judged⟩

/-- Complete public analyzer with candidate PBPY-7 centers and donor lists derived from the
certified molecular graph. -/
def analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry certified spatial
    observations derivedPlanes derivedHelices certified.pentagonalBipyramid7SourceRecords

/-- Exact final source-to-public membership for a locally valid PBPY-7 center. -/
theorem sourcePentagonalBipyramid7SpatialAssignment_mem_completePipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourcePentagonalBipyramid7Center certified center)
    (derivedJudged : PentagonalBipyramid7DerivedRecordJudgment
      (certified.pentagonalBipyramid7SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedPentagonalBipyramid7 certified.result spatial
          certified.pentagonalBipyramid7SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
  exact pentagonalBipyramid7SpatialAssignment_mem_completePipeline_iff_agreement
    certified spatial observations derivedPlanes derivedHelices
    certified.pentagonalBipyramid7SourceRecords
    (certified.pentagonalBipyramid7SourceRecordAt center) derived assignment
    ((certified.pentagonalBipyramid7SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- Exact final refusal for a locally valid source-discovered PBPY-7 center. -/
theorem sourcePentagonalBipyramid7SpatialAssignment_not_mem_completePipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourcePentagonalBipyramid7Center certified center)
    (derivedJudged : PentagonalBipyramid7DerivedRecordJudgment
      (certified.pentagonalBipyramid7SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withDerivedPentagonalBipyramid7 certified.result spatial
          certified.pentagonalBipyramid7SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
  exact pentagonalBipyramid7SpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices
    certified.pentagonalBipyramid7SourceRecords
    (certified.pentagonalBipyramid7SourceRecordAt center) derived assignment
    ((certified.pentagonalBipyramid7SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- The graph-scheduled PBPY-7 public output is duplicate-free. -/
theorem analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    (analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
      certified spatial observations derivedPlanes derivedHelices).Nodup := by
  unfold analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
  exact analyzeCertifiedNormalizedWithPentagonalBipyramid7SpatialGeometry_nodup
    certified spatial observations derivedPlanes derivedHelices
    certified.pentagonalBipyramid7SourceRecords

/-- Literal count-one characterization at the graph-scheduled final boundary. -/
theorem sourcePentagonalBipyramid7SpatialAssignment_count_eq_one_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourcePentagonalBipyramid7Center certified center)
    (derivedJudged : PentagonalBipyramid7DerivedRecordJudgment
      (certified.pentagonalBipyramid7SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedPentagonalBipyramid7 certified.result spatial
          certified.pentagonalBipyramid7SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
  exact pentagonalBipyramid7SpatialAssignment_count_eq_one_iff_agreement
    certified spatial observations derivedPlanes derivedHelices
    certified.pentagonalBipyramid7SourceRecords
    (certified.pentagonalBipyramid7SourceRecordAt center) derived assignment
    ((certified.pentagonalBipyramid7SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- Complete independent readiness of one source-discovered center for the final public list. -/
def SourcePentagonalBipyramid7SpatialCompletePipelineReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (center : Nat) : Prop :=
  SourcePentagonalBipyramid7Center certified center ∧
    ∃ derived assignment,
      PentagonalBipyramid7DerivedRecordJudgment
        (certified.pentagonalBipyramid7SourceRecordAt center)
        certified.result spatial derived ∧
      PolyhedralObservationAssignmentJudgment certified.result derived assignment ∧
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedPentagonalBipyramid7 certified.result spatial
          certified.pentagonalBipyramid7SourceRecords).polyhedra assignment

/-- Every source-discovered ready PBPY-7 center emits exactly one independently judged public
assignment. -/
theorem every_ready_sourcePentagonalBipyramid7Center_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (ready : SourcePentagonalBipyramid7SpatialCompletePipelineReady
      certified spatial observations center) :
    ∃ assignment,
      PentagonalBipyramid7SpatialAssignmentJudgment
        (certified.pentagonalBipyramid7SourceRecordAt center)
        certified.result spatial assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithSourcePentagonalBipyramid7SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 := by
  rcases ready with
    ⟨source, derived, assignment, derivedJudged, assignmentJudged, agreement⟩
  refine ⟨assignment, ?_, ?_⟩
  · exact (pentagonalBipyramid7SpatialAssignmentJudgment_iff_independent
      certified.result spatial (certified.pentagonalBipyramid7SourceRecordAt center)
      assignment).mpr ⟨derived, derivedJudged, assignmentJudged⟩
  · exact (sourcePentagonalBipyramid7SpatialAssignment_count_eq_one_iff_agreement
      certified spatial observations derivedPlanes derivedHelices center derived assignment
      source derivedJudged assignmentJudged).mpr agreement

end TetraStereo.OneCenter
