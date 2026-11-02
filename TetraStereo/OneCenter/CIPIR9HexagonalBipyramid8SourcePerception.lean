import TetraStereo.OneCenter.CIPIR9HexagonalBipyramid8CompletePipelineIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Certified molecular source perception for HBPY-8

The coordinate recognizer should not require a caller to enumerate candidate centers or donors.
This module schedules exactly the centers having eight distinct written bonded neighbours in the
certified normalized molecular graph.  Geometry remains a separate exact-coordinate judgment:
eight-coordinate source topology alone is not asserted to imply HBPY-8 shape.
-/

open BlueBookP93.GeometryIngress

/-- Independent source-topology condition for a eight-coordinate candidate center.  The neighbor
list is the canonical exact list constructed from the normalized bond records; its `Nodup`
property is already proved for every raw molecule. -/
def SourceHexagonalBipyramid8Center
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) : Prop :=
  center < certified.result.parsed.atomCount ∧
    (certified.result.parsed.exactWrittenNeighbors center).length = 8

instance (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    Decidable (SourceHexagonalBipyramid8Center certified center) := by
  unfold SourceHexagonalBipyramid8Center
  infer_instance

/-- Canonical raw HBPY-8 candidate record at a molecular center. -/
def CertifiedChemistryNormalizationResult.hexagonalBipyramid8SourceRecordAt
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    IndexedHexagonalBipyramid8SpatialObservation :=
  { center := center
    ligands := certified.result.parsed.exactWrittenNeighbors center }

/-- Exhaustive finite source schedule of eight-coordinate candidate centers. -/
def CertifiedChemistryNormalizationResult.hexagonalBipyramid8SourceRecords
    (certified : CertifiedChemistryNormalizationResult) :
    List IndexedHexagonalBipyramid8SpatialObservation :=
  ((List.range certified.result.parsed.atomCount).filter fun center =>
      (certified.result.parsed.exactWrittenNeighbors center).length == 8).map
    certified.hexagonalBipyramid8SourceRecordAt

/-- Exact membership in the source schedule. -/
theorem CertifiedChemistryNormalizationResult.mem_hexagonalBipyramid8SourceRecords_iff
    (certified : CertifiedChemistryNormalizationResult)
    (record : IndexedHexagonalBipyramid8SpatialObservation) :
    record ∈ certified.hexagonalBipyramid8SourceRecords ↔
      ∃ center,
        SourceHexagonalBipyramid8Center certified center ∧
        record = certified.hexagonalBipyramid8SourceRecordAt center := by
  unfold CertifiedChemistryNormalizationResult.hexagonalBipyramid8SourceRecords
  rw [List.mem_map]
  constructor
  · rintro ⟨center, centerPresent, rfl⟩
    have filtered := List.mem_filter.mp centerPresent
    exact ⟨center,
      ⟨by simpa using (List.mem_range.mp filtered.1), by simpa using filtered.2⟩,
      rfl⟩
  · rintro ⟨center, ⟨centerBound, eight⟩, rfl⟩
    exact ⟨center, List.mem_filter.mpr
      ⟨List.mem_range.mpr centerBound, by simp [eight]⟩, rfl⟩

/-- The canonical record at a given center is scheduled exactly on the independent source
condition. -/
theorem CertifiedChemistryNormalizationResult.hexagonalBipyramid8SourceRecordAt_mem_iff
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    certified.hexagonalBipyramid8SourceRecordAt center ∈
        certified.hexagonalBipyramid8SourceRecords ↔
      SourceHexagonalBipyramid8Center certified center := by
  rw [certified.mem_hexagonalBipyramid8SourceRecords_iff]
  constructor
  · rintro ⟨other, source, same⟩
    have centerEq : center = other := congrArg
      IndexedHexagonalBipyramid8SpatialObservation.center same
    simpa [centerEq] using source
  · intro source
    exact ⟨center, source, rfl⟩

/-- The source schedule contains no duplicate center/ligand record. -/
theorem CertifiedChemistryNormalizationResult.hexagonalBipyramid8SourceRecords_nodup
    (certified : CertifiedChemistryNormalizationResult) :
    certified.hexagonalBipyramid8SourceRecords.Nodup := by
  unfold CertifiedChemistryNormalizationResult.hexagonalBipyramid8SourceRecords
  apply List.Nodup.map
  · intro first second same
    exact congrArg IndexedHexagonalBipyramid8SpatialObservation.center same
  · exact List.nodup_range.filter _

/-- Every scheduled source center itself lies in the certified parsed atom range. -/
theorem SourceHexagonalBipyramid8Center.center_bounded
    (certified : CertifiedChemistryNormalizationResult) (center : Nat)
    (source : SourceHexagonalBipyramid8Center certified center) :
    center < certified.result.parsed.atomCount :=
  source.1

/-- The canonical donor list at an HBPY-8 source center has exactly eight entries. -/
theorem SourceHexagonalBipyramid8Center.ligands_length
    (certified : CertifiedChemistryNormalizationResult) (center : Nat)
    (source : SourceHexagonalBipyramid8Center certified center) :
    (certified.hexagonalBipyramid8SourceRecordAt center).ligands.length = 8 :=
  source.2

/-- All eight source donors are distinct. -/
theorem SourceHexagonalBipyramid8Center.ligands_nodup
    (certified : CertifiedChemistryNormalizationResult) (center : Nat)
    (_source : SourceHexagonalBipyramid8Center certified center) :
    (certified.hexagonalBipyramid8SourceRecordAt center).ligands.Nodup := by
  exact certified.result.parsed.exactWrittenNeighbors_nodup center

/-- All eight scheduled source donors are in the certified parsed atom range. -/
theorem SourceHexagonalBipyramid8Center.ligands_bounded
    (certified : CertifiedChemistryNormalizationResult) (center ligand : Nat)
    (_source : SourceHexagonalBipyramid8Center certified center)
    (member : ligand ∈
      (certified.hexagonalBipyramid8SourceRecordAt center).ligands) :
    ligand < certified.result.parsed.atomCount := by
  exact certified.result.parsed.exactWrittenNeighbors_bound center ligand member

/-- Exact derived-observation semantics after source scheduling and coordinate perception. -/
theorem CertifiedChemistryNormalizationResult.mem_sourceDerivedHexagonalBipyramid8Records_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    derived ∈ certified.result.derivedHexagonalBipyramid8SpatialRecords spatial
        certified.hexagonalBipyramid8SourceRecords ↔
      ∃ center,
        SourceHexagonalBipyramid8Center certified center ∧
        HexagonalBipyramid8DerivedRecordJudgment
          (certified.hexagonalBipyramid8SourceRecordAt center)
          certified.result spatial derived := by
  rw [certified.result.mem_derivedHexagonalBipyramid8SpatialRecords_iff]
  constructor
  · rintro ⟨record, recordPresent, judged⟩
    rcases (certified.mem_hexagonalBipyramid8SourceRecords_iff record).mp recordPresent with
      ⟨center, source, rfl⟩
    exact ⟨center, source, judged⟩
  · rintro ⟨center, source, judged⟩
    exact ⟨certified.hexagonalBipyramid8SourceRecordAt center,
      (certified.hexagonalBipyramid8SourceRecordAt_mem_iff center).mpr source, judged⟩

/-- Complete public analyzer with candidate HBPY-8 centers and donor lists derived from the
certified molecular graph. -/
def analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry certified spatial
    observations derivedPlanes derivedHelices certified.hexagonalBipyramid8SourceRecords

/-- Exact final source-to-public membership for a locally valid HBPY-8 center. -/
theorem sourceHexagonalBipyramid8SpatialAssignment_mem_completePipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHexagonalBipyramid8Center certified center)
    (derivedJudged : HexagonalBipyramid8DerivedRecordJudgment
      (certified.hexagonalBipyramid8SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHexagonalBipyramid8 certified.result spatial
          certified.hexagonalBipyramid8SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
  exact hexagonalBipyramid8SpatialAssignment_mem_completePipeline_iff_agreement
    certified spatial observations derivedPlanes derivedHelices
    certified.hexagonalBipyramid8SourceRecords
    (certified.hexagonalBipyramid8SourceRecordAt center) derived assignment
    ((certified.hexagonalBipyramid8SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- Exact final refusal for a locally valid source-discovered HBPY-8 center. -/
theorem sourceHexagonalBipyramid8SpatialAssignment_not_mem_completePipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHexagonalBipyramid8Center certified center)
    (derivedJudged : HexagonalBipyramid8DerivedRecordJudgment
      (certified.hexagonalBipyramid8SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withDerivedHexagonalBipyramid8 certified.result spatial
          certified.hexagonalBipyramid8SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
  exact hexagonalBipyramid8SpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices
    certified.hexagonalBipyramid8SourceRecords
    (certified.hexagonalBipyramid8SourceRecordAt center) derived assignment
    ((certified.hexagonalBipyramid8SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- The graph-scheduled HBPY-8 public output is duplicate-free. -/
theorem analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    (analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
      certified spatial observations derivedPlanes derivedHelices).Nodup := by
  unfold analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
  exact analyzeCertifiedNormalizedWithHexagonalBipyramid8SpatialGeometry_nodup
    certified spatial observations derivedPlanes derivedHelices
    certified.hexagonalBipyramid8SourceRecords

/-- Literal count-one characterization at the graph-scheduled final boundary. -/
theorem sourceHexagonalBipyramid8SpatialAssignment_count_eq_one_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHexagonalBipyramid8Center certified center)
    (derivedJudged : HexagonalBipyramid8DerivedRecordJudgment
      (certified.hexagonalBipyramid8SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHexagonalBipyramid8 certified.result spatial
          certified.hexagonalBipyramid8SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
  exact hexagonalBipyramid8SpatialAssignment_count_eq_one_iff_agreement
    certified spatial observations derivedPlanes derivedHelices
    certified.hexagonalBipyramid8SourceRecords
    (certified.hexagonalBipyramid8SourceRecordAt center) derived assignment
    ((certified.hexagonalBipyramid8SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- An explicit contradictory observation at a graph-scheduled HBPY-8 center forces literal
zero multiplicity in the public output. -/
theorem excluded_sourceHexagonalBipyramid8SpatialAssignment_count_eq_zero
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHexagonalBipyramid8Center certified center)
    (derivedJudged : HexagonalBipyramid8DerivedRecordJudgment
      (certified.hexagonalBipyramid8SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment)
    (conflict : PolyhedralObservationAssignmentConflict certified.result
      (observations.withDerivedHexagonalBipyramid8 certified.result spatial
        certified.hexagonalBipyramid8SourceRecords).polyhedra assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 0 := by
  unfold analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
  exact excluded_hexagonalBipyramid8SpatialAssignment_count_eq_zero
    certified spatial observations derivedPlanes derivedHelices
    certified.hexagonalBipyramid8SourceRecords
    (certified.hexagonalBipyramid8SourceRecordAt center) derived assignment
    ((certified.hexagonalBipyramid8SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged conflict

/-- Literal zero multiplicity at a locally judged graph-scheduled HBPY-8 center is exactly an
explicit same-center observational conflict. -/
theorem sourceHexagonalBipyramid8SpatialAssignment_count_eq_zero_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHexagonalBipyramid8Center certified center)
    (derivedJudged : HexagonalBipyramid8DerivedRecordJudgment
      (certified.hexagonalBipyramid8SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 0 ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withDerivedHexagonalBipyramid8 certified.result spatial
          certified.hexagonalBipyramid8SourceRecords).polyhedra assignment := by
  rw [List.count_eq_zero]
  exact sourceHexagonalBipyramid8SpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices center derived assignment
    source derivedJudged assignmentJudged

/-- Complete independent readiness of one source-discovered center for the final public list. -/
def SourceHexagonalBipyramid8SpatialCompletePipelineReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (center : Nat) : Prop :=
  SourceHexagonalBipyramid8Center certified center ∧
    ∃ derived assignment,
      HexagonalBipyramid8DerivedRecordJudgment
        (certified.hexagonalBipyramid8SourceRecordAt center)
        certified.result spatial derived ∧
      PolyhedralObservationAssignmentJudgment certified.result derived assignment ∧
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHexagonalBipyramid8 certified.result spatial
          certified.hexagonalBipyramid8SourceRecords).polyhedra assignment

/-- Every source-discovered ready HBPY-8 center emits exactly one independently judged public
assignment. -/
theorem every_ready_sourceHexagonalBipyramid8Center_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (ready : SourceHexagonalBipyramid8SpatialCompletePipelineReady
      certified spatial observations center) :
    ∃ assignment,
      HexagonalBipyramid8SpatialAssignmentJudgment
        (certified.hexagonalBipyramid8SourceRecordAt center)
        certified.result spatial assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithSourceHexagonalBipyramid8SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 := by
  rcases ready with
    ⟨source, derived, assignment, derivedJudged, assignmentJudged, agreement⟩
  refine ⟨assignment, ?_, ?_⟩
  · exact (hexagonalBipyramid8SpatialAssignmentJudgment_iff_independent
      certified.result spatial (certified.hexagonalBipyramid8SourceRecordAt center)
      assignment).mpr ⟨derived, derivedJudged, assignmentJudged⟩
  · exact (sourceHexagonalBipyramid8SpatialAssignment_count_eq_one_iff_agreement
      certified spatial observations derivedPlanes derivedHelices center derived assignment
      source derivedJudged assignmentJudged).mpr agreement

end TetraStereo.OneCenter
