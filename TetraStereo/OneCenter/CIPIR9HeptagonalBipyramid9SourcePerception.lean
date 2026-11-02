import TetraStereo.OneCenter.CIPIR9HeptagonalBipyramid9CompletePipelineIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Certified molecular source perception for HBPY-9

The coordinate recognizer should not require a caller to enumerate candidate centers or donors.
This module schedules exactly the centers having nine distinct written bonded neighbours in the
certified normalized molecular graph.  Geometry remains a separate exact-coordinate judgment:
nine-coordinate source topology alone is not asserted to imply HBPY-9 shape.
-/

open BlueBookP93.GeometryIngress

/-- Independent source-topology condition for a nine-coordinate candidate center.  The neighbor
list is the canonical exact list constructed from the normalized bond records; its `Nodup`
property is already proved for every raw molecule. -/
def SourceHeptagonalBipyramid9Center
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) : Prop :=
  center < certified.result.parsed.atomCount ∧
    (certified.result.parsed.exactWrittenNeighbors center).length = 9

instance (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    Decidable (SourceHeptagonalBipyramid9Center certified center) := by
  unfold SourceHeptagonalBipyramid9Center
  infer_instance

/-- Canonical raw HBPY-9 candidate record at a molecular center. -/
def CertifiedChemistryNormalizationResult.heptagonalBipyramid9SourceRecordAt
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    IndexedHeptagonalBipyramid9SpatialObservation :=
  { center := center
    ligands := certified.result.parsed.exactWrittenNeighbors center }

/-- Exhaustive finite source schedule of nine-coordinate candidate centers. -/
def CertifiedChemistryNormalizationResult.heptagonalBipyramid9SourceRecords
    (certified : CertifiedChemistryNormalizationResult) :
    List IndexedHeptagonalBipyramid9SpatialObservation :=
  ((List.range certified.result.parsed.atomCount).filter fun center =>
      (certified.result.parsed.exactWrittenNeighbors center).length == 9).map
    certified.heptagonalBipyramid9SourceRecordAt

/-- Exact membership in the source schedule. -/
theorem CertifiedChemistryNormalizationResult.mem_heptagonalBipyramid9SourceRecords_iff
    (certified : CertifiedChemistryNormalizationResult)
    (record : IndexedHeptagonalBipyramid9SpatialObservation) :
    record ∈ certified.heptagonalBipyramid9SourceRecords ↔
      ∃ center,
        SourceHeptagonalBipyramid9Center certified center ∧
        record = certified.heptagonalBipyramid9SourceRecordAt center := by
  unfold CertifiedChemistryNormalizationResult.heptagonalBipyramid9SourceRecords
  rw [List.mem_map]
  constructor
  · rintro ⟨center, centerPresent, rfl⟩
    have filtered := List.mem_filter.mp centerPresent
    exact ⟨center,
      ⟨by simpa using (List.mem_range.mp filtered.1), by simpa using filtered.2⟩,
      rfl⟩
  · rintro ⟨center, ⟨centerBound, nine⟩, rfl⟩
    exact ⟨center, List.mem_filter.mpr
      ⟨List.mem_range.mpr centerBound, by simp [nine]⟩, rfl⟩

/-- The canonical record at a given center is scheduled exactly on the independent source
condition. -/
theorem CertifiedChemistryNormalizationResult.heptagonalBipyramid9SourceRecordAt_mem_iff
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    certified.heptagonalBipyramid9SourceRecordAt center ∈
        certified.heptagonalBipyramid9SourceRecords ↔
      SourceHeptagonalBipyramid9Center certified center := by
  rw [certified.mem_heptagonalBipyramid9SourceRecords_iff]
  constructor
  · rintro ⟨other, source, same⟩
    have centerEq : center = other := congrArg
      IndexedHeptagonalBipyramid9SpatialObservation.center same
    simpa [centerEq] using source
  · intro source
    exact ⟨center, source, rfl⟩

/-- The source schedule contains no duplicate center/ligand record. -/
theorem CertifiedChemistryNormalizationResult.heptagonalBipyramid9SourceRecords_nodup
    (certified : CertifiedChemistryNormalizationResult) :
    certified.heptagonalBipyramid9SourceRecords.Nodup := by
  unfold CertifiedChemistryNormalizationResult.heptagonalBipyramid9SourceRecords
  apply List.Nodup.map
  · intro first second same
    exact congrArg IndexedHeptagonalBipyramid9SpatialObservation.center same
  · exact List.nodup_range.filter _

/-- Every scheduled source center itself lies in the certified parsed atom range. -/
theorem SourceHeptagonalBipyramid9Center.center_bounded
    (certified : CertifiedChemistryNormalizationResult) (center : Nat)
    (source : SourceHeptagonalBipyramid9Center certified center) :
    center < certified.result.parsed.atomCount :=
  source.1

/-- The canonical donor list at an HBPY-9 source center has exactly nine entries. -/
theorem SourceHeptagonalBipyramid9Center.ligands_length
    (certified : CertifiedChemistryNormalizationResult) (center : Nat)
    (source : SourceHeptagonalBipyramid9Center certified center) :
    (certified.heptagonalBipyramid9SourceRecordAt center).ligands.length = 9 :=
  source.2

/-- All nine source donors are distinct. -/
theorem SourceHeptagonalBipyramid9Center.ligands_nodup
    (certified : CertifiedChemistryNormalizationResult) (center : Nat)
    (_source : SourceHeptagonalBipyramid9Center certified center) :
    (certified.heptagonalBipyramid9SourceRecordAt center).ligands.Nodup := by
  exact certified.result.parsed.exactWrittenNeighbors_nodup center

/-- All nine scheduled source donors are in the certified parsed atom range. -/
theorem SourceHeptagonalBipyramid9Center.ligands_bounded
    (certified : CertifiedChemistryNormalizationResult) (center ligand : Nat)
    (_source : SourceHeptagonalBipyramid9Center certified center)
    (member : ligand ∈
      (certified.heptagonalBipyramid9SourceRecordAt center).ligands) :
    ligand < certified.result.parsed.atomCount := by
  exact certified.result.parsed.exactWrittenNeighbors_bound center ligand member

/-- Exact derived-observation semantics after source scheduling and coordinate perception. -/
theorem CertifiedChemistryNormalizationResult.mem_sourceDerivedHeptagonalBipyramid9Records_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    derived ∈ certified.result.derivedHeptagonalBipyramid9SpatialRecords spatial
        certified.heptagonalBipyramid9SourceRecords ↔
      ∃ center,
        SourceHeptagonalBipyramid9Center certified center ∧
        HeptagonalBipyramid9DerivedRecordJudgment
          (certified.heptagonalBipyramid9SourceRecordAt center)
          certified.result spatial derived := by
  rw [certified.result.mem_derivedHeptagonalBipyramid9SpatialRecords_iff]
  constructor
  · rintro ⟨record, recordPresent, judged⟩
    rcases (certified.mem_heptagonalBipyramid9SourceRecords_iff record).mp recordPresent with
      ⟨center, source, rfl⟩
    exact ⟨center, source, judged⟩
  · rintro ⟨center, source, judged⟩
    exact ⟨certified.heptagonalBipyramid9SourceRecordAt center,
      (certified.heptagonalBipyramid9SourceRecordAt_mem_iff center).mpr source, judged⟩

/-- Complete public analyzer with candidate HBPY-9 centers and donor lists derived from the
certified molecular graph. -/
def analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry certified spatial
    observations derivedPlanes derivedHelices certified.heptagonalBipyramid9SourceRecords

/-- Exact final source-to-public membership for a locally valid HBPY-9 center. -/
theorem sourceHeptagonalBipyramid9SpatialAssignment_mem_completePipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHeptagonalBipyramid9Center certified center)
    (derivedJudged : HeptagonalBipyramid9DerivedRecordJudgment
      (certified.heptagonalBipyramid9SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHeptagonalBipyramid9 certified.result spatial
          certified.heptagonalBipyramid9SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
  exact heptagonalBipyramid9SpatialAssignment_mem_completePipeline_iff_agreement
    certified spatial observations derivedPlanes derivedHelices
    certified.heptagonalBipyramid9SourceRecords
    (certified.heptagonalBipyramid9SourceRecordAt center) derived assignment
    ((certified.heptagonalBipyramid9SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- Exact final refusal for a locally valid source-discovered HBPY-9 center. -/
theorem sourceHeptagonalBipyramid9SpatialAssignment_not_mem_completePipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHeptagonalBipyramid9Center certified center)
    (derivedJudged : HeptagonalBipyramid9DerivedRecordJudgment
      (certified.heptagonalBipyramid9SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withDerivedHeptagonalBipyramid9 certified.result spatial
          certified.heptagonalBipyramid9SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
  exact heptagonalBipyramid9SpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices
    certified.heptagonalBipyramid9SourceRecords
    (certified.heptagonalBipyramid9SourceRecordAt center) derived assignment
    ((certified.heptagonalBipyramid9SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- The graph-scheduled HBPY-9 public output is duplicate-free. -/
theorem analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    (analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
      certified spatial observations derivedPlanes derivedHelices).Nodup := by
  unfold analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
  exact analyzeCertifiedNormalizedWithHeptagonalBipyramid9SpatialGeometry_nodup
    certified spatial observations derivedPlanes derivedHelices
    certified.heptagonalBipyramid9SourceRecords

/-- Literal count-one characterization at the graph-scheduled final boundary. -/
theorem sourceHeptagonalBipyramid9SpatialAssignment_count_eq_one_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHeptagonalBipyramid9Center certified center)
    (derivedJudged : HeptagonalBipyramid9DerivedRecordJudgment
      (certified.heptagonalBipyramid9SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHeptagonalBipyramid9 certified.result spatial
          certified.heptagonalBipyramid9SourceRecords).polyhedra assignment := by
  unfold analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
  exact heptagonalBipyramid9SpatialAssignment_count_eq_one_iff_agreement
    certified spatial observations derivedPlanes derivedHelices
    certified.heptagonalBipyramid9SourceRecords
    (certified.heptagonalBipyramid9SourceRecordAt center) derived assignment
    ((certified.heptagonalBipyramid9SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged

/-- An explicit contradictory observation at a graph-scheduled HBPY-9 center forces literal
zero multiplicity in the public output. -/
theorem excluded_sourceHeptagonalBipyramid9SpatialAssignment_count_eq_zero
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHeptagonalBipyramid9Center certified center)
    (derivedJudged : HeptagonalBipyramid9DerivedRecordJudgment
      (certified.heptagonalBipyramid9SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment)
    (conflict : PolyhedralObservationAssignmentConflict certified.result
      (observations.withDerivedHeptagonalBipyramid9 certified.result spatial
        certified.heptagonalBipyramid9SourceRecords).polyhedra assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 0 := by
  unfold analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
  exact excluded_heptagonalBipyramid9SpatialAssignment_count_eq_zero
    certified spatial observations derivedPlanes derivedHelices
    certified.heptagonalBipyramid9SourceRecords
    (certified.heptagonalBipyramid9SourceRecordAt center) derived assignment
    ((certified.heptagonalBipyramid9SourceRecordAt_mem_iff center).mpr source)
    derivedJudged assignmentJudged conflict

/-- Literal zero multiplicity at a locally judged graph-scheduled HBPY-9 center is exactly an
explicit same-center observational conflict. -/
theorem sourceHeptagonalBipyramid9SpatialAssignment_count_eq_zero_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (derived : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (source : SourceHeptagonalBipyramid9Center certified center)
    (derivedJudged : HeptagonalBipyramid9DerivedRecordJudgment
      (certified.heptagonalBipyramid9SourceRecordAt center)
      certified.result spatial derived)
    (assignmentJudged :
      PolyhedralObservationAssignmentJudgment certified.result derived assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 0 ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withDerivedHeptagonalBipyramid9 certified.result spatial
          certified.heptagonalBipyramid9SourceRecords).polyhedra assignment := by
  rw [List.count_eq_zero]
  exact sourceHeptagonalBipyramid9SpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices center derived assignment
    source derivedJudged assignmentJudged

/-- Complete independent readiness of one source-discovered center for the final public list. -/
def SourceHeptagonalBipyramid9SpatialCompletePipelineReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (center : Nat) : Prop :=
  SourceHeptagonalBipyramid9Center certified center ∧
    ∃ derived assignment,
      HeptagonalBipyramid9DerivedRecordJudgment
        (certified.heptagonalBipyramid9SourceRecordAt center)
        certified.result spatial derived ∧
      PolyhedralObservationAssignmentJudgment certified.result derived assignment ∧
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withDerivedHeptagonalBipyramid9 certified.result spatial
          certified.heptagonalBipyramid9SourceRecords).polyhedra assignment

/-- Every source-discovered ready HBPY-9 center emits exactly one independently judged public
assignment. -/
theorem every_ready_sourceHeptagonalBipyramid9Center_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (center : Nat)
    (ready : SourceHeptagonalBipyramid9SpatialCompletePipelineReady
      certified spatial observations center) :
    ∃ assignment,
      HeptagonalBipyramid9SpatialAssignmentJudgment
        (certified.heptagonalBipyramid9SourceRecordAt center)
        certified.result spatial assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithSourceHeptagonalBipyramid9SpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 := by
  rcases ready with
    ⟨source, derived, assignment, derivedJudged, assignmentJudged, agreement⟩
  refine ⟨assignment, ?_, ?_⟩
  · exact (heptagonalBipyramid9SpatialAssignmentJudgment_iff_independent
      certified.result spatial (certified.heptagonalBipyramid9SourceRecordAt center)
      assignment).mpr ⟨derived, derivedJudged, assignmentJudged⟩
  · exact (sourceHeptagonalBipyramid9SpatialAssignment_count_eq_one_iff_agreement
      certified spatial observations derivedPlanes derivedHelices center derived assignment
      source derivedJudged assignmentJudged).mpr agreement

end TetraStereo.OneCenter
