import TetraStereo.OneCenter.CIPObservedPlanarSpatialConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Coordinate-derived helical P/M completeness

The legacy helical observation contains a caller-supplied orientation bit.  This module does not
trust that bit.  It verifies a finite molecule-backed helix path and terminal-reference frame,
derives `P/M` from exact rational coordinates, closes conflict handling for a finite observation
list, and integrates the result after the already certified planar-spatial analyzer.

**Sign calibration.**  The derived descriptor uses the P-92.1.2.2.1 near-to-far convention:
looking along the directed axis from the nearer path endpoint toward the farther endpoint, a
clockwise turn from the senior near reference to the senior far reference is `P`, and an
anticlockwise turn is `M`.  Equivalently, the exact triple product
`axis · (frontArm × backArm)` is positive for `P` and negative for `M`.  The producer
`coordinateDerivedHelicalAssignment?` takes its descriptor from
`IndexedHelicalGeometryObservation.spatialDescriptor?`, so this calibration is inherited
transitively; no proof in this module depends on which sign branch is named `P`.  The independent
calibration bridge is `TetraStereo.OneCenter.CIPHelicalViewingCalibration`.
-/

namespace BlueBookP93.GeometryIngress

/-- Independent finite molecular frame for an identified helix witness.  Consecutive path atoms
must be physical neighbors, terminal references must be incident to the corresponding endpoints,
and every atom index must belong to the normalized molecule.  Identification of which chemical
path is a helix remains supplied geometry/applicability evidence. -/
def MoleculeBackedHelicalFrameJudgment
    (result : ChemistryNormalizationResult)
    (record : IndexedHelicalGeometryObservation) : Prop :=
  (∀ atom ∈ record.helixPath, atom < result.parsed.atomCount) ∧
    record.frontReference < result.parsed.atomCount ∧
    record.backReference < result.parsed.atomCount ∧
    3 ≤ record.helixPath.length ∧
    record.helixPath.Nodup ∧
    record.frontReference ∉ record.helixPath ∧
    record.backReference ∉ record.helixPath ∧
    record.frontReference ≠ record.backReference ∧
    List.IsChain
      (fun first second =>
        second ∈ result.geometryPriorityState.1.writtenNeighbors first)
      record.helixPath ∧
    match record.helixPath.head?, record.helixPath.getLast? with
    | some front, some back =>
        record.frontReference ∈
          result.geometryPriorityState.1.writtenNeighbors front ∧
        record.backReference ∈
          result.geometryPriorityState.1.writtenNeighbors back
    | _, _ => False

/-- Independent complete meaning of a coordinate-derived public helical assignment.  The
descriptor is the P-92.1.2.2.1 near-to-far reading: positive triple product is `P`, negative is
`M`. -/
def CoordinateDerivedHelicalAssignmentJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  MoleculeBackedHelicalFrameJudgment result record ∧
    ∃ descriptor,
      RationalHelicalObservationJudgment spatial record descriptor ∧
      assignment =
        { unit := StereoUnit.helix record.helixPath
          outcome := StereoOutcome.helical descriptor }

end BlueBookP93.GeometryIngress

/-- Constructively decide the complete finite molecular helix-frame judgment. -/
def ChemistryNormalizationResult.moleculeBackedHelicalFrameOK?
    (result : ChemistryNormalizationResult)
    (record : IndexedHelicalGeometryObservation) : Bool :=
  record.helixPath.all (fun atom => decide (atom < result.parsed.atomCount)) &&
    decide (record.frontReference < result.parsed.atomCount) &&
    decide (record.backReference < result.parsed.atomCount) &&
    decide (3 ≤ record.helixPath.length) &&
    decide record.helixPath.Nodup &&
    !record.helixPath.contains record.frontReference &&
    !record.helixPath.contains record.backReference &&
    decide (record.frontReference ≠ record.backReference) &&
    decide (List.IsChain
      (fun first second =>
        second ∈ result.geometryPriorityState.1.writtenNeighbors first)
      record.helixPath) &&
    match record.helixPath.head?, record.helixPath.getLast? with
    | some front, some back =>
        (result.geometryPriorityState.1.writtenNeighbors front).contains
          record.frontReference &&
        (result.geometryPriorityState.1.writtenNeighbors back).contains
          record.backReference
    | _, _ => false

@[simp] theorem ChemistryNormalizationResult.moleculeBackedHelicalFrameOK?_eq_true_iff
    (result : ChemistryNormalizationResult)
    (record : IndexedHelicalGeometryObservation) :
    result.moleculeBackedHelicalFrameOK? record = true ↔
      BlueBookP93.GeometryIngress.MoleculeBackedHelicalFrameJudgment result record := by
  simp [ChemistryNormalizationResult.moleculeBackedHelicalFrameOK?,
    BlueBookP93.GeometryIngress.MoleculeBackedHelicalFrameJudgment,
    List.all_eq_true]
  cases record.helixPath.head? <;> cases record.helixPath.getLast? <;> simp
  all_goals tauto

theorem ChemistryNormalizationResult.moleculeBackedHelicalFrameOK?_eq_false_of_frontReference_mem_path
    (result : ChemistryNormalizationResult)
    (record : IndexedHelicalGeometryObservation)
    (present : record.frontReference ∈ record.helixPath) :
    result.moleculeBackedHelicalFrameOK? record = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have judged :=
    (result.moleculeBackedHelicalFrameOK?_eq_true_iff record).mp accepted
  exact judged.2.2.2.2.2.1 present

theorem ChemistryNormalizationResult.moleculeBackedHelicalFrameOK?_eq_false_of_backReference_mem_path
    (result : ChemistryNormalizationResult)
    (record : IndexedHelicalGeometryObservation)
    (present : record.backReference ∈ record.helixPath) :
    result.moleculeBackedHelicalFrameOK? record = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have judged :=
    (result.moleculeBackedHelicalFrameOK?_eq_true_iff record).mp accepted
  exact judged.2.2.2.2.2.2.1 present

/-- Derive the public helical descriptor from the exact coordinate witness.  `record.sense` is
deliberately unused.  The descriptor comes from `record.spatialDescriptor?`, so a positive
near-to-far triple product yields `P` and a negative one yields `M` (P-92.1.2.2.1). -/
def ChemistryNormalizationResult.coordinateDerivedHelicalAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHelicalGeometryObservation) : Option StereoAssignment := do
  if result.moleculeBackedHelicalFrameOK? record then
  let descriptor ← record.spatialDescriptor? spatial
  some
    { unit := StereoUnit.helix record.helixPath
      outcome := StereoOutcome.helical descriptor }
  else none

/-- Change only the legacy raw orientation field of an otherwise identical helix witness. -/
def IndexedHelicalGeometryObservation.withSense
    (record : IndexedHelicalGeometryObservation) (sense : StereoSense) :
    IndexedHelicalGeometryObservation :=
  { record with sense := sense }

/-- Coordinate-derived helical assignment is definitionally independent of the legacy raw sense. -/
@[simp] theorem ChemistryNormalizationResult.coordinateDerivedHelicalAssignment?_withSense
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHelicalGeometryObservation) (first second : StereoSense) :
    result.coordinateDerivedHelicalAssignment? spatial (record.withSense first) =
      result.coordinateDerivedHelicalAssignment? spatial (record.withSense second) := by
  rfl

/-- Exact local success theorem: the executable returns precisely the independent molecule-frame
and rational-coordinate assignment.  Because the judgment fixes the calibrated sign meaning,
this theorem is also the producer-level statement that `P` is the positive near-to-far turn and
`M` the negative one. -/
theorem ChemistryNormalizationResult.coordinateDerivedHelicalAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHelicalGeometryObservation) (assignment : StereoAssignment) :
    result.coordinateDerivedHelicalAssignment? spatial record = some assignment ↔
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalAssignmentJudgment
        result spatial record assignment := by
  constructor
  · intro computed
    unfold ChemistryNormalizationResult.coordinateDerivedHelicalAssignment? at computed
    split at computed <;> rename_i frameAccepted
    · have frame :=
        (result.moleculeBackedHelicalFrameOK?_eq_true_iff record).mp frameAccepted
      cases descriptorEq : record.spatialDescriptor? spatial with
      | none => simp [descriptorEq] at computed
      | some descriptor =>
          have geometry :=
            (record.spatialDescriptor?_eq_some_iff spatial descriptor).mp descriptorEq
          have assignmentEq : assignment =
              { unit := StereoUnit.helix record.helixPath
                outcome := StereoOutcome.helical descriptor } := by
            simpa [descriptorEq] using computed.symm
          exact ⟨frame, descriptor, geometry, assignmentEq⟩
    · simp at computed
  · rintro ⟨frame, descriptor, geometry, rfl⟩
    have frameAccepted :=
      (result.moleculeBackedHelicalFrameOK?_eq_true_iff record).mpr frame
    have descriptorEq :=
      (record.spatialDescriptor?_eq_some_iff spatial descriptor).mpr geometry
    simp [ChemistryNormalizationResult.coordinateDerivedHelicalAssignment?,
      frameAccepted, descriptorEq]

/-- Independent readiness of one molecule-backed helical coordinate witness. -/
def BlueBookP93.GeometryIngress.CoordinateDerivedHelicalReady
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHelicalGeometryObservation) : Prop :=
  ∃ assignment,
    CoordinateDerivedHelicalAssignmentJudgment result spatial record assignment

theorem ChemistryNormalizationResult.coordinateDerivedHelicalAssignment?_isSome_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHelicalGeometryObservation) :
    (result.coordinateDerivedHelicalAssignment? spatial record).isSome = true ↔
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalReady result spatial record := by
  rw [Option.isSome_iff_exists]
  exact ⟨fun ⟨assignment, computed⟩ =>
      ⟨assignment,
        (result.coordinateDerivedHelicalAssignment?_eq_some_iff
          spatial record assignment).mp computed⟩,
    fun ⟨assignment, judged⟩ =>
      ⟨assignment,
        (result.coordinateDerivedHelicalAssignment?_eq_some_iff
          spatial record assignment).mpr judged⟩⟩

/-- Exact local refusal boundary. -/
theorem ChemistryNormalizationResult.coordinateDerivedHelicalAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHelicalGeometryObservation) :
    result.coordinateDerivedHelicalAssignment? spatial record = none ↔
      ¬ BlueBookP93.GeometryIngress.CoordinateDerivedHelicalReady result spatial record := by
  rw [← not_iff_not]
  simp only [not_not]
  rw [← result.coordinateDerivedHelicalAssignment?_isSome_iff spatial record]
  exact Option.ne_none_iff_isSome

/-- A fixed molecule/coordinate/helix observation has at most one independent assignment. -/
theorem BlueBookP93.GeometryIngress.coordinateDerivedHelicalAssignmentJudgment_subsingleton
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHelicalGeometryObservation) {left right : StereoAssignment}
    (leftJudged : CoordinateDerivedHelicalAssignmentJudgment result spatial record left)
    (rightJudged : CoordinateDerivedHelicalAssignmentJudgment result spatial record right) :
    left = right := by
  have leftComputed :=
    (result.coordinateDerivedHelicalAssignment?_eq_some_iff
      spatial record left).mpr leftJudged
  have rightComputed :=
    (result.coordinateDerivedHelicalAssignment?_eq_some_iff
      spatial record right).mpr rightJudged
  rw [leftComputed] at rightComputed
  exact Option.some.inj rightComputed

/-! ## Exact finite-list helical conflict policy -/

/-- Evaluate a finite list of identified molecule-backed helix witnesses and retain a unit only
when all successful coordinate evaluations of that unit agree. -/
def ChemistryNormalizationResult.derivedHelicalSpatialAssignments
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation) : List StereoAssignment :=
  conflictFreeGeometryAssignments
    (records.filterMap (result.coordinateDerivedHelicalAssignment? spatial))

/-- Independent meaning of a conflict-free coordinate-derived helical list member. -/
def BlueBookP93.GeometryIngress.CoordinateDerivedHelicalConflictFreeAssignmentJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  (∃ record ∈ records,
    CoordinateDerivedHelicalAssignmentJudgment result spatial record assignment) ∧
  ∀ otherRecord ∈ records, ∀ otherAssignment,
    CoordinateDerivedHelicalAssignmentJudgment
      result spatial otherRecord otherAssignment →
    otherAssignment.unit = assignment.unit →
    otherAssignment.outcome = assignment.outcome

theorem ChemistryNormalizationResult.mem_derivedHelicalSpatialAssignments_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) :
    assignment ∈ result.derivedHelicalSpatialAssignments spatial records ↔
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalConflictFreeAssignmentJudgment
        result spatial records assignment := by
  rw [ChemistryNormalizationResult.derivedHelicalSpatialAssignments,
    mem_conflictFreeGeometryAssignments_iff]
  constructor
  · rintro ⟨candidatePresent, agrees⟩
    rcases List.mem_filterMap.mp candidatePresent with
      ⟨record, recordPresent, computed⟩
    refine ⟨⟨record, recordPresent,
      (result.coordinateDerivedHelicalAssignment?_eq_some_iff
        spatial record assignment).mp computed⟩, ?_⟩
    intro otherRecord otherRecordPresent otherAssignment otherJudged sameUnit
    have otherComputed :=
      (result.coordinateDerivedHelicalAssignment?_eq_some_iff
        spatial otherRecord otherAssignment).mpr otherJudged
    exact agrees otherAssignment
      (List.mem_filterMap.mpr
        ⟨otherRecord, otherRecordPresent, otherComputed⟩) sameUnit
  · rintro ⟨⟨record, recordPresent, judged⟩, allAgree⟩
    have computed :=
      (result.coordinateDerivedHelicalAssignment?_eq_some_iff
        spatial record assignment).mpr judged
    refine ⟨List.mem_filterMap.mpr ⟨record, recordPresent, computed⟩, ?_⟩
    intro otherAssignment otherCandidate sameUnit
    rcases List.mem_filterMap.mp otherCandidate with
      ⟨otherRecord, otherRecordPresent, otherComputed⟩
    exact allAgree otherRecord otherRecordPresent otherAssignment
      ((result.coordinateDerivedHelicalAssignment?_eq_some_iff
        spatial otherRecord otherAssignment).mp otherComputed) sameUnit

theorem ChemistryNormalizationResult.derivedHelicalSpatialAssignments_nodup
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedHelicalGeometryObservation) :
    (result.derivedHelicalSpatialAssignments spatial records).Nodup := by
  exact conflictFreeGeometryAssignments_nodup _

/-! ## Public planar-plus-helical coordinate analyzer -/

/-- Remove the legacy caller-supplied helical-sense route before coordinate-derived helices are
joined.  The existing planar-spatial analyzer will also remove raw planar senses. -/
def IndexedCIPGeometryObservations.withoutRawHelices
    (observations : IndexedCIPGeometryObservations) : IndexedCIPGeometryObservations :=
  { observations with helices := [] }

/-- Certified native/axial/polyhedral and coordinate-derived planar prefix. -/
def derivedPlanarHelicalSpatialBaseAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry certified spatial
    observations.withoutRawHelices derivedPlanes

/-- Independent public ownership policy for one coordinate-derived helical contribution. -/
def BlueBookP93.GeometryIngress.CoordinateDerivedHelicalPublicContributionJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  CoordinateDerivedHelicalConflictFreeAssignmentJudgment
    certified.result spatial derivedHelices assignment ∧
  ∀ existing ∈ derivedPlanarHelicalSpatialBaseAssignments
      certified spatial observations derivedPlanes,
    existing.unit ≠ assignment.unit

/-- Public coordinate-derived planar-plus-helical analyzer.  Legacy raw planar and helical senses
are excluded; exact rational geometry determines both descriptor families.  For helices the
calibrated P-92.1.2.2.1 near-to-far reading applies: positive triple product is `P`, negative is
`M`. -/
def analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    List StereoAssignment :=
  let base := derivedPlanarHelicalSpatialBaseAssignments
    certified spatial observations derivedPlanes
  let helices := (certified.result.derivedHelicalSpatialAssignments
    spatial derivedHelices).filter fun assignment =>
      !(base.any fun existing => existing.unit == assignment.unit)
  (base ++ helices).eraseDups

theorem mem_analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) :
    assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      assignment ∈ derivedPlanarHelicalSpatialBaseAssignments
        certified spatial observations derivedPlanes ∨
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalPublicContributionJudgment
        certified spatial observations derivedPlanes derivedHelices assignment := by
  simp [analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry,
    BlueBookP93.GeometryIngress.CoordinateDerivedHelicalPublicContributionJudgment,
    mem_eraseDups_iff_mem_lawful,
    certified.result.mem_derivedHelicalSpatialAssignments_iff]

theorem analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
      certified spatial observations derivedPlanes derivedHelices).Nodup := by
  unfold analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
  exact eraseDups_nodup_lawful _

/-- Independent classification of every member emitted by the combined exact-coordinate route. -/
def IndependentlyJudgedCertifiedDerivedPlanarHelicalSpatialAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedCertifiedDerivedPlanarSpatialAssignment certified spatial
      observations.withoutRawHelices derivedPlanes assignment ∨
    ∃ record ∈ derivedHelices,
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalAssignmentJudgment
        certified.result spatial record assignment

/-- End-to-end soundness: every public descriptor in the combined route is independently judged
by the earlier certified pipeline, the exact planar specification, or the exact helical
molecule/coordinate specification. -/
theorem analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (present : assignment ∈
      analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices) :
    IndependentlyJudgedCertifiedDerivedPlanarHelicalSpatialAssignment
      certified spatial observations derivedPlanes derivedHelices assignment := by
  rcases (mem_analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_iff
    certified spatial observations derivedPlanes derivedHelices assignment).mp present with
    inBase | helical
  · exact .inl
      (analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_member_judged
        certified spatial observations.withoutRawHelices derivedPlanes assignment
        (by simpa [derivedPlanarHelicalSpatialBaseAssignments] using inBase))
  · exact .inr helical.1.1

/-- Independent readiness of one supplied helix witness for public contribution. -/
def BlueBookP93.GeometryIngress.CoordinateDerivedHelicalObservationPublicReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation) : Prop :=
  record ∈ records ∧
    ∃ assignment,
      CoordinateDerivedHelicalAssignmentJudgment
        certified.result spatial record assignment ∧
      CoordinateDerivedHelicalPublicContributionJudgment certified spatial observations
        derivedPlanes records assignment

/-- Every public-ready coordinate-derived helix occurs as exactly one public assignment. -/
theorem every_publicReady_coordinateDerivedHelicalObservation_occurs_exactly_once
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (ready :
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalObservationPublicReady
        certified spatial observations derivedPlanes records record) :
    ∃! assignment,
      assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes records ∧
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalAssignmentJudgment
        certified.result spatial record assignment := by
  rcases ready with ⟨recordPresent, assignment, assignmentJudged, publicJudged⟩
  have assignmentPresent :=
    (mem_analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_iff
      certified spatial observations derivedPlanes records assignment).mpr (.inr publicJudged)
  refine ⟨assignment, ⟨assignmentPresent, assignmentJudged⟩, ?_⟩
  intro other ⟨otherPresent, otherJudged⟩
  exact BlueBookP93.GeometryIngress.coordinateDerivedHelicalAssignmentJudgment_subsingleton
    certified.result spatial record otherJudged assignmentJudged

/-- Literal public-list multiplicity form of helical exact-once completeness. -/
theorem every_publicReady_coordinateDerivedHelicalObservation_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (records : List IndexedHelicalGeometryObservation)
    (record : IndexedHelicalGeometryObservation)
    (ready :
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalObservationPublicReady
        certified spatial observations derivedPlanes records record) :
    ∃ assignment,
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalAssignmentJudgment
        certified.result spatial record assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes records) = 1 := by
  rcases every_publicReady_coordinateDerivedHelicalObservation_occurs_exactly_once
      certified spatial observations derivedPlanes records record ready with
    ⟨assignment, ⟨present, judged⟩, unique⟩
  exact ⟨assignment, judged,
    List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
        certified spatial observations derivedPlanes records) present⟩

end TetraStereo.OneCenter
