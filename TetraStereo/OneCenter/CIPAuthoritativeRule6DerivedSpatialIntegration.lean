import TetraStereo.OneCenter.CIPAuthoritativeRule6ObservedGeometryIntegration
import TetraStereo.OneCenter.CIPObservedDerivedHelicalSpatialCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Authoritative Rule 6 through the exact derived-spatial pipeline

This module carries the authoritative unannotated Rule-6 replacement through the coordinate-
derived planar and helical layers.  It supplies an exact flattened public policy, whole-list
duplicate freedom, literal exact-once emission, and independent judgment for every member.
-/

/-- The authoritative certified/observed prefix after raw planar senses have been removed and raw
axial/helical senses have passed the existing coordinate validation step. -/
def authoritativeRule6DerivedPlanarSpatialBaseAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry certified
    (observations.withoutRawPlanesAfterSpatialValidation certified.result spatial)

/-- Exact agreement and ownership policy for a coordinate-derived planar contribution above the
authoritative Rule-6 certified/observed prefix. -/
def BlueBookP93.GeometryIngress.AuthoritativeRule6PlanarDerivedPublicContributionJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  PlanarDerivedConflictFreeAssignmentJudgment
      certified.result spatial records assignment ∧
    ∀ existing ∈ authoritativeRule6DerivedPlanarSpatialBaseAssignments
        certified spatial observations,
      existing.unit ≠ assignment.unit

/-- Authoritative Rule-6 public analyzer extended with exact coordinate-derived planar units. -/
def analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation) :
    List StereoAssignment :=
  let base := authoritativeRule6DerivedPlanarSpatialBaseAssignments
    certified spatial observations
  let derived := (certified.result.derivedPlanarSpatialAssignments
    spatial derivedPlanes).filter fun assignment =>
      !(base.any fun existing => existing.unit == assignment.unit)
  (base ++ derived).eraseDups

/-- Exact membership at the authoritative planar-derived layer. -/
theorem mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) :
    assignment ∈
        analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry
          certified spatial observations derivedPlanes ↔
      assignment ∈ authoritativeRule6DerivedPlanarSpatialBaseAssignments
          certified spatial observations ∨
        BlueBookP93.GeometryIngress.AuthoritativeRule6PlanarDerivedPublicContributionJudgment
          certified spatial observations derivedPlanes assignment := by
  simp [analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry,
    BlueBookP93.GeometryIngress.AuthoritativeRule6PlanarDerivedPublicContributionJudgment,
    mem_eraseDups_iff_mem_lawful,
    certified.result.mem_derivedPlanarSpatialAssignments_iff]

/-- The authoritative planar-derived public list contains no duplicate assignments. -/
theorem analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation) :
    (analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry
      certified spatial observations derivedPlanes).Nodup := by
  unfold analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry
  exact eraseDups_nodup_lawful _

/-- Independent assignment meaning at the authoritative planar-derived boundary. -/
def IndependentlyJudgedAuthoritativeRule6DerivedPlanarSpatialAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedCertifiedGeometryStereoAssignmentWithAuthoritativeRule6 certified
      (observations.withoutRawPlanesAfterSpatialValidation certified.result spatial)
      assignment ∨
    ∃ record ∈ derivedPlanes,
      BlueBookP93.GeometryIngress.PlanarDerivedObservationAssignmentJudgment
        certified.result spatial record assignment

/-- Every member of the authoritative planar-derived list has an independent native,
observed-geometry, or exact planar-coordinate judgment. -/
theorem analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (present : assignment ∈
      analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry
        certified spatial observations derivedPlanes) :
    IndependentlyJudgedAuthoritativeRule6DerivedPlanarSpatialAssignment
      certified spatial observations derivedPlanes assignment := by
  rcases
      (mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry_iff
        certified spatial observations derivedPlanes assignment).mp present with
    base | planar
  · left
    exact analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry_member_judged
      certified
      (observations.withoutRawPlanesAfterSpatialValidation certified.result spatial)
      assignment (by
        simpa [authoritativeRule6DerivedPlanarSpatialBaseAssignments] using base)
  · exact .inr planar.1.1

/-- Authoritative planar-derived prefix after caller-supplied raw helical senses have been
removed in favor of coordinate-derived helical assignments. -/
def authoritativeRule6DerivedPlanarHelicalSpatialBaseAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry certified spatial
    observations.withoutRawHelices derivedPlanes

/-- Exact agreement and ownership policy for a coordinate-derived helical contribution above the
authoritative Rule-6 planar-derived prefix. -/
def BlueBookP93.GeometryIngress.AuthoritativeRule6CoordinateDerivedHelicalPublicContributionJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  CoordinateDerivedHelicalConflictFreeAssignmentJudgment
      certified.result spatial derivedHelices assignment ∧
    ∀ existing ∈ authoritativeRule6DerivedPlanarHelicalSpatialBaseAssignments
        certified spatial observations derivedPlanes,
      existing.unit ≠ assignment.unit

/-- Final coordinate-derived planar-plus-helical analyzer with authoritative Rule 6 installed at
the graph-native base. -/
def analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    List StereoAssignment :=
  let base := authoritativeRule6DerivedPlanarHelicalSpatialBaseAssignments
    certified spatial observations derivedPlanes
  let helices := (certified.result.derivedHelicalSpatialAssignments
    spatial derivedHelices).filter fun assignment =>
      !(base.any fun existing => existing.unit == assignment.unit)
  (base ++ helices).eraseDups

/-- Exact membership at the final authoritative coordinate-derived spatial layer. -/
theorem mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) :
    assignment ∈
        analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes derivedHelices ↔
      assignment ∈ authoritativeRule6DerivedPlanarHelicalSpatialBaseAssignments
          certified spatial observations derivedPlanes ∨
        BlueBookP93.GeometryIngress.AuthoritativeRule6CoordinateDerivedHelicalPublicContributionJudgment
            certified spatial observations derivedPlanes derivedHelices assignment := by
  simp [analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry,
    BlueBookP93.GeometryIngress.AuthoritativeRule6CoordinateDerivedHelicalPublicContributionJudgment,
    mem_eraseDups_iff_mem_lawful,
    certified.result.mem_derivedHelicalSpatialAssignments_iff]

/-- The final authoritative coordinate-derived spatial list has no duplicate assignments. -/
theorem
    analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    (analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
      certified spatial observations derivedPlanes derivedHelices).Nodup := by
  unfold analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
  exact eraseDups_nodup_lawful _

/-- A flattened independent public specification for the complete authoritative coordinate-
derived spatial list. -/
def AuthoritativeRule6DerivedSpatialPublicAssignmentJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  let rawHelixFree := observations.withoutRawHelices
  let filtered := rawHelixFree.withoutRawPlanesAfterSpatialValidation certified.result spatial
  AuthoritativeRule6ObservedGeometryPublicAssignmentJudgment certified filtered assignment ∨
    BlueBookP93.GeometryIngress.AuthoritativeRule6PlanarDerivedPublicContributionJudgment
      certified spatial rawHelixFree derivedPlanes assignment ∨
    BlueBookP93.GeometryIngress.AuthoritativeRule6CoordinateDerivedHelicalPublicContributionJudgment
        certified spatial observations derivedPlanes derivedHelices assignment

/-- Exact, fully flattened public membership theorem for the current complete authoritative
coordinate-derived spatial analyzer. -/
theorem
    mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedSpatialGeometry_iff_publicJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) :
    assignment ∈
        analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes derivedHelices ↔
      AuthoritativeRule6DerivedSpatialPublicAssignmentJudgment certified spatial observations
        derivedPlanes derivedHelices assignment := by
  rw [mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry_iff]
  unfold authoritativeRule6DerivedPlanarHelicalSpatialBaseAssignments
  rw [mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry_iff]
  unfold authoritativeRule6DerivedPlanarSpatialBaseAssignments
  rw [mem_analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry_iff]
  simp [AuthoritativeRule6DerivedSpatialPublicAssignmentJudgment, or_assoc]

/-- Independent assignment meaning at the final authoritative coordinate-derived boundary. -/
def IndependentlyJudgedAuthoritativeRule6DerivedSpatialAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedAuthoritativeRule6DerivedPlanarSpatialAssignment certified spatial
      observations.withoutRawHelices derivedPlanes assignment ∨
    ∃ record ∈ derivedHelices,
      BlueBookP93.GeometryIngress.CoordinateDerivedHelicalAssignmentJudgment
        certified.result spatial record assignment

/-- End-to-end soundness for the complete authoritative coordinate-derived spatial analyzer. -/
theorem
    analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedSpatialGeometry_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (present : assignment ∈
      analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices) :
    IndependentlyJudgedAuthoritativeRule6DerivedSpatialAssignment certified spatial observations
      derivedPlanes derivedHelices assignment := by
  rcases
      (mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry_iff
        certified spatial observations derivedPlanes derivedHelices assignment).mp present with
    base | helical
  · left
    exact analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarSpatialGeometry_member_judged
      certified spatial observations.withoutRawHelices derivedPlanes assignment (by
        simpa [authoritativeRule6DerivedPlanarHelicalSpatialBaseAssignments] using base)
  · exact .inr helical.1.1

/-- Every assignment satisfying the flattened public policy occurs literally once in the final
list. -/
theorem every_authoritativeRule6DerivedSpatialPublicAssignment_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (judged : AuthoritativeRule6DerivedSpatialPublicAssignmentJudgment certified spatial
      observations derivedPlanes derivedHelices assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 := by
  exact List.count_eq_one_of_mem
    (analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry_nodup
      certified spatial observations derivedPlanes derivedHelices)
    ((mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedSpatialGeometry_iff_publicJudgment
      certified spatial observations derivedPlanes derivedHelices assignment).mpr judged)

end TetraStereo.OneCenter
