import TetraStereo.OneCenter.CIPObservedPolyhedralCompleteness
import TetraStereo.OneCenter.CIPObservedDerivedHelicalSpatialCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# End-to-end completeness for observed IR-9 polyhedral assignments

`CIPObservedPolyhedralCompleteness` gives exact local and conflict-filtered semantics for every
polyhedral geometry admitted by the executable IR-9 router.  This module proves that a ready
polyhedral observation survives the complete public analyzer stack, including the route which
replaces raw planar and helical senses by exact-coordinate witnesses.  The final public list is
duplicate-free, so the surviving independently judged assignment occurs literally once.
-/

open BlueBookP93.GeometryIngress

/-- Independent readiness of one supplied IR-9 observation for the certified public analyzer.
It records source-list membership, the complete independent IR-9 judgment, agreement of every
valid observation for that polyhedral unit, and absence of an earlier native owner. -/
def PolyhedralObservationCertifiedPublicReady
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (record : IndexedPolyhedralGeometryObservation) : Prop :=
  record ∈ observations.polyhedra ∧
    ∃ assignment,
      PolyhedralObservationAssignmentJudgment certified.result record assignment ∧
      PolyhedralObservationAssignmentAgreement
        certified.result observations.polyhedra assignment ∧
      PolyhedralAssignmentHasNoNativeOwner
        (analyzeCertifiedNormalized certified) assignment

/-- Certification admits the exact hydrogen-expanded molecule used by all observation routes. -/
private theorem certified_expandedStereochemicalAdmissible?_eq_true
    (certified : CertifiedChemistryNormalizationResult) :
    certified.result.expandedStereochemicalAdmissible? = true := by
  rw [ChemistryNormalizationResult.expandedStereochemicalAdmissible?_eq_true_iff]
  exact certified.result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible
    certified.stereochemicalAdmissible

/-- A ready IR-9 assignment is present in the isolated observed-geometry suffix. -/
theorem PolyhedralObservationCertifiedPublicReady.mem_observedGeometryAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (record : IndexedPolyhedralGeometryObservation)
    (ready : PolyhedralObservationCertifiedPublicReady certified observations record) :
    ∃ assignment,
      PolyhedralObservationAssignmentJudgment certified.result record assignment ∧
      assignment ∈ observedGeometryAssignments certified.result observations
        (analyzeCertifiedNormalized certified) := by
  rcases ready with ⟨recordPresent, assignment, judged, agreement, noNativeOwner⟩
  have contributionPresent : assignment ∈
      certified.result.polyhedralObservedContributions observations.polyhedra
        (analyzeCertifiedNormalized certified) :=
    (certified.result.polyhedralObservedContribution_mem_iff observations.polyhedra
      (analyzeCertifiedNormalized certified) record assignment recordPresent judged).mpr
        ⟨agreement, noNativeOwner⟩
  refine ⟨assignment, judged, ?_⟩
  unfold observedGeometryAssignments
  rw [if_neg]
  · dsimp only
    simp only [List.mem_append]
    exact .inr contributionPresent
  · simp [certified_expandedStereochemicalAdmissible?_eq_true certified]

/-- A ready IR-9 assignment reaches the first public certified graph-plus-observation analyzer. -/
theorem PolyhedralObservationCertifiedPublicReady.mem_analyzeWithObservedGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (record : IndexedPolyhedralGeometryObservation)
    (ready : PolyhedralObservationCertifiedPublicReady certified observations record) :
    ∃ assignment,
      PolyhedralObservationAssignmentJudgment certified.result record assignment ∧
      assignment ∈ analyzeCertifiedNormalizedWithObservedGeometry certified observations := by
  rcases ready.mem_observedGeometryAssignments with ⟨assignment, judged, observedPresent⟩
  refine ⟨assignment, judged, ?_⟩
  unfold analyzeCertifiedNormalizedWithObservedGeometry
  exact List.mem_append_right _ observedPresent

/-- Removing raw helical senses and replacing raw planar senses by their coordinate-derived route
does not change the polyhedral record list or its independent readiness obligations. -/
theorem PolyhedralObservationCertifiedPublicReady.withoutRawHelicesAndPlanes
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (record : IndexedPolyhedralGeometryObservation)
    (ready : PolyhedralObservationCertifiedPublicReady certified observations record) :
    PolyhedralObservationCertifiedPublicReady certified
      (observations.withoutRawHelices.withoutRawPlanesAfterSpatialValidation
        certified.result spatial) record := by
  simpa [PolyhedralObservationCertifiedPublicReady,
    IndexedCIPGeometryObservations.withoutRawHelices,
    IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation,
    IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices,
    IndexedCIPGeometryObservations.withSpatiallyValidatedAxes] using ready

/-- A ready polyhedral assignment is retained in the coordinate-derived planar base. -/
theorem PolyhedralObservationCertifiedPublicReady.mem_derivedPlanarSpatialBaseAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (record : IndexedPolyhedralGeometryObservation)
    (ready : PolyhedralObservationCertifiedPublicReady certified observations record) :
    ∃ assignment,
      PolyhedralObservationAssignmentJudgment certified.result record assignment ∧
      assignment ∈ derivedPlanarSpatialBaseAssignments certified spatial
        observations.withoutRawHelices := by
  have transformedReady := ready.withoutRawHelicesAndPlanes certified spatial observations record
  rcases transformedReady.mem_analyzeWithObservedGeometry with
    ⟨assignment, judged, present⟩
  exact ⟨assignment, judged, present⟩

/-- A ready polyhedral assignment is retained after coordinate-derived planar observations join
the public result. -/
theorem PolyhedralObservationCertifiedPublicReady.mem_derivedPlanarHelicalSpatialBaseAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (ready : PolyhedralObservationCertifiedPublicReady certified observations record) :
    ∃ assignment,
      PolyhedralObservationAssignmentJudgment certified.result record assignment ∧
      assignment ∈ derivedPlanarHelicalSpatialBaseAssignments
        certified spatial observations derivedPlanes := by
  rcases ready.mem_derivedPlanarSpatialBaseAssignments certified spatial observations record with
    ⟨assignment, judged, basePresent⟩
  refine ⟨assignment, judged, ?_⟩
  unfold derivedPlanarHelicalSpatialBaseAssignments
  exact (mem_analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_iff
    certified spatial observations.withoutRawHelices derivedPlanes assignment).mpr
      (.inl basePresent)

/-- Every ready supplied IR-9 observation contributes its independently judged assignment to the
complete coordinate-derived planar-plus-helical public pipeline. -/
theorem every_publicReady_polyhedralObservation_mem_completePipeline
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (ready : PolyhedralObservationCertifiedPublicReady certified observations record) :
    ∃ assignment,
      PolyhedralObservationAssignmentJudgment certified.result record assignment ∧
      assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices := by
  rcases ready.mem_derivedPlanarHelicalSpatialBaseAssignments certified spatial observations
      derivedPlanes record with ⟨assignment, judged, basePresent⟩
  refine ⟨assignment, judged, ?_⟩
  exact (mem_analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_iff
    certified spatial observations derivedPlanes derivedHelices assignment).mpr
      (.inl basePresent)

/-- The complete local IR-9 judgment makes the emitted assignment unique for its source record. -/
theorem every_publicReady_polyhedralObservation_occurs_exactly_once
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (ready : PolyhedralObservationCertifiedPublicReady certified observations record) :
    ∃! assignment,
      assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ∧
      PolyhedralObservationAssignmentJudgment certified.result record assignment := by
  rcases every_publicReady_polyhedralObservation_mem_completePipeline certified spatial
      observations derivedPlanes derivedHelices record ready with
    ⟨assignment, judged, present⟩
  refine ⟨assignment, ⟨present, judged⟩, ?_⟩
  intro other ⟨otherPresent, otherJudged⟩
  exact polyhedralObservationAssignmentJudgment_subsingleton certified.result record
    other assignment otherJudged judged

/-- Literal final-list multiplicity form of end-to-end IR-9 completeness. -/
theorem every_publicReady_polyhedralObservation_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (ready : PolyhedralObservationCertifiedPublicReady certified observations record) :
    ∃ assignment,
      PolyhedralObservationAssignmentJudgment certified.result record assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 := by
  rcases every_publicReady_polyhedralObservation_occurs_exactly_once certified spatial
      observations derivedPlanes derivedHelices record ready with
    ⟨assignment, ⟨present, judged⟩, unique⟩
  exact ⟨assignment, judged,
    List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
        certified spatial observations derivedPlanes derivedHelices) present⟩

end TetraStereo.OneCenter
