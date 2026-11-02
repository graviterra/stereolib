import TetraStereo.OneCenter.CIPObservedPolyhedralCompletePipelineCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact final-pipeline semantics for one observed IR-9 assignment

The positive completeness theorem proves that agreement and native-unit nonownership suffice for
emission.  Here the converse is proved as well.  The essential separation lemmas establish that
no native, axial, planar, or helical branch can manufacture a literal polyhedral assignment.
-/

open BlueBookP93.GeometryIngress

private theorem polyhedralJudgment_unit_eq
    (result : ChemistryNormalizationResult)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (judged : PolyhedralObservationAssignmentJudgment result record assignment) :
    assignment.unit = StereoUnit.polyhedron record.center := by
  rcases judged with
    ⟨priorities, memberships, independentRotation?, rotation?, positions, index, absolute,
      recognitionOK, recognitionValid, priorityEq, validFrame, finiteCertificate,
      positionsRecognized, orientationRecognized, rotationEq, guardFalse, indexEq,
      absoluteEq, assignmentEq⟩
  rw [assignmentEq]

private theorem independentlyJudgedNormalized_not_polyhedral
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (center : Nat)
    (judged : IndependentlyJudgedNormalizedStereoAssignment result assignment)
    (polyhedralUnit : assignment.unit = StereoUnit.polyhedron center) : False := by
  rcases judged with tetrahedral | ordinary | routed | oddCumulene | extendedAxial
  · rcases tetrahedral with ⟨idx, idxBound, tetrahedralJudged⟩
    unfold BlueBookP93.Acyclic.PublicTetrahedralAssignmentJudgment at tetrahedralJudged
    split at tetrahedralJudged <;> rename_i atomEq
    · exact tetrahedralJudged
    · split at tetrahedralJudged <;> rename_i parityEq
      · rw [tetrahedralJudged.1] at polyhedralUnit
        cases polyhedralUnit
      · rw [tetrahedralJudged.1] at polyhedralUnit
        cases polyhedralUnit
  · rcases ordinary with ⟨record, recordPresent, ordinaryJudged⟩
    unfold BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment at ordinaryJudged
    rw [ordinaryJudged.1] at polyhedralUnit
    cases polyhedralUnit
  · rcases routed with ⟨record, recordPresent, routedJudged⟩
    unfold BlueBookP93.Acyclic.RoutedDescriptorDependentDoubleBondAssignmentJudgment at routedJudged
    unfold BlueBookP93.Acyclic.DescriptorDependentDoubleBondAssignmentJudgment at routedJudged
    rw [routedJudged.2.1] at polyhedralUnit
    cases polyhedralUnit
  · rcases oddCumulene with ⟨chain, chainPresent, oddJudged⟩
    unfold BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment at oddJudged
    rcases oddJudged with ⟨odd, frameJudged⟩
    split at frameJudged <;> rename_i frameEq
    · exact frameJudged
    · rw [frameJudged.1] at polyhedralUnit
      cases polyhedralUnit
  · rcases extendedAxial with ⟨carrier, carrierPresent, axialJudged⟩
    rw [axialJudged.1] at polyhedralUnit
    cases polyhedralUnit

private theorem authoritativeOccurrenceJudged_not_polyhedral
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (nativeCenter polyhedralCenter : Nat)
    (judged : AuthoritativeOccurrenceStereoAssignmentJudgment
      result nativeCenter assignment)
    (polyhedralUnit : assignment.unit = StereoUnit.polyhedron polyhedralCenter) : False := by
  rcases judged with ⟨spec, parity, fact, atomEq, parityEq, extendedEq, factJudged,
    assignmentEq⟩
  rw [assignmentEq] at polyhedralUnit
  cases polyhedralUnit

/-- Native graph analysis has no polyhedral output family. -/
theorem polyhedralObservationAssignment_hasNoNativeOwner
    (certified : CertifiedChemistryNormalizationResult)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (judged : PolyhedralObservationAssignmentJudgment certified.result record assignment) :
    PolyhedralAssignmentHasNoNativeOwner
      (analyzeCertifiedNormalized certified) assignment := by
  intro existing existingPresent sameUnit
  have assignmentUnit := polyhedralJudgment_unit_eq certified.result record assignment judged
  have existingPolyhedral : existing.unit = StereoUnit.polyhedron record.center :=
    sameUnit.trans assignmentUnit
  rcases analyzeCertifiedNormalized_member_judged certified existing existingPresent with
    normalized | authoritative
  · exact independentlyJudgedNormalized_not_polyhedral certified.result existing
      record.center normalized existingPolyhedral
  · rcases authoritative with ⟨nativeCenter, authoritativeJudged⟩
    exact authoritativeOccurrenceJudged_not_polyhedral certified.result existing nativeCenter
      record.center authoritativeJudged existingPolyhedral

private theorem certified_expandedStereochemicalAdmissible?_eq_true
    (certified : CertifiedChemistryNormalizationResult) :
    certified.result.expandedStereochemicalAdmissible? = true := by
  rw [ChemistryNormalizationResult.expandedStereochemicalAdmissible?_eq_true_iff]
  exact certified.result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible
    certified.stereochemicalAdmissible

/-- Exact membership in the isolated observed-geometry suffix for a fixed valid polyhedral
source record. -/
theorem polyhedralObservationAssignment_mem_observedGeometryAssignments_iff
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (judged : PolyhedralObservationAssignmentJudgment
      certified.result record assignment) :
    assignment ∈ observedGeometryAssignments certified.result observations
        (analyzeCertifiedNormalized certified) ↔
      PolyhedralObservationAssignmentAgreement
          certified.result observations.polyhedra assignment ∧
        PolyhedralAssignmentHasNoNativeOwner
          (analyzeCertifiedNormalized certified) assignment := by
  have polyhedralUnit := polyhedralJudgment_unit_eq certified.result record assignment judged
  unfold observedGeometryAssignments
  rw [if_neg]
  · dsimp only
    simp only [List.mem_append]
    constructor
    · rintro (((axial | planar) | helical) | polyhedral)
      · rcases List.mem_filter.mp axial with ⟨axialConflictFree, notNative⟩
        have axialRaw := conflictFreeGeometryAssignments_member_source _ _ axialConflictFree
        rcases List.mem_filterMap.mp axialRaw with
          ⟨axialRecord, axialRecordPresent, produced⟩
        have axialJudged := certified.result.axialGeometryObservationAssignment?_sound_P92
          axialRecord assignment produced
        rw [axialJudged.unit] at polyhedralUnit
        cases polyhedralUnit
      · have planarRaw := conflictFreeGeometryAssignments_member_source _ _ planar
        rcases List.mem_filterMap.mp planarRaw with
          ⟨planarRecord, planarRecordPresent, produced⟩
        have planarJudged := certified.result.planarGeometryObservationAssignment?_sound_P92
          planarRecord assignment produced
        rw [planarJudged.unit] at polyhedralUnit
        cases polyhedralUnit
      · have helicalRaw := conflictFreeGeometryAssignments_member_source _ _ helical
        rcases List.mem_filterMap.mp helicalRaw with
          ⟨helicalRecord, helicalRecordPresent, produced⟩
        have helicalJudged := certified.result.helicalGeometryObservationAssignment?_sound_P92
          helicalRecord assignment produced
        rw [helicalJudged.unit] at polyhedralUnit
        cases polyhedralUnit
      · exact (certified.result.polyhedralObservedContribution_mem_iff
          observations.polyhedra (analyzeCertifiedNormalized certified) record assignment
          recordPresent judged).mp polyhedral
    · intro eligible
      exact .inr ((certified.result.polyhedralObservedContribution_mem_iff
        observations.polyhedra (analyzeCertifiedNormalized certified) record assignment
        recordPresent judged).mpr eligible)
  · simp [certified_expandedStereochemicalAdmissible?_eq_true certified]

/-- Exact membership at the certified native-plus-observed public boundary. -/
theorem polyhedralObservationAssignment_mem_analyzeWithObservedGeometry_iff
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (judged : PolyhedralObservationAssignmentJudgment
      certified.result record assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithObservedGeometry certified observations ↔
      PolyhedralObservationAssignmentAgreement
          certified.result observations.polyhedra assignment ∧
        PolyhedralAssignmentHasNoNativeOwner
          (analyzeCertifiedNormalized certified) assignment := by
  unfold analyzeCertifiedNormalizedWithObservedGeometry
  rw [List.mem_append]
  constructor
  · rintro (native | observed)
    · have nativePresent : assignment ∈ analyzeCertifiedNormalized certified :=
        (List.mem_filter.mp native).1
      exact False.elim
        ((polyhedralObservationAssignment_hasNoNativeOwner certified record assignment judged)
          assignment nativePresent (by rfl))
    · exact (polyhedralObservationAssignment_mem_observedGeometryAssignments_iff
        certified observations record assignment recordPresent judged).mp observed
  · intro eligible
    exact .inr ((polyhedralObservationAssignment_mem_observedGeometryAssignments_iff
      certified observations record assignment recordPresent judged).mpr eligible)

private theorem transformed_polyhedral_obligations
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (agreement : PolyhedralObservationAssignmentAgreement
      certified.result observations.polyhedra assignment) :
    record ∈
        (observations.withoutRawHelices.withoutRawPlanesAfterSpatialValidation
          certified.result spatial).polyhedra ∧
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withoutRawHelices.withoutRawPlanesAfterSpatialValidation
          certified.result spatial).polyhedra assignment := by
  simpa [IndexedCIPGeometryObservations.withoutRawHelices,
    IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation,
    IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices,
    IndexedCIPGeometryObservations.withSpatiallyValidatedAxes] using
      And.intro recordPresent agreement

/-- Exact final public-pipeline membership for a fixed valid IR-9 record.  No other stereogenic
family can be the source of this literal assignment. -/
theorem polyhedralObservationAssignment_mem_completePipeline_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (judged : PolyhedralObservationAssignmentJudgment
      certified.result record assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentAgreement
          certified.result observations.polyhedra assignment ∧
        PolyhedralAssignmentHasNoNativeOwner
          (analyzeCertifiedNormalized certified) assignment := by
  have polyhedralUnit := polyhedralJudgment_unit_eq certified.result record assignment judged
  rw [mem_analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_iff]
  constructor
  · rintro (base | helical)
    · unfold derivedPlanarHelicalSpatialBaseAssignments at base
      rw [mem_analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_iff] at base
      rcases base with earlier | planar
      · unfold derivedPlanarSpatialBaseAssignments at earlier
        have transformedPresent : record ∈
            (observations.withoutRawHelices.withoutRawPlanesAfterSpatialValidation
              certified.result spatial).polyhedra := by
          simpa [IndexedCIPGeometryObservations.withoutRawHelices,
            IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation,
            IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices,
            IndexedCIPGeometryObservations.withSpatiallyValidatedAxes] using recordPresent
        have exactEarlier :=
          (polyhedralObservationAssignment_mem_analyzeWithObservedGeometry_iff certified
            (observations.withoutRawHelices.withoutRawPlanesAfterSpatialValidation
              certified.result spatial)
            record assignment transformedPresent judged).mp earlier
        simpa [IndexedCIPGeometryObservations.withoutRawHelices,
          IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation,
          IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices,
          IndexedCIPGeometryObservations.withSpatiallyValidatedAxes] using exactEarlier
      · rcases planar.1.1 with ⟨planarRecord, planarRecordPresent, planarJudged⟩
        rcases planarJudged with
          ⟨high, low, highPoint, lowPoint, yPoint, zPoint, planePoints, descriptor,
            frame, references, highAt, lowAt, yAt, zAt, planePointsEq, coplanar,
            descriptorJudged, assignmentEq⟩
        rw [assignmentEq] at polyhedralUnit
        cases polyhedralUnit
    · rcases helical.1.1 with ⟨helixRecord, helixRecordPresent, helixJudged⟩
      rcases helixJudged with ⟨frame, descriptor, descriptorJudged, assignmentEq⟩
      rw [assignmentEq] at polyhedralUnit
      cases polyhedralUnit
  · intro eligible
    apply Or.inl
    unfold derivedPlanarHelicalSpatialBaseAssignments
    apply (mem_analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_iff
      certified spatial observations.withoutRawHelices derivedPlanes assignment).mpr
    apply Or.inl
    unfold derivedPlanarSpatialBaseAssignments
    have transformed := transformed_polyhedral_obligations certified spatial observations record
      assignment recordPresent eligible.1
    exact (polyhedralObservationAssignment_mem_analyzeWithObservedGeometry_iff certified
      (observations.withoutRawHelices.withoutRawPlanesAfterSpatialValidation
        certified.result spatial)
      record assignment transformed.1 judged).mpr
        ⟨transformed.2, eligible.2⟩

/-- For the current analyzer's disjoint native family set, native nonownership is automatic.
Consequently same-unit observation agreement alone is the exact final membership criterion. -/
theorem polyhedralObservationAssignment_mem_completePipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (judged : PolyhedralObservationAssignmentJudgment
      certified.result record assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentAgreement
        certified.result observations.polyhedra assignment := by
  rw [polyhedralObservationAssignment_mem_completePipeline_iff certified spatial
    observations derivedPlanes derivedHelices record assignment recordPresent judged]
  simp only [and_iff_left_iff_imp]
  intro agreement
  exact polyhedralObservationAssignment_hasNoNativeOwner certified record assignment judged

/-- A concrete native assignment owns the same stereogenic unit. -/
def PolyhedralAssignmentHasNativeOwner
    (native : List StereoAssignment) (assignment : StereoAssignment) : Prop :=
  ∃ existing ∈ native, existing.unit = assignment.unit

/-- Native-owner presence is the constructive negation of the public nonownership policy. -/
theorem not_polyhedralAssignmentHasNoNativeOwner_iff_hasNativeOwner
    (native : List StereoAssignment) (assignment : StereoAssignment) :
    ¬ PolyhedralAssignmentHasNoNativeOwner native assignment ↔
      PolyhedralAssignmentHasNativeOwner native assignment := by
  classical
  simp [PolyhedralAssignmentHasNoNativeOwner, PolyhedralAssignmentHasNativeOwner]

/-- Exhaustive final refusal: a locally valid supplied polyhedral record is absent exactly when
same-unit observations conflict or a native owner exists. -/
theorem polyhedralObservationAssignment_not_mem_completePipeline_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (judged : PolyhedralObservationAssignmentJudgment
      certified.result record assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentConflict
          certified.result observations.polyhedra assignment ∨
        ¬ PolyhedralAssignmentHasNoNativeOwner
          (analyzeCertifiedNormalized certified) assignment := by
  classical
  rw [← not_polyhedralObservationAssignmentAgreement_iff_conflict]
  exact not_congr (polyhedralObservationAssignment_mem_completePipeline_iff certified spatial
    observations derivedPlanes derivedHelices record assignment recordPresent judged) |>.trans
      (not_and_or)

/-- Sharp exhaustive refusal for the current disjoint family architecture: the only possible
cause of final absence is an explicit same-unit contradictory IR-9 observation. -/
theorem polyhedralObservationAssignment_not_mem_completePipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (judged : PolyhedralObservationAssignmentJudgment
      certified.result record assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentConflict
        certified.result observations.polyhedra assignment := by
  rw [← not_polyhedralObservationAssignmentAgreement_iff_conflict]
  exact not_congr (polyhedralObservationAssignment_mem_completePipeline_iff_agreement
    certified spatial observations derivedPlanes derivedHelices record assignment
    recordPresent judged)

/-- Witness-bearing exhaustive refusal: absence is caused precisely by an explicit contradictory
polyhedral observation or an explicit native assignment owning the same unit. -/
theorem polyhedralObservationAssignment_not_mem_completePipeline_iff_conflict_or_nativeOwner
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (judged : PolyhedralObservationAssignmentJudgment
      certified.result record assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentConflict
          certified.result observations.polyhedra assignment ∨
        PolyhedralAssignmentHasNativeOwner
          (analyzeCertifiedNormalized certified) assignment := by
  rw [← not_polyhedralAssignmentHasNoNativeOwner_iff_hasNativeOwner]
  exact polyhedralObservationAssignment_not_mem_completePipeline_iff certified spatial
    observations derivedPlanes derivedHelices record assignment recordPresent judged

/-- Literal zero-multiplicity consequence of either exhaustive refusal witness. -/
theorem excluded_polyhedralObservationAssignment_count_eq_zero
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (judged : PolyhedralObservationAssignmentJudgment
      certified.result record assignment)
    (excluded : PolyhedralObservationAssignmentConflict
        certified.result observations.polyhedra assignment ∨
      PolyhedralAssignmentHasNativeOwner
        (analyzeCertifiedNormalized certified) assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 0 := by
  apply List.count_eq_zero_of_not_mem
  exact (polyhedralObservationAssignment_not_mem_completePipeline_iff_conflict_or_nativeOwner
    certified spatial observations derivedPlanes derivedHelices record assignment
    recordPresent judged).mpr excluded

end TetraStereo.OneCenter
