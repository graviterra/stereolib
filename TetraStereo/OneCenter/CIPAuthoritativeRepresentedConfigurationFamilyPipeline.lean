import TetraStereo.OneCenter.CIPRepresentedConfigurationFamilyPipeline
import TetraStereo.OneCenter.CIPAuthoritativeRule6TotalSemanticRefusal

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open AuthoritativeCIPMancudeTotality
open BlueBookP93.Cyclic

/-!
# Authoritative Rule-6 represented configuration families

This module corrects the family composition seam: its represented spatial prefix is the exact
total-semantic authoritative Rule-6 analyzer, with graph-scheduled PBPY-7/HBPY-8/HBPY-9 records
inserted before spatial conflict resolution. Fullerene, RCT-pair, spiro, and represented
lambda-spiro families are then attached with exact conflict-aware public semantics.
-/

/-- Authoritative Rule-6 spatial output, using the graph-scheduled higher-bipyramidal observation
ledger, embedded together with the represented fullerene, RCT-pair, and spiro families. -/
def analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    List CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment :=
  (analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry certified
      spatial (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
        derivedPlanes derivedHelices).map
      (fun assignment => .prior (.prior (.represented assignment))) ++
    (analyzeFullereneConfigurations fullerenes).map
      (fun assignment => .prior (.prior (.fullerene assignment))) ++
    (analyzeRCTPairConfigurations rctPairs).map
      (fun assignment => .prior (.rct assignment)) ++
    (analyzeSpiroConfigurations spiros).map .spiro

/-- The represented constructor of the corrected nested endpoint is exactly the independent
total-semantic authoritative Rule-6 spatial public judgment. -/
theorem
    represented_mem_analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro_iff_totalSemantic
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (assignment : StereoAssignment) :
    (.prior (.prior (.represented assignment)) :
        CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) ∈
        analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros ↔
      TotalSemanticAuthoritativeRule6DerivedSpatialPublicAssignmentJudgment certified spatial
        (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
          derivedPlanes derivedHelices assignment := by
  simp [analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro,
    mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedSpatialGeometry_iff_totalSemantic]

/-- Exact independent public meaning of each final constructor. The represented branch is a
genuine union because one physical polyhedral result may be justified either by the authoritative
spatial analyzer or by the source-attached lambda-spiro route. -/
def AuthoritativeRepresentedConfigurationFamilyPublicJudgment
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment → Prop
  | .prior (.prior (.represented assignment)) =>
      TotalSemanticAuthoritativeRule6DerivedSpatialPublicAssignmentJudgment certified spatial
          (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
            derivedPlanes derivedHelices assignment ∨
        ∃ lambdaAssignment : input.LocalizedLambdaSpiroSupportedACAssignment,
          input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified lambdaAssignment ∧
            localizedLambdaSpiroSupportedACToStereoAssignment lambdaAssignment = assignment
  | .prior (.prior (.fullerene assignment)) =>
      ConflictFreeFullereneConfigurationAssignmentJudgment fullerenes assignment
  | .prior (.rct assignment) =>
      ConflictFreeRCTPairConfigurationAssignmentJudgment rctPairs assignment
  | .spiro assignment =>
      ConflictFreeSpiroConfigurationAssignmentJudgment spiros assignment

/-- Final authoritative represented-family list. Lambda-spiro assignments use the same nested
represented constructor and are deduplicated against authoritative spatial results. -/
def analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    List CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment :=
  (analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs spiros ++
    (input.analyzeLocalizedLambdaSpiroSupportedAC certified).map
      (fun assignment =>
        localizedLambdaSpiroSupportedACToRepresentedAssignment assignment)).dedup

/-- Exact no-omission/no-invention theorem for the corrected final family endpoint. Unlike the
legacy member-soundness relation, every clause here includes the public agreement/ownership policy
needed for the converse. -/
theorem
    mem_analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_iff_publicJudgment
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (output : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) :
    output ∈
        analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies input certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros ↔
      AuthoritativeRepresentedConfigurationFamilyPublicJudgment input certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros output := by
  classical
  cases output with
  | prior prior =>
      cases prior with
      | prior prior =>
          cases prior with
          | represented assignment =>
              simp [analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies,
                analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro,
                AuthoritativeRepresentedConfigurationFamilyPublicJudgment,
                mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedSpatialGeometry_iff_totalSemantic,
                input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff,
                localizedLambdaSpiroSupportedACToRepresentedAssignment,
                localizedLambdaSpiroSupportedACToStereoAssignment]
          | fullerene assignment =>
              simp [analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies,
                analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro,
                AuthoritativeRepresentedConfigurationFamilyPublicJudgment,
                mem_analyzeFullereneConfigurations_iff,
                localizedLambdaSpiroSupportedACToRepresentedAssignment]
      | rct assignment =>
          simp [analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies,
            analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro,
            AuthoritativeRepresentedConfigurationFamilyPublicJudgment,
            mem_analyzeRCTPairConfigurations_iff,
            localizedLambdaSpiroSupportedACToRepresentedAssignment]
  | spiro assignment =>
      simp [analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies,
        analyzeCertifiedNormalizedWithAuthoritativeDerivedSpatialFullereneRCTAndSpiro,
        AuthoritativeRepresentedConfigurationFamilyPublicJudgment,
        mem_analyzeSpiroConfigurations_iff,
        localizedLambdaSpiroSupportedACToRepresentedAssignment]

/-- Physical deduplication makes the complete authoritative family result globally
duplicate-free. -/
theorem analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_nodup
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    (analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies input certified
      spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros).Nodup := by
  classical
  exact List.nodup_dedup _

/-- Literal multiplicity one is equivalent to the full independent public judgment. -/
theorem
    count_analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_eq_one_iff_publicJudgment
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (output : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) :
    List.count output
        (analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies input certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros) = 1 ↔
      AuthoritativeRepresentedConfigurationFamilyPublicJudgment input certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros output := by
  rw [← mem_analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_iff_publicJudgment]
  constructor
  · intro countOne
    exact List.count_pos_iff.mp (by omega)
  · exact List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_nodup input
        certified spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros)

/-- Complete authoritative endpoint certificate: exact independent family semantics for the
emitted result and total uncapped Rules-1a--6 comparison on every expanded occurrence-ligand pair. -/
theorem
    analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_member_judged_and_expandedOccurrenceComparisonsTotal
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed)
    (state : OccurrenceAuxState)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (output : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment)
    (present : output ∈
      analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies input certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros) :
    AuthoritativeRepresentedConfigurationFamilyPublicJudgment input certified spatial observations
        derivedPlanes derivedHelices fullerenes rctPairs spiros output ∧
      AuthoritativeCIPOccurrenceCompleteness.ExpandedOccurrenceRule6ComparisonsTotal certified
        state := by
  exact
    ⟨(mem_analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_iff_publicJudgment
        input certified spatial observations derivedPlanes derivedHelices fullerenes rctPairs
          spiros output).mp present,
      AuthoritativeCIPOccurrenceCompleteness.expandedOccurrenceRule6ComparisonsTotal_of_chemical_applicability
        certified kekule state⟩

end

end TetraStereo.OneCenter
