import TetraStereo.OneCenter.CIPAuthoritativeExpandedOccurrenceCompleteness
import TetraStereo.OneCenter.LocalizedSpiroLambdaSupportedSpatialACCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open BlueBookP93.Cyclic
open AuthoritativeCIPMancudeTotality

/-!
# Deduplicated represented configuration-family pipeline

This module joins the combined native/derived/higher-bipyramidal/fullerene/RCT/spiro result with
the independently exact represented lambda-spiro A/C family. Lambda-spiro results are embedded in
the existing represented `StereoAssignment` constructor and the union is deduplicated, so a single
physical polyhedral assignment found through both routes is emitted only once.
-/

/-- Erase the source-specific lambda-spiro carrier while retaining its exact physical center and
P-93 A/C polyhedral descriptor. -/
def localizedLambdaSpiroSupportedACToStereoAssignment
    {input : CertifiedLocalizedCIPInput}
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment) : StereoAssignment :=
  { unit := .polyhedron assignment.center.val
    outcome := .polyhedral assignment.descriptor }

/-- Embed a represented lambda-spiro assignment in the already public nested represented branch.
Using this constructor, rather than a new disjoint sum branch, makes duplicate physical results
from the coordinate and lambda-spiro routes definitionally comparable before `dedup`. -/
def localizedLambdaSpiroSupportedACToRepresentedAssignment
    {input : CertifiedLocalizedCIPInput}
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment) :
    CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment :=
  .prior (.prior (.represented
    (localizedLambdaSpiroSupportedACToStereoAssignment assignment)))

/-- The embedding preserves exactly the source center and the independently judged P-93
polyhedral A/C descriptor. -/
theorem localizedLambdaSpiroSupportedACToRepresentedAssignment_represents_descriptor
    {input : CertifiedLocalizedCIPInput}
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment) :
    let represented := localizedLambdaSpiroSupportedACToStereoAssignment assignment
    localizedLambdaSpiroSupportedACToRepresentedAssignment assignment =
        .prior (.prior (.represented represented)) ∧
      represented.unit = .polyhedron assignment.center.val ∧
      represented.outcome = .polyhedral assignment.descriptor := by
  exact ⟨rfl, rfl, rfl⟩

/-- Complete executable membership meaning of the represented-family union. The prior branch is
the exact existing combined endpoint; the new branch is stated by its independent source/carrier,
coordinate-router, and P-93 descriptor judgment. -/
def CertifiedRepresentedConfigurationFamilyExecutableMember
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (output : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) : Prop :=
  output ∈
      analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros ∨
    ∃ assignment : input.LocalizedLambdaSpiroSupportedACAssignment,
      input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified assignment ∧
        localizedLambdaSpiroSupportedACToRepresentedAssignment assignment = output

/-- Independent semantic meaning of every represented-family result. The prior endpoint retains
its constructor-specific independent judgment, while the lambda-spiro route carries the complete
source-molecule agreement, source-frame, coordinate-router, and P-93 A/C judgment. -/
def IndependentlyJudgedCertifiedRepresentedConfigurationFamilyAssignment
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (output : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) : Prop :=
  IndependentlyJudgedCertifiedDerivedSpatialFullereneRCTAndSpiroAssignment certified spatial
      (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
      derivedPlanes derivedHelices fullerenes rctPairs spiros output ∨
    ∃ assignment : input.LocalizedLambdaSpiroSupportedACAssignment,
      input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified assignment ∧
        localizedLambdaSpiroSupportedACToRepresentedAssignment assignment = output

/-- Final represented configuration-family analyzer. `dedup` is semantically necessary because a
lambda-spiro coordinate descriptor can already have entered through the represented spatial route. -/
def analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies
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
  (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro certified
      spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros ++
    (input.analyzeLocalizedLambdaSpiroSupportedAC certified).map
      (fun assignment =>
        localizedLambdaSpiroSupportedACToRepresentedAssignment assignment)).dedup

/-- Flattened membership is exactly the union of the prior executable endpoint and independently
judged represented lambda-spiro assignments. -/
theorem mem_analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_iff
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
    output ∈ analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies input certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros ↔
      CertifiedRepresentedConfigurationFamilyExecutableMember input certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros output := by
  classical
  simp only [analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies,
    List.mem_dedup, List.mem_append, List.mem_map,
    input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff,
    CertifiedRepresentedConfigurationFamilyExecutableMember]

/-- Deduplication gives a literal global no-duplicates result even when two correct routes expose
the same physical represented polyhedral assignment. -/
theorem analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_nodup
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    (analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies input certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs spiros).Nodup := by
  classical
  exact List.nodup_dedup _

/-- Every emitted represented-family result satisfies its constructor-appropriate independent
semantic judgment. -/
theorem analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_member_judged
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (output : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment)
    (present : output ∈
      analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies input certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros) :
    IndependentlyJudgedCertifiedRepresentedConfigurationFamilyAssignment input certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs spiros output := by
  rcases
      (mem_analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_iff input certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros output).mp
        present with prior | lambda
  · exact Or.inl
      (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_member_judged
        certified spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros
          output prior)
  · exact Or.inr lambda

/-- Literal count one is equivalent to exact executable membership for every possible nested
result, including an assignment discovered by both the prior and lambda-spiro routes. -/
theorem count_analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_eq_one_iff
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
        (analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies input certified spatial
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros) = 1 ↔
      CertifiedRepresentedConfigurationFamilyExecutableMember input certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros output := by
  rw [← mem_analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_iff]
  constructor
  · intro countOne
    exact List.count_pos_iff.mp (by omega)
  · exact List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_nodup input certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros)

/-- End-to-end certificate at the complete represented configuration endpoint: every emitted
descriptor has an independent family judgment and the exact hydrogen-expanded molecule admits a
total uncapped Rules-1a--6 comparison for every generated occurrence-ligand pair. -/
theorem
    analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_member_judged_and_expandedOccurrenceComparisonsTotal
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
      analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies input certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros) :
    IndependentlyJudgedCertifiedRepresentedConfigurationFamilyAssignment input certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros output ∧
      AuthoritativeCIPOccurrenceCompleteness.ExpandedOccurrenceRule6ComparisonsTotal certified
        state := by
  exact
    ⟨analyzeCertifiedNormalizedWithRepresentedConfigurationFamilies_member_judged input certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros output present,
      AuthoritativeCIPOccurrenceCompleteness.expandedOccurrenceRule6ComparisonsTotal_of_chemical_applicability
        certified kekule state⟩

end

end TetraStereo.OneCenter
