import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceCompleteness
import TetraStereo.OneCenter.CIPAuthoritativeExecutableConformanceTotality
import TetraStereo.OneCenter.CIPAuthoritativeRule6TotalSemanticRefusal
import TetraStereo.OneCenter.CIPObservedSpiroConfigurationPipeline
import TetraStereo.OneCenter.CIPIR9HigherBipyramidalUnifiedCompletePipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPOccurrenceCompleteness

noncomputable section

open TetraStereo.OneCenter
open RawMolecule
open AuthoritativeCIPMancudeTotality
open AuthoritativeCIPCursorSupport
open AuthoritativeCIPMoleculeCursorRanking
open BlueBookP93.Cyclic

/-!
# Complete Rules 1a--6 comparison on the public expanded ranking molecule

The occurrence comparator's chemical totality theorem is stated for an arbitrary raw molecule.
This module instantiates it on the exact hydrogen-expanded molecule consumed by public analysis and
packages the result with every emitted assignment's independent judgment.
-/

/-- Molecule-wide totality of the uncapped Rules-1a--6 comparator on the exact expanded graph used
by public analysis. The quantification covers every directed pair of actual ligand cursors of every
generated canonical occurrence and every reference index. -/
def ExpandedOccurrenceRule6ComparisonsTotal
    (certified : CertifiedChemistryNormalizationResult)
    (state : OccurrenceAuxState) : Prop :=
  let molecule := certified.result.parsed.withExplicitHydrogens
  ∀ (center : ℕ), center < molecule.atomCount →
    ∀ (reference : ℕ) (occurrence : CanonicalBranchNode),
      CanonicalCenterTreeNode molecule center occurrence →
      ∀ (left right : CanonicalRerootCursor),
        left ∈ occurrenceLigandCursors molecule occurrence →
        right ∈ occurrenceLigandCursors molecule occurrence →
        ∃ decision,
          compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
              molecule state reference (2 * molecule.atomCount + 1) left right =
            some decision

/-- Certified source chemistry and the independently stated source Kekulé condition construct
complete Rules-1a--6 comparison on the hydrogen-expanded production graph. All expanded structural,
valence, and localized-matching obligations are derived internally. -/
theorem expandedOccurrenceRule6ComparisonsTotal_of_chemical_applicability
    (certified : CertifiedChemistryNormalizationResult)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed)
    (state : OccurrenceAuxState) :
    ExpandedOccurrenceRule6ComparisonsTotal certified state := by
  have expandedAdmitted :
      certified.result.parsed.withExplicitHydrogens.StereochemicalAdmissible :=
    certified.result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible
      certified.stereochemicalAdmissible
  have expandedValence : certified.result.parsed.withExplicitHydrogens.ValenceOK :=
    certified.result.parsed.withExplicitHydrogens_preserves_valenceOK
      certified.admissible.1 certified.valenceOK
  have expandedKekule :
      LocalizedMancudeKekuleAdmissible certified.result.parsed.withExplicitHydrogens :=
    certified.result.parsed.withExplicitHydrogens_preserves_localizedMancudeKekuleAdmissible
      certified.stereochemicalAdmissible kekule
  intro center centerBound reference occurrence occurrenceGenerated left right
    leftMember rightMember
  exact
    DescriptorRule6HierarchySupport.promoted_occurrence_ligand_comparison_exists_of_chemical_applicability
        centerBound expandedAdmitted.1.1 expandedAdmitted.1.2 expandedValence expandedKekule
        reference occurrenceGenerated leftMember rightMember

/-- Every public emitted assignment simultaneously carries its independent final judgment and
molecule-wide total uncapped Rules-1a--6 comparison on the exact expanded ranking graph. -/
theorem analyzeCertifiedNormalized_member_judged_and_expandedOccurrenceRule6ComparisonsTotal
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed)
    (state : OccurrenceAuxState) :
    IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment ∧
      ExpandedOccurrenceRule6ComparisonsTotal certified state := by
  exact ⟨analyzeCertifiedNormalized_member_judged certified assignment member,
    expandedOccurrenceRule6ComparisonsTotal_of_chemical_applicability certified kekule state⟩

/-- Final pipeline connection: every assignment emitted after authoritative Rule 6, observed
polyhedral routing, coordinate-derived planar tetrahedra, and coordinate-derived helices satisfies
the exact total-semantic public judgment and carries molecule-wide total occurrence comparison on
the same expanded molecule. -/
theorem
    mem_completeRule6DerivedSpatialPipeline_totalSemantic_and_expandedOccurrenceComparisonsTotal
    (certified : CertifiedChemistryNormalizationResult)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed)
    (state : OccurrenceAuxState) (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (member : assignment ∈
      analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices) :
    TotalSemanticAuthoritativeRule6DerivedSpatialPublicAssignmentJudgment
        certified spatial observations derivedPlanes derivedHelices assignment ∧
      ExpandedOccurrenceRule6ComparisonsTotal certified state := by
  exact
    ⟨(mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedSpatialGeometry_iff_totalSemantic
        certified spatial observations derivedPlanes derivedHelices assignment).mp member,
      expandedOccurrenceRule6ComparisonsTotal_of_chemical_applicability certified kekule state⟩

/-- The expanded Rules-1a--6 totality certificate survives the final represented fullerene,
RCT-pair, and spiro family refinements.  Every emitted sum-type result simultaneously carries its
independent family judgment and total uncapped comparison evidence on the exact expanded ranking
molecule. -/
theorem
    mem_completeDerivedSpatialFullereneRCTAndSpiroPipeline_judged_and_expandedOccurrenceComparisonsTotal
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
    (member : output ∈
      analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros) :
    IndependentlyJudgedCertifiedDerivedSpatialFullereneRCTAndSpiroAssignment certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros output ∧
      ExpandedOccurrenceRule6ComparisonsTotal certified state := by
  exact
    ⟨analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_member_judged certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros output member,
      expandedOccurrenceRule6ComparisonsTotal_of_chemical_applicability certified kekule state⟩

/-- Final combined-family endpoint: graph-scheduled PBPY-7/HBPY-8/HBPY-9, the prior native and
derived spatial families, fullerene configurations, RCT pairs, and spiro configurations all retain
their exact independent member judgment and total expanded Rules-1a--6 comparison evidence. -/
theorem
    mem_completeSourceHigherBipyramidalSpatialFullereneRCTAndSpiroPipeline_judged_and_expandedOccurrenceComparisonsTotal
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
    (member : output ∈
      analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros) :
    IndependentlyJudgedCertifiedDerivedSpatialFullereneRCTAndSpiroAssignment certified spatial
        (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
        derivedPlanes derivedHelices fullerenes rctPairs spiros output ∧
      ExpandedOccurrenceRule6ComparisonsTotal certified state := by
  exact
    ⟨analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_member_judged
        certified spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros
        output member,
      expandedOccurrenceRule6ComparisonsTotal_of_chemical_applicability certified kekule state⟩

end


end TetraStereo.OneCenter.AuthoritativeCIPOccurrenceCompleteness
