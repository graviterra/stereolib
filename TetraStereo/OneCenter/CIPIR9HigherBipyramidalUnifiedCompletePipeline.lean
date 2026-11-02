import TetraStereo.OneCenter.CIPIR9PentagonalBipyramid7SourcePerception
import TetraStereo.OneCenter.CIPIR9HexagonalBipyramid8SourcePerception
import TetraStereo.OneCenter.CIPIR9HeptagonalBipyramid9SourcePerception
import TetraStereo.OneCenter.CIPObservedSpiroConfigurationPipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Unified graph-scheduled higher-bipyramidal public pipeline

PBPY-7, HBPY-8, and HBPY-9 previously had separate exact source-to-public analyzers.  A complete
consumer must run them simultaneously and apply one same-center agreement policy to their union.
This module constructs that union directly from the certified molecular graph and proves exact
positive, negative, uniqueness, and multiplicity semantics for an independently judged candidate
of any of the three families.
-/

open BlueBookP93.GeometryIngress
open BlueBookP93.Cyclic

/-- A graph-scheduled candidate in one of the three represented higher-bipyramidal families. -/
inductive HigherBipyramidalSourceCandidate where
  | pentagonal7 (center : Nat)
  | hexagonal8 (center : Nat)
  | heptagonal9 (center : Nat)
  deriving DecidableEq, Repr

namespace HigherBipyramidalSourceCandidate

def center : HigherBipyramidalSourceCandidate → Nat
  | .pentagonal7 center | .hexagonal8 center | .heptagonal9 center => center

end HigherBipyramidalSourceCandidate

/-- All coordinate-derived PBPY-7/HBPY-8/HBPY-9 observations, appended to the caller's existing
observation ledger before the single conflict-aware public analysis. -/
def IndexedCIPGeometryObservations.withSourceHigherBipyramidalSpatialGeometry
    (observations : IndexedCIPGeometryObservations)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) : IndexedCIPGeometryObservations :=
  ((observations.withDerivedPentagonalBipyramid7 certified.result spatial
      certified.pentagonalBipyramid7SourceRecords).withDerivedHexagonalBipyramid8
        certified.result spatial certified.hexagonalBipyramid8SourceRecords).withDerivedHeptagonalBipyramid9
          certified.result spatial certified.heptagonalBipyramid9SourceRecords

/-- Independent source, exact-coordinate, priority, orientation, and derived-record judgment for
one member of the unified candidate type. -/
def HigherBipyramidalDerivedRecordJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (candidate : HigherBipyramidalSourceCandidate)
    (derived : IndexedPolyhedralGeometryObservation) : Prop :=
  match candidate with
  | .pentagonal7 center =>
      SourcePentagonalBipyramid7Center certified center ∧
        PentagonalBipyramid7DerivedRecordJudgment
          (certified.pentagonalBipyramid7SourceRecordAt center)
          certified.result spatial derived
  | .hexagonal8 center =>
      SourceHexagonalBipyramid8Center certified center ∧
        HexagonalBipyramid8DerivedRecordJudgment
          (certified.hexagonalBipyramid8SourceRecordAt center)
          certified.result spatial derived
  | .heptagonal9 center =>
      SourceHeptagonalBipyramid9Center certified center ∧
        HeptagonalBipyramid9DerivedRecordJudgment
          (certified.heptagonalBipyramid9SourceRecordAt center)
          certified.result spatial derived

/-- Every independently derived record is literally in the single combined observation ledger. -/
theorem higherBipyramidalDerivedRecord_mem_combinedObservations
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (candidate : HigherBipyramidalSourceCandidate)
    (derived : IndexedPolyhedralGeometryObservation)
    (judged : HigherBipyramidalDerivedRecordJudgment
      certified spatial candidate derived) :
    derived ∈
      (observations.withSourceHigherBipyramidalSpatialGeometry
        certified spatial).polyhedra := by
  cases candidate with
  | pentagonal7 center =>
      rcases judged with ⟨source, derivedJudged⟩
      have recordPresent : certified.pentagonalBipyramid7SourceRecordAt center ∈
          certified.pentagonalBipyramid7SourceRecords :=
        (certified.pentagonalBipyramid7SourceRecordAt_mem_iff center).mpr source
      have inPentagonal : derived ∈
          certified.result.derivedPentagonalBipyramid7SpatialRecords spatial
            certified.pentagonalBipyramid7SourceRecords :=
        (certified.result.mem_derivedPentagonalBipyramid7SpatialRecords_iff
          spatial certified.pentagonalBipyramid7SourceRecords derived).mpr
            ⟨certified.pentagonalBipyramid7SourceRecordAt center,
              recordPresent, derivedJudged⟩
      exact List.mem_append.mpr (.inl
        (List.mem_append.mpr (.inl
          (List.mem_append.mpr (.inr inPentagonal)))))
  | hexagonal8 center =>
      rcases judged with ⟨source, derivedJudged⟩
      have recordPresent : certified.hexagonalBipyramid8SourceRecordAt center ∈
          certified.hexagonalBipyramid8SourceRecords :=
        (certified.hexagonalBipyramid8SourceRecordAt_mem_iff center).mpr source
      have inHexagonal : derived ∈
          certified.result.derivedHexagonalBipyramid8SpatialRecords spatial
            certified.hexagonalBipyramid8SourceRecords :=
        (certified.result.mem_derivedHexagonalBipyramid8SpatialRecords_iff
          spatial certified.hexagonalBipyramid8SourceRecords derived).mpr
            ⟨certified.hexagonalBipyramid8SourceRecordAt center,
              recordPresent, derivedJudged⟩
      exact List.mem_append.mpr (.inl
        (List.mem_append.mpr (.inr inHexagonal)))
  | heptagonal9 center =>
      rcases judged with ⟨source, derivedJudged⟩
      have recordPresent : certified.heptagonalBipyramid9SourceRecordAt center ∈
          certified.heptagonalBipyramid9SourceRecords :=
        (certified.heptagonalBipyramid9SourceRecordAt_mem_iff center).mpr source
      have inHeptagonal : derived ∈
          certified.result.derivedHeptagonalBipyramid9SpatialRecords spatial
            certified.heptagonalBipyramid9SourceRecords :=
        (certified.result.mem_derivedHeptagonalBipyramid9SpatialRecords_iff
          spatial certified.heptagonalBipyramid9SourceRecords derived).mpr
            ⟨certified.heptagonalBipyramid9SourceRecordAt center,
              recordPresent, derivedJudged⟩
      exact List.mem_append.mpr (.inr inHeptagonal)

/-- Independent final assignment judgment for any unified higher-bipyramidal candidate. -/
def HigherBipyramidalSpatialAssignmentJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment) : Prop :=
  ∃ derived,
    HigherBipyramidalDerivedRecordJudgment certified spatial candidate derived ∧
      PolyhedralObservationAssignmentJudgment certified.result derived assignment

/-- One final public analyzer runs all three graph schedules simultaneously. -/
def analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry certified spatial
    (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
    derivedPlanes derivedHelices

/-- For every independently valid candidate assignment, final membership is exactly agreement
with all valid polyhedral observations in the combined ledger. -/
theorem higherBipyramidalSpatialAssignment_mem_completePipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (judged : HigherBipyramidalSpatialAssignmentJudgment
      certified spatial candidate assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment := by
  rcases judged with ⟨derived, derivedJudged, assignmentJudged⟩
  exact polyhedralObservationAssignment_mem_completePipeline_iff_agreement
    certified spatial
    (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
    derivedPlanes derivedHelices derived assignment
    (higherBipyramidalDerivedRecord_mem_combinedObservations
      certified spatial observations candidate derived derivedJudged)
    assignmentJudged

/-- Final absence is exactly a concrete contradictory same-center IR-9 observation. -/
theorem higherBipyramidalSpatialAssignment_not_mem_completePipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (judged : HigherBipyramidalSpatialAssignmentJudgment
      certified spatial candidate assignment) :
    assignment ∉ analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment := by
  rcases judged with ⟨derived, derivedJudged, assignmentJudged⟩
  exact polyhedralObservationAssignment_not_mem_completePipeline_iff_conflict
    certified spatial
    (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
    derivedPlanes derivedHelices derived assignment
    (higherBipyramidalDerivedRecord_mem_combinedObservations
      certified spatial observations candidate derived derivedJudged)
    assignmentJudged

/-- The simultaneous graph-scheduled public result remains duplicate-free. -/
theorem analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation) :
    (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry certified spatial
      observations derivedPlanes derivedHelices).Nodup := by
  exact analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
    certified spatial
    (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
    derivedPlanes derivedHelices

/-- Literal final count one is exactly same-center observation agreement. -/
theorem higherBipyramidalSpatialAssignment_count_eq_one_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (judged : HigherBipyramidalSpatialAssignmentJudgment
      certified spatial candidate assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 1 ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment := by
  constructor
  · intro countOne
    have present : assignment ∈
        analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry certified spatial
          observations derivedPlanes derivedHelices :=
      List.count_pos_iff.mp (by omega)
    exact
      (higherBipyramidalSpatialAssignment_mem_completePipeline_iff_agreement
        certified spatial observations derivedPlanes derivedHelices candidate assignment
        judged).mp present
  · intro agreement
    have present :=
      (higherBipyramidalSpatialAssignment_mem_completePipeline_iff_agreement
        certified spatial observations derivedPlanes derivedHelices candidate assignment
        judged).mpr agreement
    exact List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry_nodup
        certified spatial observations derivedPlanes derivedHelices) present

/-- Literal final count zero is exactly a concrete contradictory observation. -/
theorem higherBipyramidalSpatialAssignment_count_eq_zero_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (judged : HigherBipyramidalSpatialAssignmentJudgment
      certified spatial candidate assignment) :
    List.count assignment
        (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry
          certified spatial observations derivedPlanes derivedHelices) = 0 ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment := by
  rw [List.count_eq_zero]
  exact higherBipyramidalSpatialAssignment_not_mem_completePipeline_iff_conflict
    certified spatial observations derivedPlanes derivedHelices candidate assignment judged

/-- Complete positive condition for one unified source candidate. -/
def HigherBipyramidalSpatialReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (candidate : HigherBipyramidalSourceCandidate) : Prop :=
  ∃ assignment,
    HigherBipyramidalSpatialAssignmentJudgment certified spatial candidate assignment ∧
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment

/-- Exhaustive negative condition: every independently valid local assignment has a concrete
same-center conflict; when physical perception fails, this statement holds vacuously. -/
def HigherBipyramidalSpatialRefusal
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (candidate : HigherBipyramidalSourceCandidate) : Prop :=
  ∀ assignment,
    HigherBipyramidalSpatialAssignmentJudgment certified spatial candidate assignment →
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment

/-- Candidate readiness is exactly existence of an independently judged final result with literal
count one. -/
theorem higherBipyramidalSpatialReady_iff_exists_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (candidate : HigherBipyramidalSourceCandidate) :
    HigherBipyramidalSpatialReady certified spatial observations candidate ↔
      ∃ assignment,
        HigherBipyramidalSpatialAssignmentJudgment certified spatial candidate assignment ∧
          List.count assignment
            (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry
              certified spatial observations derivedPlanes derivedHelices) = 1 := by
  constructor
  · rintro ⟨assignment, judged, agreement⟩
    exact ⟨assignment, judged,
      (higherBipyramidalSpatialAssignment_count_eq_one_iff_agreement
        certified spatial observations derivedPlanes derivedHelices candidate assignment
        judged).mpr agreement⟩
  · rintro ⟨assignment, judged, countOne⟩
    exact ⟨assignment, judged,
      (higherBipyramidalSpatialAssignment_count_eq_one_iff_agreement
        certified spatial observations derivedPlanes derivedHelices candidate assignment
        judged).mp countOne⟩

/-- Readiness failure is exactly the semantic refusal relation. -/
theorem not_higherBipyramidalSpatialReady_iff_refusal
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (candidate : HigherBipyramidalSourceCandidate) :
    ¬HigherBipyramidalSpatialReady certified spatial observations candidate ↔
      HigherBipyramidalSpatialRefusal certified spatial observations candidate := by
  classical
  constructor
  · intro notReady assignment judged
    apply
      (not_polyhedralObservationAssignmentAgreement_iff_conflict certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment).mp
    intro agreement
    exact notReady ⟨assignment, judged, agreement⟩
  · intro refusal ready
    rcases ready with ⟨assignment, judged, agreement⟩
    have conflict := refusal assignment judged
    exact
      ((not_polyhedralObservationAssignmentAgreement_iff_conflict certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment).mpr conflict) agreement

/-- Every unified candidate has an exact readiness/refusal classification. -/
theorem higherBipyramidalSpatial_ready_or_refusal
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (candidate : HigherBipyramidalSourceCandidate) :
    HigherBipyramidalSpatialReady certified spatial observations candidate ∨
      HigherBipyramidalSpatialRefusal certified spatial observations candidate := by
  classical
  by_cases ready : HigherBipyramidalSpatialReady certified spatial observations candidate
  · exact .inl ready
  · exact .inr
      ((not_higherBipyramidalSpatialReady_iff_refusal
        certified spatial observations candidate).mp ready)

/-! ## Unified downstream configuration-family endpoint -/

/-- One public result runs graph-scheduled PBPY-7/HBPY-8/HBPY-9 observations through the same
derived-spatial pipeline as fullerene, RCT-pair, and spiro configuration families. -/
def analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    List CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment :=
  analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
    (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
    derivedPlanes derivedHelices fullerenes rctPairs spiros

/-- Every member of the combined endpoint satisfies the established independent judgment for its
exact nested constructor and the higher-bipyramidal-augmented observation ledger. -/
theorem analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_member_judged
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
      analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros) :
    IndependentlyJudgedCertifiedDerivedSpatialFullereneRCTAndSpiroAssignment certified spatial
      (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
      derivedPlanes derivedHelices fullerenes rctPairs spiros output := by
  exact analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_member_judged certified
    spatial (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
    derivedPlanes derivedHelices fullerenes rctPairs spiros output present

/-- Constructor disjointness and the single conflict-aware spatial analysis keep the entire
combined endpoint duplicate-free. -/
theorem analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro certified
      spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros).Nodup := by
  exact analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_nodup certified spatial
    (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
    derivedPlanes derivedHelices fullerenes rctPairs spiros

/-- The three nested extension constructors preserve a represented spatial assignment exactly;
no fullerene, RCT, or spiro wrapper can erase or manufacture it. -/
theorem representedHigherBipyramidal_mem_analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_iff
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
        analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros ↔
      assignment ∈ analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry certified
        spatial observations derivedPlanes derivedHelices := by
  change
    (.prior (.prior (.represented assignment)) :
        CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) ∈
        analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
          (observations.withSourceHigherBipyramidalSpatialGeometry certified spatial)
          derivedPlanes derivedHelices fullerenes rctPairs spiros ↔ _
  rw [prior_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_iff,
    prior_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_iff,
    represented_mem_analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_iff]
  rfl

/-- A valid higher-bipyramidal assignment occurs literally once in the full combined endpoint
exactly when every same-center observation agrees. -/
theorem higherBipyramidalSpatialAssignment_count_eq_one_in_combinedPipeline_iff_agreement
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (judged : HigherBipyramidalSpatialAssignmentJudgment
      certified spatial candidate assignment) :
    List.count
        (.prior (.prior (.represented assignment)) :
          CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment)
        (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros) = 1 ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment := by
  constructor
  · intro countOne
    have embeddedPresent :
        (.prior (.prior (.represented assignment)) :
          CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) ∈
          analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro
            certified spatial observations derivedPlanes derivedHelices fullerenes rctPairs
              spiros :=
      List.count_pos_iff.mp (by omega)
    have priorPresent :=
      (representedHigherBipyramidal_mem_analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_iff
        certified spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros
          assignment).mp embeddedPresent
    exact
      (higherBipyramidalSpatialAssignment_mem_completePipeline_iff_agreement certified spatial
        observations derivedPlanes derivedHelices candidate assignment judged).mp priorPresent
  · intro agreement
    have priorPresent :=
      (higherBipyramidalSpatialAssignment_mem_completePipeline_iff_agreement certified spatial
        observations derivedPlanes derivedHelices candidate assignment judged).mpr agreement
    have embeddedPresent :=
      (representedHigherBipyramidal_mem_analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_iff
        certified spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros
          assignment).mpr priorPresent
    exact List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_nodup
        certified spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros)
      embeddedPresent

/-- Explicit same-center conflict is exactly count zero for the nested higher-bipyramidal result
in the full combined endpoint. -/
theorem higherBipyramidalSpatialAssignment_count_eq_zero_in_combinedPipeline_iff_conflict
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (judged : HigherBipyramidalSpatialAssignmentJudgment
      certified spatial candidate assignment) :
    List.count
        (.prior (.prior (.represented assignment)) :
          CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment)
        (analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros) = 0 ↔
      PolyhedralObservationAssignmentConflict certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment := by
  rw [List.count_eq_zero,
    representedHigherBipyramidal_mem_analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialFullereneRCTAndSpiro_iff]
  exact higherBipyramidalSpatialAssignment_not_mem_completePipeline_iff_conflict certified spatial
    observations derivedPlanes derivedHelices candidate assignment judged

end TetraStereo.OneCenter
