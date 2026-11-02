import TetraStereo.OneCenter.CIPObservedRCTPairConfigurationPipeline
import TetraStereo.OneCenter.P93SpiroConfigurationCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# Conflict-free P-93.5.3 spiro family and represented-pipeline attachment

The local spiro materializer is exact for supplied pattern, occurrence, CIP-token, and polyhedral
evidence.  This module lifts it to a finite observation family.  Contradictory successful records
for the same physical spiro unit are excluded symmetrically; every retained unit is unique and has
literal list count one.
-/

def candidateSpiroConfigurationAssignments
    (inputs : List SpiroConfigurationInput) :
    List SpiroConfigurationAssignment :=
  inputs.filterMap spiroConfigurationAssignment?

def SpiroConfigurationCandidateJudgment
    (inputs : List SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs, SpiroConfigurationAssignmentJudgment input assignment

theorem mem_candidateSpiroConfigurationAssignments_iff
    (inputs : List SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) :
    assignment ∈ candidateSpiroConfigurationAssignments inputs ↔
      SpiroConfigurationCandidateJudgment inputs assignment := by
  simp [candidateSpiroConfigurationAssignments,
    SpiroConfigurationCandidateJudgment,
    spiroConfigurationAssignment?_eq_some_iff]

def SpiroConfigurationAssignmentAgreement
    (inputs : List SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) : Prop :=
  ∀ other,
    SpiroConfigurationCandidateJudgment inputs other →
    other.unit = assignment.unit →
    other = assignment

def SpiroConfigurationAssignmentConflict
    (inputs : List SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) : Prop :=
  ∃ other,
    SpiroConfigurationCandidateJudgment inputs other ∧
    other.unit = assignment.unit ∧
    other ≠ assignment

def spiroConfigurationAssignmentAccepted
    (candidates : List SpiroConfigurationAssignment)
    (assignment : SpiroConfigurationAssignment) : Bool :=
  candidates.all fun other =>
    decide (other.unit = assignment.unit → other = assignment)

theorem spiroConfigurationAssignmentAccepted_eq_true_iff
    (candidates : List SpiroConfigurationAssignment)
    (assignment : SpiroConfigurationAssignment) :
    spiroConfigurationAssignmentAccepted candidates assignment = true ↔
      ∀ other ∈ candidates,
        other.unit = assignment.unit → other = assignment := by
  rw [spiroConfigurationAssignmentAccepted, List.all_eq_true]
  constructor
  · intro accepted other present sameUnit
    exact (of_decide_eq_true (accepted other present)) sameUnit
  · intro agreement other present
    exact decide_eq_true (agreement other present)

def analyzeSpiroConfigurations
    (inputs : List SpiroConfigurationInput) :
    List SpiroConfigurationAssignment :=
  let candidates := candidateSpiroConfigurationAssignments inputs
  (candidates.filter fun assignment =>
    spiroConfigurationAssignmentAccepted candidates assignment).eraseDups

def ConflictFreeSpiroConfigurationAssignmentJudgment
    (inputs : List SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) : Prop :=
  SpiroConfigurationCandidateJudgment inputs assignment ∧
    SpiroConfigurationAssignmentAgreement inputs assignment

theorem mem_analyzeSpiroConfigurations_iff
    (inputs : List SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) :
    assignment ∈ analyzeSpiroConfigurations inputs ↔
      ConflictFreeSpiroConfigurationAssignmentJudgment inputs assignment := by
  rw [analyzeSpiroConfigurations, mem_eraseDups_iff_mem_lawful]
  rw [List.mem_filter]
  rw [spiroConfigurationAssignmentAccepted_eq_true_iff]
  rw [mem_candidateSpiroConfigurationAssignments_iff]
  unfold ConflictFreeSpiroConfigurationAssignmentJudgment
  unfold SpiroConfigurationAssignmentAgreement
  constructor
  · rintro ⟨candidate, agreement⟩
    exact ⟨candidate, fun other otherJudged sameUnit =>
      agreement other
        ((mem_candidateSpiroConfigurationAssignments_iff inputs other).mpr otherJudged)
        sameUnit⟩
  · rintro ⟨candidate, agreement⟩
    exact ⟨candidate, fun other otherPresent sameUnit =>
      agreement other
        ((mem_candidateSpiroConfigurationAssignments_iff inputs other).mp otherPresent)
        sameUnit⟩

theorem analyzeSpiroConfigurations_nodup
    (inputs : List SpiroConfigurationInput) :
    (analyzeSpiroConfigurations inputs).Nodup := by
  unfold analyzeSpiroConfigurations
  exact eraseDups_nodup_lawful _

theorem not_spiroConfigurationAssignmentAgreement_iff_conflict
    (inputs : List SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) :
    ¬SpiroConfigurationAssignmentAgreement inputs assignment ↔
      SpiroConfigurationAssignmentConflict inputs assignment := by
  classical
  constructor
  · intro notAgreement
    by_contra noConflict
    apply notAgreement
    intro other otherJudged sameUnit
    by_contra different
    exact noConflict ⟨other, otherJudged, sameUnit, different⟩
  · rintro ⟨other, otherJudged, sameUnit, different⟩ agreement
    exact different (agreement other otherJudged sameUnit)

theorem spiroConfigurationAssignment_mem_iff_agreement
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : SpiroConfigurationAssignmentJudgment input assignment) :
    assignment ∈ analyzeSpiroConfigurations inputs ↔
      SpiroConfigurationAssignmentAgreement inputs assignment := by
  rw [mem_analyzeSpiroConfigurations_iff]
  unfold ConflictFreeSpiroConfigurationAssignmentJudgment
  simp only [and_iff_right_iff_imp]
  intro _agreement
  exact ⟨input, inputPresent, judged⟩

theorem spiroConfigurationAssignment_not_mem_iff_conflict
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : SpiroConfigurationAssignmentJudgment input assignment) :
    assignment ∉ analyzeSpiroConfigurations inputs ↔
      SpiroConfigurationAssignmentConflict inputs assignment := by
  rw [← not_spiroConfigurationAssignmentAgreement_iff_conflict]
  exact not_congr (spiroConfigurationAssignment_mem_iff_agreement
    inputs input assignment inputPresent judged)

theorem analyzeSpiroConfigurations_sameUnit_eq
    (inputs : List SpiroConfigurationInput)
    {left right : SpiroConfigurationAssignment}
    (leftPresent : left ∈ analyzeSpiroConfigurations inputs)
    (rightPresent : right ∈ analyzeSpiroConfigurations inputs)
    (sameUnit : right.unit = left.unit) :
    right = left := by
  have leftJudged :=
    (mem_analyzeSpiroConfigurations_iff inputs left).mp leftPresent
  have rightJudged :=
    (mem_analyzeSpiroConfigurations_iff inputs right).mp rightPresent
  exact leftJudged.2 right rightJudged.1 sameUnit

def SpiroConfigurationInputPublicReady
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput) : Prop :=
  input ∈ inputs ∧
    ∃ assignment,
      SpiroConfigurationAssignmentJudgment input assignment ∧
      ConflictFreeSpiroConfigurationAssignmentJudgment inputs assignment

def SpiroConfigurationInputPublicRefusal
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput) : Prop :=
  input ∉ inputs ∨
    SpiroConfigurationRefusal input ∨
    ∃ assignment,
      SpiroConfigurationAssignmentJudgment input assignment ∧
      SpiroConfigurationAssignmentConflict inputs assignment

theorem spiroConfigurationInputPublicReady_iff_not_refusal
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput) :
    SpiroConfigurationInputPublicReady inputs input ↔
      ¬SpiroConfigurationInputPublicRefusal inputs input := by
  classical
  constructor
  · rintro ⟨inputPresent, assignment, localJudged, familyJudged⟩ refusal
    rcases refusal with absent | localRefusal | ⟨other, otherJudged, conflict⟩
    · exact absent inputPresent
    · have localReady : SpiroConfigurationReady input := ⟨assignment, localJudged⟩
      exact ((spiroConfigurationReady_iff_not_refusal input).mp localReady) localRefusal
    · have sameAssignment := spiroConfigurationAssignmentJudgment_subsingleton
        input otherJudged localJudged
      subst other
      exact ((not_spiroConfigurationAssignmentAgreement_iff_conflict
        inputs assignment).mpr conflict) familyJudged.2
  · intro noRefusal
    have inputPresent : input ∈ inputs := by
      by_contra absent
      exact noRefusal (.inl absent)
    have noLocalRefusal : ¬SpiroConfigurationRefusal input := by
      intro refusal
      exact noRefusal (.inr (.inl refusal))
    obtain ⟨assignment, localJudged⟩ :=
      (spiroConfigurationReady_iff_not_refusal input).mpr noLocalRefusal
    have noConflict :
        ¬SpiroConfigurationAssignmentConflict inputs assignment := by
      intro conflict
      exact noRefusal (.inr (.inr ⟨assignment, localJudged, conflict⟩))
    have agreement :
        SpiroConfigurationAssignmentAgreement inputs assignment := by
      by_contra notAgreement
      exact noConflict
        ((not_spiroConfigurationAssignmentAgreement_iff_conflict
          inputs assignment).mp notAgreement)
    exact ⟨inputPresent, assignment, localJudged,
      ⟨⟨input, inputPresent, localJudged⟩, agreement⟩⟩

theorem not_spiroConfigurationInputPublicReady_iff_refusal
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput) :
    ¬SpiroConfigurationInputPublicReady inputs input ↔
      SpiroConfigurationInputPublicRefusal inputs input := by
  rw [spiroConfigurationInputPublicReady_iff_not_refusal]
  simp

theorem every_publicReady_spiroConfigurationInput_occurs_exactly_once
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput)
    (ready : SpiroConfigurationInputPublicReady inputs input) :
    ∃! assignment,
      assignment ∈ analyzeSpiroConfigurations inputs ∧
      SpiroConfigurationAssignmentJudgment input assignment := by
  rcases ready with ⟨_inputPresent, assignment, localJudged, familyJudged⟩
  have assignmentPresent :=
    (mem_analyzeSpiroConfigurations_iff inputs assignment).mpr familyJudged
  refine ⟨assignment, ⟨assignmentPresent, localJudged⟩, ?_⟩
  intro other ⟨_otherPresent, otherJudged⟩
  exact spiroConfigurationAssignmentJudgment_subsingleton
    input otherJudged localJudged

theorem every_publicReady_spiroConfigurationInput_count_eq_one
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput)
    (ready : SpiroConfigurationInputPublicReady inputs input) :
    ∃ assignment,
      SpiroConfigurationAssignmentJudgment input assignment ∧
      List.count assignment (analyzeSpiroConfigurations inputs) = 1 := by
  rcases every_publicReady_spiroConfigurationInput_occurs_exactly_once
      inputs input ready with
    ⟨assignment, ⟨present, judged⟩, _unique⟩
  exact ⟨assignment, judged,
    List.count_eq_one_of_mem (analyzeSpiroConfigurations_nodup inputs) present⟩

theorem spiroConfigurationAssignment_count_eq_zero_of_conflict
    (inputs : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : SpiroConfigurationAssignmentJudgment input assignment)
    (conflict : SpiroConfigurationAssignmentConflict inputs assignment) :
    List.count assignment (analyzeSpiroConfigurations inputs) = 0 := by
  rw [List.count_eq_zero]
  exact (spiroConfigurationAssignment_not_mem_iff_conflict
    inputs input assignment inputPresent judged).mpr conflict

end BlueBookP93.Cyclic

open BlueBookP93.Cyclic

/-! ## Attachment after the represented, fullerene, and RCT families -/

inductive CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment where
  | prior (assignment : CertifiedDerivedSpatialFullereneAndRCTAssignment)
  | spiro (assignment : SpiroConfigurationAssignment)
  deriving DecidableEq, Repr

def analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    List CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment :=
  (analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT certified spatial observations
      derivedPlanes derivedHelices fullerenes rctPairs).map .prior ++
    (analyzeSpiroConfigurations spiros).map .spiro

theorem prior_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (assignment : CertifiedDerivedSpatialFullereneAndRCTAssignment) :
    .prior assignment ∈
        analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros ↔
      assignment ∈ analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs := by
  simp [analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro]

theorem spiro_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) :
    .spiro assignment ∈
        analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros ↔
      assignment ∈ analyzeSpiroConfigurations spiros := by
  simp [analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro]

theorem analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    (analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs spiros).Nodup := by
  rw [analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro]
  apply List.Nodup.append
  · exact (analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_nodup certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs).map (by
        intro left right equal
        cases equal
        rfl)
  · exact (analyzeSpiroConfigurations_nodup spiros).map (by
        intro left right equal
        cases equal
        rfl)
  · rw [List.disjoint_left]
    intro output priorPresent spiroPresent
    obtain ⟨assignment, _present, rfl⟩ := List.mem_map.mp priorPresent
    simp at spiroPresent

def IndependentlyJudgedCertifiedDerivedSpatialFullereneRCTAndSpiroAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput) :
    CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment → Prop
  | .prior assignment =>
      IndependentlyJudgedCertifiedDerivedSpatialFullereneAndRCTAssignment certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs assignment
  | .spiro assignment =>
      ConflictFreeSpiroConfigurationAssignmentJudgment spiros assignment

theorem analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_member_judged
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
      analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros) :
    IndependentlyJudgedCertifiedDerivedSpatialFullereneRCTAndSpiroAssignment certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs spiros output := by
  cases output with
  | prior assignment =>
      exact analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_member_judged certified
        spatial observations derivedPlanes derivedHelices fullerenes rctPairs assignment
        ((prior_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_iff certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros
          assignment).mp present)
  | spiro assignment =>
      exact (mem_analyzeSpiroConfigurations_iff spiros assignment).mp
        ((spiro_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_iff certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros
          assignment).mp present)

theorem every_publicReady_spiroConfigurationInput_count_eq_one_in_extended_pipeline
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (input : SpiroConfigurationInput)
    (ready : SpiroConfigurationInputPublicReady spiros input) :
    ∃ assignment,
      SpiroConfigurationAssignmentJudgment input assignment ∧
      List.count (.spiro assignment)
        (analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros) = 1 := by
  rcases every_publicReady_spiroConfigurationInput_count_eq_one
      spiros input ready with ⟨assignment, judged, familyCount⟩
  refine ⟨assignment, judged, ?_⟩
  have familyPresent : assignment ∈ analyzeSpiroConfigurations spiros := by
    by_contra absent
    have familyCountZero : List.count assignment (analyzeSpiroConfigurations spiros) = 0 :=
      List.count_eq_zero.mpr absent
    omega
  have publicPresent :
      CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment.spiro assignment ∈
        analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro certified spatial
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros :=
    (spiro_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_iff certified
      spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros
      assignment).mpr familyPresent
  exact List.count_eq_one_of_mem
    (analyzeCertifiedNormalizedWithDerivedSpatialFullereneRCTAndSpiro_nodup certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs spiros) publicPresent

end TetraStereo.OneCenter
