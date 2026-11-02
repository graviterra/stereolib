import TetraStereo.OneCenter.CIPObservedFullereneConfigurationPipeline
import TetraStereo.OneCenter.P93RCTPairConfigurationCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# Conflict-free P-93.5.1.3 RCT family and represented-pipeline attachment

The local RCT pair analyzer is exact for supplied ring-side evidence.  Here it is lifted to an
arbitrary finite observation family.  A physical unit is the ring key together with the ligand
locant.  Same-unit contradictions are removed symmetrically, and every exclusion, uniqueness, and
multiplicity claim is stated against independent local judgments.
-/

def RCTPairConfigurationAssignment.physicalUnit
    (assignment : RCTPairConfigurationAssignment) : List Nat × Nat :=
  (assignment.unit, assignment.ligand.locant)

def candidateRCTPairConfigurationAssignments
    (inputs : List RCTPairConfigurationInput) :
    List RCTPairConfigurationAssignment :=
  inputs.filterMap rctPairConfigurationAssignment?

def RCTPairConfigurationCandidateJudgment
    (inputs : List RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs,
    RCTPairConfigurationAssignmentJudgment input assignment

theorem mem_candidateRCTPairConfigurationAssignments_iff
    (inputs : List RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) :
    assignment ∈ candidateRCTPairConfigurationAssignments inputs ↔
      RCTPairConfigurationCandidateJudgment inputs assignment := by
  simp [candidateRCTPairConfigurationAssignments,
    RCTPairConfigurationCandidateJudgment,
    rctPairConfigurationAssignment?_eq_some_iff]

def RCTPairConfigurationAssignmentAgreement
    (inputs : List RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) : Prop :=
  ∀ other,
    RCTPairConfigurationCandidateJudgment inputs other →
    other.physicalUnit = assignment.physicalUnit →
    other = assignment

def RCTPairConfigurationAssignmentConflict
    (inputs : List RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) : Prop :=
  ∃ other,
    RCTPairConfigurationCandidateJudgment inputs other ∧
    other.physicalUnit = assignment.physicalUnit ∧
    other ≠ assignment

def rctPairConfigurationAssignmentAccepted
    (candidates : List RCTPairConfigurationAssignment)
    (assignment : RCTPairConfigurationAssignment) : Bool :=
  candidates.all fun other =>
    decide (other.physicalUnit = assignment.physicalUnit → other = assignment)

theorem rctPairConfigurationAssignmentAccepted_eq_true_iff
    (candidates : List RCTPairConfigurationAssignment)
    (assignment : RCTPairConfigurationAssignment) :
    rctPairConfigurationAssignmentAccepted candidates assignment = true ↔
      ∀ other ∈ candidates,
        other.physicalUnit = assignment.physicalUnit → other = assignment := by
  rw [rctPairConfigurationAssignmentAccepted, List.all_eq_true]
  constructor
  · intro accepted other present sameUnit
    exact (of_decide_eq_true (accepted other present)) sameUnit
  · intro agreement other present
    exact decide_eq_true (agreement other present)

def analyzeRCTPairConfigurations
    (inputs : List RCTPairConfigurationInput) :
    List RCTPairConfigurationAssignment :=
  let candidates := candidateRCTPairConfigurationAssignments inputs
  (candidates.filter fun assignment =>
    rctPairConfigurationAssignmentAccepted candidates assignment).eraseDups

def ConflictFreeRCTPairConfigurationAssignmentJudgment
    (inputs : List RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) : Prop :=
  RCTPairConfigurationCandidateJudgment inputs assignment ∧
    RCTPairConfigurationAssignmentAgreement inputs assignment

theorem mem_analyzeRCTPairConfigurations_iff
    (inputs : List RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) :
    assignment ∈ analyzeRCTPairConfigurations inputs ↔
      ConflictFreeRCTPairConfigurationAssignmentJudgment inputs assignment := by
  rw [analyzeRCTPairConfigurations, mem_eraseDups_iff_mem_lawful]
  rw [List.mem_filter]
  rw [rctPairConfigurationAssignmentAccepted_eq_true_iff]
  rw [mem_candidateRCTPairConfigurationAssignments_iff]
  unfold ConflictFreeRCTPairConfigurationAssignmentJudgment
  unfold RCTPairConfigurationAssignmentAgreement
  constructor
  · rintro ⟨candidate, agreement⟩
    exact ⟨candidate, fun other otherJudged sameUnit =>
      agreement other
        ((mem_candidateRCTPairConfigurationAssignments_iff inputs other).mpr otherJudged)
        sameUnit⟩
  · rintro ⟨candidate, agreement⟩
    exact ⟨candidate, fun other otherPresent sameUnit =>
      agreement other
        ((mem_candidateRCTPairConfigurationAssignments_iff inputs other).mp otherPresent)
        sameUnit⟩

theorem analyzeRCTPairConfigurations_nodup
    (inputs : List RCTPairConfigurationInput) :
    (analyzeRCTPairConfigurations inputs).Nodup := by
  unfold analyzeRCTPairConfigurations
  exact eraseDups_nodup_lawful _

theorem not_rctPairConfigurationAssignmentAgreement_iff_conflict
    (inputs : List RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) :
    ¬ RCTPairConfigurationAssignmentAgreement inputs assignment ↔
      RCTPairConfigurationAssignmentConflict inputs assignment := by
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

theorem rctPairConfigurationAssignment_mem_iff_agreement
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : RCTPairConfigurationAssignmentJudgment input assignment) :
    assignment ∈ analyzeRCTPairConfigurations inputs ↔
      RCTPairConfigurationAssignmentAgreement inputs assignment := by
  rw [mem_analyzeRCTPairConfigurations_iff]
  unfold ConflictFreeRCTPairConfigurationAssignmentJudgment
  simp only [and_iff_right_iff_imp]
  intro _agreement
  exact ⟨input, inputPresent, judged⟩

theorem rctPairConfigurationAssignment_not_mem_iff_conflict
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : RCTPairConfigurationAssignmentJudgment input assignment) :
    assignment ∉ analyzeRCTPairConfigurations inputs ↔
      RCTPairConfigurationAssignmentConflict inputs assignment := by
  rw [← not_rctPairConfigurationAssignmentAgreement_iff_conflict]
  exact not_congr (rctPairConfigurationAssignment_mem_iff_agreement
    inputs input assignment inputPresent judged)

theorem analyzeRCTPairConfigurations_samePhysicalUnit_eq
    (inputs : List RCTPairConfigurationInput)
    {left right : RCTPairConfigurationAssignment}
    (leftPresent : left ∈ analyzeRCTPairConfigurations inputs)
    (rightPresent : right ∈ analyzeRCTPairConfigurations inputs)
    (sameUnit : right.physicalUnit = left.physicalUnit) :
    right = left := by
  have leftJudged := (mem_analyzeRCTPairConfigurations_iff inputs left).mp leftPresent
  have rightJudged := (mem_analyzeRCTPairConfigurations_iff inputs right).mp rightPresent
  exact leftJudged.2 right rightJudged.1 sameUnit

def RCTPairConfigurationInputPublicReady
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput) : Prop :=
  input ∈ inputs ∧
    ∃ assignment,
      RCTPairConfigurationAssignmentJudgment input assignment ∧
      ConflictFreeRCTPairConfigurationAssignmentJudgment inputs assignment

def RCTPairConfigurationInputPublicRefusal
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput) : Prop :=
  input ∉ inputs ∨
    RCTPairConfigurationRefusal input ∨
    ∃ assignment,
      RCTPairConfigurationAssignmentJudgment input assignment ∧
      RCTPairConfigurationAssignmentConflict inputs assignment

theorem rctPairConfigurationInputPublicReady_iff_not_refusal
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput) :
    RCTPairConfigurationInputPublicReady inputs input ↔
      ¬ RCTPairConfigurationInputPublicRefusal inputs input := by
  classical
  constructor
  · rintro ⟨inputPresent, assignment, localJudged, familyJudged⟩ refusal
    rcases refusal with absent | localRefusal | ⟨other, otherJudged, conflict⟩
    · exact absent inputPresent
    · have localReady : RCTPairConfigurationReady input := ⟨assignment, localJudged⟩
      exact ((rctPairConfigurationReady_iff_not_refusal input).mp localReady) localRefusal
    · have sameAssignment := rctPairConfigurationAssignmentJudgment_subsingleton
        input otherJudged localJudged
      subst other
      exact ((not_rctPairConfigurationAssignmentAgreement_iff_conflict
        inputs assignment).mpr conflict) familyJudged.2
  · intro noRefusal
    have inputPresent : input ∈ inputs := by
      by_contra absent
      exact noRefusal (.inl absent)
    have noLocalRefusal : ¬ RCTPairConfigurationRefusal input := by
      intro refusal
      exact noRefusal (.inr (.inl refusal))
    obtain ⟨assignment, localJudged⟩ :=
      (rctPairConfigurationReady_iff_not_refusal input).mpr noLocalRefusal
    have noConflict : ¬ RCTPairConfigurationAssignmentConflict inputs assignment := by
      intro conflict
      exact noRefusal (.inr (.inr ⟨assignment, localJudged, conflict⟩))
    have agreement : RCTPairConfigurationAssignmentAgreement inputs assignment := by
      by_contra notAgreement
      exact noConflict
        ((not_rctPairConfigurationAssignmentAgreement_iff_conflict
          inputs assignment).mp notAgreement)
    exact ⟨inputPresent, assignment, localJudged,
      ⟨⟨input, inputPresent, localJudged⟩, agreement⟩⟩

theorem not_rctPairConfigurationInputPublicReady_iff_refusal
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput) :
    ¬ RCTPairConfigurationInputPublicReady inputs input ↔
      RCTPairConfigurationInputPublicRefusal inputs input := by
  rw [rctPairConfigurationInputPublicReady_iff_not_refusal]
  simp

theorem every_publicReady_rctPairConfigurationInput_occurs_exactly_once
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput)
    (ready : RCTPairConfigurationInputPublicReady inputs input) :
    ∃! assignment,
      assignment ∈ analyzeRCTPairConfigurations inputs ∧
      RCTPairConfigurationAssignmentJudgment input assignment := by
  rcases ready with ⟨_inputPresent, assignment, localJudged, familyJudged⟩
  have assignmentPresent :=
    (mem_analyzeRCTPairConfigurations_iff inputs assignment).mpr familyJudged
  refine ⟨assignment, ⟨assignmentPresent, localJudged⟩, ?_⟩
  intro other ⟨_otherPresent, otherJudged⟩
  exact rctPairConfigurationAssignmentJudgment_subsingleton
    input otherJudged localJudged

theorem every_publicReady_rctPairConfigurationInput_count_eq_one
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput)
    (ready : RCTPairConfigurationInputPublicReady inputs input) :
    ∃ assignment,
      RCTPairConfigurationAssignmentJudgment input assignment ∧
      List.count assignment (analyzeRCTPairConfigurations inputs) = 1 := by
  rcases every_publicReady_rctPairConfigurationInput_occurs_exactly_once
      inputs input ready with ⟨assignment, ⟨present, judged⟩, _unique⟩
  exact ⟨assignment, judged,
    List.count_eq_one_of_mem (analyzeRCTPairConfigurations_nodup inputs) present⟩

theorem rctPairConfigurationAssignment_count_eq_zero_of_conflict
    (inputs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : RCTPairConfigurationAssignmentJudgment input assignment)
    (conflict : RCTPairConfigurationAssignmentConflict inputs assignment) :
    List.count assignment (analyzeRCTPairConfigurations inputs) = 0 := by
  rw [List.count_eq_zero]
  exact (rctPairConfigurationAssignment_not_mem_iff_conflict
    inputs input assignment inputPresent judged).mpr conflict

end BlueBookP93.Cyclic

open BlueBookP93.Cyclic

/-! ## Attachment after the derived-spatial and fullerene families -/

inductive CertifiedDerivedSpatialFullereneAndRCTAssignment where
  | prior (assignment : CertifiedDerivedSpatialAndFullereneAssignment)
  | rct (assignment : RCTPairConfigurationAssignment)
  deriving DecidableEq, Repr

def analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput) :
    List CertifiedDerivedSpatialFullereneAndRCTAssignment :=
  (analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene certified spatial observations
      derivedPlanes derivedHelices fullerenes).map .prior ++
    (analyzeRCTPairConfigurations rctPairs).map .rct

theorem prior_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (assignment : CertifiedDerivedSpatialAndFullereneAssignment) :
    .prior assignment ∈
        analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT certified spatial observations
          derivedPlanes derivedHelices fullerenes rctPairs ↔
      assignment ∈ analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene certified spatial
        observations derivedPlanes derivedHelices fullerenes := by
  simp [analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT]

theorem rct_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) :
    .rct assignment ∈
        analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT certified spatial observations
          derivedPlanes derivedHelices fullerenes rctPairs ↔
      assignment ∈ analyzeRCTPairConfigurations rctPairs := by
  simp [analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT]

theorem analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput) :
    (analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT certified spatial observations
      derivedPlanes derivedHelices fullerenes rctPairs).Nodup := by
  rw [analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT]
  apply List.Nodup.append
  · exact (analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_nodup certified spatial
      observations derivedPlanes derivedHelices fullerenes).map (by
        intro left right equal
        cases equal
        rfl)
  · exact (analyzeRCTPairConfigurations_nodup rctPairs).map (by
        intro left right equal
        cases equal
        rfl)
  · rw [List.disjoint_left]
    intro output priorPresent rctPresent
    obtain ⟨assignment, _present, rfl⟩ := List.mem_map.mp priorPresent
    simp at rctPresent

def IndependentlyJudgedCertifiedDerivedSpatialFullereneAndRCTAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput) :
    CertifiedDerivedSpatialFullereneAndRCTAssignment → Prop
  | .prior assignment =>
      IndependentlyJudgedCertifiedDerivedSpatialAndFullereneAssignment certified spatial
        observations derivedPlanes derivedHelices fullerenes assignment
  | .rct assignment =>
      ConflictFreeRCTPairConfigurationAssignmentJudgment rctPairs assignment

theorem analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (output : CertifiedDerivedSpatialFullereneAndRCTAssignment)
    (present : output ∈
      analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT certified spatial observations
        derivedPlanes derivedHelices fullerenes rctPairs) :
    IndependentlyJudgedCertifiedDerivedSpatialFullereneAndRCTAssignment certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs output := by
  cases output with
  | prior assignment =>
      exact analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_member_judged certified
        spatial observations derivedPlanes derivedHelices fullerenes assignment
        ((prior_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_iff certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs assignment).mp
          present)
  | rct assignment =>
      exact (mem_analyzeRCTPairConfigurations_iff rctPairs assignment).mp
        ((rct_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_iff certified
          spatial observations derivedPlanes derivedHelices fullerenes rctPairs assignment).mp
          present)

theorem every_publicReady_rctPairConfigurationInput_count_eq_one_in_extended_pipeline
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (input : RCTPairConfigurationInput)
    (ready : RCTPairConfigurationInputPublicReady rctPairs input) :
    ∃ assignment,
      RCTPairConfigurationAssignmentJudgment input assignment ∧
      List.count (.rct assignment)
        (analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT certified spatial observations
          derivedPlanes derivedHelices fullerenes rctPairs) = 1 := by
  rcases every_publicReady_rctPairConfigurationInput_count_eq_one
      rctPairs input ready with ⟨assignment, judged, familyCount⟩
  refine ⟨assignment, judged, ?_⟩
  have familyPresent : assignment ∈ analyzeRCTPairConfigurations rctPairs := by
    by_contra absent
    have familyCountZero : List.count assignment (analyzeRCTPairConfigurations rctPairs) = 0 :=
      List.count_eq_zero.mpr absent
    omega
  have publicPresent : CertifiedDerivedSpatialFullereneAndRCTAssignment.rct assignment ∈
      analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT certified spatial observations
        derivedPlanes derivedHelices fullerenes rctPairs :=
    (rct_mem_analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_iff certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs assignment).mpr familyPresent
  exact List.count_eq_one_of_mem
    (analyzeCertifiedNormalizedWithDerivedSpatialFullereneAndRCT_nodup certified spatial
      observations derivedPlanes derivedHelices fullerenes rctPairs) publicPresent

end TetraStereo.OneCenter
