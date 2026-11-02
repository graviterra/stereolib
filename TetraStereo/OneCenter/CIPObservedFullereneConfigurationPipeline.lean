import TetraStereo.OneCenter.CIPObservedDerivedHelicalSpatialExactness
import TetraStereo.OneCenter.P93FullereneConfigurationCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# Conflict-free P-93.5.6 fullerene family and public-pipeline attachment

The local fullerene classifier is functional for one supplied cage.  This module closes the
finite-family boundary: independently valid records for the same physical cage must agree, a
concrete disagreement is the exhaustive reason for excluding an otherwise valid record, and
every admitted assignment occurs literally once.  It then attaches the fullerene family to the
existing represented public pipeline through disjoint sum constructors, so no pre-existing
stereogenic-unit family can collide with a fullerene result.

The opaque `unit` key and the five substitution tests remain supplied perception evidence.  The
results here prove exact report assembly and descriptor semantics once that evidence is supplied;
they do not claim graph-level fullerene recognition.
-/

/-- Raw locally successful assignments before same-cage conflict resolution. -/
def candidateFullereneConfigurationAssignments
    (inputs : List FullereneConfigurationInput) :
    List FullereneConfigurationAssignment :=
  inputs.filterMap fullereneConfigurationAssignment?

/-- Independent source-level meaning of membership in the raw candidate list. -/
def FullereneConfigurationCandidateJudgment
    (inputs : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs,
    FullereneConfigurationAssignmentJudgment input assignment

/-- The raw executable candidate list is exact against the independent local judgments. -/
theorem mem_candidateFullereneConfigurationAssignments_iff
    (inputs : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ candidateFullereneConfigurationAssignments inputs ↔
      FullereneConfigurationCandidateJudgment inputs assignment := by
  simp [candidateFullereneConfigurationAssignments,
    FullereneConfigurationCandidateJudgment,
    fullereneConfigurationAssignment?_eq_some_iff]

/-- All independently successful records naming this physical cage agree with this assignment. -/
def FullereneConfigurationAssignmentAgreement
    (inputs : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∀ other,
    FullereneConfigurationCandidateJudgment inputs other →
    other.unit = assignment.unit →
    other = assignment

/-- An explicit independently successful record contradicts this assignment on the same cage. -/
def FullereneConfigurationAssignmentConflict
    (inputs : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ other,
    FullereneConfigurationCandidateJudgment inputs other ∧
    other.unit = assignment.unit ∧
    other ≠ assignment

/-- Boolean realization of same-cage agreement over the finite candidate list. -/
def fullereneConfigurationAssignmentAccepted
    (candidates : List FullereneConfigurationAssignment)
    (assignment : FullereneConfigurationAssignment) : Bool :=
  candidates.all fun other =>
    decide (other.unit = assignment.unit → other = assignment)

theorem fullereneConfigurationAssignmentAccepted_eq_true_iff
    (candidates : List FullereneConfigurationAssignment)
    (assignment : FullereneConfigurationAssignment) :
    fullereneConfigurationAssignmentAccepted candidates assignment = true ↔
      ∀ other ∈ candidates,
        other.unit = assignment.unit → other = assignment := by
  rw [fullereneConfigurationAssignmentAccepted, List.all_eq_true]
  constructor
  · intro accepted other present sameUnit
    exact (of_decide_eq_true (accepted other present)) sameUnit
  · intro agreement other present
    exact decide_eq_true (agreement other present)

/-- Retain only assignments on which every successful record for the same cage agrees. -/
def analyzeFullereneConfigurations
    (inputs : List FullereneConfigurationInput) :
    List FullereneConfigurationAssignment :=
  let candidates := candidateFullereneConfigurationAssignments inputs
  (candidates.filter fun assignment =>
    fullereneConfigurationAssignmentAccepted candidates assignment).eraseDups

/-- Independent complete family judgment: a local source exists and all same-cage sources agree. -/
def ConflictFreeFullereneConfigurationAssignmentJudgment
    (inputs : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  FullereneConfigurationCandidateJudgment inputs assignment ∧
    FullereneConfigurationAssignmentAgreement inputs assignment

/-- Exact public-list membership for the finite conflict-free fullerene family. -/
theorem mem_analyzeFullereneConfigurations_iff
    (inputs : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeFullereneConfigurations inputs ↔
      ConflictFreeFullereneConfigurationAssignmentJudgment inputs assignment := by
  rw [analyzeFullereneConfigurations, mem_eraseDups_iff_mem_lawful]
  rw [List.mem_filter]
  rw [fullereneConfigurationAssignmentAccepted_eq_true_iff]
  rw [mem_candidateFullereneConfigurationAssignments_iff]
  unfold ConflictFreeFullereneConfigurationAssignmentJudgment
  unfold FullereneConfigurationAssignmentAgreement
  constructor
  · rintro ⟨candidate, agreement⟩
    exact ⟨candidate, fun other otherJudged sameUnit =>
      agreement other
        ((mem_candidateFullereneConfigurationAssignments_iff inputs other).mpr otherJudged)
        sameUnit⟩
  · rintro ⟨candidate, agreement⟩
    exact ⟨candidate, fun other otherPresent sameUnit =>
      agreement other
        ((mem_candidateFullereneConfigurationAssignments_iff inputs other).mp otherPresent)
        sameUnit⟩

/-- The conflict-free fullerene family is duplicate-free for every finite input list. -/
theorem analyzeFullereneConfigurations_nodup
    (inputs : List FullereneConfigurationInput) :
    (analyzeFullereneConfigurations inputs).Nodup := by
  unfold analyzeFullereneConfigurations
  exact eraseDups_nodup_lawful _

/-- Failure of global same-cage agreement is exactly an explicit contradictory assignment. -/
theorem not_fullereneConfigurationAssignmentAgreement_iff_conflict
    (inputs : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    ¬ FullereneConfigurationAssignmentAgreement inputs assignment ↔
      FullereneConfigurationAssignmentConflict inputs assignment := by
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

/-- For a fixed independently valid source record, family membership is precisely agreement. -/
theorem fullereneConfigurationAssignment_mem_iff_agreement
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : FullereneConfigurationAssignmentJudgment input assignment) :
    assignment ∈ analyzeFullereneConfigurations inputs ↔
      FullereneConfigurationAssignmentAgreement inputs assignment := by
  rw [mem_analyzeFullereneConfigurations_iff]
  unfold ConflictFreeFullereneConfigurationAssignmentJudgment
  simp only [and_iff_right_iff_imp]
  intro _agreement
  exact ⟨input, inputPresent, judged⟩

/-- For a fixed independently valid source record, exclusion is precisely a concrete conflict. -/
theorem fullereneConfigurationAssignment_not_mem_iff_conflict
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : FullereneConfigurationAssignmentJudgment input assignment) :
    assignment ∉ analyzeFullereneConfigurations inputs ↔
      FullereneConfigurationAssignmentConflict inputs assignment := by
  rw [← not_fullereneConfigurationAssignmentAgreement_iff_conflict]
  exact not_congr (fullereneConfigurationAssignment_mem_iff_agreement
    inputs input assignment inputPresent judged)

/-- No two emitted fullerene assignments can name the same physical cage differently. -/
theorem analyzeFullereneConfigurations_sameUnit_eq
    (inputs : List FullereneConfigurationInput)
    {left right : FullereneConfigurationAssignment}
    (leftPresent : left ∈ analyzeFullereneConfigurations inputs)
    (rightPresent : right ∈ analyzeFullereneConfigurations inputs)
    (sameUnit : right.unit = left.unit) :
    right = left := by
  have leftJudged :=
    (mem_analyzeFullereneConfigurations_iff inputs left).mp leftPresent
  have rightJudged :=
    (mem_analyzeFullereneConfigurations_iff inputs right).mp rightPresent
  exact leftJudged.2 right rightJudged.1 sameUnit

/-- One supplied record is publicly ready exactly when it has a local assignment that survives
the independently stated same-cage agreement policy. -/
def FullereneConfigurationInputPublicReady
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput) : Prop :=
  input ∈ inputs ∧
    ∃ assignment,
      FullereneConfigurationAssignmentJudgment input assignment ∧
      ConflictFreeFullereneConfigurationAssignmentJudgment inputs assignment




def FullereneConfigurationInputPublicRefusal
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput) : Prop :=
  input ∉ inputs ∨
    FullereneConfigurationRefusal input ∨
    ∃ assignment,
      FullereneConfigurationAssignmentJudgment input assignment ∧
      FullereneConfigurationAssignmentConflict inputs assignment

/-- Positive public readiness is exactly the absence of every explicit refusal case. -/
theorem fullereneConfigurationInputPublicReady_iff_not_refusal
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput) :
    FullereneConfigurationInputPublicReady inputs input ↔
      ¬ FullereneConfigurationInputPublicRefusal inputs input := by
  classical
  constructor
  · rintro ⟨inputPresent, assignment, localJudged, familyJudged⟩ refusal
    rcases refusal with absent | localRefusal | ⟨other, otherJudged, conflict⟩
    · exact absent inputPresent
    · have localReady : FullereneConfigurationReady input := ⟨assignment, localJudged⟩
      exact ((fullereneConfigurationReady_iff_not_refusal input).mp localReady) localRefusal
    · have sameAssignment := fullereneConfigurationAssignmentJudgment_subsingleton
        input otherJudged localJudged
      subst other
      exact ((not_fullereneConfigurationAssignmentAgreement_iff_conflict
        inputs assignment).mpr conflict) familyJudged.2
  · intro noRefusal
    have inputPresent : input ∈ inputs := by
      by_contra absent
      exact noRefusal (.inl absent)
    have noLocalRefusal : ¬ FullereneConfigurationRefusal input := by
      intro refusal
      exact noRefusal (.inr (.inl refusal))
    obtain ⟨assignment, localJudged⟩ :=
      (fullereneConfigurationReady_iff_not_refusal input).mpr noLocalRefusal
    have noConflict : ¬ FullereneConfigurationAssignmentConflict inputs assignment := by
      intro conflict
      exact noRefusal (.inr (.inr ⟨assignment, localJudged, conflict⟩))
    have agreement : FullereneConfigurationAssignmentAgreement inputs assignment := by
      by_contra notAgreement
      exact noConflict
        ((not_fullereneConfigurationAssignmentAgreement_iff_conflict
          inputs assignment).mp notAgreement)
    exact ⟨inputPresent, assignment, localJudged,
      ⟨⟨input, inputPresent, localJudged⟩, agreement⟩⟩

/-- Negated public readiness has no opaque executable failure: it is exactly the explicit
absent/local-refusal/conflict disjunction. -/
theorem not_fullereneConfigurationInputPublicReady_iff_refusal
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput) :
    ¬ FullereneConfigurationInputPublicReady inputs input ↔
      FullereneConfigurationInputPublicRefusal inputs input := by
  rw [fullereneConfigurationInputPublicReady_iff_not_refusal]
  simp

/-- Every public-ready fullerene record has exactly one independently valid public assignment. -/
theorem every_publicReady_fullereneConfigurationInput_occurs_exactly_once
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput)
    (ready : FullereneConfigurationInputPublicReady inputs input) :
    ∃! assignment,
      assignment ∈ analyzeFullereneConfigurations inputs ∧
      FullereneConfigurationAssignmentJudgment input assignment := by
  rcases ready with ⟨_inputPresent, assignment, localJudged, familyJudged⟩
  have assignmentPresent :=
    (mem_analyzeFullereneConfigurations_iff inputs assignment).mpr familyJudged
  refine ⟨assignment, ⟨assignmentPresent, localJudged⟩, ?_⟩
  intro other ⟨_otherPresent, otherJudged⟩
  exact fullereneConfigurationAssignmentJudgment_subsingleton
    input otherJudged localJudged

/-- Literal finite-list multiplicity form of fullerene exact-once completeness. -/
theorem every_publicReady_fullereneConfigurationInput_count_eq_one
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput)
    (ready : FullereneConfigurationInputPublicReady inputs input) :
    ∃ assignment,
      FullereneConfigurationAssignmentJudgment input assignment ∧
      List.count assignment (analyzeFullereneConfigurations inputs) = 1 := by
  rcases every_publicReady_fullereneConfigurationInput_occurs_exactly_once
      inputs input ready with
    ⟨assignment, ⟨present, judged⟩, _unique⟩
  exact ⟨assignment, judged,
    List.count_eq_one_of_mem (analyzeFullereneConfigurations_nodup inputs) present⟩

/-- A contradicted locally valid assignment has literal multiplicity zero. -/
theorem fullereneConfigurationAssignment_count_eq_zero_of_conflict
    (inputs : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment)
    (inputPresent : input ∈ inputs)
    (judged : FullereneConfigurationAssignmentJudgment input assignment)
    (conflict : FullereneConfigurationAssignmentConflict inputs assignment) :
    List.count assignment (analyzeFullereneConfigurations inputs) = 0 := by
  rw [List.count_eq_zero]
  exact (fullereneConfigurationAssignment_not_mem_iff_conflict
    inputs input assignment inputPresent judged).mpr conflict

/-- Every emitted family result contains exactly the class-dependent descriptor kinds mandated
by the independent P-93.5.6 relation. -/
theorem analyzeFullereneConfigurations_member_requirements_exact
    (inputs : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment)
    (present : assignment ∈ analyzeFullereneConfigurations inputs) :
    assignment.payloads.map FullereneDescriptorPayload.requirement =
      RequiredFullereneDescriptorKinds assignment.chiralityType := by
  rcases ((mem_analyzeFullereneConfigurations_iff inputs assignment).mp present).1 with
    ⟨input, _inputPresent, localJudged⟩
  exact localJudged.requirements_exact input assignment

end BlueBookP93.Cyclic

open BlueBookP93.Cyclic

/-! ## Attachment to the represented public pipeline -/

/-- Disjoint public result carrier extending all currently represented outcomes with P-93.5.6
fullerene configurations without changing the identity of any prior result. -/
inductive CertifiedDerivedSpatialAndFullereneAssignment where
  | represented (assignment : StereoAssignment)
  | fullerene (assignment : FullereneConfigurationAssignment)
  deriving DecidableEq, Repr

/-- Existing certified spatial results followed by the independently conflict-resolved fullerene
family.  The sum constructors make cross-family collision impossible by construction. -/
def analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput) :
    List CertifiedDerivedSpatialAndFullereneAssignment :=
  (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
      certified spatial observations derivedPlanes derivedHelices).map
      .represented ++
    (analyzeFullereneConfigurations fullerenes).map .fullerene

theorem represented_mem_analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (assignment : StereoAssignment) :
    .represented assignment ∈
        analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene certified spatial observations
          derivedPlanes derivedHelices fullerenes ↔
      assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices := by
  simp [analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene]

theorem fullerene_mem_analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    .fullerene assignment ∈
        analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene certified spatial observations
          derivedPlanes derivedHelices fullerenes ↔
      assignment ∈ analyzeFullereneConfigurations fullerenes := by
  simp [analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene]

/-- The extended represented pipeline is duplicate-free, including across the old/new boundary. -/
theorem analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput) :
    (analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene certified spatial observations
      derivedPlanes derivedHelices fullerenes).Nodup := by
  rw [analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene]
  apply List.Nodup.append
  · exact (analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_nodup
      certified spatial observations derivedPlanes derivedHelices).map (by
        intro left right equal
        cases equal
        rfl)
  · exact (analyzeFullereneConfigurations_nodup fullerenes).map (by
        intro left right equal
        cases equal
        rfl)
  · rw [List.disjoint_left]
    intro output representedPresent fullerenePresent
    obtain ⟨assignment, _present, rfl⟩ := List.mem_map.mp representedPresent
    simp at fullerenePresent

/-- Independent classification of every member of the extended represented pipeline. -/
def IndependentlyJudgedCertifiedDerivedSpatialAndFullereneAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput) :
    CertifiedDerivedSpatialAndFullereneAssignment → Prop
  | .represented assignment =>
      IndependentlyJudgedCertifiedDerivedPlanarHelicalSpatialAssignment certified spatial
        observations derivedPlanes derivedHelices assignment
  | .fullerene assignment =>
      ConflictFreeFullereneConfigurationAssignmentJudgment fullerenes assignment

/-- End-to-end semantic soundness of every result in the extended represented pipeline. -/
theorem analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (output : CertifiedDerivedSpatialAndFullereneAssignment)
    (present : output ∈
      analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene certified spatial observations
        derivedPlanes derivedHelices fullerenes) :
    IndependentlyJudgedCertifiedDerivedSpatialAndFullereneAssignment certified spatial
      observations derivedPlanes derivedHelices fullerenes output := by
  cases output with
  | represented assignment =>
      exact analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry_member_judged
        certified spatial observations derivedPlanes derivedHelices assignment
        ((represented_mem_analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_iff
          certified spatial observations derivedPlanes derivedHelices fullerenes assignment).mp
          present)
  | fullerene assignment =>
      exact (mem_analyzeFullereneConfigurations_iff fullerenes assignment).mp
        ((fullerene_mem_analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_iff
          certified spatial observations derivedPlanes derivedHelices fullerenes assignment).mp
          present)

/-- Every public-ready fullerene record occurs literally once in the final extended list. -/
theorem every_publicReady_fullereneConfigurationInput_count_eq_one_in_extended_pipeline
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (input : FullereneConfigurationInput)
    (ready : FullereneConfigurationInputPublicReady fullerenes input) :
    ∃ assignment,
      FullereneConfigurationAssignmentJudgment input assignment ∧
      List.count (.fullerene assignment)
        (analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene certified spatial observations
          derivedPlanes derivedHelices fullerenes) = 1 := by
  rcases every_publicReady_fullereneConfigurationInput_count_eq_one
      fullerenes input ready with ⟨assignment, judged, familyCount⟩
  refine ⟨assignment, judged, ?_⟩
  have familyPresent : assignment ∈ analyzeFullereneConfigurations fullerenes := by
    by_contra absent
    have familyCountZero :
        List.count assignment (analyzeFullereneConfigurations fullerenes) = 0 :=
      List.count_eq_zero.mpr absent
    omega
  have publicPresent : CertifiedDerivedSpatialAndFullereneAssignment.fullerene assignment ∈
      analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene certified spatial observations
        derivedPlanes derivedHelices fullerenes :=
    (fullerene_mem_analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_iff
      certified spatial observations derivedPlanes derivedHelices fullerenes assignment).mpr
      familyPresent
  exact List.count_eq_one_of_mem
    (analyzeCertifiedNormalizedWithDerivedSpatialAndFullerene_nodup certified spatial
      observations derivedPlanes derivedHelices fullerenes) publicPresent

end TetraStereo.OneCenter
