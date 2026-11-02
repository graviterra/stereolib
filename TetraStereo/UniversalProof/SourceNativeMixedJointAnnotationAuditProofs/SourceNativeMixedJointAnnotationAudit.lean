import TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
import TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
import TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
import TetraStereo.UniversalProof.SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness
import TetraStereo.UniversalProof.SourceNativeMixedJointConflictWitnessProofs.SourceNativeMixedJointConflictWitness

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace TetraStereo.UniversalProof.SourceNativeMixedJointAnnotationAuditProofs.SourceNativeMixedJointAnnotationAudit

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.ConstitutionClosedWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel.ClosedConstitutionParserModel
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
open TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit
open TetraStereo.UniversalProof.SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness































universe u

/-- A two-element fold whose first channel is absent is never a conflict. -/
theorem foldStatus_pair_none_ne_conflict {Label : Type u} [DecidableEq Label] (next : Option Label) :
    foldStatus ([none, next] : List (Option Label)) ≠ .conflict := by
  cases next with
  | none => rw [foldStatus_pair_none_none]; intro conflict; cases conflict
  | some label => rw [foldStatus_pair_none_some]; intro conflict; cases conflict

/-- The boolean "is assigned" test is exactly existence of the assigned label. -/
theorem assigned_match_eq_true {Label : Type u} (status : ChannelStatus Label) :
    ((match status with | .assigned _ => true | _ => false) : Bool) = true ↔
      ∃ label, status = .assigned label := by
  cases status <;> simp

section Audit

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)




noncomputable def jointState (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel

/-- The dependency view of the own joint state at a target. -/
noncomputable def jointView (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    source.AromaticCanonicalDependencyView target :=
  source.aromaticCanonicalDependencyView
    (jointState molecule source agreement writtenExact carrierFuel ruleFuel) target

/-- The parser channel read at the own joint state's view, final target and conversion index. -/
noncomputable def jointParserDescriptor? (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel :=
  constitutionParserRichDescriptor? molecule source agreement writtenExact target
    (jointView molecule source agreement writtenExact carrierFuel ruleFuel target) ruleFuel

/-- The drawing channel read at the own joint state's view. -/
noncomputable def jointDrawingDescriptor? (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel :=
  occurrenceOrdinaryDescriptor? source target
    (jointView molecule source agreement writtenExact carrierFuel ruleFuel target) ruleFuel

/-- The joint two-channel status at the own joint state's view. -/
noncomputable def jointStatus (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    ChannelStatus AromaticCanonicalAuxiliaryLabel :=
  mixedChannelStatus molecule source agreement writtenExact target
    (jointView molecule source agreement writtenExact carrierFuel ruleFuel target) ruleFuel

/-- The joint status unfolds to the two actual channel results in fixed order. -/
theorem jointStatus_eq_fold (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    jointStatus molecule source agreement writtenExact carrierFuel ruleFuel target =
      foldStatus [jointDrawingDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
          target,
        jointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel target] :=
  rfl

/-! ## 2. Every actual raw parity record, interpreted at the joint parser channel -/

/-- The typed issue raised by any actual source-wide mixed joint defect. -/
inductive MixedJointAnnotationIssue (source : AuthoritativeChemicalInput) where
  /-- An actual raw parity record with no joint interpretation. -/
  | rawParity (annotation : RawAtomAnnotation)
  /-- An actual raw directional token, refused unconditionally (including `false`). -/
  | rawDirection (raw : RawBondDirection)

  | mixedBond (issue : MixedBondAuditIssue source)
  /-- An annotated centre with no recognized, relevant-channel-interpreted, assigned candidate. -/
  | unresolvedAnnotatedCenter (atom : Nat)
  /-- An actual tetrahedral candidate whose joint status is a typed conflict. -/
  | jointStatusConflict (center : source.AromaticCanonicalTetrahedralCenter)
  deriving DecidableEq

/-- The actual source candidates whose conversion-pinned raw index equals one raw index. -/
noncomputable def matchingJointCandidates (annotation : RawAtomAnnotation) :
    List source.AromaticCanonicalTetrahedralCenter :=
  source.aromaticCanonicalTetrahedralCenters.filter fun candidate =>
    (parserIndexViaConversion molecule source agreement.1 candidate).val == annotation.index

/-- Source-bound meaning of one genuinely interpreted raw atom parity: the actual raw record at the
candidate's real index, the actual source candidate with its exact conversion-pinned index, the
descriptor read from the **own joint state** at the candidate's actual final occurrence and the
independent `CanonicalConstitutionParserRichDescriptor`. No expected label, caller semantics or
separately scheduled constitution label is mentioned. -/
def RawParityJointInterpretation (carrierFuel ruleFuel : Nat) (annotation : RawAtomAnnotation) :
    Prop :=
  ∃ candidate : source.AromaticCanonicalTetrahedralCenter,
    (parserIndexViaConversion molecule source agreement.1 candidate).val = annotation.index ∧
      (∃ spec, molecule.atomAt?
          (parserIndexViaConversion molecule source agreement.1 candidate).val = some spec ∧
        spec.tetrahedral? = some annotation.parity) ∧
        ∃ descriptor : AromaticCanonicalAuxiliaryLabel,
          jointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
              (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) = some descriptor ∧
            CanonicalConstitutionParserRichDescriptor molecule source agreement writtenExact
              (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)
              (jointView molecule source agreement writtenExact carrierFuel ruleFuel
                (source.aromaticCanonicalFinalOccurrence carrierFuel candidate))
              ruleFuel descriptor

/-- Formal scheduled presence test for the joint raw parity interpretation. -/
noncomputable def jointParityInterpreted? (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) : Bool :=
  (matchingJointCandidates molecule source agreement annotation).any fun candidate =>
    (match molecule.atomAt?
        (parserIndexViaConversion molecule source agreement.1 candidate).val with
     | some spec => decide (spec.tetrahedral? = some annotation.parity)
     | none => false) &&
      (jointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)).isSome

theorem matchingJointCandidates_eq_nil_iff (annotation : RawAtomAnnotation) :
    matchingJointCandidates molecule source agreement annotation = [] ↔
      ∀ candidate : source.AromaticCanonicalTetrahedralCenter,
        (parserIndexViaConversion molecule source agreement.1 candidate).val ≠
          annotation.index := by
  constructor
  · intro empty candidate indexEq
    have member : candidate ∈ matchingJointCandidates molecule source agreement annotation := by
      unfold matchingJointCandidates
      rw [List.mem_filter]
      exact ⟨(mem_aromaticCanonicalTetrahedralCenters_iff source candidate).mpr candidate.2,
        beq_iff_eq.mpr indexEq⟩
    rw [empty] at member
    exact List.not_mem_nil member
  · intro noCandidate
    cases observed : matchingJointCandidates molecule source agreement annotation with
    | nil => rfl
    | cons head tail =>
        have member : head ∈ matchingJointCandidates molecule source agreement annotation := by
          simp [observed]
        unfold matchingJointCandidates at member
        rw [List.mem_filter] at member
        exact absurd (beq_iff_eq.mp member.2) (noCandidate head)

theorem not_jointInterpreted_of_no_matching_candidate (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation)
    (noCandidate : ∀ candidate : source.AromaticCanonicalTetrahedralCenter,
      (parserIndexViaConversion molecule source agreement.1 candidate).val ≠ annotation.index) :
    ¬ RawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
      annotation := by
  rintro ⟨candidate, indexEq, _⟩
  exact noCandidate candidate indexEq



theorem jointParityInterpreted?_eq_true_iff (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) :
    jointParityInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel annotation =
        true ↔
      RawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
        annotation := by
  unfold jointParityInterpreted? RawParityJointInterpretation
  rw [List.any_eq_true]
  constructor
  · rintro ⟨candidate, member, matched⟩
    unfold matchingJointCandidates at member
    rw [List.mem_filter] at member
    have indexEq :
        (parserIndexViaConversion molecule source agreement.1 candidate).val =
          annotation.index :=
      beq_iff_eq.mp member.2
    obtain ⟨specMatched, stateIsSome⟩ := Bool.and_eq_true_iff.mp matched
    refine ⟨candidate, indexEq, ?_, ?_⟩
    · cases observed : molecule.atomAt?
          (parserIndexViaConversion molecule source agreement.1 candidate).val with
      | none => simp [observed] at specMatched
      | some spec =>
          exact ⟨spec, rfl, of_decide_eq_true (by simpa only [observed] using specMatched)⟩
    · obtain ⟨descriptor, stateEq⟩ := Option.isSome_iff_exists.mp stateIsSome
      exact ⟨descriptor, stateEq,
        (constitutionParserRichDescriptor?_eq_some_iff_canonical molecule source agreement
          writtenExact (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)
          (jointView molecule source agreement writtenExact carrierFuel ruleFuel
            (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)) ruleFuel
          descriptor).mp stateEq⟩
  · rintro ⟨candidate, indexEq, specData, descriptor, stateEq, _meaning⟩
    refine ⟨candidate, ?_, ?_⟩
    · unfold matchingJointCandidates
      rw [List.mem_filter]
      exact ⟨(mem_aromaticCanonicalTetrahedralCenters_iff source candidate).mpr candidate.2,
        beq_iff_eq.mpr indexEq⟩
    · obtain ⟨spec, specEq, parityEq⟩ := specData
      simp [specEq, parityEq, stateEq]

noncomputable def jointParityIssue? (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) : Option (MixedJointAnnotationIssue source) :=
  if matchingJointCandidates molecule source agreement annotation = [] then
    some (.rawParity annotation)
  else if jointParityInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel
      annotation = true then none
  else some (.rawParity annotation)

theorem jointParityIssue?_eq_none_iff (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) :
    jointParityIssue? molecule source agreement writtenExact carrierFuel ruleFuel annotation = none ↔
      RawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
        annotation := by
  unfold jointParityIssue?
  by_cases empty : matchingJointCandidates molecule source agreement annotation = []
  · rw [if_pos empty]
    exact ⟨fun h => absurd h (by simp), fun interpreted =>
      absurd interpreted (not_jointInterpreted_of_no_matching_candidate molecule source agreement
        writtenExact carrierFuel ruleFuel annotation
        ((matchingJointCandidates_eq_nil_iff molecule source agreement annotation).mp empty))⟩
  · rw [if_neg empty]
    by_cases supported : jointParityInterpreted? molecule source agreement writtenExact carrierFuel
        ruleFuel annotation = true
    · rw [if_pos supported]
      exact ⟨fun _ => (jointParityInterpreted?_eq_true_iff molecule source agreement writtenExact
          carrierFuel ruleFuel annotation).mp supported, fun _ => rfl⟩
    · rw [if_neg supported]
      exact ⟨fun h => absurd h (by simp), fun interpreted =>
        absurd ((jointParityInterpreted?_eq_true_iff molecule source agreement writtenExact
          carrierFuel ruleFuel annotation).mpr interpreted) supported⟩

noncomputable def rawParityJointIssues (carrierFuel ruleFuel : Nat) :
    List (MixedJointAnnotationIssue source) :=
  (rawAtomAnnotations molecule).filterMap
    (jointParityIssue? molecule source agreement writtenExact carrierFuel ruleFuel)

theorem rawParityJointIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    rawParityJointIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      ∀ annotation, annotation ∈ rawAtomAnnotations molecule →
        RawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
          annotation := by
  unfold rawParityJointIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty annotation present
    exact (jointParityIssue?_eq_none_iff molecule source agreement writtenExact carrierFuel ruleFuel
      annotation).mp (empty annotation present)
  · intro interpreted annotation present
    exact (jointParityIssue?_eq_none_iff molecule source agreement writtenExact carrierFuel ruleFuel
      annotation).mpr (interpreted annotation present)

/-! ## 3. Every actual raw directional token, including `false`, is refused -/

def rawDirectionJointIssues : List (MixedJointAnnotationIssue source) :=
  (rawBondDirections molecule).map MixedJointAnnotationIssue.rawDirection

theorem rawDirectionJointIssues_eq_nil_iff :
    rawDirectionJointIssues molecule source = [] ↔ rawBondDirections molecule = [] := by
  unfold rawDirectionJointIssues
  rw [List.map_eq_nil_iff]

/-- Every actual raw directional bond, `false` included, is an unconditional typed issue. -/
theorem rawDirection_flagged (raw : RawBondDirection) (present : raw ∈ rawBondDirections molecule) :
    MixedJointAnnotationIssue.rawDirection raw ∈ rawDirectionJointIssues molecule source := by
  unfold rawDirectionJointIssues
  exact List.mem_map.mpr ⟨raw, present, rfl⟩



def mixedBondJointIssues : List (MixedJointAnnotationIssue source) :=
  (mixedBondAuditIssues source).map MixedJointAnnotationIssue.mixedBond

theorem mixedBondJointIssues_eq_nil_iff :
    mixedBondJointIssues source = [] ↔ MixedBondAnnotationsAccepted source := by
  unfold mixedBondJointIssues
  rw [List.map_eq_nil_iff, mixedBondAuditIssues_eq_nil_iff]

/-! ## 5. Annotated diagram centres: absolute configurations and wedge endpoints -/

/-- Every absolute-scope source atom configuration index. -/
def absoluteConfigurationAtoms : List Nat :=
  (sourceAtomConfigurations source).filterMap fun configuration =>
    if configuration.scope = DiagramConfigurationScope.absolute then some configuration.atom
    else none

/-- Every actual solid/hashed wedge endpoint source index of the source diagram. -/
def wedgeEndpoints : List Nat :=
  match source.diagram? with
  | none => []
  | some diagram =>
      (diagram.bonds.filter fun bond =>
        decide (bond.style = .solidWedge ∨ bond.style = .hashedWedge)).map DiagramBond.source

/-- Every actual annotated source atom index: absolute configurations and wedge endpoints. -/
def annotatedSourceAtoms : List Nat :=
  absoluteConfigurationAtoms source ++ wedgeEndpoints source

/-- The actual source candidates at a source atom index, by constructive center membership. -/
noncomputable def candidatesAt (atomIndex : Nat) :
    List source.AromaticCanonicalTetrahedralCenter :=
  source.aromaticCanonicalTetrahedralCenters.filter fun candidate =>
    candidate.1.val == atomIndex

theorem mem_candidatesAt_iff (atomIndex : Nat)
    (candidate : source.AromaticCanonicalTetrahedralCenter) :
    candidate ∈ candidatesAt source atomIndex ↔
      candidate ∈ source.aromaticCanonicalTetrahedralCenters ∧ candidate.1.val = atomIndex := by
  unfold candidatesAt
  rw [List.mem_filter]
  exact ⟨fun h => ⟨h.1, beq_iff_eq.mp h.2⟩, fun h => ⟨h.1, beq_iff_eq.mpr h.2⟩⟩

/-- One actual annotated source atom is covered: a recognized actual final candidate whose
**relevant** channel is interpreted (drawing for a wedge, parser for a configuration) and whose
joint status is `assigned`.  An unresolved relevant channel fails even when the other channel
assigns. -/
def AnnotatedCenterInterpreted (carrierFuel ruleFuel : Nat) (atomIndex : Nat) : Prop :=
  ∃ candidate ∈ candidatesAt source atomIndex,
    (atomIndex ∉ wedgeEndpoints source ∨
      jointDrawingDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) ≠ none) ∧
    (atomIndex ∉ absoluteConfigurationAtoms source ∨
      jointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) ≠ none) ∧
    (∃ label, jointStatus molecule source agreement writtenExact carrierFuel ruleFuel
      (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) = .assigned label)

noncomputable def annotatedCenterInterpreted? (carrierFuel ruleFuel : Nat) (atomIndex : Nat) : Bool :=
  (candidatesAt source atomIndex).any fun candidate =>
    (decide (atomIndex ∈ wedgeEndpoints source →
        jointDrawingDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) ≠ none) &&
      decide (atomIndex ∈ absoluteConfigurationAtoms source →
        jointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) ≠ none)) &&
    (match jointStatus molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) with
     | .assigned _ => true
     | _ => false)

theorem annotatedCenterInterpreted?_eq_true_iff (carrierFuel ruleFuel : Nat) (atomIndex : Nat) :
    annotatedCenterInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel atomIndex =
        true ↔
      AnnotatedCenterInterpreted molecule source agreement writtenExact carrierFuel ruleFuel
        atomIndex := by
  unfold annotatedCenterInterpreted? AnnotatedCenterInterpreted
  rw [List.any_eq_true]
  constructor
  · rintro ⟨candidate, member, matched⟩
    rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at matched
    obtain ⟨⟨wedgeMatched, parserMatched⟩, assignedMatched⟩ := matched
    refine ⟨candidate, member, ?_, ?_, ?_⟩
    · by_cases wedgePresent : atomIndex ∈ wedgeEndpoints source
      · exact Or.inr (of_decide_eq_true wedgeMatched wedgePresent)
      · exact Or.inl wedgePresent
    · by_cases parserPresent : atomIndex ∈ absoluteConfigurationAtoms source
      · exact Or.inr (of_decide_eq_true parserMatched parserPresent)
      · exact Or.inl parserPresent
    · cases status : jointStatus molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) with
      | unassigned => simp [status] at assignedMatched
      | assigned label => simp
      | conflict => simp [status] at assignedMatched
  · rintro ⟨candidate, member, wedgeReq, parserReq, assigned⟩
    refine ⟨candidate, member, ?_⟩
    rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact decide_eq_true_eq.mpr fun wedgePresent =>
        wedgeReq.elim (fun notMem => absurd wedgePresent notMem) (fun present => present)
    · exact decide_eq_true_eq.mpr fun parserPresent =>
        parserReq.elim (fun notMem => absurd parserPresent notMem) (fun present => present)
    · obtain ⟨label, hstatus⟩ := assigned
      simp [hstatus]

noncomputable def annotatedCenterIssues (carrierFuel ruleFuel : Nat) :
    List (MixedJointAnnotationIssue source) :=
  (annotatedSourceAtoms source).filterMap fun atomIndex =>
    if annotatedCenterInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel
        atomIndex = true then none
    else some (.unresolvedAnnotatedCenter atomIndex)

theorem annotatedCenterIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    annotatedCenterIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      ∀ atomIndex, atomIndex ∈ annotatedSourceAtoms source →
        AnnotatedCenterInterpreted molecule source agreement writtenExact carrierFuel ruleFuel
          atomIndex := by
  unfold annotatedCenterIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty atomIndex present
    by_contra notInterpreted
    have h := empty atomIndex present
    have notTrue : ¬ (annotatedCenterInterpreted? molecule source agreement writtenExact carrierFuel
        ruleFuel atomIndex = true) :=
      fun htrue => notInterpreted
        ((annotatedCenterInterpreted?_eq_true_iff molecule source agreement writtenExact carrierFuel
          ruleFuel atomIndex).mp htrue)
    rw [if_neg notTrue] at h
    exact absurd h (by simp)
  · intro interpreted atomIndex present
    rw [if_pos ((annotatedCenterInterpreted?_eq_true_iff molecule source agreement writtenExact
      carrierFuel ruleFuel atomIndex).mpr (interpreted atomIndex present))]

/-! ## 6. Typed conflict by global refusal over every actual candidate -/

noncomputable def globalConflictIssues (carrierFuel ruleFuel : Nat) :
    List (MixedJointAnnotationIssue source) :=
  source.aromaticCanonicalTetrahedralCenters.filterMap fun center =>
    if jointStatus molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) = .conflict then
      some (.jointStatusConflict center)
    else none

theorem globalConflictIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    globalConflictIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      ∀ center, center ∈ source.aromaticCanonicalTetrahedralCenters →
        jointStatus molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel center) ≠ .conflict := by
  unfold globalConflictIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty center present conflict
    have h := empty center present
    rw [if_pos conflict] at h
    exact absurd h (by simp)
  · intro noConflict center present
    rw [if_neg (noConflict center present)]



noncomputable def mixedJointAnnotationAudit (carrierFuel ruleFuel : Nat) :
    List (MixedJointAnnotationIssue source) :=
  rawParityJointIssues molecule source agreement writtenExact carrierFuel ruleFuel ++
    (rawDirectionJointIssues molecule source ++
      (mixedBondJointIssues source ++
        (annotatedCenterIssues molecule source agreement writtenExact carrierFuel ruleFuel ++
          globalConflictIssues molecule source agreement writtenExact carrierFuel ruleFuel)))





theorem mixedJointAnnotationAudit_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    mixedJointAnnotationAudit molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      (∀ annotation, annotation ∈ rawAtomAnnotations molecule →
        RawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
          annotation) ∧
      rawBondDirections molecule = [] ∧
      MixedBondAnnotationsAccepted source ∧
      (∀ atomIndex, atomIndex ∈ annotatedSourceAtoms source →
        AnnotatedCenterInterpreted molecule source agreement writtenExact carrierFuel ruleFuel
          atomIndex) ∧
      (∀ center, center ∈ source.aromaticCanonicalTetrahedralCenters →
        jointStatus molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel center) ≠ .conflict) := by
  unfold mixedJointAnnotationAudit
  rw [List.append_eq_nil_iff, List.append_eq_nil_iff, List.append_eq_nil_iff,
    List.append_eq_nil_iff, rawParityJointIssues_eq_nil_iff, rawDirectionJointIssues_eq_nil_iff,
    mixedBondJointIssues_eq_nil_iff, annotatedCenterIssues_eq_nil_iff,
    globalConflictIssues_eq_nil_iff]


theorem accepted_raw_parity_has_joint_meaning (carrierFuel ruleFuel : Nat)
    (accepted : mixedJointAnnotationAudit molecule source agreement writtenExact carrierFuel ruleFuel
      = [])
    (annotation : RawAtomAnnotation) (present : annotation ∈ rawAtomAnnotations molecule) :
    ∃ candidate descriptor,
      (parserIndexViaConversion molecule source agreement.1 candidate).val = annotation.index ∧
        jointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
            (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) = some descriptor ∧
          CanonicalConstitutionParserRichDescriptor molecule source agreement writtenExact
            (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)
            (jointView molecule source agreement writtenExact carrierFuel ruleFuel
              (source.aromaticCanonicalFinalOccurrence carrierFuel candidate))
            ruleFuel descriptor := by
  obtain ⟨candidate, indexEq, _spec, descriptor, stateEq, meaning⟩ :=
    ((mixedJointAnnotationAudit_eq_nil_iff molecule source agreement writtenExact carrierFuel
      ruleFuel).mp accepted).1 annotation present
  exact ⟨candidate, descriptor, indexEq, stateEq, meaning⟩

end Audit

/-! ## 8. Closed witnesses -/

namespace ClosedJointAudit

/-- The drawing channel is absent at the coordinate-free closed parser source for every view. -/
theorem parserSource_drawing_absent {carrierFuel : Nat}
    (target : parserSource.AromaticCanonicalOccurrence carrierFuel)
    (view : parserSource.AromaticCanonicalDependencyView target) :
    occurrenceOrdinaryDescriptor? parserSource target view 2 = none :=
  occurrenceOrdinaryDescriptor?_eq_none_of_extraction_none parserSource
    (fun center => extract?_eq_none_of_atomPositions_none parserSource
      annotatedRawCF.toDiagramConfiguration rfl rfl center) target view 2

/-- The actual parser channel emits `R` at the closed target for every view of the source. -/
theorem parserSource_parser_R (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    constitutionParserRichDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 = some (.chiral RS.R) :=
  parser_actual_constitution_descriptor_R view

/-- The joint status at the closed target is assigned `R` at every view. -/
theorem parserSource_jointStatus_R
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    mixedChannelStatus annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 = .assigned (.chiral RS.R) := by
  unfold mixedChannelStatus mixedChannelOutputs
  rw [parserSource_drawing_absent parserTarget view, parserSource_parser_R view]
  exact foldStatus_pair_none_some (Label := AromaticCanonicalAuxiliaryLabel) (.chiral RS.R)

theorem parserCenter_raw_zero :
    (parserIndexViaConversion annotatedRawCF parserSource parserSource_annotationAgreement.1
      parserCenter).val = 0 :=
  ConstitutionClosedWitness.parserSource_index_identity

theorem parserCenter_val_zero : parserCenter.1.val = 0 := by
  rw [← parserIndexViaConversion_val annotatedRawCF parserSource
    parserSource_annotationAgreement.1 parserCenter]
  exact ConstitutionClosedWitness.parserSource_index_identity

theorem parserCenter_centerMem :
    parserCenter ∈ parserSource.aromaticCanonicalTetrahedralCenters :=
  (mem_aromaticCanonicalTetrahedralCenters_iff parserSource parserCenter).mpr parserCenter.2

/-- The closed carbon raw parity is genuinely interpreted at the own joint parser channel. -/
theorem parserSource_raw_parity_interpreted :
    RawParityJointInterpretation annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2
      { index := 0, parity := TetrahedralInputParity.clockwise } := by
  have channelR := parserSource_parser_R
    (jointView annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2 parserTarget)
  refine ⟨parserCenter, parserCenter_raw_zero, ?_, .chiral RS.R, channelR, ?_⟩
  · refine ⟨({ AtomSpec.aliphatic .C with
        tetrahedral? := some TetrahedralInputParity.clockwise } : AtomSpec), ?_, ?_⟩
    · rw [parserCenter_raw_zero]
      exact SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness.parserSource_atom
    · exact SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness.parserSource_spec_parity
  · exact (constitutionParserRichDescriptor?_eq_some_iff_canonical annotatedRawCF parserSource
      parserSource_annotationAgreement parserSource_writtenExact parserTarget
      (jointView annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact 0 2 parserTarget) 2 (.chiral RS.R)).mp channelR

theorem parserSource_rawAtomAnnotations :
    rawAtomAnnotations annotatedRawCF =
      [{ index := 0, parity := TetrahedralInputParity.clockwise }] := by
  decide +kernel

theorem parserSource_no_raw_directions : rawBondDirections annotatedRawCF = [] := by
  decide +kernel


theorem parserSource_bondAudit_clean : MixedBondAnnotationsAccepted parserSource :=
  (mixedBondAuditIssues_eq_nil_iff parserSource).mp (by decide +kernel)

theorem parserSource_absoluteConfigurationAtoms :
    absoluteConfigurationAtoms parserSource = [0] := by
  decide +kernel

theorem parserSource_no_wedgeEndpoints : wedgeEndpoints parserSource = [] := by
  decide +kernel

theorem parserSource_no_wedge_zero : ¬ (0 ∈ wedgeEndpoints parserSource) := by
  rw [parserSource_no_wedgeEndpoints]
  simp

/-- The closed carbon annotated atom is covered at the own joint state. -/
theorem parserSource_annotated_zero_interpreted :
    AnnotatedCenterInterpreted annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2 0 := by
  refine ⟨parserCenter, (mem_candidatesAt_iff parserSource 0 parserCenter).mpr
    ⟨parserCenter_centerMem, parserCenter_val_zero⟩, ?_, ?_, ?_⟩
  · exact Or.inl parserSource_no_wedge_zero
  · refine Or.inr ?_
    intro absent
    have eq : jointParserDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact 0 2
        (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter) = some (.chiral RS.R) :=
      parserSource_parser_R (jointView annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact 0 2 parserTarget)
    rw [eq] at absent
    exact absurd absent (by simp)
  · refine ⟨.chiral RS.R, ?_⟩
    exact parserSource_jointStatus_R
      (jointView annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact 0 2 parserTarget)

theorem parserSource_annotatedCovered (atomIndex : Nat)
    (present : atomIndex ∈ annotatedSourceAtoms parserSource) :
    AnnotatedCenterInterpreted annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2 atomIndex := by
  rw [show annotatedSourceAtoms parserSource = [0] from by
    unfold annotatedSourceAtoms
    rw [parserSource_absoluteConfigurationAtoms, parserSource_no_wedgeEndpoints]
    rfl] at present
  rw [List.mem_singleton] at present
  rw [present]
  exact parserSource_annotated_zero_interpreted

/-- The only actual tetrahedral candidate of the coordinate-free closed source has no conflict: the
absent drawing channel leaves only `unassigned`/`assigned`. -/
theorem parserSource_no_conflict (center : parserSource.AromaticCanonicalTetrahedralCenter) :
    jointStatus annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2
      (parserSource.aromaticCanonicalFinalOccurrence 0 center) ≠ .conflict := by
  intro conflict
  unfold jointStatus mixedChannelStatus mixedChannelOutputs at conflict
  rw [parserSource_drawing_absent _ (jointView annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2
    (parserSource.aromaticCanonicalFinalOccurrence 0 center))] at conflict
  exact foldStatus_pair_none_ne_conflict _ conflict




theorem parserSource_audit_pass :
    mixedJointAnnotationAudit annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2 = [] := by
  rw [mixedJointAnnotationAudit_eq_nil_iff]
  refine ⟨?_, parserSource_no_raw_directions, parserSource_bondAudit_clean, ?_, ?_⟩
  · intro annotation present
    rw [parserSource_rawAtomAnnotations, List.mem_singleton] at present
    rw [present]
    exact parserSource_raw_parity_interpreted
  · exact parserSource_annotatedCovered
  · intro center _present
    exact parserSource_no_conflict center

/-! ### The complete solid-wedge source is refused by its own joint conflict -/

theorem solid_jointStatus_conflict :
    jointStatus annotatedRawCF newSource newSource_annotationAgreement parserSource_writtenExact 0 2
      newTarget = .conflict := by
  show mixedChannelStatus annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget
      (newSource.aromaticCanonicalDependencyView
        (mixedScheduledState annotatedRawCF newSource newSource_annotationAgreement
          parserSource_writtenExact 0 2) newTarget) 2 = .conflict
  exact SourceNativeMixedJointConflictWitnessProofs.SourceNativeMixedJointConflictWitness.retained_joint_status_conflict

theorem newCenter_centerMem : newCenter ∈ newSource.aromaticCanonicalTetrahedralCenters :=
  (mem_aromaticCanonicalTetrahedralCenters_iff newSource newCenter).mpr newCenter.2


theorem solid_audit_refused :
    mixedJointAnnotationAudit annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact 0 2 ≠ [] := by
  intro empty
  have member : MixedJointAnnotationIssue.jointStatusConflict newCenter ∈
      globalConflictIssues annotatedRawCF newSource newSource_annotationAgreement
        parserSource_writtenExact 0 2 := by
    unfold globalConflictIssues
    rw [List.mem_filterMap]
    refine ⟨newCenter, newCenter_centerMem, ?_⟩
    exact if_pos solid_jointStatus_conflict
  have present : MixedJointAnnotationIssue.jointStatusConflict newCenter ∈
      mixedJointAnnotationAudit annotatedRawCF newSource newSource_annotationAgreement
        parserSource_writtenExact 0 2 := by
    unfold mixedJointAnnotationAudit
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inr (List.mem_append.mpr (Or.inr member)))))))
  rw [empty] at present
  exact List.not_mem_nil present

end ClosedJointAudit

end TetraStereo.UniversalProof.SourceNativeMixedJointAnnotationAuditProofs.SourceNativeMixedJointAnnotationAudit
