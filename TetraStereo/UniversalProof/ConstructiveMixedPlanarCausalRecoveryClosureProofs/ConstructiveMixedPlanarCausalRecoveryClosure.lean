import TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofsLibrary.MixedPlanarCausalRecovery
import TetraStereo.UniversalProof.ReviewedMixedPlanarCausalRecoveryClosureProofs.ReviewedMixedPlanarCausalRecoveryClosure
import TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence
import TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
import TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.ConstructiveMixedPlanarCausalRecoveryClosureProofs.ConstructiveMixedPlanarCausalRecoveryClosure

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence
open TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
open TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit
open TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel
open TetraStereo.UniversalProof.ReviewedMixedPlanarCausalRecoveryClosureProofs.ReviewedMixedPlanarCausalRecoveryClosure





























































/-! ## 1. The source-generated typed issue -/

/-- Every actual source-wide joint planar defect, in one typed sum. Each constructor names the actual
source datum that produced it; none is a supplied conclusion or a chemical nonstereogenicity claim. -/
inductive PlanarJointIssue (source : AuthoritativeChemicalInput) where
  /-- An actual raw parity record with no joint planar-parser interpretation. -/
  | rawParity (annotation : RawAtomAnnotation)
  /-- An actual raw directional token, refused unconditionally (including `false`). -/
  | rawDirection (raw : RawBondDirection)

  | mixedBond (issue : MixedBondAuditIssue source)
  /-- An annotated centre with no recognized, relevant-channel-interpreted, assigned candidate. -/
  | unresolvedAnnotatedCenter (atom : Nat)
  /-- An actual tetrahedral candidate whose joint status is a typed conflict. -/
  | jointStatusConflict (center : source.AromaticCanonicalTetrahedralCenter)
  deriving DecidableEq

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)

/-! ## 2. Raw parity: a formal source-generated interpretation test -/

/-- The actual source candidates whose conversion-pinned raw index equals one raw index. -/
noncomputable def planarMatchingCandidates (annotation : RawAtomAnnotation) :
    List source.AromaticCanonicalTetrahedralCenter :=
  source.aromaticCanonicalTetrahedralCenters.filter fun candidate =>
    (parserIndexViaConversion molecule source agreement.1 candidate).val == annotation.index

/-- Source-generated presence test for one actual raw atom parity: an actual candidate whose
conversion-pinned raw record carries the copied parity and whose own-view planar parser descriptor is
present. It reads no expected label, caller comparator or success callback. -/
noncomputable def planarParityInterpreted? (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) : Bool :=
  (planarMatchingCandidates molecule source agreement annotation).any fun candidate =>
    (match molecule.atomAt?
        (parserIndexViaConversion molecule source agreement.1 candidate).val with
     | some spec => decide (spec.tetrahedral? = some annotation.parity)
     | none => false) &&
      (planarJointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)).isSome




theorem planarParityInterpreted?_eq_true_iff (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) :
    planarParityInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel annotation =
        true ↔
      PlanarRawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
        annotation := by
  unfold planarParityInterpreted? PlanarRawParityJointInterpretation
  rw [List.any_eq_true]
  constructor
  · rintro ⟨candidate, member, matched⟩
    unfold planarMatchingCandidates at member
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
        planarConstitutionParserRichDescriptor?_sound molecule source agreement writtenExact
          (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)
          (planarJointView molecule source agreement writtenExact carrierFuel ruleFuel
            (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)) ruleFuel descriptor
          (by simpa only [planarJointParserDescriptor?] using stateEq)⟩
  · rintro ⟨candidate, indexEq, specData, descriptor, stateEq, _meaning⟩
    refine ⟨candidate, ?_, ?_⟩
    · unfold planarMatchingCandidates
      rw [List.mem_filter]
      exact ⟨(mem_aromaticCanonicalTetrahedralCenters_iff source candidate).mpr candidate.2,
        beq_iff_eq.mpr indexEq⟩
    · obtain ⟨spec, specEq, parityEq⟩ := specData
      simp [specEq, parityEq, stateEq]

/-- The source-generated issue raised by one actual raw parity record. -/
noncomputable def planarParityIssue? (carrierFuel ruleFuel : Nat) (annotation : RawAtomAnnotation) :
    Option (PlanarJointIssue source) :=
  if planarParityInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel
      annotation = true then none
  else some (.rawParity annotation)

theorem planarParityIssue?_eq_none_iff (carrierFuel ruleFuel : Nat) (annotation : RawAtomAnnotation) :
    planarParityIssue? molecule source agreement writtenExact carrierFuel ruleFuel annotation = none ↔
      PlanarRawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
        annotation := by
  unfold planarParityIssue?
  by_cases supported : planarParityInterpreted? molecule source agreement writtenExact carrierFuel
      ruleFuel annotation = true
  · rw [if_pos supported]
    exact ⟨fun _ => (planarParityInterpreted?_eq_true_iff molecule source agreement writtenExact
        carrierFuel ruleFuel annotation).mp supported, fun _ => rfl⟩
  · rw [if_neg supported]
    exact ⟨fun h => absurd h (by simp), fun interpreted =>
      absurd ((planarParityInterpreted?_eq_true_iff molecule source agreement writtenExact
        carrierFuel ruleFuel annotation).mpr interpreted) supported⟩

/-- Every actual raw parity record, tested by the formal noncomputable model. -/
noncomputable def planarRawParityIssues (carrierFuel ruleFuel : Nat) :
    List (PlanarJointIssue source) :=
  (rawAtomAnnotations molecule).filterMap
    (planarParityIssue? molecule source agreement writtenExact carrierFuel ruleFuel)

theorem planarRawParityIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    planarRawParityIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      ∀ annotation, annotation ∈ rawAtomAnnotations molecule →
        PlanarRawParityJointInterpretation molecule source agreement writtenExact carrierFuel
          ruleFuel annotation := by
  unfold planarRawParityIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty annotation present
    exact (planarParityIssue?_eq_none_iff molecule source agreement writtenExact carrierFuel ruleFuel
      annotation).mp (empty annotation present)
  · intro interpreted annotation present
    exact (planarParityIssue?_eq_none_iff molecule source agreement writtenExact carrierFuel ruleFuel
      annotation).mpr (interpreted annotation present)



/-- Every actual raw directional token, `false` included, is refused unconditionally. -/
def planarRawDirectionIssues : List (PlanarJointIssue source) :=
  (rawBondDirections molecule).map PlanarJointIssue.rawDirection

theorem planarRawDirectionIssues_eq_nil_iff :
    planarRawDirectionIssues molecule source = [] ↔ rawBondDirections molecule = [] := by
  unfold planarRawDirectionIssues
  rw [List.map_eq_nil_iff]


def planarMixedBondIssues : List (PlanarJointIssue source) :=
  (mixedBondAuditIssues source).map PlanarJointIssue.mixedBond

theorem planarMixedBondIssues_eq_nil_iff :
    planarMixedBondIssues source = [] ↔ MixedBondAnnotationsAccepted source := by
  unfold planarMixedBondIssues
  rw [List.map_eq_nil_iff, mixedBondAuditIssues_eq_nil_iff]

/-- Source-generated coverage test for one actual annotated atom: an actual candidate at the index
whose **relevant** channel is interpreted (drawing for a wedge, planar parser for a configuration)
and whose own-view joint status is `assigned`. -/
noncomputable def planarAnnotatedCenterInterpreted? (carrierFuel ruleFuel : Nat) (atomIndex : Nat) :
    Bool :=
  (planarCandidatesAt source atomIndex).any fun candidate =>
    (decide (atomIndex ∈ planarWedgeEndpoints source →
        planarJointDrawingDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) ≠ none) &&
      decide (atomIndex ∈ planarAbsoluteConfigurationAtoms source →
        planarJointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) ≠ none)) &&
    (match planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) with
     | .assigned _ => true
     | _ => false)

theorem planarAnnotatedCenterInterpreted?_eq_true_iff (carrierFuel ruleFuel : Nat)
    (atomIndex : Nat) :
    planarAnnotatedCenterInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel
        atomIndex = true ↔
      PlanarAnnotatedCenterInterpreted molecule source agreement writtenExact carrierFuel ruleFuel
        atomIndex := by
  unfold planarAnnotatedCenterInterpreted? PlanarAnnotatedCenterInterpreted
  rw [List.any_eq_true]
  constructor
  · rintro ⟨candidate, member, matched⟩
    rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at matched
    obtain ⟨⟨wedgeMatched, parserMatched⟩, assignedMatched⟩ := matched
    refine ⟨candidate, member, ?_, ?_, ?_⟩
    · by_cases wedgePresent : atomIndex ∈ planarWedgeEndpoints source
      · exact Or.inr (of_decide_eq_true wedgeMatched wedgePresent)
      · exact Or.inl wedgePresent
    · by_cases parserPresent : atomIndex ∈ planarAbsoluteConfigurationAtoms source
      · exact Or.inr (of_decide_eq_true parserMatched parserPresent)
      · exact Or.inl parserPresent
    · cases status : planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel
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

/-- Every actual annotated source atom (absolute configuration or wedge endpoint), tested by the formal noncomputable model. -/
noncomputable def planarAnnotatedCenterIssues (carrierFuel ruleFuel : Nat) :
    List (PlanarJointIssue source) :=
  (planarAnnotatedSourceAtoms source).filterMap fun atomIndex =>
    if planarAnnotatedCenterInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel
        atomIndex = true then none
    else some (.unresolvedAnnotatedCenter atomIndex)

theorem planarAnnotatedCenterIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    planarAnnotatedCenterIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      ∀ atomIndex, atomIndex ∈ planarAnnotatedSourceAtoms source →
        PlanarAnnotatedCenterInterpreted molecule source agreement writtenExact carrierFuel ruleFuel
          atomIndex := by
  unfold planarAnnotatedCenterIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty atomIndex present
    by_contra notInterpreted
    have h := empty atomIndex present
    have notTrue : ¬ (planarAnnotatedCenterInterpreted? molecule source agreement writtenExact
        carrierFuel ruleFuel atomIndex = true) :=
      fun htrue => notInterpreted
        ((planarAnnotatedCenterInterpreted?_eq_true_iff molecule source agreement writtenExact
          carrierFuel ruleFuel atomIndex).mp htrue)
    rw [if_neg notTrue] at h
    exact absurd h (by simp)
  · intro interpreted atomIndex present
    rw [if_pos ((planarAnnotatedCenterInterpreted?_eq_true_iff molecule source agreement writtenExact
      carrierFuel ruleFuel atomIndex).mpr (interpreted atomIndex present))]





noncomputable def planarPartialAuditIssues (carrierFuel ruleFuel : Nat) :
    List (PlanarJointIssue source) :=
  planarRawParityIssues molecule source agreement writtenExact carrierFuel ruleFuel ++
    (planarRawDirectionIssues molecule source ++
      (planarMixedBondIssues source ++
        planarAnnotatedCenterIssues molecule source agreement writtenExact carrierFuel ruleFuel))




theorem planarPartialAuditIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    planarPartialAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      PlanarJointPartialAudit molecule source agreement writtenExact carrierFuel ruleFuel := by
  unfold planarPartialAuditIssues PlanarJointPartialAudit
  rw [List.append_eq_nil_iff, List.append_eq_nil_iff, List.append_eq_nil_iff,
    planarRawParityIssues_eq_nil_iff, planarRawDirectionIssues_eq_nil_iff,
    planarMixedBondIssues_eq_nil_iff, planarAnnotatedCenterIssues_eq_nil_iff]





noncomputable def planarConflictIssues (carrierFuel ruleFuel : Nat) :
    List (PlanarJointIssue source) :=
  (planarGlobalConflictIssues molecule source agreement writtenExact carrierFuel ruleFuel).map
    PlanarJointIssue.jointStatusConflict

theorem planarConflictIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    planarConflictIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      PlanarGlobalConflictFree molecule source agreement writtenExact carrierFuel ruleFuel := by
  unfold planarConflictIssues PlanarGlobalConflictFree
  rw [List.map_eq_nil_iff]



noncomputable def planarFullAuditIssues (carrierFuel ruleFuel : Nat) :
    List (PlanarJointIssue source) :=
  planarConflictIssues molecule source agreement writtenExact carrierFuel ruleFuel ++
    planarPartialAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel



theorem planarFullAuditIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    planarFullAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      PlanarJointAuditObligation molecule source agreement writtenExact carrierFuel ruleFuel := by
  unfold planarFullAuditIssues PlanarJointAuditObligation
  rw [List.append_eq_nil_iff, planarConflictIssues_eq_nil_iff,
    planarPartialAuditIssues_eq_nil_iff]

/-! ## 6. Conflict issues from an actual two-channel disagreement -/

/-- Two actual successful channels with different labels are a typed conflict at the own-view status. -/
theorem planarJointStatus_conflict_of_channel_disagreement (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : planarJointDrawingDescriptor? molecule source agreement writtenExact carrierFuel
      ruleFuel target = some leftLabel)
    (parser : planarJointParserDescriptor? molecule source agreement writtenExact carrierFuel
      ruleFuel target = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel target =
      .conflict := by
  rw [planarJointStatus_eq_fold, drawing, parser]
  exact foldStatus_pair_some_some_diff leftLabel rightLabel different

/-- An actual candidate conflict produces a joint-status-conflict issue. -/
theorem jointStatusConflict_mem_conflictIssues (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (conflict : planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) = .conflict) :
    PlanarJointIssue.jointStatusConflict center ∈ planarConflictIssues molecule source agreement
      writtenExact carrierFuel ruleFuel := by
  unfold planarConflictIssues
  apply List.mem_map.mpr
  refine ⟨center, ?_, rfl⟩
  unfold planarGlobalConflictIssues
  rw [List.mem_filterMap]
  exact ⟨center, (source.mem_aromaticCanonicalTetrahedralCenters_iff center).mpr center.2,
    by rw [if_pos conflict]⟩

/-- An actual candidate conflict forces a nonempty full issue list. -/
theorem planarFullAuditIssues_ne_nil_of_candidate_conflict (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (conflict : planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) = .conflict) :
    planarFullAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel ≠ [] := by
  intro empty
  have present : PlanarJointIssue.jointStatusConflict center ∈ planarFullAuditIssues molecule source
      agreement writtenExact carrierFuel ruleFuel := by
    unfold planarFullAuditIssues
    exact List.mem_append.mpr (Or.inl (jointStatusConflict_mem_conflictIssues molecule source
      agreement writtenExact carrierFuel ruleFuel center conflict))
  rw [empty] at present
  exact List.not_mem_nil present

/-! ## 7. The source-owned planar transaction -/

/-- One row per actual connectivity-only tetrahedral candidate, in canonical source index order. -/
structure PlanarScheduledRow (source : AuthoritativeChemicalInput) where
  center : source.AromaticCanonicalTetrahedralCenter
  label : Option AromaticCanonicalAuxiliaryLabel
  deriving DecidableEq

/-- The source-generated report: one row per actual candidate, whose label is read from the model's
own scheduled state at the candidate's actual final occurrence. -/
noncomputable def planarSourceReport (carrierFuel ruleFuel : Nat) :
    List (PlanarScheduledRow source) :=
  source.aromaticCanonicalTetrahedralCenters.map fun center =>
    { center, label := planarJointState molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) }

theorem mem_planarSourceReport_iff (carrierFuel ruleFuel : Nat) (row : PlanarScheduledRow source) :
    row ∈ planarSourceReport molecule source agreement writtenExact carrierFuel ruleFuel ↔
      row.label = planarJointState molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) := by
  constructor
  · intro present
    rcases List.mem_map.mp present with ⟨center, _, same⟩
    subst row
    rfl
  · intro same
    apply List.mem_map.mpr
    refine ⟨row.center,
      (source.mem_aromaticCanonicalTetrahedralCenters_iff row.center).mpr row.center.property, ?_⟩
    cases row with
    | mk center label =>
        change label = planarJointState molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel center) at same
        subst label
        rfl

/-- The own model's dependency view at the candidate's actual final occurrence. -/
noncomputable def planarSourceView (carrierFuel ruleFuel : Nat)
    (row : PlanarScheduledRow source) :
    source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) :=
  source.aromaticCanonicalDependencyView
    (planarJointState molecule source agreement writtenExact carrierFuel ruleFuel)
    (source.aromaticCanonicalFinalOccurrence carrierFuel row.center)

/-- Genuine joint-model binding and independent meaning for every row label: the label is the own
scheduled model state value at the candidate's actual final occurrence and, whenever assigned, satisfies
the named joint planarity `PlanarMixedJointDescriptor` under the same own view. No chemical
completeness is asserted. -/
def PlanarSourceRowMeaning (carrierFuel ruleFuel : Nat) (row : PlanarScheduledRow source) : Prop :=
  ∃ state : source.AromaticCanonicalAuxiliaryState carrierFuel,
    (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
        ruleFuel)).CIPModel state ∧
      state (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) = row.label ∧
        ∀ descriptor, row.label = some descriptor →
          PlanarMixedJointDescriptor molecule source agreement writtenExact
            (source.aromaticCanonicalFinalOccurrence carrierFuel row.center)
            (source.aromaticCanonicalDependencyView state
              (source.aromaticCanonicalFinalOccurrence carrierFuel row.center)) ruleFuel descriptor

/-- Every generated row carries the own joint model output meaning, via the model's own soundness. -/
theorem planarSourceReport_member_sound (carrierFuel ruleFuel : Nat)
    (row : PlanarScheduledRow source)
    (present : row ∈ planarSourceReport molecule source agreement writtenExact carrierFuel ruleFuel) :
    PlanarSourceRowMeaning molecule source agreement writtenExact carrierFuel ruleFuel row := by
  have emitted := (mem_planarSourceReport_iff molecule source agreement writtenExact carrierFuel
    ruleFuel row).mp present
  refine ⟨planarJointState molecule source agreement writtenExact carrierFuel ruleFuel,
    planarMixedScheduledState_cipModel molecule source agreement writtenExact carrierFuel ruleFuel,
    emitted.symm, ?_⟩
  intro descriptor assigned
  exact planarMixedModel_output_sound molecule source agreement writtenExact
    (planarJointState molecule source agreement writtenExact carrierFuel ruleFuel)
    (planarMixedScheduledState_cipModel molecule source agreement writtenExact carrierFuel ruleFuel)
    (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) descriptor
    (emitted.symm.trans assigned)

/-- The **source-owned planar transaction**: admit the source-generated report exactly when the
source's own full issue list is empty. -/
noncomputable def planarSourceProduce (carrierFuel ruleFuel : Nat) :
    Option (List (PlanarScheduledRow source)) :=
  if planarFullAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] then
    some (planarSourceReport molecule source agreement writtenExact carrierFuel ruleFuel)
  else none

theorem planarSourceProduce_eq_some_iff (carrierFuel ruleFuel : Nat)
    (rows : List (PlanarScheduledRow source)) :
    planarSourceProduce molecule source agreement writtenExact carrierFuel ruleFuel = some rows ↔
      planarFullAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ∧
        rows = planarSourceReport molecule source agreement writtenExact carrierFuel ruleFuel := by
  classical
  by_cases accepted : planarFullAuditIssues molecule source agreement writtenExact carrierFuel
      ruleFuel = []
  · simp [planarSourceProduce, accepted, eq_comm]
  · simp [planarSourceProduce, accepted]

theorem planarSourceProduce_eq_none_iff (carrierFuel ruleFuel : Nat) :
    planarSourceProduce molecule source agreement writtenExact carrierFuel ruleFuel = none ↔
      planarFullAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel ≠ [] := by
  classical
  by_cases accepted : planarFullAuditIssues molecule source agreement writtenExact carrierFuel
      ruleFuel = []
  <;> simp [planarSourceProduce, accepted]


theorem planarSourceProduce_iff_obligation (carrierFuel ruleFuel : Nat)
    (rows : List (PlanarScheduledRow source)) :
    planarSourceProduce molecule source agreement writtenExact carrierFuel ruleFuel = some rows ↔
      PlanarJointAuditObligation molecule source agreement writtenExact carrierFuel ruleFuel ∧
        rows = planarSourceReport molecule source agreement writtenExact carrierFuel ruleFuel := by
  rw [planarSourceProduce_eq_some_iff molecule source agreement writtenExact carrierFuel ruleFuel
      rows,
    planarFullAuditIssues_eq_nil_iff molecule source agreement writtenExact carrierFuel ruleFuel]

/-- Any actual issue refuses the whole transaction. -/
theorem planarSourceProduce_refuses_issue (carrierFuel ruleFuel : Nat) (issue : PlanarJointIssue source)
    (present : issue ∈ planarFullAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel) :
    planarSourceProduce molecule source agreement writtenExact carrierFuel ruleFuel = none := by
  apply (planarSourceProduce_eq_none_iff molecule source agreement writtenExact carrierFuel
    ruleFuel).mpr
  intro empty
  rw [empty] at present
  exact List.not_mem_nil present

/-- **Refusal on a genuine two-channel disagreement**: two actual successful channels with different
labels force a nonempty full issue list and a refused transaction, at any actual candidate. -/
theorem planarSourceProduce_refuses_of_channel_disagreement (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : planarJointDrawingDescriptor? molecule source agreement writtenExact carrierFuel
      ruleFuel (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some leftLabel)
    (parser : planarJointParserDescriptor? molecule source agreement writtenExact carrierFuel
      ruleFuel (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    planarSourceProduce molecule source agreement writtenExact carrierFuel ruleFuel = none := by
  apply (planarSourceProduce_eq_none_iff molecule source agreement writtenExact carrierFuel
    ruleFuel).mpr
  exact planarFullAuditIssues_ne_nil_of_candidate_conflict molecule source agreement writtenExact
    carrierFuel ruleFuel center
    (planarJointStatus_conflict_of_channel_disagreement molecule source agreement writtenExact
      carrierFuel ruleFuel (source.aromaticCanonicalFinalOccurrence carrierFuel center) leftLabel
      rightLabel drawing parser different)



/-- In the drawing-absent domain the source-generated conflict issues are forced empty. -/
theorem planarConflictIssues_eq_nil_of_drawingAbsent (absent : DrawingAbsentEverywhere source)
    (carrierFuel ruleFuel : Nat) :
    planarConflictIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] :=
  (planarConflictIssues_eq_nil_iff molecule source agreement writtenExact carrierFuel
    ruleFuel).mpr
    (planarGlobalConflictFree_of_drawingAbsent molecule source agreement writtenExact absent
      carrierFuel ruleFuel)




theorem planarFullAuditIssues_eq_nil_of_drawingAbsent_of_partial
    (absent : DrawingAbsentEverywhere source) (carrierFuel ruleFuel : Nat)
    (partialAudit : planarPartialAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel
      = []) :
    planarFullAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] := by
  unfold planarFullAuditIssues
  rw [List.append_eq_nil_iff]
  exact ⟨planarConflictIssues_eq_nil_of_drawingAbsent molecule source agreement writtenExact absent
    carrierFuel ruleFuel, partialAudit⟩

end TetraStereo.UniversalProof.ConstructiveMixedPlanarCausalRecoveryClosureProofs.ConstructiveMixedPlanarCausalRecoveryClosure
