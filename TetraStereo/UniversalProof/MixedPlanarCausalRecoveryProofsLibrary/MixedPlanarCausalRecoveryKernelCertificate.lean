import TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofsLibrary.MixedPlanarCausalRecovery
import TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserClosureProofs.SourceNativeAnnotatedPlanarParserClosure
import TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate

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




























































/-! ## 1. Generic kernel facts about the two-element merge -/

/-- Within the two-element merge, two successes with the *same* label assign that label. -/
theorem planarMixedTwoElement_same_assigned :
    foldStatus ([some (.chiral .R), some (.chiral .R)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .assigned (.chiral .R) := by decide

/-- Within the two-element merge, opposite uppercase labels are a typed conflict. -/
theorem planarMixedTwoElement_opposite_conflict :
    foldStatus ([some (.chiral .R), some (.chiral .S)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .conflict := by decide

/-- Within the two-element merge, an upper/lower-case `chiral`/`pseudoasymmetric` mismatch is a
typed conflict; the local merge never prefers one channel over the other. -/
theorem planarMixedTwoElement_upperLowerCase_conflict :
    foldStatus ([some (.chiral .R), some (.pseudoasymmetric .r)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .conflict := by decide

/-- Within the two-element merge, an absent drawing channel beside a parser success assigns the
parser label. -/
theorem planarMixedTwoElement_absent_success :
    foldStatus ([none, some (.chiral .R)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .assigned (.chiral .R) := by decide

/-! ## 2. The actual closed annotated nine-atom alkene source -/

namespace ClosedAnnotatedPlanarWitness

abbrev annotatedSource : AuthoritativeChemicalInput :=
  TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.source

abbrev annotatedRaw : RawMolecule :=
  TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.annotatedRaw

abbrev annotatedDiagram : DiagramConfiguration :=
  TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.diagram

local instance : NeZero annotatedSource.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

noncomputable abbrev annotatedTarget : annotatedSource.AromaticCanonicalOccurrence 1 :=
  TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.target

noncomputable abbrev annotatedCenter : annotatedSource.AromaticCanonicalTetrahedralCenter :=
  TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.center

abbrev annotatedAgreement : RawAnnotationAgreement annotatedRaw annotatedSource :=
  TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.actual_annotation_agreement

abbrev annotatedWrittenExact : annotatedRaw.WrittenNeighborExact :=
  TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.actual_written_exact

/-- The actual source diagram writes only plain bonds, so its centre-0 incident records contain no
wedge. This is the concrete fact from which drawing absence is derived, not supplied. -/
theorem annotated_diagram_wedge_count_zero :
    (wedgeRecords (incidentRecords annotatedDiagram 0)).length = 0 := by decide +kernel

/-- The source recovered centre really is atom `0`. -/
theorem annotated_center_val : annotatedCenter.1.val = 0 := by decide

/-- The actual recovered centre admits no extracted drawing frame: the exactly-one-wedge admission
condition of `AdmittedDiagram` fails at the plain-bond centre. -/
theorem annotated_extract_none : extract? annotatedSource annotatedCenter.1 = none := by
  rw [extract?_eq_none_iff_not_recognized]
  rintro ⟨diagram', positions, diagramEq, _positionsEq, admitted⟩
  have diagramObserved : annotatedSource.diagram? = some annotatedDiagram := rfl
  have diagramEq' : diagram' = annotatedDiagram :=
    Option.some.inj (diagramEq.symm.trans diagramObserved)
  rw [annotated_center_val, diagramEq'] at admitted
  obtain ⟨_, _, _, _, _, _, _, _, _, wedgeCount, _⟩ := admitted
  rw [annotated_diagram_wedge_count_zero] at wedgeCount
  exact Nat.zero_ne_one wedgeCount

/-- The drawing channel is absent at the actual target for **every** dependency view, derived from
the actual plain bonds. -/
theorem annotated_drawing_absent
    (view : annotatedSource.AromaticCanonicalDependencyView annotatedTarget) :
    occurrenceOrdinaryDescriptor? annotatedSource annotatedTarget view 4 = none :=
  occurrenceOrdinaryDescriptor?_eq_none_of_recovered_extract_none annotatedSource annotatedTarget view
    4
    (fun c recovered => by
      have recovered' : annotatedSource.aromaticCanonicalOccurrenceTetrahedralCenter? annotatedTarget =
          some annotatedCenter :=
        TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.actual_recovered_center
      rw [recovered'] at recovered
      have centerEq : c = annotatedCenter := (Option.some.inj recovered).symm
      rw [centerEq]
      exact annotated_extract_none)



theorem annotated_parser_R
    (view : annotatedSource.AromaticCanonicalDependencyView annotatedTarget) :
    planarConstitutionParserRichDescriptor? annotatedRaw annotatedSource annotatedAgreement
      annotatedWrittenExact annotatedTarget view 4 = some (.chiral RS.R) :=
  TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserClosureProofs.SourceNativeAnnotatedPlanarParserClosure.actual_planar_descriptor_R
    view

/-- The recomputed NEW joint status at the closed target is `assigned R` at every view. -/
theorem annotated_jointStatus_R
    (view : annotatedSource.AromaticCanonicalDependencyView annotatedTarget) :
    planarMixedChannelStatus annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      annotatedTarget view 4 = .assigned (.chiral RS.R) := by
  unfold planarMixedChannelStatus planarMixedChannelOutputs
  rw [annotated_drawing_absent view, annotated_parser_R view]
  exact foldStatus_pair_none_some (Label := AromaticCanonicalAuxiliaryLabel) (.chiral RS.R)

/-- The NEW joint evaluator emits the planar parser's actual `R` at the closed target for every
view. The drawing channel is genuinely absent, not forced. -/
theorem annotated_jointDescriptor_R
    (view : annotatedSource.AromaticCanonicalDependencyView annotatedTarget) :
    planarMixedJointDescriptor? annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      annotatedTarget view 4 = some (.chiral RS.R) :=
  (planarMixedJointDescriptor?_eq_some_iff_status annotatedRaw annotatedSource annotatedAgreement
    annotatedWrittenExact annotatedTarget view 4 (.chiral RS.R)).mpr (annotated_jointStatus_R view)

/-- The named NEW joint assignment, with each successful channel's own independent meaning (the
drawing conjunct is vacuous here because the drawing channel is absent). -/
theorem annotated_output_meaning
    (view : annotatedSource.AromaticCanonicalDependencyView annotatedTarget) :
    PlanarMixedJointDescriptor annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      annotatedTarget view 4 (.chiral RS.R) :=
  (planarMixedJointDescriptor?_eq_some_iff_descriptor annotatedRaw annotatedSource annotatedAgreement
    annotatedWrittenExact annotatedTarget view 4 (.chiral RS.R)).mp
    (annotated_jointDescriptor_R view)

/-- The closed target's NEW joint status is never a typed conflict: the absent drawing channel
leaves only `unassigned`/`assigned`. -/
theorem annotated_no_conflict
    (view : annotatedSource.AromaticCanonicalDependencyView annotatedTarget) :
    planarMixedChannelStatus annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      annotatedTarget view 4 ≠ .conflict := by
  rw [annotated_jointStatus_R view]
  intro conflict
  cases conflict

/-- Joint success does not imply both local channels are present: the joint evaluator emits `R`
while local `PlanarMixedChannelsResolved` readiness is false because the drawing channel is absent. -/
theorem annotated_joint_success_not_resolved
    (view : annotatedSource.AromaticCanonicalDependencyView annotatedTarget) :
    planarMixedJointDescriptor? annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
        annotatedTarget view 4 = some (.chiral RS.R) ∧
      ¬ PlanarMixedChannelsResolved annotatedRaw annotatedSource annotatedAgreement
        annotatedWrittenExact annotatedTarget view 4 := by
  refine ⟨annotated_jointDescriptor_R view, ?_⟩
  intro resolved
  unfold PlanarMixedChannelsResolved at resolved
  exact resolved.1 (annotated_drawing_absent view)

/-! ### The joint scheduler over the actual closed source -/

/-- The internally scheduled NEW joint state of the actual closed source. -/
noncomputable def closedJointState : annotatedSource.AromaticCanonicalAuxiliaryState 1 :=
  planarMixedScheduledState annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact 1 4

theorem closedJointState_cipModel :
    (annotatedSource.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics annotatedRaw annotatedSource annotatedAgreement
        annotatedWrittenExact 1 4)).CIPModel closedJointState :=
  planarMixedScheduledState_cipModel annotatedRaw annotatedSource annotatedAgreement
    annotatedWrittenExact 1 4

/-- The actual internally constructed NEW joint model state assigns `R` at the closed target, from
its own model equation; no old model state or label is supplied. -/
theorem closedJointState_R : closedJointState annotatedTarget = some (.chiral RS.R) := by
  rw [← planarMixedModel_evaluates annotatedRaw annotatedSource annotatedAgreement
    annotatedWrittenExact closedJointState closedJointState_cipModel annotatedTarget]
  exact (planarMixedJointDescriptor?_eq_some_iff_status annotatedRaw annotatedSource annotatedAgreement
    annotatedWrittenExact annotatedTarget
    (annotatedSource.aromaticCanonicalDependencyView closedJointState annotatedTarget) 4
    (.chiral RS.R)).mpr (annotated_jointStatus_R
      (annotatedSource.aromaticCanonicalDependencyView closedJointState annotatedTarget))

/-- The scheduled NEW joint model output carries the named joint assignment at the closed target. -/
theorem closedJointState_R_meaning :
    PlanarMixedJointDescriptor annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      annotatedTarget
      (annotatedSource.aromaticCanonicalDependencyView closedJointState annotatedTarget) 4
      (.chiral RS.R) :=
  planarMixedModel_output_sound annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
    closedJointState closedJointState_cipModel annotatedTarget (.chiral RS.R) closedJointState_R



/-- The conversion component of the actual agreement: the source semantic molecule is the checked
parser conversion of `annotatedRaw`. -/
theorem annotated_agreement_conversion :
    annotatedRaw.toSemanticMolecule? = some annotatedSource.molecule :=
  annotatedAgreement.1


theorem annotated_agreement_record :
    RawAnnotationRecordAgreement annotatedRaw annotatedSource :=
  annotatedAgreement.2


theorem annotated_agreement_audit_nil :
    rawAnnotationAgreementIssues annotatedRaw annotatedSource = [] :=
  (rawAnnotationAgreementIssues_eq_nil_iff annotatedRaw annotatedSource).mpr annotatedAgreement.2

/-- The conversion pins the source atom-index space to the raw parser atom-index space exactly. -/
theorem annotated_agreement_index_identity (index : Nat) :
    listGet? annotatedSource.molecule.atoms index =
      (annotatedRaw.atomAt? index).bind AtomSpec.toSemanticAtom? :=
  RawAnnotationAgreement.semanticAtom_index_identity annotatedRaw annotatedSource annotatedAgreement
    index



/-- The actual raw molecule carries no directional bond record (`up`/`down`). -/
theorem annotated_no_raw_directions : rawBondDirections annotatedRaw = [] := by decide +kernel

/-- The single actual raw atom parity of the source: a clockwise carbon parity at index `0`. -/
theorem annotated_rawAtomAnnotations :
    rawAtomAnnotations annotatedRaw =
      [{ index := 0, parity := TetrahedralInputParity.clockwise }] := by decide +kernel




theorem annotated_mixedBond_accepted : MixedBondAnnotationsAccepted annotatedSource :=
  (mixedBondAuditIssues_eq_nil_iff annotatedSource).mp (by decide +kernel)

/-- The only absolute-scope annotated atom is the configuration at index `0`. -/
theorem annotated_absoluteConfigurationAtoms :
    planarAbsoluteConfigurationAtoms annotatedSource = [0] := by decide +kernel

/-- The source diagram has no solid/hashed wedge endpoint. -/
theorem annotated_no_wedgeEndpoints : planarWedgeEndpoints annotatedSource = [] := by decide +kernel

/-- The sole actual annotated source atom is index `0`. -/
theorem annotated_annotatedSourceAtoms : planarAnnotatedSourceAtoms annotatedSource = [0] := by
  unfold planarAnnotatedSourceAtoms
  rw [annotated_absoluteConfigurationAtoms, annotated_no_wedgeEndpoints]
  rfl

/-- The NEW joint parser channel at the closed target is `some R`, read at the NEW joint own view. -/
theorem annotated_jointParserDescriptor_R :
    planarJointParserDescriptor? annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      1 4 (annotatedSource.aromaticCanonicalFinalOccurrence 1 annotatedCenter) =
        some (.chiral RS.R) := by
  unfold planarJointParserDescriptor?
  exact annotated_parser_R (planarJointView annotatedRaw annotatedSource annotatedAgreement
    annotatedWrittenExact 1 4 annotatedTarget)

/-- The NEW joint drawing channel at the closed target is absent, read at the NEW joint own view. -/
theorem annotated_jointDrawingDescriptor_none :
    planarJointDrawingDescriptor? annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      1 4 (annotatedSource.aromaticCanonicalFinalOccurrence 1 annotatedCenter) = none := by
  unfold planarJointDrawingDescriptor?
  exact annotated_drawing_absent (planarJointView annotatedRaw annotatedSource annotatedAgreement
    annotatedWrittenExact 1 4 annotatedTarget)

/-- The NEW joint status at the closed target, at the NEW joint own view, is `assigned R`. -/
theorem annotated_jointOwnStatus_R :
    planarJointStatus annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact 1 4
      (annotatedSource.aromaticCanonicalFinalOccurrence 1 annotatedCenter) =
        .assigned (.chiral RS.R) := by
  rw [planarJointStatus_eq_fold, annotated_jointDrawingDescriptor_none,
    annotated_jointParserDescriptor_R]
  exact foldStatus_pair_none_some (Label := AromaticCanonicalAuxiliaryLabel) (.chiral RS.R)

/-- **Annotated drawing-centre coverage at index `0`**: the actual recovered candidate covers the
sole absolute configuration, its relevant planar parser channel is interpreted, and its NEW joint
status is assigned. -/
theorem annotated_annotatedCenter_interpreted_zero :
    PlanarAnnotatedCenterInterpreted annotatedRaw annotatedSource annotatedAgreement
      annotatedWrittenExact 1 4 0 := by
  refine ⟨annotatedCenter, ?_, ?_, ?_, ?_⟩
  · unfold planarCandidatesAt
    rw [List.mem_filter]
    exact ⟨(mem_aromaticCanonicalTetrahedralCenters_iff annotatedSource annotatedCenter).mpr
      annotatedCenter.2, beq_iff_eq.mpr annotated_center_val⟩
  · exact Or.inl (by rw [annotated_no_wedgeEndpoints]; simp)
  · exact Or.inr (by
      intro absent
      rw [annotated_jointParserDescriptor_R] at absent
      exact absurd absent (by simp))
  · exact ⟨.chiral RS.R, annotated_jointOwnStatus_R⟩



theorem annotated_annotatedCenter_coverage (atomIndex : Nat)
    (present : atomIndex ∈ planarAnnotatedSourceAtoms annotatedSource) :
    PlanarAnnotatedCenterInterpreted annotatedRaw annotatedSource annotatedAgreement
      annotatedWrittenExact 1 4 atomIndex := by
  rw [annotated_annotatedSourceAtoms, List.mem_singleton] at present
  rw [present]
  exact annotated_annotatedCenter_interpreted_zero

/-- The conversion-pinned raw index of the actual recovered centre is numerically `0`. -/
theorem annotated_raw_index :
    (parserIndexViaConversion annotatedRaw annotatedSource annotatedAgreement.1 annotatedCenter).val = 0 := by
  rw [TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.parserIndexViaConversion_val
      annotatedRaw annotatedSource annotatedAgreement.1 annotatedCenter]
  exact annotated_center_val

/-- The actual raw specification at parser index `0`: the copied clockwise carbon parity. -/
theorem annotated_rawAtom_zero :
    annotatedRaw.atomAt? 0 =
      some { AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise } :=
  rfl

/-- **Raw-parity interpretation at the NEW joint own views**: the sole actual raw parity record is
interpreted by the actual planar parser channel through the conversion-pinned index. -/
theorem annotated_rawParity_interpreted (annotation : RawAtomAnnotation)
    (present : annotation ∈ rawAtomAnnotations annotatedRaw) :
    PlanarRawParityJointInterpretation annotatedRaw annotatedSource annotatedAgreement
      annotatedWrittenExact 1 4 annotation := by
  rw [annotated_rawAtomAnnotations, List.mem_singleton] at present
  rw [present]
  refine planarRawParityJointInterpretation_of_candidate annotatedRaw annotatedSource
    annotatedAgreement annotatedWrittenExact 1 4
    { index := 0, parity := TetrahedralInputParity.clockwise } annotatedCenter
    annotated_raw_index ?_ (.chiral RS.R) annotated_jointParserDescriptor_R
  exact ⟨{ AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise },
    by simpa only [annotated_raw_index] using annotated_rawAtom_zero, rfl⟩






theorem annotated_partialAudit :
    PlanarJointPartialAudit annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact 1 4 :=
  ⟨annotated_rawParity_interpreted, annotated_no_raw_directions, annotated_mixedBond_accepted,
    annotated_annotatedCenter_coverage⟩

end ClosedAnnotatedPlanarWitness

end TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate

/-! Trust checks for the generic NEW joint causal/conflict proofs and all closed witnesses above. -/

assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedJointDescriptor?_eq_some_iff_status
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedJointDescriptor?_eq_none_iff_status
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedJointDescriptor?_eq_some_iff_descriptor
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedConflictDiagnostic_witness
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedConflictDiagnostic_nonassignment
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedChannelStatus_conflict_of_actual_disagreement
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedOutcome_iff
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.existsUnique_planarMixedCIPModel
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedScheduledState_cipModel
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedModel_evaluates
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedModel_unique
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedModel_output_sound
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedModel_conflict_nonassignment
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarMixedModel_finalCenter_conflict_nonassignment
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarGlobalConflictIssues_eq_nil_iff
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel.planarRawParityJointInterpretation_of_candidate
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.planarMixedTwoElement_upperLowerCase_conflict
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_diagram_wedge_count_zero
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_extract_none
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_drawing_absent
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_jointStatus_R
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_jointDescriptor_R
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_output_meaning
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_no_conflict
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_joint_success_not_resolved
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.closedJointState_cipModel
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.closedJointState_R
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.closedJointState_R_meaning
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_agreement_conversion
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_agreement_record
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_agreement_audit_nil
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_agreement_index_identity
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_no_raw_directions
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_rawAtomAnnotations
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_mixedBond_accepted
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_absoluteConfigurationAtoms
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_no_wedgeEndpoints
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_annotatedSourceAtoms
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_jointParserDescriptor_R
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_jointDrawingDescriptor_none
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_jointOwnStatus_R
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_annotatedCenter_interpreted_zero
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_annotatedCenter_coverage
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_raw_index
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_rawAtom_zero
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_rawParity_interpreted
assert_kernel_only TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness.annotated_partialAudit
