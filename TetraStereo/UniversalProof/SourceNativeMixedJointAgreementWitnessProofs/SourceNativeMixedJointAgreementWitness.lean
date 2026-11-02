import TetraStereo.UniversalProof.SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness
import TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
import TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace TetraStereo.UniversalProof.SourceNativeMixedJointAgreementWitnessProofs.SourceNativeMixedJointAgreementWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.RationalTetrahedralPermutation
open TetraStereo.OneCenter.Rule6HandednessSemantics
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness

open SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
open SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit



























abbrev agreeingDiagram : DiagramConfiguration :=
  { SingleWedgeSourceRegression.diagram with
    atomConfigurations := annotatedRawCF.toDiagramConfiguration.atomConfigurations }

/-- The actual complete solid-wedge source with the actual clockwise raw annotation and no spatial
channel. -/
abbrev agreeingSource : AuthoritativeChemicalInput :=
  { SingleWedgeSourceRegression.source with diagram? := some agreeingDiagram }

theorem agreeingSource_conversion :
    annotatedRawCF.toSemanticMolecule? = some agreeingSource.molecule := by
  show annotatedRawCF.toSemanticMolecule? = some SingleWedgeSourceRegression.molecule
  exact annotatedRawCF_toSemanticMolecule

theorem agreeingSource_recordAudit : rawAnnotationAgreementIssues annotatedRawCF agreeingSource = [] := by
  decide +kernel

theorem agreeingSource_annotationAgreement : RawAnnotationAgreement annotatedRawCF agreeingSource :=
  ⟨agreeingSource_conversion,
    (rawAnnotationAgreementIssues_eq_nil_iff annotatedRawCF agreeingSource).mp
      agreeingSource_recordAudit⟩

theorem agreeingSource_not_authoritative :
    ¬ annotatedRawCF.AuthoritativeStructureAgreement agreeingSource := by
  intro agreement
  have same : some agreeingDiagram = some annotatedRawCF.toDiagramConfiguration := agreement.2
  have distinct : agreeingDiagram ≠ annotatedRawCF.toDiagramConfiguration := by decide +kernel
  exact distinct (Option.some.inj same)





theorem agreeingSource_preliminary_audit_clean : mixedBondAuditIssues agreeingSource = [] := by
  decide +kernel

/-! ## 2. The source's own center, target, roots, frame and priorities -/

/-- The connectivity-only tetrahedral candidate of the agreeing source is the committed carbon center. -/
def agreeingCenter : agreeingSource.AromaticCanonicalTetrahedralCenter :=
  SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter

/-- The final occurrence target of the agreeing source at carrier zero. -/
noncomputable def agreeingTarget : agreeingSource.AromaticCanonicalOccurrence 0 :=
  agreeingSource.aromaticCanonicalFinalOccurrence 0 agreeingCenter

/-- The actual returned reroot roots of the agreeing source, in carrier order. -/
noncomputable def agreeingRoots : List (agreeingSource.AromaticCanonicalRerootCursor 0) :=
  finalOccurrenceRoots agreeingSource 0 agreeingCenter

/-- The actual returned root list has four cursors. -/
theorem agreeingRoots_length : agreeingRoots.length = 4 := by rfl

/-- The source-indexed four-ligand frame built from the actual returned roots. -/
noncomputable def agreeingFrame : agreeingSource.AromaticCanonicalOccurrenceFourLigandFrame 0 :=
  { roots := agreeingRoots, rootsLength := agreeingRoots_length }

/-- The returned occurrence ligand frame is literally the reconstructed root list. -/
theorem agreeingTarget_roots_returned :
    agreeingSource.aromaticCanonicalOccurrenceLigandFrame? agreeingTarget = some agreeingFrame.roots :=
  finalOccurrenceRoots_are_returned agreeingSource 0 agreeingCenter

/-- The conversion pinned into `agreeingSource_annotationAgreement` is exactly `agreeingSource_conversion`. -/
theorem agreeingSource_annotationAgreement_fst :
    agreeingSource_annotationAgreement.1 = agreeingSource_conversion := rfl

/-- The conversion-only parser index of the actual center is raw index `0`. -/
theorem agreeingSource_index_identity :
    (parserIndexViaConversion annotatedRawCF agreeingSource agreeingSource_conversion agreeingCenter).val =
      0 := rfl

/-- The identity raw written alignment: the actual raw written frame at the agreeing center is the
literal written order `[1, 2, 3, 4]`, read through `parserIndexViaConversion`. -/
theorem agreeingSource_raw_frame :
    rawWrittenLigandFrame annotatedRawCF
      (parserIndexViaConversion annotatedRawCF agreeingSource agreeingSource_conversion agreeingCenter) =
      [1, 2, 3, 4] := by
  unfold rawWrittenLigandFrame
  rw [agreeingSource_index_identity]
  exact parserSource_written_endpoints

/-- The actual returned root IDs of the agreeing source are `[1, 2, 3, 4]`. -/
theorem agreeingSource_root_ids :
    occurrenceRootIDs agreeingSource agreeingRoots = [some 1, some 2, some 3, some 4] := by rfl

/-- The finite source-ID alignment of the actual written frame against the actual returned IDs is
the identity slot list. -/
theorem agreeingSource_slot_alignment :
    findSlotAlignment?
      (rawWrittenLigandFrame annotatedRawCF
        (parserIndexViaConversion annotatedRawCF agreeingSource agreeingSource_conversion agreeingCenter))
      (occurrenceRootIDs agreeingSource agreeingRoots) = some [0, 1, 2, 3] := by
  rw [agreeingSource_raw_frame, agreeingSource_root_ids]
  decide +kernel

/-- Every actual returned cursor is a real source-neighbour root with real provenance. -/
theorem agreeingRoots_real : OccurrenceRootsReal agreeingSource agreeingFrame := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

/-- The concrete atomic priorities of the actual returned cursors `F, Cl, Br, I`. -/
def agreeingAtomicPriorityValue : Fin 4 → Nat
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 35
  | ⟨3, _⟩ => 53

/-- The actual source-indexed atomic priorities are exactly `9/17/35/53`. -/
theorem agreeing_actual_atomic_priority (slot : Fin 4) :
    occurrenceAtomicPriority agreeingSource agreeingFrame slot = agreeingAtomicPriorityValue slot := by
  fin_cases slot <;> rfl

/-- The actual source-indexed atomic priorities are injective. -/
theorem agreeing_actual_atomic_priority_injective :
    Function.Injective (occurrenceAtomicPriority agreeingSource agreeingFrame) := by
  have injective : Function.Injective agreeingAtomicPriorityValue := by decide +kernel
  intro left right equal
  apply injective
  simpa only [agreeing_actual_atomic_priority] using equal

/-- Independently descending priority permutations are uniquely `[3, 2, 1, 0]`; no arbitrary tracked
record is quantified over. -/
theorem agreeing_actual_priority_order_unique (order : List (Fin 4))
    (perm : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right =>
      occurrenceAtomicPriority agreeingSource agreeingFrame right <
        occurrenceAtomicPriority agreeingSource agreeingFrame left)) :
    order = [3, 2, 1, 0] := by
  have reversedPerm : ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by decide +kernel
  have reversedDescending : ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      occurrenceAtomicPriority agreeingSource agreeingFrame right <
        occurrenceAtomicPriority agreeingSource agreeingFrame left) := by
    simp only [agreeing_actual_atomic_priority]
    decide +kernel
  exact (perm.trans reversedPerm.symm).eq_of_pairwise
    (fun _ _ _ _ higher reverse => False.elim (Nat.lt_asymm higher reverse))
    descending reversedDescending

/-- The agreeing source has no ordinary canonical double bond; its molecule is the committed CFClBrI
constitution. -/
theorem agreeingSource_no_ordinary_double_bond :
    agreeingSource.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : agreeingSource.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

/-! ## 3. The constitution parser channel emits R for every actual view -/

/-- The actual constitution parser channel emits `R` for every dependency view of the agreeing source,
from the actual production key/sort, strict priority uniqueness and the actual written order. -/
theorem agreeingSource_parser_descriptor_R
    (view : agreeingSource.AromaticCanonicalDependencyView agreeingTarget) :
    constitutionParserRichDescriptor? annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact agreeingTarget view 2 = some (.chiral RS.R) := by
  obtain ⟨keys, tracked, keysComputed, trackedComputed, perm, descending, zero⟩ :=
    exists_occurrence_production_keys_and_safe_order agreeingSource agreeingTarget view agreeingFrame
      agreeingTarget_roots_returned agreeingRoots_real agreeing_actual_atomic_priority_injective
      agreeingSource_no_ordinary_double_bond
  have keysComputed2 : agreeingSource.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      agreeingTarget view 2 agreeingRoots = some keys := keysComputed
  have orderEq := agreeing_actual_priority_order_unique tracked.highestFirst perm descending
  have writtenOrder : tracked.highestFirst.map
      (fun position => ([0, 1, 2, 3] : List Nat).getD position.val 0) = [3, 2, 1, 0] := by
    rw [orderEq]
    rfl
  have rawEq := writtenFramePriorityDescriptor_clockwise_reverse [0, 1, 2, 3]
    tracked.highestFirst writtenOrder
  have recovered : agreeingSource.aromaticCanonicalOccurrenceTetrahedralCenter? agreeingTarget =
      some agreeingCenter := occurrenceTetrahedralCenter?_final agreeingSource 0 agreeingCenter
  have evidenceComputed : constitutionParserRichPriorityEvidence? annotatedRawCF agreeingSource
      agreeingSource_annotationAgreement parserSource_writtenExact agreeingTarget view 2 =
      some
        ({ slots := [0, 1, 2, 3]
           keys := keys
           tracked := tracked
           writtenParity := .clockwise
           raw := RS.R } : ParserRichPriorityEvidence agreeingSource 0) := by
    simp [constitutionParserRichPriorityEvidence?, recovered,
      agreeingSource_index_identity, parserSource_atom, agreeingTarget_roots_returned, agreeingFrame,
      agreeingSource_slot_alignment, keysComputed2, trackedComputed, rawEq]
  simp [constitutionParserRichDescriptor?, evidenceComputed, zero, classifyTetrahedralRSPseudo_zero]

/-! ## Actual complete solid-wedge drawing -/

/-- The actual complete solid-wedge drawing frame, extracted from the agreeing source's own complete
diagram (three plain bonds and the solid wedge at iodine). -/
def agreeingDrawing : SingleWedgeSource.Frame :=
  frameOfDiagram agreeingCenter.1.val agreeingDiagram SingleWedgeSourceRegression.positions

/-- The complete wedge is an actual bound source frame of the agreeing source. -/
theorem agreeingSource_frame_bound : SourceFrame agreeingSource agreeingCenter.1.val agreeingDrawing :=
  ⟨agreeingDiagram, SingleWedgeSourceRegression.positions, rfl, rfl, by decide +kernel, rfl⟩

/-- First-shell atomic numbers of the actual CFClBrI source are injective. -/
theorem agreeingSource_atomZ_injective :
    Function.Injective agreeingSource.molecule.toLocalizedMoleculeGraph.atomZ := by
  intro left right
  fin_cases left <;> fin_cases right <;> decide +kernel

/-- Actual drawing endpoint atomic separation for the agreeing source. -/
theorem agreeingSource_separation (drawing : SingleWedgeSource.Frame) :
    SourceEndpointAtomicSeparation agreeingSource drawing := by
  intro left right _leftPresent _rightPresent sameAtomicNumber
  exact agreeingSource_atomZ_injective sameAtomicNumber

/-- The reverse written priority permutation is a permutation of the four slots. -/
theorem agreeingSource_descending_slots_perm :
    ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by decide

/-- The actual written priorities descend in the reverse written order. -/
theorem agreeingSource_written_descending :
    ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      writtenAtomicPriority agreeingSource agreeingDrawing right <
        writtenAtomicPriority agreeingSource agreeingDrawing left) := by
  decide +kernel

/-- The actual nondegenerate solid-wedge geometry (reverse-order oriented volume `-3`) classifies
the reverse written order as `R` under the calibrated sign convention. -/
theorem agreeingSource_sorted_geometry :
    descriptorOfPriorityOrderedPoints?
      (([3, 2, 1, 0] : List (Fin 4)).map
        (pointVector agreeingDrawing.first agreeingDrawing.second agreeingDrawing.third agreeingDrawing.fourth)) =
      some RS.R := by
  decide +kernel

/-- The drawing-only empty-auxiliary descriptor of the complete solid wedge is `R`, through the
generic exact priority theorem (a guide, not cross-source label equality). -/
theorem agreeingSource_empty_descriptor_R :
    ordinaryEmptyAuxiliaryDescriptor? agreeingSource 0 2 agreeingCenter = some (.chiral RS.R) :=
  ordinaryDescriptor?_eq_chiral_of_zero_carrier_written_priority
    agreeingSource agreeingCenter
    (agreeingSource.aromaticCanonicalDependencyView (fun _ => none)
      (agreeingSource.aromaticCanonicalFinalOccurrence 0 agreeingCenter))
    agreeingDrawing agreeingSource_frame_bound (agreeingSource_separation agreeingDrawing)
    [3, 2, 1, 0] agreeingSource_descending_slots_perm agreeingSource_written_descending RS.R
    agreeingSource_sorted_geometry

/-- The drawing channel emits `R` for every actual view of the same source and target. -/
theorem agreeingSource_drawing_R
    (view : agreeingSource.AromaticCanonicalDependencyView agreeingTarget) :
    occurrenceOrdinaryDescriptor? agreeingSource agreeingTarget view 2 = some (.chiral RS.R) := by
  change occurrenceOrdinaryDescriptor? agreeingSource
      (agreeingSource.aromaticCanonicalFinalOccurrence 0 agreeingCenter) view 2 = some (.chiral RS.R)
  rw [occurrenceOrdinaryDescriptor?_final_eq]
  rw [ordinaryDescriptor?_eq_empty_auxiliary_zero_carrier agreeingSource agreeingCenter agreeingDrawing
    agreeingSource_frame_bound (agreeingSource_separation agreeingDrawing) view]
  exact agreeingSource_empty_descriptor_R

/-! ## One actual joint scheduler and its own dependency view -/

noncomputable def jointSemantics : agreeingSource.AromaticCanonicalRuleSemantics 0 :=
  mixedAuxiliarySemantics annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact 0 2

noncomputable def jointScheduledState : agreeingSource.AromaticCanonicalAuxiliaryState 0 :=
  mixedScheduledState annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact 0 2

noncomputable def jointView : agreeingSource.AromaticCanonicalDependencyView agreeingTarget :=
  agreeingSource.aromaticCanonicalDependencyView jointScheduledState agreeingTarget

theorem joint_model_exists_unique :
    ∃! state, (agreeingSource.aromaticCanonicalOccurrenceSystem jointSemantics).CIPModel state :=
  existsUnique_mixedCIPModel annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact 0 2

theorem jointScheduledState_cipModel :
    (agreeingSource.aromaticCanonicalOccurrenceSystem jointSemantics).CIPModel jointScheduledState :=
  mixedScheduledState_cipModel annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact 0 2

theorem joint_model_unique (state : agreeingSource.AromaticCanonicalAuxiliaryState 0)
    (model : (agreeingSource.aromaticCanonicalOccurrenceSystem jointSemantics).CIPModel state) :
    state = jointScheduledState :=
  mixedModel_unique annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact 0 2 state model

theorem joint_status_assigned_R :
    mixedChannelStatus annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact agreeingTarget jointView 2 = .assigned (.chiral RS.R) := by
  unfold mixedChannelStatus mixedChannelOutputs
  rw [agreeingSource_drawing_R jointView, agreeingSource_parser_descriptor_R jointView]
  exact foldStatus_pair_some_same (Label := AromaticCanonicalAuxiliaryLabel) (.chiral RS.R)

theorem localMixedChannelsResolved :
    MixedChannelsResolved annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact agreeingTarget jointView 2 := by
  unfold MixedChannelsResolved
  rw [agreeingSource_drawing_R jointView, agreeingSource_parser_descriptor_R jointView]
  simp

theorem joint_scheduled_R : jointScheduledState agreeingTarget = some (.chiral RS.R) := by
  rw [← mixedModel_evaluates annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact jointScheduledState jointScheduledState_cipModel agreeingTarget]
  exact (mixedJointDescriptor?_eq_some_iff_status annotatedRawCF agreeingSource
    agreeingSource_annotationAgreement parserSource_writtenExact agreeingTarget jointView 2
    (.chiral RS.R)).mpr joint_status_assigned_R

theorem both_independent_meanings_at_joint_view :
    CanonicalConstitutionParserRichDescriptor annotatedRawCF agreeingSource
        agreeingSource_annotationAgreement parserSource_writtenExact agreeingTarget jointView 2
        (.chiral RS.R) ∧
      CanonicalOccurrenceOrdinaryDescriptor agreeingSource agreeingTarget jointView 2 (.chiral RS.R) :=
  ⟨(constitutionParserRichDescriptor?_eq_some_iff_canonical annotatedRawCF agreeingSource
      agreeingSource_annotationAgreement parserSource_writtenExact agreeingTarget jointView 2
      (.chiral RS.R)).mp (agreeingSource_parser_descriptor_R jointView),
   (occurrenceOrdinaryDescriptor?_eq_some_iff_canonical agreeingSource agreeingTarget jointView 2
      (.chiral RS.R)).mp (agreeingSource_drawing_R jointView)⟩

theorem joint_scheduled_meaning :
    MixedJointDescriptor annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact agreeingTarget jointView 2 (.chiral RS.R) :=
  mixedModel_output_sound annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact jointScheduledState jointScheduledState_cipModel agreeingTarget
    (.chiral RS.R) joint_scheduled_R

end TetraStereo.UniversalProof.SourceNativeMixedJointAgreementWitnessProofs.SourceNativeMixedJointAgreementWitness
