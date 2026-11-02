import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
import TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
import TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
import TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
import TetraStereo.OneCenter.AuthoritativeSingleWedgeExactPriorityDescriptor
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceDescriptor

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace TetraStereo.UniversalProof.SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness

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

















































/-! ## 1. The actual complete source -/

/-- The complete CFClBrI drawing with the actual raw annotation records from the normalized parser
molecule.  Bonds and positions are the committed complete single-wedge diagram with the hashed
glyph; `atomConfigurations` is the literal `annotatedRawCF` raw annotation materialization
(absolute scope by default). -/
def newDiagram : DiagramConfiguration :=
  { SingleWedgeSourceRegression.diagramWithStyle .hashedWedge with
    atomConfigurations := annotatedRawCF.toDiagramConfiguration.atomConfigurations }

/-- The new source: the committed semantic molecule, no spatial channel, and the complete diagram
carrying the actual raw absolute annotation record. -/
def newSource : AuthoritativeChemicalInput :=
  { molecule := SingleWedgeSourceRegression.molecule
    spatial? := none
    diagram? := some newDiagram }

/-- The new source has no spatial channel. -/
theorem newSource_spatial_none : newSource.spatial? = none := rfl

/-- The new source diagram is exactly the complete `newDiagram`. -/
theorem newSource_diagram : newSource.diagram? = some newDiagram := rfl

/-- The actual raw carbon annotation is an absolute configuration record of the new source's own
diagram, not of a parser-materialized diagram. -/
theorem newSource_diagram_contains_annotation :
    ({ atom := 0, parity := TetrahedralInputParity.clockwise } : DiagramAtomConfiguration) ∈
      newDiagram.atomConfigurations := by
  decide +kernel

/-- The checked semantic conversion of the actual normalized raw molecule lands on the new source. -/
theorem newSource_conversion :
    annotatedRawCF.toSemanticMolecule? = some newSource.molecule := by
  show annotatedRawCF.toSemanticMolecule? = some SingleWedgeSourceRegression.molecule
  exact annotatedRawCF_toSemanticMolecule


theorem newSource_recordAudit :
    rawAnnotationAgreementIssues annotatedRawCF newSource = [] := by
  decide +kernel

/-- The bidirectional raw annotation records agree on the actual complete source. -/
theorem newSource_recordAgreement :
    RawAnnotationRecordAgreement annotatedRawCF newSource :=
  (rawAnnotationAgreementIssues_eq_nil_iff annotatedRawCF newSource).mp newSource_recordAudit



theorem newSource_annotationAgreement :
    RawAnnotationAgreement annotatedRawCF newSource :=
  ⟨newSource_conversion, newSource_recordAgreement⟩

/-- The complete drawing genuinely fails whole `AuthoritativeStructureAgreement`: the actual
annotation records agree, but the complete wedge geometry is not parser materialization. -/
theorem newSource_not_authoritative :
    ¬ annotatedRawCF.AuthoritativeStructureAgreement newSource := by
  intro agreement
  have same : some newDiagram = some annotatedRawCF.toDiagramConfiguration := agreement.2
  have distinct : newDiagram ≠ annotatedRawCF.toDiagramConfiguration := by decide +kernel
  exact distinct (Option.some.inj same)

/-- The two agreements are separated on the same actual source: record agreement holds, whole
diagram equality fails. -/
theorem newSource_agreementSeparation :
    RawAnnotationAgreement annotatedRawCF newSource ∧
      ¬ annotatedRawCF.AuthoritativeStructureAgreement newSource :=
  ⟨newSource_annotationAgreement, newSource_not_authoritative⟩

/-! ## 2. The source's own center, target, roots, frame and priorities -/

/-- The perceived tetrahedral center of the new source is the committed carbon center. -/
def newCenter : newSource.AromaticCanonicalTetrahedralCenter :=
  SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter

/-- The final occurrence target of the new source at carrier zero. -/
noncomputable def newTarget : newSource.AromaticCanonicalOccurrence 0 :=
  newSource.aromaticCanonicalFinalOccurrence 0 newCenter

/-- The actual returned reroot roots of the new source, in carrier order. -/
noncomputable def newRoots : List (newSource.AromaticCanonicalRerootCursor 0) :=
  finalOccurrenceRoots newSource 0 newCenter

/-- The actual returned root list has four cursors. -/
theorem newRoots_length : newRoots.length = 4 := by rfl

/-- The source-indexed four-ligand frame built from the actual returned roots. -/
noncomputable def newFrame : newSource.AromaticCanonicalOccurrenceFourLigandFrame 0 :=
  { roots := newRoots, rootsLength := newRoots_length }

/-- The returned occurrence ligand frame is literally the reconstructed root list. -/
theorem newTarget_roots_returned :
    newSource.aromaticCanonicalOccurrenceLigandFrame? newTarget = some newFrame.roots :=
  finalOccurrenceRoots_are_returned newSource 0 newCenter

/-- The conversion pinned into `newSource_annotationAgreement` is exactly `newSource_conversion`. -/
theorem newSource_annotationAgreement_fst :
    newSource_annotationAgreement.1 = newSource_conversion := rfl

/-- The conversion-only parser index of the actual center is raw index `0`. -/
theorem newSource_index_identity :
    (parserIndexViaConversion annotatedRawCF newSource newSource_conversion newCenter).val =
      0 := rfl

/-- The identity raw written alignment: the actual raw written frame at the new center is the
literal written order `[1, 2, 3, 4]`, read through `parserIndexViaConversion`. -/
theorem newSource_raw_frame :
    rawWrittenLigandFrame annotatedRawCF
      (parserIndexViaConversion annotatedRawCF newSource newSource_conversion newCenter) =
      [1, 2, 3, 4] := by
  unfold rawWrittenLigandFrame
  rw [newSource_index_identity]
  exact parserSource_written_endpoints

/-- The actual returned root IDs of the new source are `[1, 2, 3, 4]`. -/
theorem newSource_root_ids :
    occurrenceRootIDs newSource newRoots = [some 1, some 2, some 3, some 4] := by rfl

/-- The finite source-ID alignment of the actual written frame against the actual returned IDs is
the identity slot list. -/
theorem newSource_slot_alignment :
    findSlotAlignment?
      (rawWrittenLigandFrame annotatedRawCF
        (parserIndexViaConversion annotatedRawCF newSource newSource_conversion newCenter))
      (occurrenceRootIDs newSource newRoots) = some [0, 1, 2, 3] := by
  rw [newSource_raw_frame, newSource_root_ids]
  decide +kernel

/-- Every actual returned cursor is a real source-neighbour root with real provenance. -/
theorem newRoots_real : OccurrenceRootsReal newSource newFrame := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

/-- The concrete atomic priorities of the actual returned cursors `F, Cl, Br, I`. -/
def newAtomicPriorityValue : Fin 4 → Nat
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 35
  | ⟨3, _⟩ => 53

/-- The actual source-indexed atomic priorities are exactly `9/17/35/53`. -/
theorem new_actual_atomic_priority (slot : Fin 4) :
    occurrenceAtomicPriority newSource newFrame slot = newAtomicPriorityValue slot := by
  fin_cases slot <;> rfl

/-- The actual source-indexed atomic priorities are injective. -/
theorem new_actual_atomic_priority_injective :
    Function.Injective (occurrenceAtomicPriority newSource newFrame) := by
  have injective : Function.Injective newAtomicPriorityValue := by decide +kernel
  intro left right equal
  apply injective
  simpa only [new_actual_atomic_priority] using equal

/-- Independently descending priority permutations are uniquely `[3, 2, 1, 0]`; no arbitrary tracked
record is quantified over. -/
theorem new_actual_priority_order_unique (order : List (Fin 4))
    (perm : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right =>
      occurrenceAtomicPriority newSource newFrame right <
        occurrenceAtomicPriority newSource newFrame left)) :
    order = [3, 2, 1, 0] := by
  have reversedPerm : ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by decide +kernel
  have reversedDescending : ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      occurrenceAtomicPriority newSource newFrame right <
        occurrenceAtomicPriority newSource newFrame left) := by
    simp only [new_actual_atomic_priority]
    decide +kernel
  exact (perm.trans reversedPerm.symm).eq_of_pairwise
    (fun _ _ _ _ higher reverse => False.elim (Nat.lt_asymm higher reverse))
    descending reversedDescending

/-- The new source has no ordinary canonical double bond; its molecule is the committed CFClBrI
constitution. -/
theorem newSource_no_ordinary_double_bond :
    newSource.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : newSource.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

/-! ## 3. The constitution parser channel emits R for every actual view -/

/-- The actual constitution parser channel emits `R` for every dependency view of the new source,
from the actual production key/sort, strict priority uniqueness and the actual written order. -/
theorem newSource_parser_descriptor_R
    (view : newSource.AromaticCanonicalDependencyView newTarget) :
    constitutionParserRichDescriptor? annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget view 2 = some (.chiral RS.R) := by
  obtain ⟨keys, tracked, keysComputed, trackedComputed, perm, descending, zero⟩ :=
    exists_occurrence_production_keys_and_safe_order newSource newTarget view newFrame
      newTarget_roots_returned newRoots_real new_actual_atomic_priority_injective
      newSource_no_ordinary_double_bond
  have keysComputed2 : newSource.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      newTarget view 2 newRoots = some keys := keysComputed
  have orderEq := new_actual_priority_order_unique tracked.highestFirst perm descending
  have writtenOrder : tracked.highestFirst.map
      (fun position => ([0, 1, 2, 3] : List Nat).getD position.val 0) = [3, 2, 1, 0] := by
    rw [orderEq]
    rfl
  have rawEq := writtenFramePriorityDescriptor_clockwise_reverse [0, 1, 2, 3]
    tracked.highestFirst writtenOrder
  have recovered : newSource.aromaticCanonicalOccurrenceTetrahedralCenter? newTarget =
      some newCenter := occurrenceTetrahedralCenter?_final newSource 0 newCenter
  have evidenceComputed : constitutionParserRichPriorityEvidence? annotatedRawCF newSource
      newSource_annotationAgreement parserSource_writtenExact newTarget view 2 =
      some
        ({ slots := [0, 1, 2, 3]
           keys := keys
           tracked := tracked
           writtenParity := .clockwise
           raw := RS.R } : ParserRichPriorityEvidence newSource 0) := by
    simp [constitutionParserRichPriorityEvidence?, recovered,
      newSource_index_identity, parserSource_atom, newTarget_roots_returned, newFrame,
      newSource_slot_alignment, keysComputed2, trackedComputed, rawEq]
  simp [constitutionParserRichDescriptor?, evidenceComputed, zero, classifyTetrahedralRSPseudo_zero]

/-! ## 4. The source's own scheduled constitution model -/

/-- The internally scheduled constitution auxiliary semantics of the actual source. -/
noncomputable def newSemantics : newSource.AromaticCanonicalRuleSemantics 0 :=
  constitutionParserRichAuxiliarySemantics annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact 0 2

/-- The internally scheduled constitution state of the actual source. -/
noncomputable def newScheduledState : newSource.AromaticCanonicalAuxiliaryState 0 :=
  constitutionParserRichScheduledState annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact 0 2

/-- The scheduled constitution state is a fixed point of the source's own occurrence system. -/
theorem newScheduledState_cipModel :
    (newSource.aromaticCanonicalOccurrenceSystem newSemantics).CIPModel newScheduledState :=
  constitutionParserRichScheduledState_cipModel annotatedRawCF newSource
    newSource_annotationAgreement parserSource_writtenExact 0 2

/-- The single scheduled dependency view shared by the parser and drawing channels. -/
noncomputable def newScheduledView : newSource.AromaticCanonicalDependencyView newTarget :=
  newSource.aromaticCanonicalDependencyView newScheduledState newTarget

/-- The actual internally constructed scheduled constitution state assigns `R` at the actual
target, from its own model equation; no old model state or label is supplied. -/
theorem newScheduled_R : newScheduledState newTarget = some (.chiral RS.R) := by
  rw [← constitutionParserRichModel_evaluates annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact newScheduledState newScheduledState_cipModel newTarget]
  exact newSource_parser_descriptor_R _

/-- The scheduled `R` retains the independent constitution rich meaning. -/
theorem newScheduled_R_meaning :
    ConstitutionParserRichDescriptorMeaning annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget newScheduledView 2 (.chiral RS.R) :=
  constitutionParserRichModel_output_sound annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact newScheduledState newScheduledState_cipModel newTarget (.chiral RS.R)
    newScheduled_R

/-! ## 5. The drawing channel emits S on the same source/target/view -/

/-- The actual complete hashed-wedge drawing frame, extracted from the new source's own complete
diagram (three plain bonds and the hashed wedge at iodine). -/
def newDrawing : SingleWedgeSource.Frame :=
  frameOfDiagram newCenter.1.val newDiagram SingleWedgeSourceRegression.positions

/-- The complete wedge is an actual bound source frame of the new source. -/
theorem newSource_frame_bound : SourceFrame newSource newCenter.1.val newDrawing :=
  ⟨newDiagram, SingleWedgeSourceRegression.positions, rfl, rfl, by decide +kernel, rfl⟩

/-- First-shell atomic numbers of the actual CFClBrI source are injective. -/
theorem newSource_atomZ_injective :
    Function.Injective newSource.molecule.toLocalizedMoleculeGraph.atomZ := by
  intro left right
  fin_cases left <;> fin_cases right <;> decide +kernel

/-- Actual drawing endpoint atomic separation for the new source. -/
theorem newSource_separation (drawing : SingleWedgeSource.Frame) :
    SourceEndpointAtomicSeparation newSource drawing := by
  intro left right _leftPresent _rightPresent sameAtomicNumber
  exact newSource_atomZ_injective sameAtomicNumber

/-- The reverse written priority permutation is a permutation of the four slots. -/
theorem newSource_descending_slots_perm :
    ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by decide

/-- The actual written priorities descend in the reverse written order. -/
theorem newSource_written_descending :
    ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      writtenAtomicPriority newSource newDrawing right <
        writtenAtomicPriority newSource newDrawing left) := by
  decide +kernel

/-- The actual nondegenerate hashed-wedge geometry (reverse-order oriented volume `+3`) classifies
the reverse written order as `S` under the calibrated sign convention. -/
theorem newSource_sorted_geometry :
    descriptorOfPriorityOrderedPoints?
      (([3, 2, 1, 0] : List (Fin 4)).map
        (pointVector newDrawing.first newDrawing.second newDrawing.third newDrawing.fourth)) =
      some RS.S := by
  decide +kernel

/-- The drawing-only empty-auxiliary descriptor of the complete hashed wedge is `S`, through the
generic exact priority theorem (a guide, not cross-source label equality). -/
theorem newSource_empty_descriptor_S :
    ordinaryEmptyAuxiliaryDescriptor? newSource 0 2 newCenter = some (.chiral RS.S) :=
  ordinaryDescriptor?_eq_chiral_of_zero_carrier_written_priority
    newSource newCenter
    (newSource.aromaticCanonicalDependencyView (fun _ => none)
      (newSource.aromaticCanonicalFinalOccurrence 0 newCenter))
    newDrawing newSource_frame_bound (newSource_separation newDrawing)
    [3, 2, 1, 0] newSource_descending_slots_perm newSource_written_descending RS.S
    newSource_sorted_geometry

/-- The drawing channel emits `S` for every actual view of the same source and target. -/
theorem newSource_drawing_S
    (view : newSource.AromaticCanonicalDependencyView newTarget) :
    occurrenceOrdinaryDescriptor? newSource newTarget view 2 = some (.chiral RS.S) := by
  change occurrenceOrdinaryDescriptor? newSource
      (newSource.aromaticCanonicalFinalOccurrence 0 newCenter) view 2 = some (.chiral RS.S)
  rw [occurrenceOrdinaryDescriptor?_final_eq]
  rw [ordinaryDescriptor?_eq_empty_auxiliary_zero_carrier newSource newCenter newDrawing
    newSource_frame_bound (newSource_separation newDrawing) view]
  exact newSource_empty_descriptor_S

/-! ## 6. The actual unequal R/S conflict at one shared view -/

/-- The constitution parser channel result at the shared scheduled view. -/
theorem newSource_parser_R_at_scheduled :
    constitutionParserRichDescriptor? annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget newScheduledView 2 = some (.chiral RS.R) :=
  newSource_parser_descriptor_R newScheduledView

/-- The drawing channel result at the shared scheduled view. -/
theorem newSource_drawing_S_at_scheduled :
    occurrenceOrdinaryDescriptor? newSource newTarget newScheduledView 2 = some (.chiral RS.S) :=
  newSource_drawing_S newScheduledView

/-- The two actual channel outputs at the same source/target/view. -/
noncomputable def newConflictOutputs : List (Option AromaticCanonicalAuxiliaryLabel) :=
  [ constitutionParserRichDescriptor? annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget newScheduledView 2,
    occurrenceOrdinaryDescriptor? newSource newTarget newScheduledView 2 ]

/-- The computed conflict outputs are literally the unequal `R` and `S` labels. -/
theorem newConflictOutputs_eq :
    newConflictOutputs = [some (.chiral RS.R), some (.chiral RS.S)] := by
  simp [newConflictOutputs, newSource_parser_R_at_scheduled, newSource_drawing_S_at_scheduled]

/-- The actual fold status of the two channels is a genuine conflict; absence cannot supply this
witness and no channel precedence is chosen. -/
theorem newSource_conflict : foldStatus newConflictOutputs = .conflict := by
  rw [newConflictOutputs_eq]
  exact foldStatus_opposite_labels_conflict

/-- Both independent meanings are preserved as the two sides of the conflict, at the same source,
target and view.  No joint model over two different scheduled states is asserted. -/
theorem newSource_conflict_meaning :
    ConstitutionParserRichDescriptorMeaning annotatedRawCF newSource newSource_annotationAgreement
        parserSource_writtenExact newTarget newScheduledView 2 (.chiral RS.R) ∧
      OccurrenceOrdinaryDescriptorMeaning newSource newTarget newScheduledView 2 (.chiral RS.S) :=
  ⟨newScheduled_R_meaning,
    occurrenceOrdinaryDescriptor?_sound newSource newTarget newScheduledView 2 (.chiral RS.S)
      newSource_drawing_S_at_scheduled⟩

end TetraStereo.UniversalProof.SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness
