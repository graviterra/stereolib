import TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence

/-!
An inhabited rich parser emission for the actual annotated CFClBrI source. The source-indexed
carrier, returned cursors, real atoms and distinct atomic priorities are reconstructed here.
The actual production key builder and safe tracked sorter then determine the priority order.
Clockwise written parity is evaluated against that order; no label or execution success is an
input. The earlier conditional witness's unrestricted assertion about EVERY tracked order is
not used: uniqueness below applies only to a permutation with independent descending priority.
This proves this concrete parser channel, not mixed-input annotation agreement or source approval.
-/

noncomputable def parserTarget : parserSource.AromaticCanonicalOccurrence 0 :=
  parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter

noncomputable def parserRoots : List (parserSource.AromaticCanonicalRerootCursor 0) :=
  finalOccurrenceRoots parserSource 0 parserCenter

theorem parser_roots_length : parserRoots.length = 4 := by rfl

noncomputable def parserFrame : parserSource.AromaticCanonicalOccurrenceFourLigandFrame 0 :=
  { roots := parserRoots, rootsLength := parser_roots_length }

theorem parser_actual_returned_frame :
    parserSource.aromaticCanonicalOccurrenceLigandFrame? parserTarget = some parserFrame.roots :=
  finalOccurrenceRoots_are_returned parserSource 0 parserCenter

theorem parser_actual_root_ids : occurrenceRootIDs parserSource parserRoots =
    [some 1, some 2, some 3, some 4] := by rfl

theorem parser_actual_roots_real : OccurrenceRootsReal parserSource parserFrame := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

def parserAtomicPriorityValue : Fin 4 → Nat
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 35
  | ⟨3, _⟩ => 53

theorem parser_actual_atomic_priority (slot : Fin 4) :
    occurrenceAtomicPriority parserSource parserFrame slot = parserAtomicPriorityValue slot := by
  fin_cases slot <;> rfl

theorem parser_actual_atomic_priority_injective :
    Function.Injective (occurrenceAtomicPriority parserSource parserFrame) := by
  have injective : Function.Injective parserAtomicPriorityValue := by decide +kernel
  intro left right equal
  apply injective
  simpa only [parser_actual_atomic_priority] using equal

theorem parser_actual_slot_alignment :
    findSlotAlignment?
      (rawWrittenLigandFrame annotatedRawCF
        (parserIndexOfAromaticCanonicalCenter annotatedRawCF parserSource
          parserSource_agreement parserCenter))
      (occurrenceRootIDs parserSource parserRoots) = some [0, 1, 2, 3] := by
  rw [SourceNativeRichParserOccurrence.ClosedParserWitness.parserOccurrence_raw_frame,
    parser_actual_root_ids]
  decide +kernel

/-- Uniqueness concerns an independently descending permutation, not an arbitrary tracked record. -/
theorem parser_actual_priority_order_unique (order : List (Fin 4))
    (perm : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right =>
      occurrenceAtomicPriority parserSource parserFrame right <
        occurrenceAtomicPriority parserSource parserFrame left)) :
    order = [3, 2, 1, 0] := by
  have reversedPerm : ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by decide +kernel
  have reversedDescending : ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      occurrenceAtomicPriority parserSource parserFrame right <
        occurrenceAtomicPriority parserSource parserFrame left) := by
    simp only [parser_actual_atomic_priority]
    decide +kernel
  exact (perm.trans reversedPerm.symm).eq_of_pairwise
    (fun _ _ _ _ higher reverse => False.elim (Nat.lt_asymm higher reverse))
    descending reversedDescending

/-- Actual rich emission for every restricted dependency view, with no successful gate assumed. -/
theorem parser_actual_rich_descriptor_R
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    occurrenceParserRichDescriptor? annotatedRawCF parserSource parserSource_agreement
      parserSource_writtenExact parserTarget view 2 = some (.chiral RS.R) := by
  obtain ⟨keys, tracked, keysComputed, trackedComputed, perm, descending, zero⟩ :=
    exists_occurrence_production_keys_and_safe_order parserSource parserTarget view
      parserFrame parser_actual_returned_frame parser_actual_roots_real
      parser_actual_atomic_priority_injective
      SourceNativeRichParserOccurrence.ClosedParserWitness.parserSource_no_ordinary_double_bond
  have keysComputed2 : parserSource.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      parserTarget view 2 parserRoots = some keys := keysComputed
  have orderEq := parser_actual_priority_order_unique tracked.highestFirst perm descending
  have writtenOrder : tracked.highestFirst.map
      (fun position => ([0, 1, 2, 3] : List Nat).getD position.val 0) = [3, 2, 1, 0] := by
    rw [orderEq]
    rfl
  have rawEq := writtenFramePriorityDescriptor_clockwise_reverse [0, 1, 2, 3]
    tracked.highestFirst writtenOrder
  have recovered : parserSource.aromaticCanonicalOccurrenceTetrahedralCenter? parserTarget =
      some parserCenter := occurrenceTetrahedralCenter?_final parserSource 0 parserCenter
  have evidenceComputed : occurrenceParserRichPriorityEvidence? annotatedRawCF parserSource
      parserSource_agreement parserSource_writtenExact parserTarget view 2 =
      some
        ({ slots := [0, 1, 2, 3]
           keys := keys
           tracked := tracked
           writtenParity := .clockwise
           raw := RS.R } : ParserRichPriorityEvidence parserSource 0) := by
    simp [occurrenceParserRichPriorityEvidence?, recovered, parserCenter_raw_index,
      SourceNativeRichParserOccurrence.ClosedParserWitness.parserSource_atom,
      parser_actual_returned_frame, parserFrame, parser_actual_slot_alignment,
      keysComputed2, trackedComputed, rawEq]
  simp [occurrenceParserRichDescriptor?, evidenceComputed, zero, classifyTetrahedralRSPseudo_zero]

theorem parser_actual_rich_descriptor_meaning
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    OccurrenceParserRichDescriptorMeaning annotatedRawCF parserSource parserSource_agreement
      parserSource_writtenExact parserTarget view 2 (.chiral RS.R) :=
  occurrenceParserRichDescriptor?_sound annotatedRawCF parserSource parserSource_agreement
    parserSource_writtenExact parserTarget view 2 (.chiral RS.R)
      (parser_actual_rich_descriptor_R view)

end TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness
