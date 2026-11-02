import TetraStereo.UniversalProof.NativeSourcePhysicalCoordinates
import TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.OneCenter.CIPAuthoritativeRule6UnannotatedChemicalCompleteness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge













-- writtenSlot? is re-exported from NativeSourcePhysicalCoordinates.



-- writtenSlot?_eq_some is re-exported from NativeSourcePhysicalCoordinates.


section Aligned

variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
variable (center : source.AromaticCanonicalTetrahedralCenter)
variable (domain : SingleLeafDomain raw center.1.val)
variable (four : (recordNeighbors raw center.1.val).length = 4)

include converted domain four

theorem actual_returned_id_at (slot : Fin 4) :
    (finalOccurrenceRootIDs source carrierFuel center)[slot.val]? =
      some (some (slotAtomID raw source converted carrierFuel center domain four slot)) := by
  let frame := actualFrame raw source converted carrierFuel center domain four
  have bound : slot.val < frame.roots.length := by rw [frame.rootsLength]; exact slot.isLt
  change (frame.roots.map (cursorAtomID source))[slot.val]? = _
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  obtain ⟨atom, _, current, _, equal⟩ :=
    actual_slot_endpoint raw source converted carrierFuel center domain four slot
  change some (cursorAtomID source (frame.cursorAt slot)) = _
  change (frame.cursorAt slot).occurrence.1.node.current? = some atom at current
  rw [equal]
  unfold cursorAtomID
  rw [current]
  rfl

theorem actual_aligned_written_lookup (slots : List Nat)
    (matching : ExactSlotAlignment (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source carrierFuel center) slots) (slot : Fin 4) :
    (raw.writtenNeighbors center.1.val)[slots.getD slot.val 0]? =
      some (slotAtomID raw source converted carrierFuel center domain four slot) := by
  have length : slots.length = 4 := matching.2.2.1.length_eq.trans (List.length_range (n := 4))
  have bound : slot.val < slots.length := by rw [length]; exact slot.isLt
  have slotObserved : slots[slot.val]? = some (slots.getD slot.val 0) := by
    rw [List.getElem?_eq_getElem bound]
    exact congrArg some (List.getElem_eq_getD 0)
  have indexed := congrArg (fun ids : List (Option Nat) => ids[slot.val]?) matching.2.2.2
  simp only [List.getElem?_map, slotObserved, Option.map_some] at indexed
  rw [actual_returned_id_at raw source converted carrierFuel center domain four slot] at indexed
  exact Option.some.inj indexed

theorem actual_written_slot_recovered (slots : List Nat)
    (matching : ExactSlotAlignment (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source carrierFuel center) slots) (slot : Fin 4) :
    writtenSlot? (raw.writtenNeighbors center.1.val)
      (slotAtomID raw source converted carrierFuel center domain four slot) =
        some (slots.getD slot.val 0) :=
  writtenSlot?_eq_some _ matching.2.1 _ _
    (actual_aligned_written_lookup raw source converted carrierFuel center domain four slots matching slot)

/-- Actual position lookup succeeds for every canonical slot order, including the derived sorter.
No identity slot alignment is used. -/
theorem actual_priority_positions (slots : List Nat)
    (matching : ExactSlotAlignment (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source carrierFuel center) slots) (order : List (Fin 4)) :
    (order.map (slotAtomID raw source converted carrierFuel center domain four)).mapM
      (writtenSlot? (raw.writtenNeighbors center.1.val)) =
        some (order.map fun slot => slots.getD slot.val 0) := by
  induction order with
  | nil => rfl
  | cons slot remaining inductionHypothesis =>
      simp only [List.map_cons, List.mapM_cons,
        actual_written_slot_recovered raw source converted carrierFuel center domain four slots matching slot,
        inductionHypothesis]
      rfl

/-- This is the exact algebra used by the runtime consumer after its actual lookup has returned.
It applies to arbitrary genuine nonidentity slot alignments. -/
theorem actual_parity_transport (parity : TetrahedralInputParity) (slots : List Nat)
    (matching : ExactSlotAlignment (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source carrierFuel center) slots)
    (order : List (Fin 4)) :
    ((order.map (slotAtomID raw source converted carrierFuel center domain four)).mapM
      (writtenSlot? (raw.writtenNeighbors center.1.val))).map
        (fun positions => RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions)) =
      some (writtenFramePriorityDescriptor parity slots order) := by
  rw [actual_priority_positions raw source converted carrierFuel center domain four slots matching order]
  rfl

end Aligned

/-- Exact runtime consumer lookup fragment, retaining the actual lone-pair/written ligand API. -/
def runtimePriorityPositions? (raw : RawMolecule) (center : Nat)
    (sorted : List CanonicalRerootCursor) : Option (List Nat) :=
  sorted.mapM fun cursor =>
    ((raw.ligandsWithLonePair center).zipIdx.find? fun entry => entry.1 == cursor.node.atom).map Prod.snd

theorem actual_written_four (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) :
    (raw.writtenNeighbors center).length = 4 :=
  (written_neighbors_perm_records raw center domain written).length_eq.trans four

/-- The runtime consumer receives the actual four generated roots, with no phantom replacement. -/
theorem actual_runtime_frame (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) :
    occurrenceLigandFrame? raw (canonicalCenterRoot center) =
      some (generatedRuntimeRoots raw center) := by
  have writtenFour := actual_written_four raw center domain written four
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center writtenFour
  have rootLength : (generatedRuntimeRoots raw center).length = 4 := by
    rw [generatedRuntimeRoots_eq raw center domain.leaf, List.length_map, four]
  unfold occurrenceLigandFrame?
  change (if (raw.ligandsWithLonePair center).length != 4 then none else
    if (generatedRuntimeRoots raw center).length == 4 then some (generatedRuntimeRoots raw center)
      else _) = some (generatedRuntimeRoots raw center)
  simp [ligands, writtenFour, rootLength]

/-- GENERAL actual formal assignment / actual runtime lookup algebra agreement. The parity is
the actual input record, not a desired output. Runtime auxiliary discovery, adjacent refusal and
the public normalized wrapper are deliberately not inferred from the lookup fragment. -/
theorem actual_runtime_formal_descriptor_transport (raw : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement raw source)
    (written : raw.WrittenNeighborExact) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ runtimeResult positions descriptor,
      occurrenceLigandFrame? raw (canonicalCenterRoot center.1.val) =
        some (generatedRuntimeRoots raw center.1.val) ∧
      sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
        (generatedRuntimeRoots raw center.1.val) = some runtimeResult ∧
      runtimePriorityPositions? raw center.1.val runtimeResult.1 = some positions ∧
      descriptor = RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions) ∧
      constitutionParserRichDescriptor? raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) (.chiral descriptor) ∧ runtimeResult.2 = 0 := by
  classical
  obtain ⟨keys, tracked, runtimeResult, keyComputed, safeComputed, runtimeComputed, sameIDs,
      sourceZero, runtimeZero⟩ :=
    actual_runtime_source_priority_alignment raw source agreement.1 carrierFuel center domain four
      noDouble view state runtimeFuel
  obtain ⟨slots, slotsComputed⟩ :=
    converted_written_alignment_exists raw source agreement.1 carrierFuel center domain written four
  have matching := findSlotAlignment?_sound _ _ _ slotsComputed
  let positions := tracked.highestFirst.map (fun slot => slots.getD slot.val 0)
  let descriptor := writtenFramePriorityDescriptor parity slots tracked.highestFirst
  have writtenFour := actual_written_four raw center.1.val domain written four
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center.1.val writtenFour
  have positionsComputed : runtimePriorityPositions? raw center.1.val runtimeResult.1 = some positions := by
    unfold runtimePriorityPositions?
    rw [ligands]
    change runtimeResult.1.mapM
      ((writtenSlot? (raw.writtenNeighbors center.1.val)) ∘ (fun cursor => cursor.node.atom)) = _
    rw [← List.mapM_map, ← sameIDs]
    exact actual_priority_positions raw source agreement.1 carrierFuel center domain four
      slots matching tracked.highestFirst
  change source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
    (2 * (carrierFuel + 1)) (finalOccurrenceRoots source carrierFuel center) = some keys at keyComputed
  let evidence : ParserRichPriorityEvidence source carrierFuel :=
    { slots := slots, keys := keys, tracked := tracked, writtenParity := parity, raw := descriptor }
  have evidenceComputed : constitutionParserRichPriorityEvidence? raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some evidence := by
    have slotsForRoots : findSlotAlignment? (raw.writtenNeighbors center.1.val)
        ((finalOccurrenceRoots source carrierFuel center).map (cursorAtomID source)) = some slots :=
      slotsComputed
    simp [constitutionParserRichPriorityEvidence?, occurrenceTetrahedralCenter?_final,
      parserIndexViaConversion_val, rawWrittenLigandFrame, atomObserved, parityObserved,
      finalOccurrenceRoots_are_returned, occurrenceRootIDs,
      slotsForRoots, keyComputed, safeComputed, evidence]
    rfl
  have descriptorComputed : constitutionParserRichDescriptor? raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some (.chiral descriptor) := by
    simp [constitutionParserRichDescriptor?, evidenceComputed, evidence, sourceZero,
      classifyTetrahedralRSPseudo]
  exact ⟨runtimeResult, positions, descriptor,
    actual_runtime_frame raw center.1.val domain written four, runtimeComputed, positionsComputed, rfl,
    descriptorComputed, constitutionParserRichDescriptor?_sound raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (.chiral descriptor) descriptorComputed, runtimeZero⟩

namespace ClosedCF

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness

abbrev raw : RawMolecule := annotatedRawCF
abbrev source : AuthoritativeChemicalInput := parserSource
abbrev center : source.AromaticCanonicalTetrahedralCenter := parserCenter

theorem actual_annotation_agreement : RawAnnotationAgreement raw source :=
  ConstitutionClosedWitness.parserSource_annotationAgreement

theorem actual_written_exact : raw.WrittenNeighborExact := parserSource_writtenExact

/-- The observed input tag is closed data, not a caller expected descriptor. -/
theorem actual_input_parity :
    raw.atomAt? center.1.val =
      some { AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise } := rfl

/-- An inhabited SAME-source instance of the general actual-sort/lookup/parity bridge. It does not
assert the separate runtime adjacent-refusal or auxiliary-discovery stages. -/
theorem actual_descriptor_transport
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ runtimeResult positions descriptor,
      occurrenceLigandFrame? raw (canonicalCenterRoot center.1.val) =
        some (generatedRuntimeRoots raw center.1.val) ∧
      sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
        (generatedRuntimeRoots raw center.1.val) = some runtimeResult ∧
      runtimePriorityPositions? raw center.1.val runtimeResult.1 = some positions ∧
      descriptor = RawMolecule.descriptorOfParity TetrahedralInputParity.clockwise
        (RawMolecule.permutationIsEven positions) ∧
      constitutionParserRichDescriptor? raw source actual_annotation_agreement actual_written_exact
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2 = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source actual_annotation_agreement actual_written_exact
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2 (.chiral descriptor) ∧
      runtimeResult.2 = 0 :=
  actual_runtime_formal_descriptor_transport raw source actual_annotation_agreement actual_written_exact
    0 center
    TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_domain
    TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_four
    TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_noDouble
    { AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise }
    actual_input_parity TetrahedralInputParity.clockwise (by rfl) view state runtimeFuel

end ClosedCF

end TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
