import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
import TetraStereo.UniversalProof.NativeSourcePhysicalCoordinates

set_option autoImplicit false

namespace TetraStereo.UniversalProof.FamilySourceBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment

/-! Shared physical-slot transport and source-evaluation composition. None of these
results assumes a final CIP model or desired descriptor. Source-specific proofs supply
actual endpoint observations and successful local operations; the scheduler constructs
its own state. Atomic-number injectivity is deliberately not required. -/

theorem aligned_written_lookup (written slots : List Nat) (rootIDs : List (Option Nat))
    (endpoint : Fin 4 → Nat) (matching : ExactSlotAlignment written rootIDs slots)
    (observed : ∀ slot : Fin 4, rootIDs[slot.val]? = some (some (endpoint slot)))
    (slot : Fin 4) : written[slots.getD slot.val 0]? = some (endpoint slot) := by
  have length : slots.length = 4 := matching.2.2.1.length_eq.trans (List.length_range (n := 4))
  have bound : slot.val < slots.length := by rw [length]; exact slot.isLt
  have slotObserved : slots[slot.val]? = some (slots.getD slot.val 0) := by
    rw [List.getElem?_eq_getElem bound]
    exact congrArg some (List.getElem_eq_getD 0)
  have indexed := congrArg (fun ids : List (Option Nat) => ids[slot.val]?) matching.2.2.2
  dsimp only at indexed
  rw [observed slot] at indexed
  simp only [List.getElem?_map, slotObserved, Option.map_some] at indexed
  exact Option.some.inj indexed

theorem aligned_priority_positions (written slots : List Nat) (rootIDs : List (Option Nat))
    (endpoint : Fin 4 → Nat) (matching : ExactSlotAlignment written rootIDs slots)
    (observed : ∀ slot : Fin 4, rootIDs[slot.val]? = some (some (endpoint slot)))
    (order : List (Fin 4)) :
    (order.map endpoint).mapM (writtenSlot? written) =
      some (order.map fun slot => slots.getD slot.val 0) := by
  induction order with
  | nil => rfl
  | cons slot rest ih =>
      have recovered := writtenSlot?_eq_some _ matching.2.1 _ _
        (aligned_written_lookup written slots rootIDs endpoint matching observed slot)
      simp only [List.map_cons, List.mapM_cons, recovered, ih]
      rfl

theorem written_descriptor_of_positions (parity : TetrahedralInputParity)
    (slots positions : List Nat) (order : List (Fin 4))
    (aligned : order.map (fun slot => slots.getD slot.val 0) = positions) :
    writtenFramePriorityDescriptor parity slots order =
      descriptorOfParity parity (permutationIsEven positions) := by
  unfold writtenFramePriorityDescriptor
  rw [aligned]

/-- Compose the actual parser/source operations. The resulting record retains the
computed parity and tracked order, including its pseudoasymmetric comparison count. -/
theorem rich_evidence_of_steps (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (slots : List Nat) (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center)
    (atomComputed : molecule.atomAt? center.val.val = some spec)
    (parityComputed : spec.tetrahedral? = some parity)
    (rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target = some roots)
    (slotsComputed : findSlotAlignment? (molecule.writtenNeighbors center.val.val)
      (occurrenceRootIDs source roots) = some slots)
    (keysComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view ruleFuel roots = some keys)
    (orderComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked) :
    constitutionParserRichPriorityEvidence? molecule source agreement writtenExact target view ruleFuel =
      some
        { slots := slots
          keys := keys
          tracked := tracked
          writtenParity := parity
          raw := writtenFramePriorityDescriptor parity slots tracked.highestFirst } := by
  simp only [constitutionParserRichPriorityEvidence?, centerComputed, Bind.bind, Option.bind,
    parserIndexViaConversion_val, rawWrittenLigandFrame, atomComputed, parityComputed,
    rootsComputed, slotsComputed, keysComputed, orderComputed]

/-- Classification preserves the actual pseudo count; zero is only a special case. -/
theorem rich_descriptor_of_evidence (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (computed : constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence) :
    constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel =
      some (classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons) := by
  unfold constitutionParserRichDescriptor?
  rw [computed]
  rfl

/-- Evaluate the internally constructed scheduler, with no caller-supplied model. -/
theorem scheduled_evaluation (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    (carrierFuel ruleFuel : Nat) (target : source.AromaticCanonicalOccurrence carrierFuel) :
    constitutionParserRichDescriptor? molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView
        (constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel ruleFuel)
        target) ruleFuel =
      constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel ruleFuel target :=
  constitutionParserRichModel_evaluates molecule source agreement writtenExact _
    (constitutionParserRichScheduledState_cipModel molecule source agreement writtenExact carrierFuel ruleFuel)
    target

/-- A result valid at every dependency view is also produced by the genuine scheduler. -/
theorem scheduled_output_of_all_views (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    (carrierFuel ruleFuel : Nat) (target : source.AromaticCanonicalOccurrence carrierFuel)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : ∀ view, constitutionParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel = some descriptor) :
    constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel ruleFuel target =
      some descriptor := by
  rw [← scheduled_evaluation]
  exact computed _

/-- Soundness for an observed scheduled output, using the model constructed internally. -/
theorem scheduled_output_sound (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    (carrierFuel ruleFuel : Nat) (target : source.AromaticCanonicalOccurrence carrierFuel)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : constitutionParserRichScheduledState molecule source agreement writtenExact
      carrierFuel ruleFuel target = some descriptor) :
    ConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView
        (constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel ruleFuel)
        target) ruleFuel descriptor :=
  constitutionParserRichModel_output_sound molecule source agreement writtenExact _
    (constitutionParserRichScheduledState_cipModel molecule source agreement writtenExact carrierFuel ruleFuel)
    target descriptor computed

end TetraStereo.UniversalProof.FamilySourceBridge
