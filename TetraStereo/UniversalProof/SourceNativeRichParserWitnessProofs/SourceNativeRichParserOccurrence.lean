import TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceReadiness

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.Rule6HandednessSemantics
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment


































/-! ## 1. Raw written-frame descriptor from actual parity and actual priority order -/

/-- Raw `R/S` from a written-frame `TetrahedralInputParity` and the actual returned-cursor priority
order.  The order is given as returned occurrence positions; `slots` maps each position to its
actual aligned written slot, so `order.map (fun p => slots.getD p.val 0)` is the actual priority
order expressed in written slots.  This is exactly `descriptorOfFinFourOrdering` without the
noncomputable frame permutation: `RawMolecule.permutationIsEven` reads the priority-order list. -/
def writtenFramePriorityDescriptor (parity : TetrahedralInputParity) (slots : List Nat)
    (order : List (Fin 4)) : RS :=
  RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven (order.map fun position => slots.getD position.val 0))

/-- A strictly descending written priority order `I > Br > Cl > F` on the written slots `[0,1,2,3]`
carries the even permutation `[3,2,1,0]`, so the actual `@@` (`clockwise`) annotation emits `R`. -/
theorem writtenFramePriorityDescriptor_clockwise_reverse (slots : List Nat) (order : List (Fin 4))
    (reversed : order.map (fun position => slots.getD position.val 0) = [3, 2, 1, 0]) :
    writtenFramePriorityDescriptor .clockwise slots order = RS.R := by
  unfold writtenFramePriorityDescriptor
  rw [reversed]
  rfl

/-- The written-frame evaluation agrees with the `S₄` descriptor whenever a permutation's
production list is the actual priority order in written slots.  This is the universal parity law in
its list form. -/
theorem writtenFramePriorityDescriptor_eq_descriptorOfFinFourOrdering
    (parity : TetrahedralInputParity) (slots : List Nat) (order : List (Fin 4))
    (permutation : Equiv.Perm (Fin 4))
    (listEq : finFourPermutationList permutation = order.map fun position => slots.getD position.val 0) :
    writtenFramePriorityDescriptor parity slots order =
      descriptorOfFinFourOrdering parity permutation := by
  unfold writtenFramePriorityDescriptor descriptorOfFinFourOrdering
  rw [listEq]

/-! ## 2. The parser-only rich priority channel -/

/-- Actual returned occurrence endpoint IDs are the retained roots; the raw written slot frame is
the actual parser written-neighbour view.  Both are used below.  This record retains the actual
computation inputs so a later soundness statement can mention them directly. -/
structure ParserRichPriorityEvidence (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  /-- Actual returned occurrence position to actual written-slot alignment. -/
  slots : List Nat
  /-- Actual produced Rules-3--5 occurrence key frame. -/
  keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel
  /-- Actual strict tracked priority order of the returned cursors. -/
  tracked : TrackedLocalizedLigandOrder
  /-- Actual copied parser written-frame parity. -/
  writtenParity : TetrahedralInputParity
  /-- Actual raw written-frame descriptor computed from the actual parity and priority order. -/
  raw : RS

/-- Actual parser-only rich priority evidence at an arbitrary original occurrence target.  It
recovers the real center from the occurrence node, reads the copied annotation from the actual
normalized raw record, aligns the actual raw written frame against the actual returned cursor IDs,
runs the committed Rules-3--5 key builder and strict tracked sorter, and computes the raw descriptor
from the actual raw written parity and the actual priority order (expressed in actual written
slots). -/
noncomputable def occurrenceParserRichPriorityEvidence? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (_writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option (ParserRichPriorityEvidence source carrierFuel) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let spec ← molecule.atomAt? rawCenter.val
  let writtenParity ← spec.tetrahedral?
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  let slots ← findSlotAlignment? (rawWrittenLigandFrame molecule rawCenter)
    (occurrenceRootIDs source roots)
  let keys ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    target view ruleFuel roots
  let tracked ← source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys
  some
    { slots := slots
      keys := keys
      tracked := tracked
      writtenParity := writtenParity
      raw := writtenFramePriorityDescriptor writtenParity slots tracked.highestFirst }

/-- Independent complete meaning of one parser-only rich priority evidence record.  It mentions the
recovered real occurrence center, the actual raw annotation provenance inside the source's pinned
parser diagram, the actual declarative reroot frame, the actual raw-written/endpoint alignment, the
produced Rules-3--5 key frame judgment, the strict tracked-order judgment including its sort
derivation, the universal all-`S₄` parity transport law, and the actual raw written-frame
descriptor.  It contains no expected label, no comparison callback, and no successful-sort
equation. -/
def OccurrenceParserRichPriorityEvidenceMeaning (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (_writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel) : Prop :=
  molecule.WrittenNeighborExact ∧
    ∃ center roots spec writtenParity diagram slotPerm,
      source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center ∧
        molecule.atomAt?
            (parserIndexOfAromaticCanonicalCenter molecule source agreement center).val = some spec ∧
        spec.tetrahedral? = some writtenParity ∧
        evidence.writtenParity = writtenParity ∧
        source.diagram? = some diagram ∧
        ({ atom := (parserIndexOfAromaticCanonicalCenter molecule source agreement center).val,
            parity := writtenParity } : DiagramAtomConfiguration) ∈ diagram.atomConfigurations ∧
        source.DeclarativeAromaticCanonicalRerootChildren
          { occurrence := target, previous? := none } roots ∧
        ExactSlotAlignment
          (rawWrittenLigandFrame molecule
            (parserIndexOfAromaticCanonicalCenter molecule source agreement center))
          (occurrenceRootIDs source roots) evidence.slots ∧
        source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyFrame
          target view ruleFuel roots evidence.keys ∧
        source.DeclarativeSafeAromaticCanonicalOccurrenceRule3Through5TrackedOrder
          evidence.keys evidence.tracked ∧
        finFourPermutationList slotPerm = evidence.slots ∧
        (∀ ordering : Equiv.Perm (Fin 4),
          descriptorOfFinFourOrdering (transportSlotParity writtenParity evidence.slots) ordering =
            descriptorOfFinFourOrdering writtenParity (ordering.trans slotPerm)) ∧
        evidence.raw =
          writtenFramePriorityDescriptor writtenParity evidence.slots
            evidence.tracked.highestFirst

/-- Every parser-only rich priority evidence record is the actual recovered center, the actual raw
annotation, the actual declarative reroot frame, the actual endpoint alignment, the actual key
frame and strict tracked order, the universal parity transport law, and the actual raw descriptor. -/
theorem occurrenceParserRichPriorityEvidence?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (computed : occurrenceParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence) :
    OccurrenceParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence := by
  unfold occurrenceParserRichPriorityEvidence? at computed
  refine ⟨writtenExact, ?_⟩
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases atomComputed : molecule.atomAt?
          (parserIndexOfAromaticCanonicalCenter molecule source agreement center).val with
      | none => simp [centerComputed, atomComputed] at computed
      | some spec =>
          cases parityComputed : spec.tetrahedral? with
          | none => simp [centerComputed, atomComputed, parityComputed] at computed
          | some writtenParity =>
              cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
              | none => simp [centerComputed, rootsComputed] at computed
              | some roots =>
                  cases slotsComputed : findSlotAlignment?
                      (rawWrittenLigandFrame molecule
                        (parserIndexOfAromaticCanonicalCenter molecule source agreement center))
                      (occurrenceRootIDs source roots) with
                  | none => simp [centerComputed, atomComputed, rootsComputed,
                      slotsComputed] at computed
                  | some slots =>
                      cases keysComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
                          target view ruleFuel roots with
                      | none => simp [centerComputed, rootsComputed, keysComputed] at computed
                      | some keys =>
                          cases trackedComputed :
                              source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys with
                          | none => simp [centerComputed, rootsComputed, keysComputed,
                              trackedComputed] at computed
                          | some tracked =>
                              simp [centerComputed, atomComputed, parityComputed, rootsComputed,
                                slotsComputed, keysComputed, trackedComputed] at computed
                              subst evidence
                              obtain ⟨diagram, diagramEq, diagramMember⟩ :=
                                molecule.authoritativeStructureAgreement_diagram_contains_tetrahedral
                                  source agreement
                                  (parserIndexOfAromaticCanonicalCenter molecule source agreement
                                    center).val spec writtenParity atomComputed parityComputed
                              obtain ⟨slotPerm, slotList, transportLaw⟩ :=
                                transportSlotParity_descriptor_universal writtenParity
                                  (rawWrittenLigandFrame molecule
                                    (parserIndexOfAromaticCanonicalCenter molecule source agreement
                                      center))
                                  (occurrenceRootIDs source roots) slots
                                  (findSlotAlignment?_sound _ _ slots slotsComputed)
                              exact ⟨center, roots, spec, writtenParity, diagram, slotPerm,
                                rfl, atomComputed, parityComputed, rfl, diagramEq,
                                diagramMember,
                                source.aromaticCanonicalOccurrenceLigandFrame?_sound target roots
                                  rootsComputed,
                                findSlotAlignment?_sound _ _ slots slotsComputed,
                                source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
                                  target view ruleFuel roots keys keysComputed,
                                source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
                                  keys tracked trackedComputed,
                                slotList, transportLaw, rfl⟩

/-! ## 3. The rich parser-only descriptor -/

/-- Rich parser-only descriptor at an arbitrary original occurrence target: the actual raw
written-frame descriptor classified by the actual number of pseudo comparisons made by the strict
tracked sorter.  This is the parser-only analogue of `occurrenceOrdinaryDescriptor?`, with the raw
written parity replacing three-dimensional points. -/
noncomputable def occurrenceParserRichDescriptor? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ← occurrenceParserRichPriorityEvidence? molecule source agreement writtenExact
    target view ruleFuel
  some (classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons)

/-- Independent complete meaning of one parser-only rich descriptor emission. -/
def OccurrenceParserRichDescriptorMeaning (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence,
    OccurrenceParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence ∧
      descriptor = classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons

/-- Every parser-only rich descriptor emission has the complete meaning above: no hidden success
branch, no caller permutation, no expected label and no separate evidence channel. -/
theorem occurrenceParserRichDescriptor?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : occurrenceParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel = some descriptor) :
    OccurrenceParserRichDescriptorMeaning molecule source agreement writtenExact target view ruleFuel
      descriptor := by
  unfold occurrenceParserRichDescriptor? at computed
  cases evidenceComputed : occurrenceParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      simp [evidenceComputed] at computed
      subst descriptor
      exact ⟨evidence,
        occurrenceParserRichPriorityEvidence?_sound molecule source agreement writtenExact
          target view ruleFuel evidence evidenceComputed,
        rfl⟩

/-! ## 4. Universal written-frame parity law for the parser channel -/




theorem parserOccurrence_transport_universal (parity : TetrahedralInputParity)
    (endpoints : List Nat) (rootIDs : List (Option Nat)) (slots : List Nat)
    (matching : ExactSlotAlignment endpoints rootIDs slots) :
    ∃ slotPerm : Equiv.Perm (Fin 4),
      finFourPermutationList slotPerm = slots ∧
        ∀ ordering : Equiv.Perm (Fin 4),
          descriptorOfFinFourOrdering (transportSlotParity parity slots) ordering =
            descriptorOfFinFourOrdering parity (ordering.trans slotPerm) :=
  transportSlotParity_descriptor_universal parity endpoints rootIDs slots matching









namespace ClosedParserWitness

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open SingleWedgeSourceRegression

/-- The actual raw written ligand frame at the recovered carbon is the literal written order. -/
theorem parserOccurrence_raw_frame :
    rawWrittenLigandFrame annotatedRawCF
      (parserIndexOfAromaticCanonicalCenter annotatedRawCF parserSource
        parserSource_agreement parserCenter) = [1, 2, 3, 4] := by
  unfold rawWrittenLigandFrame
  rw [parserCenter_raw_index]
  exact parserSource_written_endpoints

/-- The actual copied annotation parity at raw index `0` is `clockwise`. -/
theorem parserSource_atom :
    annotatedRawCF.atomAt? 0 =
      some { AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise } := by
  rfl

theorem parserSource_spec_parity :
    (AtomSpec.tetrahedral?
        ({ AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise } :
          AtomSpec)) = some TetrahedralInputParity.clockwise := rfl



theorem parserOccurrence_roots_length (fuel : Nat) :
    (finalOccurrenceRoots parserSource fuel parserCenter).length = 4 := by
  obtain ⟨slots, computed⟩ := parserOccurrence_alignment_exists fuel
  obtain ⟨center, roots, centerComputed, children, matching⟩ :=
    occurrenceParserSlotAlignment?_sound annotatedRawCF parserSource parserSource_agreement
      (parserSource.aromaticCanonicalFinalOccurrence fuel parserCenter) slots computed
  rw [occurrenceTetrahedralCenter?_final parserSource fuel parserCenter] at centerComputed
  have centerEq : center = parserCenter := (Option.some.inj centerComputed).symm
  subst center
  have returned : parserSource.aromaticCanonicalOccurrenceLigandFrame?
      (parserSource.aromaticCanonicalFinalOccurrence fuel parserCenter) = some roots :=
    (parserSource.aromaticCanonicalOccurrenceLigandFrame?_eq_some_iff _ roots).mpr children
  have rootsEq : roots = finalOccurrenceRoots parserSource fuel parserCenter := by
    rw [finalOccurrenceRoots_are_returned] at returned
    exact (Option.some.inj returned).symm
  have perm := ExactSlotAlignment.rootIDs_perm_endpoints _ _ _ matching
  have lengthEq : (occurrenceRootIDs parserSource roots).length = 4 := by
    have raw := perm.length_eq
    rw [parserOccurrence_raw_frame] at raw
    simpa using raw
  have rootsLength : roots.length = 4 := by simpa [occurrenceRootIDs] using lengthEq
  rw [← rootsEq]
  exact rootsLength

/-- The parser source contains no ordinary canonical double bond; its molecule is the committed
CFClBrI constitution. -/
theorem parserSource_no_ordinary_double_bond :
    parserSource.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : parserSource.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

/-- The preserved universal-order premise is impossible: an arbitrary tracked record can have
empty `highestFirst`, whose mapped written order cannot equal the four-entry reverse order. -/
theorem atomicWrittenOrder_impossible (slots : List Nat) :
    ¬ (∀ tracked : TrackedLocalizedLigandOrder,
      tracked.highestFirst.map (fun position => slots.getD position.val 0) = [3, 2, 1, 0]) := by
  intro universalOrder
  have emptyOrder := universalOrder { highestFirst := [], pseudoComparisons := 0 }
  exact (by decide : ([] : List Nat) ≠ [3, 2, 1, 0]) emptyOrder

/-- Obsolete conditional API, retained unchanged. Its `atomicWrittenOrder` premise quantifies over
every arbitrary tracked record and is unsatisfiable by `atomicWrittenOrder_impossible`. Therefore
this theorem is vacuous and is not an inhabited restricted-domain or parser-emission witness. A
successor must prove the written order of the actual returned safe tracked result instead. -/
theorem parserSource_atomic_separated_chiral_R
    (view : parserSource.AromaticCanonicalDependencyView
      (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter))
    (frame : AromaticCanonicalOccurrenceFourLigandFrame parserSource 0)
    (frameRoots : frame.roots = finalOccurrenceRoots parserSource 0 parserCenter)
    (real : OccurrenceRootsReal parserSource frame)
    (injective : Function.Injective (occurrenceAtomicPriority parserSource frame))
    (slots : List Nat)
    (findComputed : findSlotAlignment?
        (rawWrittenLigandFrame annotatedRawCF
          (parserIndexOfAromaticCanonicalCenter annotatedRawCF parserSource
            parserSource_agreement parserCenter))
        (occurrenceRootIDs parserSource (finalOccurrenceRoots parserSource 0 parserCenter)) =
      some slots)
    (atomicWrittenOrder : ∀ tracked : TrackedLocalizedLigandOrder,
      tracked.highestFirst.map (fun position => slots.getD position.val 0) = [3, 2, 1, 0]) :
    occurrenceParserRichDescriptor? annotatedRawCF parserSource parserSource_agreement
      parserSource_writtenExact
      (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter) view 2 =
      some (.chiral RS.R) := by
  have returned : parserSource.aromaticCanonicalOccurrenceLigandFrame?
      (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter) = some frame.roots := by
    rw [frameRoots]
    exact finalOccurrenceRoots_are_returned parserSource 0 parserCenter
  obtain ⟨keys, tracked, keysComputed, trackedComputed, _perm, _descending, pseudoZero⟩ :=
    exists_occurrence_production_keys_and_safe_order parserSource
      (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter)
      view frame returned real injective parserSource_no_ordinary_double_bond
  have keysComputed' :
      parserSource.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter) view 2
        (finalOccurrenceRoots parserSource 0 parserCenter) = some keys := by
    rw [frameRoots] at keysComputed
    simpa using keysComputed
  have evidenceComputed : occurrenceParserRichPriorityEvidence? annotatedRawCF parserSource
      parserSource_agreement parserSource_writtenExact
      (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter) view 2 =
      some
        { slots := slots
          keys := keys
          tracked := tracked
          writtenParity := TetrahedralInputParity.clockwise
          raw := writtenFramePriorityDescriptor TetrahedralInputParity.clockwise slots
            tracked.highestFirst } := by
    simp [occurrenceParserRichPriorityEvidence?, occurrenceTetrahedralCenter?_final,
      parserCenter_raw_index, parserSource_atom,
      finalOccurrenceRoots_are_returned, findComputed, keysComputed', trackedComputed]
  unfold occurrenceParserRichDescriptor?
  rw [evidenceComputed]
  change some (classifyTetrahedralRSPseudo
    (writtenFramePriorityDescriptor TetrahedralInputParity.clockwise slots tracked.highestFirst)
    tracked.pseudoComparisons) = some (.chiral RS.R)
  have rawEq : writtenFramePriorityDescriptor TetrahedralInputParity.clockwise slots
      tracked.highestFirst = RS.R :=
    writtenFramePriorityDescriptor_clockwise_reverse slots tracked.highestFirst
      (atomicWrittenOrder tracked)
  simp [rawEq, pseudoZero]

end ClosedParserWitness

end TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
