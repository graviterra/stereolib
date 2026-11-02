import TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
import TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.Rule6HandednessSemantics
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
























































/-! ## 1. Conversion-only parser index -/

/-- The raw parser index of an actual semantic source center, transported by the checked semantic
conversion equality **only**.  Unlike `parserIndexOfAromaticCanonicalCenter` this needs no diagram
equality; the two agree definitionally when both premises are available. -/
def parserIndexViaConversion (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (conversion : molecule.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) : Fin molecule.atomCount :=
  Fin.cast (molecule.toSemanticMolecule?_atomCount source.molecule conversion) center.val

/-- The conversion-only parser index carries exactly the source center's numerical value. -/
theorem parserIndexViaConversion_val (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (conversion : molecule.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (parserIndexViaConversion molecule source conversion center).val = center.val.val := rfl

/-- Exact index identity: transporting the conversion-only index back through the same conversion
returns the actual source center index; no diagram equality is used. -/
theorem parserIndexViaConversion_converted (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (conversion : molecule.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    molecule.convertedAtomIndex source conversion
        (parserIndexViaConversion molecule source conversion center) = center.val := by
  apply Fin.ext
  rfl

/-- The weaker premise does not change the recovered raw atom: whenever full structural agreement
is also available the conversion-only index is the committed parser index. -/
theorem parserIndexViaConversion_eq_parserIndexOf (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    parserIndexViaConversion molecule source agreement.1 center =
      parserIndexOfAromaticCanonicalCenter molecule source agreement center := by
  apply Fin.ext
  rfl

/-! ## 2. Actual raw written frame and actual returned endpoint IDs -/

/-- Actual returned occurrence endpoint IDs at one recovered source center, aligned against the
actual raw written frame through the finite `findSlotAlignment?` matcher.  Fail-closed on missing
centers, missing frames, non-four frames, duplicate endpoints and unmatched IDs. -/
noncomputable def constitutionOccurrenceSlotAlignment? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (conversion : molecule.toSemanticMolecule? = some source.molecule) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel) : Option (List Nat) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let rawCenter := parserIndexViaConversion molecule source conversion center
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  findSlotAlignment? (rawWrittenLigandFrame molecule rawCenter) (occurrenceRootIDs source roots)

/-- Independent meaning of a successful constitution alignment, stated directly over the recovered
center, the actual declarative reroot frame and the actual endpoint-ID correspondence.  It mentions
no search, no success equation and no caller permutation. -/
def ConstitutionOccurrenceSlotAlignment (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (conversion : molecule.toSemanticMolecule? = some source.molecule) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) (slots : List Nat) : Prop :=
  source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center ∧
    source.DeclarativeAromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } roots ∧
    ExactSlotAlignment
      (rawWrittenLigandFrame molecule
        (parserIndexViaConversion molecule source conversion center))
      (occurrenceRootIDs source roots) slots

/-- Every successful constitution alignment is the actual recovered center, the actual declarative
reroot frame, and an actual endpoint-ID correspondence. -/
theorem constitutionOccurrenceSlotAlignment?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (conversion : molecule.toSemanticMolecule? = some source.molecule) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel) (slots : List Nat)
    (computed : constitutionOccurrenceSlotAlignment? molecule source conversion target = some slots) :
    ∃ center roots,
      ConstitutionOccurrenceSlotAlignment molecule source conversion target center roots slots := by
  unfold constitutionOccurrenceSlotAlignment? at computed
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
      | none => simp [centerComputed, rootsComputed] at computed
      | some roots =>
          cases found : findSlotAlignment?
              (rawWrittenLigandFrame molecule
                (parserIndexViaConversion molecule source conversion center))
              (occurrenceRootIDs source roots) with
          | none => simp [centerComputed, rootsComputed, found] at computed
          | some positions =>
              simp [centerComputed, rootsComputed, found] at computed
              subst slots
              exact ⟨center, roots, centerComputed,
                source.aromaticCanonicalOccurrenceLigandFrame?_sound target roots rootsComputed,
                findSlotAlignment?_sound _ _ positions found⟩

/-- Any genuine four-slot alignment yields the universal all-`S₄` parity transport law, so a later
rich descriptor keeps its pseudoasymmetric classification across the actual slot permutation. -/
theorem constitutionOccurrence_transport_universal (parity : TetrahedralInputParity)
    (endpoints : List Nat) (rootIDs : List (Option Nat)) (slots : List Nat)
    (matching : ExactSlotAlignment endpoints rootIDs slots) :
    ∃ slotPerm : Equiv.Perm (Fin 4),
      finFourPermutationList slotPerm = slots ∧
        ∀ ordering : Equiv.Perm (Fin 4),
          descriptorOfFinFourOrdering (transportSlotParity parity slots) ordering =
            descriptorOfFinFourOrdering parity (ordering.trans slotPerm) :=
  transportSlotParity_descriptor_universal parity endpoints rootIDs slots matching

/-! ## 3. Actual raw annotation matched to an actual absolute source configuration -/

/-- The actual raw parity stored at a real parser index is an actual raw annotation record. -/
theorem rawAtomAnnotation_mem (molecule : RawMolecule) (index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (bound : index < molecule.atomCount)
    (atomObserved : molecule.atomAt? index = some spec)
    (parityObserved : spec.tetrahedral? = some parity) :
    ({ index := index, parity := parity } : RawAtomAnnotation) ∈ rawAtomAnnotations molecule := by
  unfold rawAtomAnnotations
  rw [List.mem_filterMap]
  exact ⟨index, List.mem_range.mpr bound, by simp [atomObserved, parityObserved]⟩



theorem recordAgreement_matched_absolute_configuration (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (index : Nat) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (bound : index < molecule.atomCount)
    (atomObserved : molecule.atomAt? index = some spec)
    (parityObserved : spec.tetrahedral? = some parity) :
    ∃ configuration, configuration ∈ sourceAtomConfigurations source ∧
      configuration.atom = index ∧ configuration.parity = parity ∧
        configuration.scope = DiagramConfigurationScope.absolute :=
  agreement.2.1 _
    (rawAtomAnnotation_mem molecule index spec parity bound atomObserved parityObserved)






/-- Actual constitution rich priority evidence at an arbitrary original occurrence target.  It
recovers the real center from the occurrence node, reads the copied annotation from the actual
normalized raw record through the conversion-only index, aligns the actual raw written frame against
the actual returned cursor IDs, runs the committed Rules-3--5 key builder and strict tracked sorter,
and computes the raw descriptor from the actual raw written parity and the actual priority order.
It never reads `source.diagram?` as a whole. -/
noncomputable def constitutionParserRichPriorityEvidence? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (_writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option (ParserRichPriorityEvidence source carrierFuel) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let rawCenter := parserIndexViaConversion molecule source agreement.1 center
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







def ConstitutionParserRichPriorityEvidenceMeaning (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (_writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel) : Prop :=
  molecule.WrittenNeighborExact ∧
    ∃ center roots spec writtenParity configuration slotPerm,
      source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center ∧
        molecule.atomAt?
            (parserIndexViaConversion molecule source agreement.1 center).val = some spec ∧
        spec.tetrahedral? = some writtenParity ∧
        evidence.writtenParity = writtenParity ∧
        ({ index := (parserIndexViaConversion molecule source agreement.1 center).val,
            parity := writtenParity } : RawAtomAnnotation) ∈ rawAtomAnnotations molecule ∧
        configuration ∈ sourceAtomConfigurations source ∧
        configuration.atom = (parserIndexViaConversion molecule source agreement.1 center).val ∧
        configuration.parity = writtenParity ∧
        configuration.scope = DiagramConfigurationScope.absolute ∧
        source.DeclarativeAromaticCanonicalRerootChildren
          { occurrence := target, previous? := none } roots ∧
        ExactSlotAlignment
          (rawWrittenLigandFrame molecule
            (parserIndexViaConversion molecule source agreement.1 center))
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

/-- Every constitution rich priority evidence record is exactly the actual recovered center, the
actual raw annotation (record and matched absolute configuration), the actual declarative reroot
frame, the actual endpoint alignment, the actual key frame and strict tracked order, the universal
parity transport law and the actual raw descriptor. -/
theorem constitutionParserRichPriorityEvidence?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (computed : constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence) :
    ConstitutionParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence := by
  unfold constitutionParserRichPriorityEvidence? at computed
  refine ⟨writtenExact, ?_⟩
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases atomComputed : molecule.atomAt?
          (parserIndexViaConversion molecule source agreement.1 center).val with
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
                        (parserIndexViaConversion molecule source agreement.1 center))
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
                              have memAnnot :
                                  ({ index := (parserIndexViaConversion molecule source
                                        agreement.1 center).val, parity := writtenParity } :
                                      RawAtomAnnotation) ∈ rawAtomAnnotations molecule :=
                                rawAtomAnnotation_mem molecule
                                  (parserIndexViaConversion molecule source agreement.1
                                    center).val spec writtenParity
                                  (parserIndexViaConversion molecule source agreement.1
                                    center).isLt atomComputed parityComputed
                              obtain ⟨configuration, configMem, atomEq, parityEq, scopeEq⟩ :=
                                recordAgreement_matched_absolute_configuration molecule source
                                  agreement
                                  (parserIndexViaConversion molecule source agreement.1
                                    center).val spec writtenParity
                                  (parserIndexViaConversion molecule source agreement.1
                                    center).isLt atomComputed parityComputed
                              obtain ⟨slotPerm, slotList, transportLaw⟩ :=
                                transportSlotParity_descriptor_universal writtenParity
                                  (rawWrittenLigandFrame molecule
                                    (parserIndexViaConversion molecule source agreement.1 center))
                                  (occurrenceRootIDs source roots) slots
                                  (findSlotAlignment?_sound _ _ slots slotsComputed)
                              exact ⟨center, roots, spec, writtenParity, configuration, slotPerm,
                                rfl, atomComputed, parityComputed, rfl, memAnnot, configMem,
                                atomEq, parityEq, scopeEq,
                                source.aromaticCanonicalOccurrenceLigandFrame?_sound target roots
                                  rootsComputed,
                                findSlotAlignment?_sound _ _ slots slotsComputed,
                                source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
                                  target view ruleFuel roots keys keysComputed,
                                source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
                                  keys tracked trackedComputed,
                                slotList, transportLaw, rfl⟩

/-! ## 5. The rich descriptor classifying law -/

/-- Constitution rich descriptor at an arbitrary original occurrence target: the actual raw
written-frame descriptor classified by the actual number of pseudo comparisons made by the strict
tracked sorter.  This is the parser-constitution analogue of `occurrenceOrdinaryDescriptor?` and
needs no full raw diagram equality. -/
noncomputable def constitutionParserRichDescriptor? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ← constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
    target view ruleFuel
  some (classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons)

/-- Independent complete meaning of one constitution rich descriptor emission. -/
def ConstitutionParserRichDescriptorMeaning (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence,
    ConstitutionParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence ∧
      descriptor = classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons

/-- Every constitution rich descriptor emission has the complete meaning above: no hidden success
branch, no caller permutation and no expected label. -/
theorem constitutionParserRichDescriptor?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : constitutionParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel = some descriptor) :
    ConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact target view
      ruleFuel descriptor := by
  unfold constitutionParserRichDescriptor? at computed
  cases evidenceComputed : constitutionParserRichPriorityEvidence? molecule source agreement
      writtenExact target view ruleFuel with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      simp [evidenceComputed] at computed
      subst descriptor
      exact ⟨evidence,
        constitutionParserRichPriorityEvidence?_sound molecule source agreement writtenExact
          target view ruleFuel evidence evidenceComputed,
        rfl⟩

/-! ## 6. Initial atom-parity domain restriction

Optional: on the domain with no actual raw directional bond record, the record agreement is exactly
the bidirectional atom-parity agreement together with the explicit source-side absence of
directional records.  A mixed directional source is refused explicitly, not silently accepted. -/

/-- The initial atom-parity domain: the actual raw records carry no directional bond record. -/
def NoRawDirectionalRecords (molecule : RawMolecule) : Prop :=
  rawBondDirections molecule = []

/-- The initial atom-parity domain agreement: the bidirectional atom-parity record correspondence,
plus the explicit absence of directional records on the source side. -/
def AtomParityRecordAgreement (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    Prop :=
  (∀ annotation, annotation ∈ rawAtomAnnotations molecule →
      ∃ configuration, configuration ∈ sourceAtomConfigurations source ∧
        configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
          configuration.scope = DiagramConfigurationScope.absolute) ∧
    (∀ configuration, configuration ∈ sourceAtomConfigurations source →
      ∃ annotation, annotation ∈ rawAtomAnnotations molecule ∧
        configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
          configuration.scope = DiagramConfigurationScope.absolute) ∧
      diagramDirectionalBonds source = []

/-- On the atom-parity domain the source must also carry no directional record: the diagram-to-raw
direction of the record agreement has no raw directional record to match. -/
theorem noSourceDirectionalBonds_of_recordAgreement (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationRecordAgreement molecule source)
    (noRaw : NoRawDirectionalRecords molecule) :
    diagramDirectionalBonds source = [] := by
  unfold NoRawDirectionalRecords at noRaw
  by_contra nonempty
  obtain ⟨entry, present⟩ := List.exists_mem_of_ne_nil (diagramDirectionalBonds source) nonempty
  obtain ⟨raw, rawMem, _⟩ := agreement.2.2.2 entry present
  rw [noRaw] at rawMem
  exact List.not_mem_nil rawMem

/-- Forward restriction: record agreement on the atom-parity domain yields the atom-parity
agreement with an explicit source-side directional absence. -/
theorem atomParityRecordAgreement_of_recordAgreement (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (noRaw : NoRawDirectionalRecords molecule)
    (agreement : RawAnnotationRecordAgreement molecule source) :
    AtomParityRecordAgreement molecule source :=
  ⟨agreement.1, agreement.2.1,
    noSourceDirectionalBonds_of_recordAgreement molecule source agreement noRaw⟩

/-- Backward restriction: the atom-parity agreement together with the atom-parity domain rebuilds
the record agreement; the directional components are vacuous rather than silently assumed. -/
theorem recordAgreement_of_atomParityRecordAgreement (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (noRaw : NoRawDirectionalRecords molecule)
    (atomAgreement : AtomParityRecordAgreement molecule source) :
    RawAnnotationRecordAgreement molecule source := by
  obtain ⟨atomsRaw, atomsDiagram, noSource⟩ := atomAgreement
  unfold NoRawDirectionalRecords at noRaw
  refine ⟨atomsRaw, atomsDiagram, ?_, ?_⟩
  · intro raw rawMem
    rw [noRaw] at rawMem
    exact False.elim (List.not_mem_nil rawMem)
  · intro entry entryMem
    rw [noSource] at entryMem
    exact False.elim (List.not_mem_nil entryMem)

/-- **Exact domain characterisation**: on the atom-parity domain the record agreement is exactly the
bidirectional atom-parity agreement plus the explicit source-side directional absence. -/
theorem recordAgreement_iff_atomParity_of_noRawDirectional (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (noRaw : NoRawDirectionalRecords molecule) :
    RawAnnotationRecordAgreement molecule source ↔ AtomParityRecordAgreement molecule source :=
  ⟨atomParityRecordAgreement_of_recordAgreement molecule source noRaw,
    recordAgreement_of_atomParityRecordAgreement molecule source noRaw⟩








namespace ConstitutionClosedWitness

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness

/-- The conversion-only parser index at the actual closed carbon center is exactly raw index `0`. -/
theorem parserSource_index_identity :
    (parserIndexViaConversion annotatedRawCF parserSource
      annotatedRawCF_toSemanticMolecule parserCenter).val = 0 := rfl

/-- Exact index identity for the actual closed source: the reverse transport returns the actual
semantic center index. -/
theorem parserSource_index_converted :
    annotatedRawCF.convertedAtomIndex parserSource annotatedRawCF_toSemanticMolecule
        (parserIndexViaConversion annotatedRawCF parserSource
          annotatedRawCF_toSemanticMolecule parserCenter) = parserCenter.val :=
  parserIndexViaConversion_converted annotatedRawCF parserSource
    annotatedRawCF_toSemanticMolecule parserCenter



theorem parserSource_annotationAgreement :
    RawAnnotationAgreement annotatedRawCF parserSource :=
  TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement.ClosedAuditExamples.positive_agreement



theorem parserSource_matched_absolute_configuration :
    ∃ configuration, configuration ∈ sourceAtomConfigurations parserSource ∧
      configuration.atom = 0 ∧ configuration.parity = TetrahedralInputParity.clockwise ∧
        configuration.scope = DiagramConfigurationScope.absolute :=
  recordAgreement_matched_absolute_configuration annotatedRawCF parserSource
    parserSource_annotationAgreement 0
    { AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise }
    TetrahedralInputParity.clockwise (by decide) (by rfl) (by rfl)

/-- The actual closed parser source aligns its actual raw written frame with the actual returned
occurrence endpoint IDs through the conversion-only index. -/
theorem parserSource_constitution_alignment_exists (fuel : Nat) :
    ∃ slots, constitutionOccurrenceSlotAlignment? annotatedRawCF parserSource
      annotatedRawCF_toSemanticMolecule
      (parserSource.aromaticCanonicalFinalOccurrence fuel parserCenter) = some slots := by
  have recovered := occurrenceTetrahedralCenter?_final parserSource fuel parserCenter
  have frames := finalOccurrenceRoots_are_returned parserSource fuel parserCenter
  have endpoints : rawWrittenLigandFrame annotatedRawCF
      (parserIndexViaConversion annotatedRawCF parserSource
        annotatedRawCF_toSemanticMolecule parserCenter) = [1, 2, 3, 4] := by
    unfold rawWrittenLigandFrame
    rw [parserSource_index_identity]
    exact parserSource_written_endpoints
  have sameIDs :
      (occurrenceRootIDs parserSource
        (finalOccurrenceRoots parserSource fuel parserCenter)).Perm ([1, 2, 3, 4].map some) := by
    have rootPerm := parserSource_root_ids fuel
    simpa [occurrenceRootIDs, finalOccurrenceRootIDs] using rootPerm
  obtain ⟨positions, found⟩ := findSlotAlignment?_exists_of_perm [1, 2, 3, 4] _
    (by decide) (by decide) sameIDs
  refine ⟨positions, ?_⟩
  simp [constitutionOccurrenceSlotAlignment?, recovered, frames, endpoints, found]

end ConstitutionClosedWitness

end TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
