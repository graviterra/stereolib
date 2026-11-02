import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.Rule6HandednessSemantics
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge










































/-! ## 1. The actual planar constitution rich priority channel -/









noncomputable def planarConstitutionParserRichPriorityEvidence? (molecule : RawMolecule)
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
  let keys ← buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
    source target view ruleFuel roots
  let tracked ← source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys
  some
    { slots := slots
      keys := keys
      tracked := tracked
      writtenParity := writtenParity
      raw := writtenFramePriorityDescriptor writtenParity slots tracked.highestFirst }









def PlanarConstitutionParserRichPriorityEvidenceMeaning (molecule : RawMolecule)
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
        DeclarativeAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame
          source target view ruleFuel roots evidence.keys ∧
        source.DeclarativeSafeAromaticCanonicalOccurrenceRule3Through5TrackedOrder
          evidence.keys evidence.tracked ∧
        finFourPermutationList slotPerm = evidence.slots ∧
        (∀ ordering : Equiv.Perm (Fin 4),
          descriptorOfFinFourOrdering (transportSlotParity writtenParity evidence.slots) ordering =
            descriptorOfFinFourOrdering writtenParity (ordering.trans slotPerm)) ∧
        evidence.raw =
          writtenFramePriorityDescriptor writtenParity evidence.slots
            evidence.tracked.highestFirst

/-- Every planar constitution rich priority evidence record is exactly the actual recovered center,
the actual raw annotation (record and matched absolute configuration), the actual declarative reroot
frame, the actual endpoint alignment, the actual planar key frame and strict tracked order, the
universal parity transport law and the actual raw descriptor. -/
theorem planarConstitutionParserRichPriorityEvidence?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (computed : planarConstitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence) :
    PlanarConstitutionParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence := by
  unfold planarConstitutionParserRichPriorityEvidence? at computed
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
                      cases keysComputed :
                          buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
                            source target view ruleFuel roots with
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
                                buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?_sound
                                  source target view ruleFuel roots keys keysComputed,
                                source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
                                  keys tracked trackedComputed,
                                slotList, transportLaw, rfl⟩

/-- Projection retaining the **NEW** planar key judgment from a successful evidence meaning: the
independent planar declarative judgment is present, at the actual recovered center and actual returned
roots, and never the old spatial key meaning. -/
theorem PlanarConstitutionParserRichPriorityEvidenceMeaning.planar_key_judgment
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (meaning : PlanarConstitutionParserRichPriorityEvidenceMeaning molecule source agreement
      writtenExact target view ruleFuel evidence) :
    ∃ center roots,
      source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center ∧
        DeclarativeAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame
          source target view ruleFuel roots evidence.keys := by
  obtain ⟨_, center, roots, spec, writtenParity, configuration, slotPerm,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := meaning
  exact ⟨center, roots, h1, h12⟩

/-- Projection retaining the actual strict tracked order and its actual `pseudoComparisons` record
from a successful evidence meaning; the pseudo count is never supplied by a caller. -/
theorem PlanarConstitutionParserRichPriorityEvidenceMeaning.tracked_judgment
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (meaning : PlanarConstitutionParserRichPriorityEvidenceMeaning molecule source agreement
      writtenExact target view ruleFuel evidence) :
    source.DeclarativeSafeAromaticCanonicalOccurrenceRule3Through5TrackedOrder
      evidence.keys evidence.tracked := by
  obtain ⟨_, center, roots, spec, writtenParity, configuration, slotPerm,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := meaning
  exact h13

/-- Projection retaining the actual raw written-frame descriptor from a successful evidence meaning:
it is the descriptor of the actual written parity and the actual strict-tracked priority order, with
no expected label. -/
theorem PlanarConstitutionParserRichPriorityEvidenceMeaning.raw_descriptor_self
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (meaning : PlanarConstitutionParserRichPriorityEvidenceMeaning molecule source agreement
      writtenExact target view ruleFuel evidence) :
    evidence.raw =
      writtenFramePriorityDescriptor evidence.writtenParity evidence.slots
        evidence.tracked.highestFirst := by
  obtain ⟨_, center, roots, spec, writtenParity, configuration, slotPerm,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := meaning
  rw [h4]
  exact h16

/-! ## 2. Refusal when the actual planar Rule-3 frame is unresolved -/

/-- The actual planar constitution rich channel refuses whenever the actual planar Rule-3 frame is
unresolved at the actual returned occurrence frame.  The hypothesis is about the genuinely recovered
frame (the equation is the actual ligand-frame result), not about any caller-supplied cursor list. -/
theorem planarConstitutionParserRichPriorityEvidence?_eq_none_of_planar_frame_unresolved
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (unresolved : ∀ roots, source.aromaticCanonicalOccurrenceLigandFrame? target = some roots →
      buildAromaticCanonicalPlanarRule3Frame? source ruleFuel roots = none) :
    planarConstitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = none := by
  unfold planarConstitutionParserRichPriorityEvidence?
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp
  | some center =>
      cases atomComputed : molecule.atomAt?
          (parserIndexViaConversion molecule source agreement.1 center).val with
      | none => simp [atomComputed]
      | some spec =>
          cases parityComputed : spec.tetrahedral? with
          | none => simp [atomComputed, parityComputed]
          | some writtenParity =>
              cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
              | none => simp
              | some roots =>
                  have keysNone := buildPlanarRule3Through5Frame?_eq_none_of_rule3_failure
                    source target view ruleFuel roots (unresolved roots rootsComputed)
                  cases slotsComputed : findSlotAlignment?
                      (rawWrittenLigandFrame molecule
                        (parserIndexViaConversion molecule source agreement.1 center))
                      (occurrenceRootIDs source roots) with
                  | none => simp [atomComputed, slotsComputed]
                  | some slots => simp [keysNone]

/-! ## 3. The planar constitution rich descriptor -/

/-- Planar constitution rich descriptor at an arbitrary original occurrence target: the actual raw
written-frame descriptor classified by the actual number of pseudo comparisons made by the strict
tracked sorter.  It reads no expected label, no supplied comparator and no success callback. -/
noncomputable def planarConstitutionParserRichDescriptor? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ← planarConstitutionParserRichPriorityEvidence? molecule source agreement writtenExact
    target view ruleFuel
  some (classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons)

/-- Independent complete meaning of one planar constitution rich descriptor emission. -/
def PlanarConstitutionParserRichDescriptorMeaning (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence,
    PlanarConstitutionParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence ∧
      descriptor = classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons

/-- Every planar constitution rich descriptor emission has the complete meaning above: no hidden
success branch, no caller permutation and no expected label. -/
theorem planarConstitutionParserRichDescriptor?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel = some descriptor) :
    PlanarConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact target view
      ruleFuel descriptor := by
  unfold planarConstitutionParserRichDescriptor? at computed
  cases evidenceComputed : planarConstitutionParserRichPriorityEvidence? molecule source agreement
      writtenExact target view ruleFuel with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      simp [evidenceComputed] at computed
      subst descriptor
      exact ⟨evidence,
        planarConstitutionParserRichPriorityEvidence?_sound molecule source agreement writtenExact
          target view ruleFuel evidence evidenceComputed,
        rfl⟩

/-- A successful descriptor emission exposes the actual raw written descriptor and the actual pseudo
comparison count of the actual strict tracked order. -/
theorem planarConstitutionParserRichDescriptor?_eq_some_classify (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel = some descriptor) :
    ∃ evidence,
      planarConstitutionParserRichPriorityEvidence? molecule source agreement writtenExact
          target view ruleFuel = some evidence ∧
        descriptor =
          classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons := by
  unfold planarConstitutionParserRichDescriptor? at computed
  cases evidenceComputed : planarConstitutionParserRichPriorityEvidence? molecule source agreement
      writtenExact target view ruleFuel with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      simp [evidenceComputed] at computed
      exact ⟨evidence, rfl, computed.symm⟩

/-- The descriptor refuses whenever the actual planar Rule-3 frame is unresolved. -/
theorem planarConstitutionParserRichDescriptor?_eq_none_of_planar_frame_unresolved
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (unresolved : ∀ roots, source.aromaticCanonicalOccurrenceLigandFrame? target = some roots →
      buildAromaticCanonicalPlanarRule3Frame? source ruleFuel roots = none) :
    planarConstitutionParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel = none := by
  unfold planarConstitutionParserRichDescriptor?
  rw [planarConstitutionParserRichPriorityEvidence?_eq_none_of_planar_frame_unresolved
    molecule source agreement writtenExact target view ruleFuel unresolved]
  rfl

/-! ## 4. Canonical assigned/unassigned constitution-planar outcomes -/

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)

/-- The canonical planar constitution parser descriptor judgment: the actual planar channel succeeds
with an actual evidence record carrying the complete independent meaning. -/
def CanonicalPlanarConstitutionParserRichDescriptor {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence,
    planarConstitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence ∧
    PlanarConstitutionParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence ∧
    descriptor = classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons

theorem canonical_planar_constitution_parser_rich_descriptor_sound {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (canonical : CanonicalPlanarConstitutionParserRichDescriptor molecule source agreement
      writtenExact target view ruleFuel descriptor) :
    PlanarConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact
      target view ruleFuel descriptor := by
  obtain ⟨evidence, _, meaning, classified⟩ := canonical
  exact ⟨evidence, meaning, classified⟩

theorem planarConstitutionParserRichDescriptor?_eq_some_iff_canonical {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel =
      some descriptor ↔
    CanonicalPlanarConstitutionParserRichDescriptor molecule source agreement writtenExact
      target view ruleFuel descriptor := by
  constructor
  · intro computed
    unfold planarConstitutionParserRichDescriptor? at computed
    cases evidenceComputed : planarConstitutionParserRichPriorityEvidence? molecule source agreement
        writtenExact target view ruleFuel with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        simp [evidenceComputed] at computed
        subst descriptor
        exact ⟨evidence, evidenceComputed,
          planarConstitutionParserRichPriorityEvidence?_sound molecule source agreement writtenExact
            target view ruleFuel evidence evidenceComputed, rfl⟩
  · rintro ⟨evidence, computed, _, rfl⟩
    simp [planarConstitutionParserRichDescriptor?, computed]

theorem planarConstitutionParserRichDescriptor?_eq_none_iff_no_canonical {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel =
      none ↔
      ¬∃ descriptor, CanonicalPlanarConstitutionParserRichDescriptor molecule source agreement
        writtenExact target view ruleFuel descriptor := by
  constructor
  · intro absent ⟨descriptor, canonical⟩
    have computed := (planarConstitutionParserRichDescriptor?_eq_some_iff_canonical
      molecule source agreement writtenExact target view ruleFuel descriptor).mpr canonical
    rw [absent] at computed
    contradiction
  · intro absent
    cases computed : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact
        target view ruleFuel with
    | none => rfl
    | some descriptor =>
        exact False.elim (absent ⟨descriptor,
          (planarConstitutionParserRichDescriptor?_eq_some_iff_canonical molecule source agreement
            writtenExact target view ruleFuel descriptor).mp computed⟩)

/-- Canonical outcome of the constitution-planar evaluator: `none` is the *unassigned* outcome
(no canonical descriptor exists) and `some descriptor` is the *assigned* outcome. -/
def PlanarConstitutionParserRichOutcome {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  match outcome with
  | none => ¬∃ descriptor, CanonicalPlanarConstitutionParserRichDescriptor molecule source agreement
      writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor
  | some descriptor => CanonicalPlanarConstitutionParserRichDescriptor molecule source agreement
      writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor

theorem planarConstitutionParserRichOutcome_iff {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) :
    PlanarConstitutionParserRichOutcome molecule source agreement writtenExact ruleFuel state target
        outcome ↔
      planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = outcome := by
  cases outcome with
  | none => exact (planarConstitutionParserRichDescriptor?_eq_none_iff_no_canonical
      molecule source agreement writtenExact target _ ruleFuel).symm
  | some descriptor => exact (planarConstitutionParserRichDescriptor?_eq_some_iff_canonical
      molecule source agreement writtenExact target _ ruleFuel descriptor).symm

/-- Independent source-canonical chemical semantics for the constitution-planar channel; its complete
optional-outcome correspondence is the exactness above. -/
noncomputable def planarConstitutionParserRichAuxiliarySemantics (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalRuleSemantics carrierFuel where
  DeclarativeDerivation := PlanarConstitutionParserRichOutcome molecule source agreement
    writtenExact ruleFuel
  executableRule := fun target view =>
    planarConstitutionParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel
  derivation_executable_iff := planarConstitutionParserRichOutcome_iff molecule source agreement
    writtenExact ruleFuel

/-- Any independently justified constitution-planar semantics has exactly one complete occurrence
model; the scheduled-model construction and full-agreement execution equivalence are retained for the
root. -/
theorem existsUnique_planarConstitutionParserRichCIPModel (carrierFuel ruleFuel : Nat) :
    ∃! state, (source.aromaticCanonicalOccurrenceSystem
      (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel state :=
  source.existsUnique_aromaticCanonicalCIPModel
    (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
      carrierFuel ruleFuel)

end TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence
