import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Totality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TetraStereo.UniversalProof.SourceNativeParserRule6AdapterProofs.SourceNativeParserRule6Adapter

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.Rule6HandednessSemantics
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge





















































noncomputable def constitutionParserRule6WrittenReading? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) : Option RS := do
  let evidence ← constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
    target view ruleFuel
  some
    (writtenFramePriorityDescriptor evidence.writtenParity evidence.slots
      evidence.tracked.highestFirst)

/-- Independent complete meaning of one written-frame reading: the actual constitution rich priority
evidence (recovered center, actual raw annotation provenance, actual declarative reroot frame,
actual endpoint alignment, produced Rules-3--5 key frame, strict tracked-order judgment, universal
all-`S₄` parity transport law) and the actual `writtenFramePriorityDescriptor` value. -/
def ConstitutionParserRule6WrittenMeaning (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (reading : RS) : Prop :=
  ∃ evidence : ParserRichPriorityEvidence source carrierFuel,
    ConstitutionParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence ∧
      reading =
        writtenFramePriorityDescriptor evidence.writtenParity evidence.slots
          evidence.tracked.highestFirst

/-- Every written-frame reading is exactly the actual rich priority evidence and its actual
`writtenFramePriorityDescriptor` value. -/
theorem constitutionParserRule6WrittenReading?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) (reading : RS)
    (computed : constitutionParserRule6WrittenReading? molecule source agreement writtenExact
      target view ruleFuel = some reading) :
    ConstitutionParserRule6WrittenMeaning molecule source agreement writtenExact target view
      ruleFuel reading := by
  unfold constitutionParserRule6WrittenReading? at computed
  cases evidenceComputed : constitutionParserRichPriorityEvidence? molecule source agreement
      writtenExact target view ruleFuel with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      simp [evidenceComputed] at computed
      subst reading
      exact ⟨evidence,
        constitutionParserRichPriorityEvidence?_sound molecule source agreement writtenExact
          target view ruleFuel evidence evidenceComputed,
        rfl⟩

/-! ## 2. The parser Rule-6 adapter into the authoritative promoted pipeline -/












noncomputable def constitutionParserRule3Through6Descriptor? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (_writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) : Option RS := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let rawCenter := parserIndexViaConversion molecule source agreement.1 center
  let spec ← molecule.atomAt? rawCenter.val
  let writtenParity ← spec.tetrahedral?
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  let slots ← findSlotAlignment? (rawWrittenLigandFrame molecule rawCenter)
    (occurrenceRootIDs source roots)
  source.aromaticCanonicalRule3Through6Descriptor? center.1 target view ruleFuel roots
    (transportSlotParity writtenParity slots)









def ConstitutionParserRule3Through6Meaning (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (_writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : RS) : Prop :=
  molecule.WrittenNeighborExact ∧
    ∃ center roots slots spec writtenParity configuration slotPerm,
      source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center ∧
        molecule.atomAt?
            (parserIndexViaConversion molecule source agreement.1 center).val = some spec ∧
        spec.tetrahedral? = some writtenParity ∧
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
          (occurrenceRootIDs source roots) slots ∧
        finFourPermutationList slotPerm = slots ∧
        (∀ ordering : Equiv.Perm (Fin 4),
          descriptorOfFinFourOrdering (transportSlotParity writtenParity slots) ordering =
            descriptorOfFinFourOrdering writtenParity (ordering.trans slotPerm)) ∧
        source.AromaticCanonicalRule3Through6CompleteDescriptorJudgment center.1 target view
          ruleFuel roots (transportSlotParity writtenParity slots) descriptor ∧
        source.AromaticCanonicalRule3Through6ExecutableDescriptorJudgment center.1 target view
          ruleFuel roots (transportSlotParity writtenParity slots) descriptor

/-- Every parser Rule-6 adapter emission has the complete meaning above.  The proof composes the
conversion-only index, the actual record agreement, the fail-closed finite alignment, the universal
all-`S₄` transport law and the committed scheduler's soundness and totality results; it never
assumes an expected descriptor. -/
theorem constitutionParserRule3Through6Descriptor?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) (descriptor : RS)
    (computed : constitutionParserRule3Through6Descriptor? molecule source agreement writtenExact
      target view ruleFuel = some descriptor) :
    ConstitutionParserRule3Through6Meaning molecule source agreement writtenExact target view
      ruleFuel descriptor := by
  unfold constitutionParserRule3Through6Descriptor? at computed
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
                  | none =>
                      simp [centerComputed, atomComputed, rootsComputed,
                        slotsComputed] at computed
                  | some slots =>
                      have finalComputed :
                          source.aromaticCanonicalRule3Through6Descriptor? center.1 target view
                            ruleFuel roots (transportSlotParity writtenParity slots) =
                              some descriptor := by
                        simpa [centerComputed, atomComputed, parityComputed, rootsComputed,
                          slotsComputed] using computed
                      have memAnnot :
                          ({ index := (parserIndexViaConversion molecule source agreement.1
                                center).val, parity := writtenParity } :
                              RawAtomAnnotation) ∈ rawAtomAnnotations molecule :=
                        rawAtomAnnotation_mem molecule
                          (parserIndexViaConversion molecule source agreement.1 center).val spec
                          writtenParity
                          (parserIndexViaConversion molecule source agreement.1 center).isLt
                          atomComputed parityComputed
                      obtain ⟨configuration, configMem, atomEq, parityEq, scopeEq⟩ :=
                        recordAgreement_matched_absolute_configuration molecule source agreement
                          (parserIndexViaConversion molecule source agreement.1 center).val spec
                          writtenParity
                          (parserIndexViaConversion molecule source agreement.1 center).isLt
                          atomComputed parityComputed
                      obtain ⟨slotPerm, slotList, transportLaw⟩ :=
                        transportSlotParity_descriptor_universal writtenParity
                          (rawWrittenLigandFrame molecule
                            (parserIndexViaConversion molecule source agreement.1 center))
                          (occurrenceRootIDs source roots) slots
                          (findSlotAlignment?_sound _ _ slots slotsComputed)
                      exact ⟨center, roots, slots, spec, writtenParity, configuration, slotPerm,
                        rfl, atomComputed, parityComputed, memAnnot, configMem, atomEq,
                        parityEq, scopeEq,
                        source.aromaticCanonicalOccurrenceLigandFrame?_sound target roots
                          rootsComputed,
                        findSlotAlignment?_sound _ _ slots slotsComputed,
                        slotList, transportLaw,
                        source.aromaticCanonicalRule3Through6Descriptor?_sound center.1 target view
                          ruleFuel roots (transportSlotParity writtenParity slots) descriptor
                          finalComputed,
                        (source.aromaticCanonicalRule3Through6Descriptor?_eq_some_iff_executableJudgment
                          center.1 target view ruleFuel roots
                          (transportSlotParity writtenParity slots) descriptor).mp finalComputed⟩

/-- The adapter fails closed when the occurrence target carries no real tetrahedral center: no
descriptor is emitted rather than an arbitrary one. -/
theorem constitutionParserRule3Through6Descriptor?_eq_none_of_no_center (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (missing : source.aromaticCanonicalOccurrenceTetrahedralCenter? target = none) :
    constitutionParserRule3Through6Descriptor? molecule source agreement writtenExact target view
      ruleFuel = none := by
  unfold constitutionParserRule3Through6Descriptor?
  rw [missing]
  rfl

/-! ## 3. Rule-6 promotion resolves an actual Rules-1a--5 tie

The strengthened comparator exhausts Rules 1a--5 first and only then consults the Rule-6 promotion
layers.  These lemmas isolate the promotion-decisive case: the two literal promotion heads `1` and
`0` are compared, and because the sparse-layer order compares the head sphere of the root outward,
a strictly greater head decides the whole comparison. -/

/-- A strictly greater first sparse layer decides the whole sparse-layers comparison as `gt`,
independently of every deeper merged sphere. -/
theorem compareSparseLayers_cons_gt {α : Type*}
    (compare : α → α → Ordering) (a b : α)
    (leftRest rightRest : List (List (OfficialSparseEntry α)))
    (compared : compare a b = Ordering.gt) :
    OfficialRuleMajorKey.compareSparseLayers compare
      ([([], a)] :: leftRest) ([([], b)] :: rightRest) = Ordering.gt := by
  simp [OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
    OfficialRuleMajorKey.compareSparseEntry, List.compareLex, compareLex, Ordering.byKey,
    flip, compared]

/-- Head form: when both promotion layer lists begin with the literal marker layers `[([], a)]` and
`[([], b)]` and `compare a b = gt`, the whole sparse-layers comparison is `gt`. -/
theorem compareSparseLayers_of_head_gt {α : Type*} (compare : α → α → Ordering) (a b : α)
    (left right : List (List (OfficialSparseEntry α)))
    (compared : compare a b = Ordering.gt)
    (leftHead : left.head? = some [([], a)]) (rightHead : right.head? = some [([], b)]) :
    OfficialRuleMajorKey.compareSparseLayers compare left right = Ordering.gt := by
  cases left with
  | nil => simp at leftHead
  | cons leftLayer leftRest =>
      cases right with
      | nil => simp at rightHead
      | cons rightLayer rightRest =>
          simp only [List.head?_cons, Option.some.injEq] at leftHead rightHead
          subst leftLayer
          subst rightLayer
          exact compareSparseLayers_cons_gt compare a b leftRest rightRest compared

/-- **Promotion-decisive comparison.**  When two promoted keys tie completely under Rules 1a--5, and
their actual Rule-6 promotion layer lists begin with the literal markers `1` and `0`, the
strengthened Rules-1a--6 comparator resolves the tie to `gt` purely by Rule 6.  The tie is the
explicit prerequisite; the promotion heads and the marker comparison are the proved content. -/
theorem compareAromaticCanonicalRule3Through6PromotedKeys_of_tie_of_head_gt
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRule3Through6PromotedKey)
    (priorTie : source.compareAromaticCanonicalOccurrenceRule3Through5Keys
      left.prior right.prior = Ordering.eq)
    (leftHead : left.promotion.head? = some [([], 1)])
    (rightHead : right.promotion.head? = some [([], 0)]) :
    source.compareAromaticCanonicalRule3Through6PromotedKeys left right = Ordering.gt := by
  rw [source.compareAromaticCanonicalRule3Through6PromotedKeys_of_prior_eq left right priorTie]
  exact compareSparseLayers_of_head_gt OfficialRuleMajorKey.compareNat 1 0 left.promotion
    right.promotion (by decide) leftHead rightHead

/-- **Rule-6-dependent backend decision.**  On a complete Rules-1a--5 tie with promotion heads `1`
and `0`, the indexed-key comparison used by the authoritative backend is `gt` *and* the tracked
decision carries the pseudoasymmetric (`pseudo`) signal, exactly the `prior = eq ∧ ordering ≠ eq`
case that the backend defines as a Rule-6-dependent comparison. -/
theorem compareAromaticCanonicalRule3Through6IndexedKeys_of_tie_of_head_gt
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel)
    (priorTie : source.compareAromaticCanonicalOccurrenceRule3Through5Keys
      left.key.prior right.key.prior = Ordering.eq)
    (leftHead : left.key.promotion.head? = some [([], 1)])
    (rightHead : right.key.promotion.head? = some [([], 0)]) :
    (source.compareAromaticCanonicalRule3Through6IndexedKeys left right).ordering =
        Ordering.gt ∧
      (source.compareAromaticCanonicalRule3Through6IndexedKeys left right).pseudo := by
  have promoted := compareAromaticCanonicalRule3Through6PromotedKeys_of_tie_of_head_gt
    source left.key right.key priorTie leftHead rightHead
  refine ⟨?_, ?_⟩
  · rw [source.compareAromaticCanonicalRule3Through6IndexedKeys_ordering]
    exact promoted
  · exact (source.compareAromaticCanonicalRule3Through6IndexedKeys_pseudo_iff left right).mpr
      ⟨priorTie, by rw [promoted]; decide⟩

/-! ## 4. Conditional reference-sensitivity lemmas

The literal promotion marker is `1` at the reference cursor and `0` otherwise. Conditional
successful builds at one cursor under different references have the same prior and different
promotion heads. No source or successful build is constructed in this section; these comparisons
do not rank distinct ligands under the common reference required by an actual backend ranking. -/

/-- The literal promotion marker is `1` at a cursor whose actual node is the reference. -/
theorem aromaticCanonicalRule6PromotionMarker_eq_one_of_current
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (reference : source.AromaticCanonicalAtom)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (current : cursor.occurrence.1.node.current? = some reference) :
    aromaticCanonicalRule6PromotionMarker reference cursor = 1 := by
  unfold aromaticCanonicalRule6PromotionMarker
  simp [current]

/-- The literal promotion marker is `0` at an actual cursor whose node is *not* the reference. -/
theorem aromaticCanonicalRule6PromotionMarker_eq_zero_of_current_ne
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (reference otherReference : source.AromaticCanonicalAtom)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (current : cursor.occurrence.1.node.current? = some reference)
    (different : otherReference ≠ reference) :
    aromaticCanonicalRule6PromotionMarker otherReference cursor = 0 := by
  unfold aromaticCanonicalRule6PromotionMarker
  rw [current]
  have distinct : ¬ (some reference = some otherReference) := by
    intro same
    exact different (Option.some.inj same).symm
  simp [distinct]

/-- Every successful promoted build heads its promotion layers with the literal marker layer for the
reference at the cursor. -/
theorem buildAromaticCanonicalRule3Through6PromotedKey?_promotion_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view reference fuel cursor = some key →
      key.promotion.head? =
        some [([], aromaticCanonicalRule6PromotionMarker reference cursor)]
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalRule3Through6PromotedKey? at computed
      cases priorComputed :
          source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            excluded target view 0 cursor with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, aromaticCanonicalRerootChildren?] at computed
          let children := source.aromaticCanonicalRerootChildren cursor
          by_cases terminal : children = []
          · simp [children, terminal] at computed
            subst key
            simp
          · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalRule3Through6PromotedKey? at computed
      cases priorComputed :
          source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            excluded target view (fuel + 1) cursor with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, aromaticCanonicalRerootChildren?] at computed
          let children := source.aromaticCanonicalRerootChildren cursor
          by_cases terminal : children = []
          · simp [children, terminal] at computed
            subst key
            simp
          · cases childKeysComputed : children.mapM
                (source.buildAromaticCanonicalRule3Through6PromotedKey?
                  excluded target view reference fuel) with
            | none => simp [children, terminal, childKeysComputed] at computed
            | some childKeys =>
                let compare := source.compareAromaticCanonicalRule3Through6PromotedKeys
                let sorted := sortAromaticCanonicalRule3Through6PromotedKeys compare childKeys
                simp [children, terminal, childKeysComputed] at computed
                subst key
                simp

/-- The two promoted builds of one actual cursor under two references share one Rules-1a--5 prior:
the reference-invariance theorem transfers directly to the parser reference split. -/
theorem parserRule6ReferenceSplit_prior_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference otherReference : source.AromaticCanonicalAtom) (fuel : Nat)
    (left right : source.AromaticCanonicalRule3Through6PromotedKey)
    (leftComputed :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view reference fuel cursor = some left)
    (rightComputed :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view otherReference fuel cursor = some right) :
    left.prior = right.prior :=
  source.buildAromaticCanonicalRule3Through6PromotedKey?_prior_reference_invariant
    excluded target view reference otherReference fuel cursor left right leftComputed rightComputed

/-- Conditional sensitivity to two different references at one cursor. Successful builds and a
prior tie imply literal promotion heads `1` and `0` and comparison `gt`. These premises are not
inhabited here, and the comparison does not rank distinct ligands under one common reference.
A closed legal promotion-dependent source/backend/parser witness remains required. -/
theorem parserRule6ReferenceSplit_resolves
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference otherReference : source.AromaticCanonicalAtom) (fuel : Nat)
    (left right : source.AromaticCanonicalRule3Through6PromotedKey)
    (leftComputed :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view reference fuel cursor = some left)
    (rightComputed :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view otherReference fuel cursor = some right)
    (priorTie : source.compareAromaticCanonicalOccurrenceRule3Through5Keys
      left.prior right.prior = Ordering.eq)
    (current : cursor.occurrence.1.node.current? = some reference)
    (different : otherReference ≠ reference) :
    left.promotion.head? = some [([], 1)] ∧
      right.promotion.head? = some [([], 0)] ∧
        source.compareAromaticCanonicalRule3Through6PromotedKeys left right = Ordering.gt := by
  have leftMarker :=
    aromaticCanonicalRule6PromotionMarker_eq_one_of_current reference cursor current
  have rightMarker :=
    aromaticCanonicalRule6PromotionMarker_eq_zero_of_current_ne reference otherReference cursor
      current different
  have leftHead :=
    buildAromaticCanonicalRule3Through6PromotedKey?_promotion_head
      source excluded target view reference fuel cursor left leftComputed
  have rightHead :=
    buildAromaticCanonicalRule3Through6PromotedKey?_promotion_head
      source excluded target view otherReference fuel cursor right rightComputed
  refine ⟨?_, ?_, ?_⟩
  · rw [leftHead, leftMarker]
  · rw [rightHead, rightMarker]
  · exact compareAromaticCanonicalRule3Through6PromotedKeys_of_tie_of_head_gt source left right
      priorTie (by rw [leftHead, leftMarker]) (by rw [rightHead, rightMarker])

end TetraStereo.UniversalProof.SourceNativeParserRule6AdapterProofs.SourceNativeParserRule6Adapter
