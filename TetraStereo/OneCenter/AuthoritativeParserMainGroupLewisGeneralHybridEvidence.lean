import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridEvidence
import TetraStereo.OneCenter.AuthoritativeParserElectronicInventoryRefinement

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Parser annotations into generalized-Lewis hybrid evidence

`RawMolecule` does not currently contain lone-pair, vacancy, or radical-position syntax.  This
module therefore does not claim to infer those data from the existing parser.  It defines the
small, explicit sidecar which a future parser/file-format observation layer must supply, transports
its raw atom indices through the proved parser-to-semantic conversion, and checks every transported
inventory against the independent generalized Lewis ledger.

An out-of-range raw index is rejected before materialization.  For valid indices, duplicate raw
keys are exactly duplicate semantic record keys because conversion preserves atom indices.  The
resulting certified analyzer inherits exact membership, no-duplication, and the per-bond
success/refusal dichotomy from the generalized-Lewis hybrid analyzer.
-/

/-- Electronic-state datum that is genuinely absent from the current `RawMolecule` syntax.
Its `atomIndex` is a parser atom index; all four counts are independent observations to be checked
against the generalized Lewis ledger, not conclusions drawn from connectivity. -/
structure ParserAtomElectronicStateAnnotation where
  atomIndex : Nat
  implicitProtia : Nat
  lonePairs : Nat
  vacancies : Nat
  unpairedElectronPositions : Nat
  deriving DecidableEq, Repr

namespace ParserAtomElectronicStateAnnotation

/-- Raw key used for duplicate detection before semantic materialization. -/
def key (annotation : ParserAtomElectronicStateAnnotation) : Nat :=
  annotation.atomIndex

/-- Literal electronic inventory recorded by the parser-side observation. -/
def inventory (annotation : ParserAtomElectronicStateAnnotation) :
    AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory where
  implicitProtia := annotation.implicitProtia
  lonePairs := annotation.lonePairs
  vacancies := annotation.vacancies
  unpairedElectronPositions := annotation.unpairedElectronPositions

end ParserAtomElectronicStateAnnotation

namespace RawMolecule

open AuthoritativeChemicalInput

/-- Every parser-side annotation names an atom actually present in the raw molecule. -/
def EveryParserAtomElectronicStateAnnotationIndexValid
    (molecule : RawMolecule)
    (annotations : List ParserAtomElectronicStateAnnotation) : Prop :=
  ∀ annotation, annotation ∈ annotations → annotation.atomIndex < molecule.atomCount

/-- Exact negative case for raw-index validation. -/
def HasInvalidParserAtomElectronicStateAnnotationIndex
    (molecule : RawMolecule)
    (annotations : List ParserAtomElectronicStateAnnotation) : Prop :=
  ∃ annotation ∈ annotations, ¬ annotation.atomIndex < molecule.atomCount

theorem not_everyParserAtomElectronicStateAnnotationIndexValid_iff_hasInvalid
    (molecule : RawMolecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    ¬ molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations ↔
      molecule.HasInvalidParserAtomElectronicStateAnnotationIndex annotations := by
  simp [EveryParserAtomElectronicStateAnnotationIndexValid,
    HasInvalidParserAtomElectronicStateAnnotationIndex]

/-- Materialize one valid raw annotation as a semantic atom record.  Invalid raw indices have no
record and are refused by the public bridge rather than silently discarded. -/
noncomputable def parserAtomElectronicStateRecord?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation) :
    Option source.AromaticCanonicalAtomElectronicStateRecord := by
  classical
  exact if valid : annotation.atomIndex < molecule.atomCount then
    some {
      atom := molecule.convertedAtomIndex source converted ⟨annotation.atomIndex, valid⟩
      inventory := annotation.inventory
    }
  else none

@[simp] theorem parserAtomElectronicStateRecord?_eq_none_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation) :
    molecule.parserAtomElectronicStateRecord? source converted annotation = none ↔
      ¬ annotation.atomIndex < molecule.atomCount := by
  classical
  simp [parserAtomElectronicStateRecord?]

/-- Exact content theorem for one materialized parser annotation. -/
theorem parserAtomElectronicStateRecord?_eq_some_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation)
    (record : source.AromaticCanonicalAtomElectronicStateRecord) :
    molecule.parserAtomElectronicStateRecord? source converted annotation = some record ↔
      annotation.atomIndex < molecule.atomCount ∧
        record.atom.val = annotation.atomIndex ∧
          record.inventory = annotation.inventory := by
  classical
  unfold parserAtomElectronicStateRecord?
  split
  next valid =>
    constructor
    · intro computed
      have recordIdentity :
          ({ atom := molecule.convertedAtomIndex source converted
                ⟨annotation.atomIndex, valid⟩,
              inventory := annotation.inventory } :
            source.AromaticCanonicalAtomElectronicStateRecord) = record :=
        Option.some.inj computed
      subst record
      exact ⟨valid, molecule.convertedAtomIndex_val source converted _, rfl⟩
    · rintro ⟨_validAgain, atomValue, inventoryIdentity⟩
      have atomIdentity :
          record.atom = molecule.convertedAtomIndex source converted
            ⟨annotation.atomIndex, valid⟩ := by
        apply Fin.ext
        simpa using atomValue
      cases record with
      | mk recordAtom recordInventory =>
          simp only at atomIdentity inventoryIdentity ⊢
          subst recordAtom
          subst recordInventory
          rfl
  next invalid =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨valid, _atomValue, _inventoryIdentity⟩
    exact invalid valid

/-- Materialize all parser-side annotations.  Public certification separately proves that no
annotation was lost to an invalid raw index. -/
noncomputable def parserAtomElectronicStateRecords
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    List source.AromaticCanonicalAtomElectronicStateRecord :=
  annotations.filterMap (molecule.parserAtomElectronicStateRecord? source converted)

/-- Under raw-index validity, the materialized record keys are literally the raw annotation keys.
This is the key fact preventing duplicate parser records from being hidden by transport. -/
theorem map_parserAtomElectronicStateRecords_key
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (valid : molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations) :
    (molecule.parserAtomElectronicStateRecords source converted annotations).map
        AromaticCanonicalAtomElectronicStateRecord.key =
      annotations.map ParserAtomElectronicStateAnnotation.key := by
  classical
  unfold parserAtomElectronicStateRecords
  induction annotations with
  | nil => rfl
  | cons annotation rest inductionHypothesis =>
      have headValid : annotation.atomIndex < molecule.atomCount :=
        valid annotation (by simp)
      have restValid : molecule.EveryParserAtomElectronicStateAnnotationIndexValid rest := by
        intro candidate present
        exact valid candidate (by simp [present])
      simp [parserAtomElectronicStateRecord?, headValid,
        AromaticCanonicalAtomElectronicStateRecord.key,
        ParserAtomElectronicStateAnnotation.key,
        inductionHypothesis restValid]

theorem parserAtomElectronicStateRecords_keys_nodup_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (valid : molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations) :
    ((molecule.parserAtomElectronicStateRecords source converted annotations).map
        AromaticCanonicalAtomElectronicStateRecord.key).Nodup ↔
      (annotations.map ParserAtomElectronicStateAnnotation.key).Nodup := by
  rw [molecule.map_parserAtomElectronicStateRecords_key source converted annotations valid]

/-- Independent semantic meaning of one parser-side annotation.  The existential index witness
makes out-of-range annotations false rather than vacuously valid. -/
def ParserAtomElectronicStateAnnotationSatisfiesMainGroupLewisGeneral
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation) : Prop :=
  ∃ valid : annotation.atomIndex < molecule.atomCount,
    source.MainGroupLewisGeneralAtomInventory
      (molecule.convertedAtomIndex source converted ⟨annotation.atomIndex, valid⟩)
      annotation.inventory

/-- Every materialized record satisfies the generalized Lewis ledger iff every raw annotation
does.  Thus validation is against the independent semantic relation, not merely against the
executable lookup result. -/
theorem every_parserAtomElectronicStateRecord_general_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (valid : molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations) :
    (∀ record, record ∈ molecule.parserAtomElectronicStateRecords source converted annotations →
      source.MainGroupLewisGeneralAtomInventory record.atom record.inventory) ↔
      ∀ annotation, annotation ∈ annotations →
        molecule.ParserAtomElectronicStateAnnotationSatisfiesMainGroupLewisGeneral
          source converted annotation := by
  classical
  constructor
  · intro recordsGeneral annotation present
    have annotationValid := valid annotation present
    refine ⟨annotationValid, ?_⟩
    apply recordsGeneral
      { atom := molecule.convertedAtomIndex source converted
          ⟨annotation.atomIndex, annotationValid⟩,
        inventory := annotation.inventory }
    unfold parserAtomElectronicStateRecords
    apply List.mem_filterMap.mpr
    exact ⟨annotation, present, by simp [parserAtomElectronicStateRecord?, annotationValid]⟩
  · intro annotationsGeneral record present
    unfold parserAtomElectronicStateRecords at present
    rcases List.mem_filterMap.mp present with ⟨annotation, annotationPresent, computed⟩
    have annotationGeneral := annotationsGeneral annotation annotationPresent
    rcases annotationGeneral with ⟨annotationValid, annotationGeneral⟩
    have exactContent :=
      (molecule.parserAtomElectronicStateRecord?_eq_some_iff
        source converted annotation record).mp computed
    have atomIdentity : record.atom =
        molecule.convertedAtomIndex source converted
          ⟨annotation.atomIndex, annotationValid⟩ := by
      apply Fin.ext
      simpa using exactContent.2.1
    simpa [atomIdentity, exactContent.2.2] using annotationGeneral

/-- The generic supplied-record well-formedness predicate is exactly raw key uniqueness plus
independent generalized-Lewis validity of every annotation. -/
theorem parserMainGroupLewisGeneralSuppliedRecordsWellFormed_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (valid : molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations) :
    source.MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed
        (molecule.parserAtomElectronicStateRecords source converted annotations) ↔
      (annotations.map ParserAtomElectronicStateAnnotation.key).Nodup ∧
        ∀ annotation, annotation ∈ annotations →
          molecule.ParserAtomElectronicStateAnnotationSatisfiesMainGroupLewisGeneral
            source converted annotation := by
  unfold AuthoritativeChemicalInput.MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed
  rw [molecule.parserAtomElectronicStateRecords_keys_nodup_iff
      source converted annotations valid,
    molecule.every_parserAtomElectronicStateRecord_general_iff
      source converted annotations valid]

/-- Parser-level readiness: no annotation is discarded, and its exact materialization satisfies
the already-proved generalized-Lewis hybrid certification predicate. -/
def ParserMainGroupLewisGeneralHybridCertificationReady
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) : Prop :=
  molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations ∧
    source.MainGroupLewisGeneralHybridCertificationReady
      (molecule.parserAtomElectronicStateRecords source converted annotations)

/-- Exhaustive parser-level refusal.  The first branch is the raw transport boundary; the second
expands into source-invalid, duplicate-record, ledger-invalid, and unresolved-endpoint cases. -/
def ParserMainGroupLewisGeneralHybridCertificationRefusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) : Prop :=
  molecule.HasInvalidParserAtomElectronicStateAnnotationIndex annotations ∨
    source.MainGroupLewisGeneralHybridCertificationRefusal
      (molecule.parserAtomElectronicStateRecords source converted annotations)

/-- Exact positive theorem.  Parser-level certification succeeds precisely when indices are in
range, the source is structurally valid, raw annotation keys are unique, every raw annotation
satisfies the independent generalized Lewis ledger, and every retained endpoint is supplied or
uniquely inferable. -/
theorem parserMainGroupLewisGeneralHybridCertificationReady_iff_exact_conditions
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    molecule.ParserMainGroupLewisGeneralHybridCertificationReady
        source converted annotations ↔
      molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations ∧
      source.StructurallyWellFormed ∧
      (annotations.map ParserAtomElectronicStateAnnotation.key).Nodup ∧
      (∀ annotation, annotation ∈ annotations →
        molecule.ParserAtomElectronicStateAnnotationSatisfiesMainGroupLewisGeneral
          source converted annotation) ∧
      source.EveryIndividualDoubleBondEndpointMainGroupLewisGeneralHybridResolved
        (molecule.parserAtomElectronicStateRecords source converted annotations) := by
  constructor
  · rintro ⟨valid, sourceWellFormed, suppliedWellFormed, resolved⟩
    have rawWellFormed :=
      (molecule.parserMainGroupLewisGeneralSuppliedRecordsWellFormed_iff
        source converted annotations valid).mp suppliedWellFormed
    exact ⟨valid, sourceWellFormed, rawWellFormed.1, rawWellFormed.2, resolved⟩
  · rintro ⟨valid, sourceWellFormed, uniqueKeys, annotationsGeneral, resolved⟩
    have suppliedWellFormed :=
      (molecule.parserMainGroupLewisGeneralSuppliedRecordsWellFormed_iff
        source converted annotations valid).mpr ⟨uniqueKeys, annotationsGeneral⟩
    exact ⟨valid, sourceWellFormed, suppliedWellFormed, resolved⟩

theorem not_parserMainGroupLewisGeneralHybridCertificationReady_iff_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    ¬ molecule.ParserMainGroupLewisGeneralHybridCertificationReady
        source converted annotations ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  unfold ParserMainGroupLewisGeneralHybridCertificationReady
    ParserMainGroupLewisGeneralHybridCertificationRefusal
  rw [not_and_or,
    molecule.not_everyParserAtomElectronicStateAnnotationIndexValid_iff_hasInvalid,
    source.not_mainGroupLewisGeneralHybridCertificationReady_iff_refusal]

/-- Exact public refusal theorem with duplicate annotations stated in raw parser keys. -/
theorem parserMainGroupLewisGeneralHybridCertificationRefusal_iff_exact_cases
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations ↔
      molecule.HasInvalidParserAtomElectronicStateAnnotationIndex annotations ∨
      ¬ source.StructurallyWellFormed ∨
      ¬ (annotations.map ParserAtomElectronicStateAnnotation.key).Nodup ∨
      (∃ annotation ∈ annotations,
        ¬ molecule.ParserAtomElectronicStateAnnotationSatisfiesMainGroupLewisGeneral
          source converted annotation) ∨
      (∃ endpoint partner,
        source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
        source.aromaticCanonicalAtomElectronicStateLookup?
            (molecule.parserAtomElectronicStateRecords source converted annotations)
            endpoint = none ∧
        ¬ ∃ inventory,
          source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory endpoint inventory) := by
  classical
  by_cases invalid :
      molecule.HasInvalidParserAtomElectronicStateAnnotationIndex annotations
  · simp [ParserMainGroupLewisGeneralHybridCertificationRefusal, invalid]
  · have valid : molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations :=
      Classical.byContradiction fun notValid =>
        invalid ((molecule.not_everyParserAtomElectronicStateAnnotationIndexValid_iff_hasInvalid
          annotations).mp notValid)
    have keys := molecule.map_parserAtomElectronicStateRecords_key
      source converted annotations valid
    have generalEquivalence := molecule.every_parserAtomElectronicStateRecord_general_iff
      source converted annotations valid
    have invalidRecordsEquivalence := not_congr generalEquivalence
    push_neg at invalidRecordsEquivalence
    unfold ParserMainGroupLewisGeneralHybridCertificationRefusal
      AuthoritativeChemicalInput.MainGroupLewisGeneralHybridCertificationRefusal
    rw [keys, invalidRecordsEquivalence]

/-- Certified semantic evidence obtained from validated parser annotations. -/
noncomputable def certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations) :
    CertifiedAuthoritativeChemicalInputWithAtomElectronicStates :=
  source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
    (molecule.parserAtomElectronicStateRecords source converted annotations) ready.2

/-- Exact parser-side certifier. -/
noncomputable def certifyMainGroupLewisGeneralHybridAtomElectronicStatesOfParser?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    Option CertifiedAuthoritativeChemicalInputWithAtomElectronicStates := by
  classical
  exact if ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations then
    some (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
      source converted annotations ready)
  else none

@[simp] theorem certifyMainGroupLewisGeneralHybridAtomElectronicStatesOfParser?_isSome_iff_ready
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    (molecule.certifyMainGroupLewisGeneralHybridAtomElectronicStatesOfParser?
      source converted annotations).isSome ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationReady
        source converted annotations := by
  classical
  simp [certifyMainGroupLewisGeneralHybridAtomElectronicStatesOfParser?]

@[simp] theorem certifyMainGroupLewisGeneralHybridAtomElectronicStatesOfParser?_eq_none_iff_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    molecule.certifyMainGroupLewisGeneralHybridAtomElectronicStatesOfParser?
        source converted annotations = none ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  rw [← molecule.not_parserMainGroupLewisGeneralHybridCertificationReady_iff_refusal
    source converted annotations]
  simp [certifyMainGroupLewisGeneralHybridAtomElectronicStatesOfParser?]

/-- Total ordinary-double-bond analyzer guarded by exact parser-side validation. -/
noncomputable def analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    Option (List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) := by
  classical
  exact if ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations then
    some ((molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
      source converted annotations ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt)
  else none

@[simp] theorem analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?_eq_none_iff_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    molecule.analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel viewAt = none ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  rw [← molecule.not_parserMainGroupLewisGeneralHybridCertificationReady_iff_refusal
    source converted annotations]
  simp [analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?]

theorem analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    molecule.analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel viewAt =
      some ((molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
        source converted annotations ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt) := by
  classical
  simp [analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?, ready]

theorem analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?_some_nodup
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignments : List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (computed : molecule.analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence?
      source converted annotations carrierFuel viewAt = some assignments) :
    assignments.Nodup := by
  classical
  unfold analyzeOrdinaryDoubleBondsOfParserMainGroupLewisGeneralHybridEvidence? at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst assignments
    exact (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
      source converted annotations ready).analyzeOrdinaryDoubleBonds_nodup carrierFuel viewAt
  next notReady => contradiction

/-- Exact public membership theorem for the certified parser-annotation analyzer. -/
theorem mem_certifiedParserMainGroupLewisGeneralHybridAnalyzeOrdinaryDoubleBonds_iff_canonical
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈
        (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
          source converted annotations ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
            source converted annotations ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) assignment := by
  exact (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
    source converted annotations ready).mem_analyzeOrdinaryDoubleBonds_iff_canonical
      carrierFuel viewAt assignment

/-- Every retained bond is either emitted exactly once under readiness or receives the exhaustive
inventory-aware refusal and no automatic assignment. -/
theorem every_certifiedParserMainGroupLewisGeneralHybridIndividualDoubleBond_exact_success_or_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel
          (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
            source converted annotations ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈
            (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
              source converted annotations ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt ∧
          assignment.bond = bond) ∨
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel
          (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
            source converted annotations ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel
          (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
            source converted annotations ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) = none) := by
  exact (molecule.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfParserReady
    source converted annotations ready).every_individualDoubleBond_exact_success_or_refusal
      carrierFuel viewAt

end RawMolecule
end TetraStereo.OneCenter
