import TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
import TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeDevelopmentTransaction
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard









































/-! ## 1. Actual raw annotation records and actual source diagram records -/

/-- One actual normalized raw atom parity, retaining its parser index. -/
structure RawAtomAnnotation where
  index : Nat
  parity : TetrahedralInputParity
  deriving DecidableEq, Repr

/-- One actual normalized raw directional bond record (`up`/`down`, i.e. `/`/`\`) with its bool. -/
structure RawBondDirection where
  bond : RawBond
  direction : Bool
  deriving DecidableEq, Repr

/-- Every real raw atom index whose normalized specification carries a tetrahedral parity. -/
def rawAtomAnnotations (molecule : RawMolecule) : List RawAtomAnnotation :=
  (List.range molecule.atomCount).filterMap fun index =>
    (molecule.atomAt? index).bind fun spec =>
      spec.tetrahedral?.map fun parity => { index := index, parity := parity }

/-- Every actual raw directional bond record, retaining its endpoint order and direction bool. -/
def rawBondDirections (molecule : RawMolecule) : List RawBondDirection :=
  molecule.bonds.filterMap fun bond =>
    bond.kind.directional?.map fun direction => { bond := bond, direction := direction }

/-- Every actual source diagram atom configuration, including out-of-range indices. -/
def sourceAtomConfigurations (source : AuthoritativeChemicalInput) :
    List DiagramAtomConfiguration :=
  (source.diagram?.map DiagramConfiguration.atomConfigurations).getD []

/-- Every actual source diagram directional bond, paired with its `/`-vs-`\` bool. -/
def diagramDirectionalBonds (source : AuthoritativeChemicalInput) : List (DiagramBond × Bool) :=
  ((source.diagram?.map DiagramConfiguration.bonds).getD []).filterMap fun bond =>
    match bond.style with
    | .directionalUp => some (bond, true)
    | .directionalDown => some (bond, false)
    | _ => none

/-! ## 2. Independent bidirectional projection meaning -/

/-- Index/parity/scope match between one raw annotation and one diagram atom configuration. -/
def RawAtomAnnotation.matchesConfiguration (annotation : RawAtomAnnotation)
    (configuration : DiagramAtomConfiguration) : Bool :=
  (configuration.atom == annotation.index) &&
    ((configuration.parity == annotation.parity) &&
      (configuration.scope == DiagramConfigurationScope.absolute))

theorem RawAtomAnnotation.matchesConfiguration_eq_true_iff (annotation : RawAtomAnnotation)
    (configuration : DiagramAtomConfiguration) :
    annotation.matchesConfiguration configuration = true ↔
      configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
        configuration.scope = DiagramConfigurationScope.absolute := by
  unfold RawAtomAnnotation.matchesConfiguration
  simp only [Bool.and_eq_true, beq_iff_eq]

/-- A raw annotation is supported by the actual source diagram records. -/
def RawAtomAnnotation.supportedBy (annotation : RawAtomAnnotation)
    (source : AuthoritativeChemicalInput) : Bool :=
  (sourceAtomConfigurations source).any annotation.matchesConfiguration

theorem RawAtomAnnotation.supportedBy_eq_true_iff (annotation : RawAtomAnnotation)
    (source : AuthoritativeChemicalInput) :
    annotation.supportedBy source = true ↔
      ∃ configuration, configuration ∈ sourceAtomConfigurations source ∧
        configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
          configuration.scope = DiagramConfigurationScope.absolute := by
  unfold RawAtomAnnotation.supportedBy
  rw [List.any_eq_true]
  constructor
  · rintro ⟨configuration, present, matched⟩
    exact ⟨configuration, present,
      (RawAtomAnnotation.matchesConfiguration_eq_true_iff annotation configuration).mp matched⟩
  · rintro ⟨configuration, present, atomEq, parityEq, scopeEq⟩
    exact ⟨configuration, present,
      (RawAtomAnnotation.matchesConfiguration_eq_true_iff annotation configuration).mpr
        ⟨atomEq, parityEq, scopeEq⟩⟩

/-- A diagram atom configuration is supported by the actual raw annotation records. -/
def rawConfigurationSupported? (configuration : DiagramAtomConfiguration)
    (molecule : RawMolecule) : Bool :=
  (rawAtomAnnotations molecule).any fun annotation => annotation.matchesConfiguration configuration

theorem rawConfigurationSupported?_eq_true_iff (configuration : DiagramAtomConfiguration)
    (molecule : RawMolecule) :
    rawConfigurationSupported? configuration molecule = true ↔
      ∃ annotation, annotation ∈ rawAtomAnnotations molecule ∧
        configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
          configuration.scope = DiagramConfigurationScope.absolute := by
  unfold rawConfigurationSupported?
  rw [List.any_eq_true]
  constructor
  · rintro ⟨annotation, present, matched⟩
    exact ⟨annotation, present,
      (RawAtomAnnotation.matchesConfiguration_eq_true_iff annotation configuration).mp matched⟩
  · rintro ⟨annotation, present, atomEq, parityEq, scopeEq⟩
    exact ⟨annotation, present,
      (RawAtomAnnotation.matchesConfiguration_eq_true_iff annotation configuration).mpr
        ⟨atomEq, parityEq, scopeEq⟩⟩

/-- Directed-endpoint-orientation and `/`-vs-`\` direction match between a raw bond and a diagram
bond.  Orientation is exact: a reversed record never matches, and `false` is never dropped. -/
def RawBondDirection.matchesDiagramBond (raw : RawBondDirection)
    (entry : DiagramBond × Bool) : Bool :=
  (entry.1.source == raw.bond.source) &&
    ((entry.1.target == raw.bond.target) && decide (entry.2 = raw.direction))

theorem RawBondDirection.matchesDiagramBond_eq_true_iff (raw : RawBondDirection)
    (entry : DiagramBond × Bool) :
    raw.matchesDiagramBond entry = true ↔
      entry.1.source = raw.bond.source ∧ entry.1.target = raw.bond.target ∧
        entry.2 = raw.direction := by
  unfold RawBondDirection.matchesDiagramBond
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

/-- A raw direction is supported by the actual source diagram directional records. -/
def RawBondDirection.supportedByDiagram (raw : RawBondDirection)
    (source : AuthoritativeChemicalInput) : Bool :=
  (diagramDirectionalBonds source).any raw.matchesDiagramBond

theorem RawBondDirection.supportedByDiagram_eq_true_iff (raw : RawBondDirection)
    (source : AuthoritativeChemicalInput) :
    raw.supportedByDiagram source = true ↔
      ∃ entry, entry ∈ diagramDirectionalBonds source ∧
        entry.1.source = raw.bond.source ∧ entry.1.target = raw.bond.target ∧
          entry.2 = raw.direction := by
  unfold RawBondDirection.supportedByDiagram
  rw [List.any_eq_true]
  constructor
  · rintro ⟨entry, present, matched⟩
    exact ⟨entry, present,
      (RawBondDirection.matchesDiagramBond_eq_true_iff raw entry).mp matched⟩
  · rintro ⟨entry, present, sourceEq, targetEq, directionEq⟩
    exact ⟨entry, present,
      (RawBondDirection.matchesDiagramBond_eq_true_iff raw entry).mpr
        ⟨sourceEq, targetEq, directionEq⟩⟩

/-- A diagram directional bond is supported by the actual raw directional records. -/
def rawBondSupported? (entry : DiagramBond × Bool) (molecule : RawMolecule) : Bool :=
  (rawBondDirections molecule).any fun raw => raw.matchesDiagramBond entry

theorem rawBondSupported?_eq_true_iff (entry : DiagramBond × Bool) (molecule : RawMolecule) :
    rawBondSupported? entry molecule = true ↔
      ∃ raw, raw ∈ rawBondDirections molecule ∧
        entry.1.source = raw.bond.source ∧ entry.1.target = raw.bond.target ∧
          entry.2 = raw.direction := by
  unfold rawBondSupported?
  rw [List.any_eq_true]
  constructor
  · rintro ⟨raw, present, matched⟩
    exact ⟨raw, present, (RawBondDirection.matchesDiagramBond_eq_true_iff raw entry).mp matched⟩
  · rintro ⟨raw, present, sourceEq, targetEq, directionEq⟩
    exact ⟨raw, present,
      (RawBondDirection.matchesDiagramBond_eq_true_iff raw entry).mpr
        ⟨sourceEq, targetEq, directionEq⟩⟩



/-- One typed raw-related record disagreeing across the two inputs. -/
inductive RawAnnotationAgreementIssue where
  | unsupportedRawAtomParity (annotation : RawAtomAnnotation)
  | unsupportedDiagramAtomConfiguration (configuration : DiagramAtomConfiguration)
  | unsupportedRawBondDirection (raw : RawBondDirection)
  | unsupportedDiagramDirectionalBond (bond : DiagramBond) (direction : Bool)
  deriving DecidableEq

theorem option_ite_none_eq_none_iff {α : Type*} (condition : Bool) (value : α) :
    (if condition then (none : Option α) else some value) = none ↔ condition = true := by
  cases condition <;> simp

def rawAtomIssues (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    List RawAnnotationAgreementIssue :=
  (rawAtomAnnotations molecule).filterMap fun annotation =>
    if annotation.supportedBy source then none
    else some (.unsupportedRawAtomParity annotation)

def diagramAtomIssues (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    List RawAnnotationAgreementIssue :=
  (sourceAtomConfigurations source).filterMap fun configuration =>
    if rawConfigurationSupported? configuration molecule then none
    else some (.unsupportedDiagramAtomConfiguration configuration)

def rawBondIssues (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    List RawAnnotationAgreementIssue :=
  (rawBondDirections molecule).filterMap fun raw =>
    if raw.supportedByDiagram source then none
    else some (.unsupportedRawBondDirection raw)

def diagramBondIssues (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    List RawAnnotationAgreementIssue :=
  (diagramDirectionalBonds source).filterMap fun entry =>
    if rawBondSupported? entry molecule then none
    else some (.unsupportedDiagramDirectionalBond entry.1 entry.2)


def rawAnnotationAgreementIssues (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    List RawAnnotationAgreementIssue :=
  rawAtomIssues molecule source ++ diagramAtomIssues molecule source ++
    rawBondIssues molecule source ++ diagramBondIssues molecule source

theorem rawAtomIssues_eq_nil_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    rawAtomIssues molecule source = [] ↔
      ∀ annotation, annotation ∈ rawAtomAnnotations molecule →
        ∃ configuration, configuration ∈ sourceAtomConfigurations source ∧
          configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
            configuration.scope = DiagramConfigurationScope.absolute := by
  unfold rawAtomIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty annotation present
    have supported : annotation.supportedBy source = true :=
      (option_ite_none_eq_none_iff (α := RawAnnotationAgreementIssue)
        (annotation.supportedBy source) (.unsupportedRawAtomParity annotation)).mp
        (empty annotation present)
    exact (RawAtomAnnotation.supportedBy_eq_true_iff annotation source).mp supported
  · intro recordAgreement annotation present
    have supported : annotation.supportedBy source = true :=
      (RawAtomAnnotation.supportedBy_eq_true_iff annotation source).mpr
        (recordAgreement annotation present)
    exact (option_ite_none_eq_none_iff (α := RawAnnotationAgreementIssue)
      (annotation.supportedBy source) (.unsupportedRawAtomParity annotation)).mpr supported

theorem diagramAtomIssues_eq_nil_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    diagramAtomIssues molecule source = [] ↔
      ∀ configuration, configuration ∈ sourceAtomConfigurations source →
        ∃ annotation, annotation ∈ rawAtomAnnotations molecule ∧
          configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
            configuration.scope = DiagramConfigurationScope.absolute := by
  unfold diagramAtomIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty configuration present
    have supported : rawConfigurationSupported? configuration molecule = true :=
      (option_ite_none_eq_none_iff (α := RawAnnotationAgreementIssue)
        (rawConfigurationSupported? configuration molecule)
        (.unsupportedDiagramAtomConfiguration configuration)).mp (empty configuration present)
    exact (rawConfigurationSupported?_eq_true_iff configuration molecule).mp supported
  · intro recordAgreement configuration present
    have supported : rawConfigurationSupported? configuration molecule = true :=
      (rawConfigurationSupported?_eq_true_iff configuration molecule).mpr
        (recordAgreement configuration present)
    exact (option_ite_none_eq_none_iff (α := RawAnnotationAgreementIssue)
      (rawConfigurationSupported? configuration molecule)
      (.unsupportedDiagramAtomConfiguration configuration)).mpr supported

theorem rawBondIssues_eq_nil_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    rawBondIssues molecule source = [] ↔
      ∀ raw, raw ∈ rawBondDirections molecule →
        ∃ entry, entry ∈ diagramDirectionalBonds source ∧
          entry.1.source = raw.bond.source ∧ entry.1.target = raw.bond.target ∧
            entry.2 = raw.direction := by
  unfold rawBondIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty raw present
    have supported : raw.supportedByDiagram source = true :=
      (option_ite_none_eq_none_iff (α := RawAnnotationAgreementIssue)
        (raw.supportedByDiagram source) (.unsupportedRawBondDirection raw)).mp
        (empty raw present)
    exact (RawBondDirection.supportedByDiagram_eq_true_iff raw source).mp supported
  · intro recordAgreement raw present
    have supported : raw.supportedByDiagram source = true :=
      (RawBondDirection.supportedByDiagram_eq_true_iff raw source).mpr
        (recordAgreement raw present)
    exact (option_ite_none_eq_none_iff (α := RawAnnotationAgreementIssue)
      (raw.supportedByDiagram source) (.unsupportedRawBondDirection raw)).mpr supported

theorem diagramBondIssues_eq_nil_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    diagramBondIssues molecule source = [] ↔
      ∀ entry, entry ∈ diagramDirectionalBonds source →
        ∃ raw, raw ∈ rawBondDirections molecule ∧
          entry.1.source = raw.bond.source ∧ entry.1.target = raw.bond.target ∧
            entry.2 = raw.direction := by
  unfold diagramBondIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty entry present
    have supported : rawBondSupported? entry molecule = true :=
      (option_ite_none_eq_none_iff (α := RawAnnotationAgreementIssue)
        (rawBondSupported? entry molecule)
        (.unsupportedDiagramDirectionalBond entry.1 entry.2)).mp (empty entry present)
    exact (rawBondSupported?_eq_true_iff entry molecule).mp supported
  · intro recordAgreement entry present
    have supported : rawBondSupported? entry molecule = true :=
      (rawBondSupported?_eq_true_iff entry molecule).mpr (recordAgreement entry present)
    exact (option_ite_none_eq_none_iff (α := RawAnnotationAgreementIssue)
      (rawBondSupported? entry molecule)
      (.unsupportedDiagramDirectionalBond entry.1 entry.2)).mpr supported

/-- Every diagram atom configuration with no matching raw specification is an explicit issue.  This
covers unmatched records and out-of-range indices (every raw annotation index lies in
`List.range molecule.atomCount`), so no diagram atom event is silently dropped. -/
theorem diagramConfiguration_flagged_of_unmatched (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (configuration : DiagramAtomConfiguration)
    (present : configuration ∈ sourceAtomConfigurations source)
    (unmatched : ¬ ∃ annotation, annotation ∈ rawAtomAnnotations molecule ∧
        configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
          configuration.scope = DiagramConfigurationScope.absolute) :
    RawAnnotationAgreementIssue.unsupportedDiagramAtomConfiguration configuration ∈
      rawAnnotationAgreementIssues molecule source := by
  have falseSupported : rawConfigurationSupported? configuration molecule = false :=
    Bool.eq_false_of_not_eq_true fun supported =>
      unmatched ((rawConfigurationSupported?_eq_true_iff configuration molecule).mp supported)
  have inDiagram : RawAnnotationAgreementIssue.unsupportedDiagramAtomConfiguration configuration ∈
      diagramAtomIssues molecule source := by
    unfold diagramAtomIssues
    rw [List.mem_filterMap]
    exact ⟨configuration, present, by simp [falseSupported]⟩
  unfold rawAnnotationAgreementIssues
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inr inDiagram)))))

/-- The independent record agreement: full bidirectional raw-to-diagram and diagram-to-raw
correspondence of the atom-parity and directional-bond records. -/
def RawAnnotationRecordAgreement (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    Prop :=
  (∀ annotation, annotation ∈ rawAtomAnnotations molecule →
      ∃ configuration, configuration ∈ sourceAtomConfigurations source ∧
        configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
          configuration.scope = DiagramConfigurationScope.absolute) ∧
    (∀ configuration, configuration ∈ sourceAtomConfigurations source →
      ∃ annotation, annotation ∈ rawAtomAnnotations molecule ∧
        configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
          configuration.scope = DiagramConfigurationScope.absolute) ∧
      (∀ raw, raw ∈ rawBondDirections molecule →
        ∃ entry, entry ∈ diagramDirectionalBonds source ∧
          entry.1.source = raw.bond.source ∧ entry.1.target = raw.bond.target ∧
            entry.2 = raw.direction) ∧
        (∀ entry, entry ∈ diagramDirectionalBonds source →
          ∃ raw, raw ∈ rawBondDirections molecule ∧
            entry.1.source = raw.bond.source ∧ entry.1.target = raw.bond.target ∧
              entry.2 = raw.direction)


theorem rawAnnotationAgreementIssues_eq_nil_iff (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) :
    rawAnnotationAgreementIssues molecule source = [] ↔
      RawAnnotationRecordAgreement molecule source := by
  unfold rawAnnotationAgreementIssues RawAnnotationRecordAgreement
  rw [List.append_eq_nil_iff, List.append_eq_nil_iff, List.append_eq_nil_iff,
    rawAtomIssues_eq_nil_iff, diagramAtomIssues_eq_nil_iff,
    rawBondIssues_eq_nil_iff, diagramBondIssues_eq_nil_iff]
  simp only [and_assoc]

theorem recordAgreement_false_of_issues (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (nonempty : rawAnnotationAgreementIssues molecule source ≠ []) :
    ¬ RawAnnotationRecordAgreement molecule source :=
  fun agreement =>
    nonempty ((rawAnnotationAgreementIssues_eq_nil_iff molecule source).mpr agreement)

/-! ## 4. Conversion pinning and restricted admission gate -/

/-- Record agreement together with the exact checked semantic conversion: the source atom-index
space is the raw parser atom-index space. -/
def RawAnnotationAgreement (molecule : RawMolecule) (source : AuthoritativeChemicalInput) : Prop :=
  molecule.toSemanticMolecule? = some source.molecule ∧
    RawAnnotationRecordAgreement molecule source

/-- The pinned conversion makes the source atom index identity exact. -/
theorem RawAnnotationAgreement.semanticAtom_index_identity (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (index : Nat) :
    listGet? source.molecule.atoms index =
      (molecule.atomAt? index).bind AtomSpec.toSemanticAtom? :=
  molecule.toSemanticMolecule?_atomAt? source.molecule agreement.1 index

theorem rawAnnotationAgreement_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    RawAnnotationAgreement molecule source ↔
      molecule.toSemanticMolecule? = some source.molecule ∧
        rawAnnotationAgreementIssues molecule source = [] := by
  unfold RawAnnotationAgreement
  rw [rawAnnotationAgreementIssues_eq_nil_iff]


def recordAudited (molecule : RawMolecule) (source : AuthoritativeChemicalInput) : Bool :=
  decide (rawAnnotationAgreementIssues molecule source = [])

theorem recordAudited_eq_true_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    recordAudited molecule source = true ↔ RawAnnotationRecordAgreement molecule source := by
  unfold recordAudited
  rw [decide_eq_true_eq, rawAnnotationAgreementIssues_eq_nil_iff]

theorem recordAudited_eq_false_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput) :
    recordAudited molecule source = false ↔ ¬ RawAnnotationRecordAgreement molecule source := by
  rw [← recordAudited_eq_true_iff]
  cases recordAudited molecule source <;> simp

/-- Conditional logical placeholder for an externally specified interpreter predicate.
The arbitrary `Prop` parameter has no interpreter implementation or completeness law here.
This definition does not establish interpretation or acceptance by a production payload API. -/
def AnnotationAdmitted (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (interpreter : Prop) : Prop :=
  RawAnnotationAgreement molecule source ∧ interpreter

theorem AnnotationAdmitted.recordAgreement (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (interpreter : Prop)
    (admitted : AnnotationAdmitted molecule source interpreter) :
    RawAnnotationRecordAgreement molecule source :=
  admitted.1.2

theorem not_annotationAdmitted_of_issue (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (interpreter : Prop)
    (nonempty : rawAnnotationAgreementIssues molecule source ≠ []) :
    ¬ AnnotationAdmitted molecule source interpreter := by
  rintro ⟨agreement, _⟩
  exact nonempty ((rawAnnotationAgreementIssues_eq_nil_iff molecule source).mpr agreement.2)






namespace ClosedAuditExamples


abbrev positiveRaw : RawMolecule := ClosedParserWitness.annotatedRawCF


abbrev positiveSource : AuthoritativeChemicalInput := ClosedParserWitness.parserSource


theorem positive_recordAudit :
    rawAnnotationAgreementIssues positiveRaw positiveSource = [] := by
  decide +kernel

theorem positive_recordAgreement : RawAnnotationRecordAgreement positiveRaw positiveSource :=
  (rawAnnotationAgreementIssues_eq_nil_iff positiveRaw positiveSource).mp positive_recordAudit

/-- The positive source satisfies the conversion-pinned agreement. -/
theorem positive_agreement : RawAnnotationAgreement positiveRaw positiveSource :=
  ⟨ClosedParserWitness.annotatedRawCF_toSemanticMolecule, positive_recordAgreement⟩

/-- The actual normalized raw molecule of the old accepted annotated request. -/
abbrev counterexampleRaw : RawMolecule :=
  ClosedRawCounterexample.annotatedRawCF.normalizeUnspecifiedBonds

/-- The clean wedge source of that same request: its diagram carries no atom configuration. -/
abbrev counterexampleSource : AuthoritativeChemicalInput := SingleWedgeSourceRegression.source

theorem counterexampleRaw_is_actual :
    counterexampleRaw = ClosedRawCounterexample.annotatedRequest.normalized.result.parsed := rfl

theorem counterexampleSource_is_actual :
    counterexampleSource = ClosedRawCounterexample.annotatedRequest.source := rfl


theorem counterexample_rawParity_issue_member :
    RawAnnotationAgreementIssue.unsupportedRawAtomParity
        { index := 0, parity := TetrahedralInputParity.clockwise } ∈
      rawAnnotationAgreementIssues counterexampleRaw counterexampleSource := by
  decide +kernel

/-- The old accepted raw annotation is rejected because the raw parity has no matching diagram
configuration. -/
theorem counterexample_audit_rejects :
    ¬ RawAnnotationRecordAgreement counterexampleRaw counterexampleSource := by
  intro agreement
  have empty :=
    (rawAnnotationAgreementIssues_eq_nil_iff counterexampleRaw counterexampleSource).mpr agreement
  have nonempty : rawAnnotationAgreementIssues counterexampleRaw counterexampleSource ≠ [] := by
    intro impossible
    have member := counterexample_rawParity_issue_member
    rw [impossible] at member
    exact List.not_mem_nil member
  exact nonempty empty

/-- The old constitution-only policy genuinely accepted that same annotated request. -/
theorem counterexample_old_policy_accepted :
    ClosedRawCounterexample.annotatedRequest.produce =
      some ClosedRawCounterexample.annotatedRequest.report :=
  ClosedRawCounterexample.annotated_old_produce_contains_S.1


abbrev wedgeDecoratedDiagram : DiagramConfiguration :=
  { positiveRaw.toDiagramConfiguration with
    atomPositions? := some [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]
    bonds := [⟨0, 1, .solidWedge, .absolute⟩] }

abbrev wedgeDecoratedSource : AuthoritativeChemicalInput :=
  { molecule := SingleWedgeSourceRegression.molecule
    diagram? := some wedgeDecoratedDiagram }


theorem wedgeDecorated_recordAudit :
    rawAnnotationAgreementIssues positiveRaw wedgeDecoratedSource = [] := by
  decide +kernel

theorem wedgeDecorated_recordAgreement :
    RawAnnotationRecordAgreement positiveRaw wedgeDecoratedSource :=
  (rawAnnotationAgreementIssues_eq_nil_iff positiveRaw wedgeDecoratedSource).mp
    wedgeDecorated_recordAudit



theorem wedgeDecorated_not_authoritative :
    ¬ positiveRaw.AuthoritativeStructureAgreement wedgeDecoratedSource := by
  intro agreement
  have same : some wedgeDecoratedDiagram = some positiveRaw.toDiagramConfiguration := agreement.2
  have distinct : wedgeDecoratedDiagram ≠ positiveRaw.toDiagramConfiguration := by decide +kernel
  exact distinct (Option.some.inj same)



theorem wedgeDecorated_separation :
    RawAnnotationRecordAgreement positiveRaw wedgeDecoratedSource ∧
      ¬ positiveRaw.AuthoritativeStructureAgreement wedgeDecoratedSource :=
  ⟨wedgeDecorated_recordAgreement, wedgeDecorated_not_authoritative⟩

end ClosedAuditExamples

end TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
