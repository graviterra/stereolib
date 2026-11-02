import TetraStereo.OneCenter.IUPACProvisionTerminalLedger

set_option autoImplicit false

















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- Semantic proof families used to compile the normative manifest. -/
inductive ProvisionKind where
  | sequenceRule
  | perception
  | spatialDescriptor
  | depiction
  | nomenclature
  | authorityData
  | sourceOnly
  deriving DecidableEq, Repr

namespace ProvisionKind

def all : List ProvisionKind :=
  [ .sequenceRule
  , .perception
  , .spatialDescriptor
  , .depiction
  , .nomenclature
  , .authorityData
  , .sourceOnly
  ]

@[simp] theorem mem_all (kind : ProvisionKind) : kind ∈ all := by
  cases kind <;> simp [all]

end ProvisionKind

/-- Independent meaning of one provision.  Different provisions may judge different observation
types without erasing them into an untyped universal syntax. -/
structure ProvisionReference where
  Observation : Type
  Applicable : AuthoritativeChemicalInput → Prop
  Judges : AuthoritativeChemicalInput → Observation → Prop

/-- Frozen source-derived program for the complete manifest.  This is the sole owner of semantic
classification and reference meaning; individual proof records cannot replace either. -/
structure FrozenProvisionCorpus where
  ChemicallyAdmitted : AuthoritativeChemicalInput → Prop
  kind : IUPACNormativeProvision → ProvisionKind
  SourceSuppliesRule : IUPACNormativeProvision → Prop
  reference : IUPACNormativeProvision → ProvisionReference

/-- Proof-bearing terminal intent for one exact corpus row. -/
inductive ProvisionDisposition (corpus : FrozenProvisionCorpus)
    (provision : IUPACNormativeProvision) where
  | conformant
      (sourcePresent : corpus.SourceSuppliesRule provision)
      (nonvacuous : ∃ input, ∃ observation,
        corpus.ChemicallyAdmitted input ∧
          (corpus.reference provision).Applicable input ∧
            (corpus.reference provision).Judges input observation)
  | notApplicable
      (sourcePresent : corpus.SourceSuppliesRule provision)
      (evidence : ∀ input,
        corpus.ChemicallyAdmitted input →
          ¬(corpus.reference provision).Applicable input)
  | sourceAbsent
      (evidence : ¬corpus.SourceSuppliesRule provision)
      (inapplicable : ∀ input,
        corpus.ChemicallyAdmitted input →
          ¬(corpus.reference provision).Applicable input)

namespace ProvisionDisposition

def IsConformant {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision} :
    ProvisionDisposition corpus provision → Prop
  | .conformant _ _ => True
  | _ => False

def IsNotApplicable {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision} :
    ProvisionDisposition corpus provision → Prop
  | .notApplicable _ _ => True
  | _ => False

def IsSourceAbsent {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision} :
    ProvisionDisposition corpus provision → Prop
  | .sourceAbsent _ _ => True
  | _ => False

def IsSourcePresent {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision} :
    ProvisionDisposition corpus provision → Prop
  | .conformant _ _ => True
  | .notApplicable _ _ => True
  | .sourceAbsent _ _ => False

theorem isSourcePresent_of_conformant {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision}
    {disposition : ProvisionDisposition corpus provision}
    (conformant : disposition.IsConformant) :
    disposition.IsSourcePresent := by
  cases disposition with
  | conformant _ _ => trivial
  | notApplicable _ _ => simp [IsConformant] at conformant
  | sourceAbsent _ _ => simp [IsConformant] at conformant

theorem source_present_of_conformant {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision}
    {disposition : ProvisionDisposition corpus provision}
    (conformant : disposition.IsConformant) :
    corpus.SourceSuppliesRule provision := by
  cases disposition with
  | conformant sourcePresent _ => exact sourcePresent
  | notApplicable _ _ => simp [IsConformant] at conformant
  | sourceAbsent _ _ => simp [IsConformant] at conformant

theorem nonvacuous_of_conformant {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision}
    {disposition : ProvisionDisposition corpus provision}
    (conformant : disposition.IsConformant) :
    ∃ input, ∃ observation,
      corpus.ChemicallyAdmitted input ∧
        (corpus.reference provision).Applicable input ∧
          (corpus.reference provision).Judges input observation := by
  cases disposition with
  | conformant _ nonvacuous => exact nonvacuous
  | notApplicable _ _ => simp [IsConformant] at conformant
  | sourceAbsent _ _ => simp [IsConformant] at conformant

/-- A source-absent disposition freezes an empty applicability relation on the admitted domain;
it cannot hide a live independent rule behind the negative terminal label. -/
theorem inapplicable_of_sourceAbsent {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision}
    {disposition : ProvisionDisposition corpus provision}
    (sourceAbsent : disposition.IsSourceAbsent) :
    ∀ input, corpus.ChemicallyAdmitted input →
      ¬(corpus.reference provision).Applicable input := by
  cases disposition with
  | conformant _ _ => simp [IsSourceAbsent] at sourceAbsent
  | notApplicable _ _ => simp [IsSourceAbsent] at sourceAbsent
  | sourceAbsent _ inapplicable => exact inapplicable

/-- A not-applicable disposition carries the same admitted-domain emptiness boundary while
retaining evidence that the authority rule itself is present. -/
theorem inapplicable_of_notApplicable {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision}
    {disposition : ProvisionDisposition corpus provision}
    (notApplicable : disposition.IsNotApplicable) :
    ∀ input, corpus.ChemicallyAdmitted input →
      ¬(corpus.reference provision).Applicable input := by
  cases disposition with
  | conformant _ _ => simp [IsNotApplicable] at notApplicable
  | notApplicable _ inapplicable => exact inapplicable
  | sourceAbsent _ _ => simp [IsNotApplicable] at notApplicable

end ProvisionDisposition

/-- Audited independent specification for one exact manifest row.  The dependent index fixes the
source section used by `sourceAudited`; semantic data is read only from the frozen corpus. -/
structure ProvisionSpec (corpus : FrozenProvisionCorpus)
    (provision : IUPACNormativeProvision) where
  sourceAudited : IUPACNormativeSource.ProvisionAuditComplete provision.source
  disposition : ProvisionDisposition corpus provision

/-- A total proof-bearing compiler for the frozen corpus. -/
structure ProvisionCompiler (corpus : FrozenProvisionCorpus) where
  spec : (provision : IUPACNormativeProvision) → ProvisionSpec corpus provision

/-- A proof-bearing compiler for a finite audited scope.  This is the staging boundary: useful
families can be compiled before source transcription for all 2,452 manifest rows is complete. -/
structure ScopedProvisionCompiler (corpus : FrozenProvisionCorpus)
    (scope : Finset IUPACNormativeProvision) where
  spec : (provision : IUPACNormativeProvision) →
    provision ∈ scope → ProvisionSpec corpus provision

namespace ProvisionCompiler

/-- Restrict a completed global compiler to any finite provision scope. -/
def restrict {corpus : FrozenProvisionCorpus}
    (compiler : ProvisionCompiler corpus) (scope : Finset IUPACNormativeProvision) :
    ScopedProvisionCompiler corpus scope where
  spec := fun provision _member => compiler.spec provision


def provisionsOfKind {corpus : FrozenProvisionCorpus}
    (_compiler : ProvisionCompiler corpus) (kind : ProvisionKind) :
    List IUPACNormativeProvision :=
  IUPACNormativeProvision.all.filter fun provision => decide (corpus.kind provision = kind)

theorem mem_provisionsOfKind_iff {corpus : FrozenProvisionCorpus}
    (compiler : ProvisionCompiler corpus) (kind : ProvisionKind) :
    ∀ provision,
      provision ∈ compiler.provisionsOfKind kind ↔ corpus.kind provision = kind := by
  intro provision
  simp [provisionsOfKind]

theorem kind_partition_exhaustive {corpus : FrozenProvisionCorpus}
    (compiler : ProvisionCompiler corpus) (provision : IUPACNormativeProvision) :
    ∃ kind, provision ∈ compiler.provisionsOfKind kind := by
  refine ⟨corpus.kind provision, ?_⟩
  exact (compiler.mem_provisionsOfKind_iff _ provision).2 rfl

theorem kind_partitions_disjoint {corpus : FrozenProvisionCorpus}
    (compiler : ProvisionCompiler corpus)
    (left right : ProvisionKind) (different : left ≠ right) :
    List.Disjoint (compiler.provisionsOfKind left) (compiler.provisionsOfKind right) := by
  rw [List.disjoint_left]
  intro provision leftMember rightMember
  have leftKind := (compiler.mem_provisionsOfKind_iff left provision).1 leftMember
  have rightKind := (compiler.mem_provisionsOfKind_iff right provision).1 rightMember
  exact different (leftKind.symm.trans rightKind)

end ProvisionCompiler

/-- Production judgment relation for the observation type frozen by the reference corpus. -/
structure ProvisionInterpreter (corpus : FrozenProvisionCorpus) where
  Produces : (provision : IUPACNormativeProvision) →
    AuthoritativeChemicalInput →
      (corpus.reference provision).Observation → Prop

/-- Production and reference define the same relation on every admitted input.  Applicability is
inside the reference side of the equivalence, so production must be empty when a row is outside
its audited applicability boundary. -/
def ProvisionCorrect (corpus : FrozenProvisionCorpus)
    (interpreter : ProvisionInterpreter corpus)
    (provision : IUPACNormativeProvision) : Prop :=
  ∀ input,
    corpus.ChemicallyAdmitted input →
      ∀ observation,
        interpreter.Produces provision input observation ↔
          (corpus.reference provision).Applicable input ∧
            (corpus.reference provision).Judges input observation

/-- One universal correctness obligation at semantic-family granularity.  It covers every row,
including `sourceAbsent`: that disposition freezes empty applicability, so correctness proves
that production is empty instead of silently exempting the row from the global refinement. -/
def ProvisionKindCorrect {corpus : FrozenProvisionCorpus}
    (_compiler : ProvisionCompiler corpus) (interpreter : ProvisionInterpreter corpus)
    (kind : ProvisionKind) : Prop :=
  ∀ provision,
    corpus.kind provision = kind →
      ProvisionCorrect corpus interpreter provision

/-- The seven strategic correctness theorems. -/
structure ProvisionCompilerCorrect {corpus : FrozenProvisionCorpus}
    (compiler : ProvisionCompiler corpus) (interpreter : ProvisionInterpreter corpus) : Prop where
  sequenceRule_correct : ProvisionKindCorrect compiler interpreter .sequenceRule
  perception_correct : ProvisionKindCorrect compiler interpreter .perception
  spatialDescriptor_correct : ProvisionKindCorrect compiler interpreter .spatialDescriptor
  depiction_correct : ProvisionKindCorrect compiler interpreter .depiction
  nomenclature_correct : ProvisionKindCorrect compiler interpreter .nomenclature
  authorityData_correct : ProvisionKindCorrect compiler interpreter .authorityData
  sourceOnly_correct : ProvisionKindCorrect compiler interpreter .sourceOnly

namespace ProvisionCompilerCorrect

/-- Project the seven family theorems to every manifest provision, across all three terminal
dispositions. -/
theorem every_provision_correct
    {corpus : FrozenProvisionCorpus}
    {compiler : ProvisionCompiler corpus} {interpreter : ProvisionInterpreter corpus}
    (correct : ProvisionCompilerCorrect compiler interpreter)
    (provision : IUPACNormativeProvision) :
    ProvisionCorrect corpus interpreter provision := by
  cases kind : corpus.kind provision with
  | sequenceRule => exact correct.sequenceRule_correct provision kind
  | perception => exact correct.perception_correct provision kind
  | spatialDescriptor => exact correct.spatialDescriptor_correct provision kind
  | depiction => exact correct.depiction_correct provision kind
  | nomenclature => exact correct.nomenclature_correct provision kind
  | authorityData => exact correct.authorityData_correct provision kind
  | sourceOnly => exact correct.sourceOnly_correct provision kind

/-- Compatibility projection for callers that already carry source-presence evidence. -/
theorem every_source_present_provision_correct
    {corpus : FrozenProvisionCorpus}
    {compiler : ProvisionCompiler corpus} {interpreter : ProvisionInterpreter corpus}
    (correct : ProvisionCompilerCorrect compiler interpreter)
    (provision : IUPACNormativeProvision)
    (_sourcePresent : (compiler.spec provision).disposition.IsSourcePresent) :
    ProvisionCorrect corpus interpreter provision :=
  correct.every_provision_correct provision

/-- Descriptor-bearing rows are source-present, so the global family theorem specializes to the
requested end-to-end conformance projection. -/
theorem every_conformant_provision_correct
    {corpus : FrozenProvisionCorpus}
    {compiler : ProvisionCompiler corpus} {interpreter : ProvisionInterpreter corpus}
    (correct : ProvisionCompilerCorrect compiler interpreter)
    (provision : IUPACNormativeProvision)
    (_conformant : (compiler.spec provision).disposition.IsConformant) :
    ProvisionCorrect corpus interpreter provision :=
  correct.every_provision_correct provision

end ProvisionCompilerCorrect

/-! ## Scoped family correctness -/



def ScopedProvisionKindCorrect {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    (_compiler : ScopedProvisionCompiler corpus scope)
    (interpreter : ProvisionInterpreter corpus) (kind : ProvisionKind) : Prop :=
  ∀ provision, ∀ _member : provision ∈ scope,
    corpus.kind provision = kind →
      ProvisionCorrect corpus interpreter provision

/-- The same seven semantic-family obligations, restricted to an independently audited finite
scope.  This is the usable correctness certificate for the first 35-row promotion. -/
structure ScopedProvisionCompilerCorrect {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    (compiler : ScopedProvisionCompiler corpus scope)
    (interpreter : ProvisionInterpreter corpus) : Prop where
  sequenceRule_correct : ScopedProvisionKindCorrect compiler interpreter .sequenceRule
  perception_correct : ScopedProvisionKindCorrect compiler interpreter .perception
  spatialDescriptor_correct :
    ScopedProvisionKindCorrect compiler interpreter .spatialDescriptor
  depiction_correct : ScopedProvisionKindCorrect compiler interpreter .depiction
  nomenclature_correct : ScopedProvisionKindCorrect compiler interpreter .nomenclature
  authorityData_correct : ScopedProvisionKindCorrect compiler interpreter .authorityData
  sourceOnly_correct : ScopedProvisionKindCorrect compiler interpreter .sourceOnly

namespace ScopedProvisionCompilerCorrect

/-- Project the seven scoped family theorems to every audited row in the scope. -/
theorem every_provision_correct
    {corpus : FrozenProvisionCorpus} {scope : Finset IUPACNormativeProvision}
    {compiler : ScopedProvisionCompiler corpus scope}
    {interpreter : ProvisionInterpreter corpus}
    (correct : ScopedProvisionCompilerCorrect compiler interpreter)
    (provision : IUPACNormativeProvision) (member : provision ∈ scope) :
    ProvisionCorrect corpus interpreter provision := by
  cases kind : corpus.kind provision with
  | sequenceRule => exact correct.sequenceRule_correct provision member kind
  | perception => exact correct.perception_correct provision member kind
  | spatialDescriptor =>
      exact correct.spatialDescriptor_correct provision member kind
  | depiction => exact correct.depiction_correct provision member kind
  | nomenclature => exact correct.nomenclature_correct provision member kind
  | authorityData => exact correct.authorityData_correct provision member kind
  | sourceOnly => exact correct.sourceOnly_correct provision member kind

/-- Compatibility projection for scoped callers that already carry source presence. -/
theorem every_source_present_provision_correct
    {corpus : FrozenProvisionCorpus} {scope : Finset IUPACNormativeProvision}
    {compiler : ScopedProvisionCompiler corpus scope}
    {interpreter : ProvisionInterpreter corpus}
    (correct : ScopedProvisionCompilerCorrect compiler interpreter)
    (provision : IUPACNormativeProvision) (member : provision ∈ scope)
    (_sourcePresent : (compiler.spec provision member).disposition.IsSourcePresent) :
    ProvisionCorrect corpus interpreter provision :=
  correct.every_provision_correct provision member

/-- Conformant scoped rows inherit production/reference correctness from their family theorem. -/
theorem every_conformant_provision_correct
    {corpus : FrozenProvisionCorpus} {scope : Finset IUPACNormativeProvision}
    {compiler : ScopedProvisionCompiler corpus scope}
    {interpreter : ProvisionInterpreter corpus}
    (correct : ScopedProvisionCompilerCorrect compiler interpreter)
    (provision : IUPACNormativeProvision) (member : provision ∈ scope)
    (_conformant : (compiler.spec provision member).disposition.IsConformant) :
    ProvisionCorrect corpus interpreter provision :=
  correct.every_provision_correct provision member

end ScopedProvisionCompilerCorrect

namespace ProvisionCompilerCorrect

/-- Restrict the seven global family theorems to any finite compiler batch.  This is the formal
reuse boundary that prevents every 54-row (or larger) work unit from becoming seven new proof
projects. -/
def restrict {corpus : FrozenProvisionCorpus}
    {compiler : ProvisionCompiler corpus} {interpreter : ProvisionInterpreter corpus}
    (correct : ProvisionCompilerCorrect compiler interpreter)
    (scope : Finset IUPACNormativeProvision) :
    ScopedProvisionCompilerCorrect (compiler.restrict scope) interpreter where
  sequenceRule_correct := by
    intro provision _member kind
    exact correct.sequenceRule_correct provision kind
  perception_correct := by
    intro provision _member kind
    exact correct.perception_correct provision kind
  spatialDescriptor_correct := by
    intro provision _member kind
    exact correct.spatialDescriptor_correct provision kind
  depiction_correct := by
    intro provision _member kind
    exact correct.depiction_correct provision kind
  nomenclature_correct := by
    intro provision _member kind
    exact correct.nomenclature_correct provision kind
  authorityData_correct := by
    intro provision _member kind
    exact correct.authorityData_correct provision kind
  sourceOnly_correct := by
    intro provision _member kind
    exact correct.sourceOnly_correct provision kind

end ProvisionCompilerCorrect

namespace ProvisionInterpreter

/-- Translate the frozen corpus to the independent propositions consumed by the closure ledger.
`EndToEndConforms` requires both an audited conformant disposition and refinement. -/
def toClosureSemantics {corpus : FrozenProvisionCorpus}
    (compiler : ProvisionCompiler corpus) (interpreter : ProvisionInterpreter corpus) :
    ProvisionClosureSemantics where
  ChemicallyAdmitted := corpus.ChemicallyAdmitted
  Applies := fun provision => (corpus.reference provision).Applicable
  EndToEndConforms := fun provision =>
    (compiler.spec provision).disposition.IsConformant ∧
      ProvisionCorrect corpus interpreter provision
  SourceSuppliesRule := corpus.SourceSuppliesRule

/-- Translate a finite compiler scope to total ledger semantics without pretending rows outside
the scope have been compiled.  End-to-end conformance therefore carries its scope witness. -/
def scopedToClosureSemantics {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    (compiler : ScopedProvisionCompiler corpus scope)
    (interpreter : ProvisionInterpreter corpus) : ProvisionClosureSemantics where
  ChemicallyAdmitted := corpus.ChemicallyAdmitted
  Applies := fun provision => (corpus.reference provision).Applicable
  EndToEndConforms := fun provision =>
    ∃ member : provision ∈ scope,
      (compiler.spec provision member).disposition.IsConformant ∧
        ProvisionCorrect corpus interpreter provision
  SourceSuppliesRule := corpus.SourceSuppliesRule

end ProvisionInterpreter

/-! ## Concrete first-batch classification -/

def primitiveP92SequenceRuleProvisions : List IUPACNormativeProvision :=
  [ .p92Rule1aAtomicNumber
  , .p92Rule1bDuplicateProximity
  , .p92Rule2IsotopeMass
  , .p92Rule3Geometry
  , .p92Rule3SeqCisTrans
  , .p92Rule3Priority
  , .p92Rule4aUnitKind
  , .p92Rule4bLikeUnlike
  , .p92Rule4bPairingMethodology
  , .p92Rule4cPseudoasymmetry
  , .p92Rule5Enantiomorph
  ]

def primitiveP93SpatialDescriptorProvisions : List IUPACNormativeProvision :=
  [ .p93PolyhedralSymbols
  , .p93PolyhedralPriorityNumbering
  , .p93TShape
  , .p93SeeSaw
  , .p93TrigonalBipyramid
  , .p93SquarePyramid
  , .p93Octahedron
  , .p93PolyhedralChirality
  ]

def primitiveIR9SpatialDescriptorProvisions : List IUPACNormativeProvision :=
  [ .ir9PolyhedralSymbols
  , .ir9SquarePlanar
  , .ir9Octahedral
  , .ir9SquarePyramidal
  , .ir9Bipyramidal
  , .ir9TShape
  , .ir9SeeSaw
  , .ir9RSTrigonalPyramidal
  , .ir9CAPolyhedral
  , .ir9CATrigonalBipyramidal
  , .ir9CASquarePyramidal
  , .ir9CASeeSaw
  , .ir9CAOctahedral
  , .ir9CAOtherBipyramidal
  , .ir9PriorityNumbers
  , .ir9PrimingConvention
  ]

@[simp] theorem primitiveP92SequenceRuleProvisionCount :
    primitiveP92SequenceRuleProvisions.length = 11 := by decide

@[simp] theorem primitiveP93SpatialDescriptorProvisionCount :
    primitiveP93SpatialDescriptorProvisions.length = 8 := by decide

@[simp] theorem primitiveIR9SpatialDescriptorProvisionCount :
    primitiveIR9SpatialDescriptorProvisions.length = 16 := by decide


theorem primitive35Classification_exact :
    primitiveP92SequenceRuleProvisions ++
        primitiveP93SpatialDescriptorProvisions ++
          primitiveIR9SpatialDescriptorProvisions =
      primitive35Provisions := by
  rfl

/-- Concrete staged classifier for the first strategic family.  Rows outside the audited first
batch intentionally remain unclassified rather than receiving a guessed semantic kind. -/
def primitive35Kind? (provision : IUPACNormativeProvision) : Option ProvisionKind :=
  if provision ∈ primitiveP92SequenceRuleProvisions then some .sequenceRule
  else if provision ∈ primitiveP93SpatialDescriptorProvisions then some .spatialDescriptor
  else if provision ∈ primitiveIR9SpatialDescriptorProvisions then some .spatialDescriptor
  else none

theorem primitive35Kind?_isSome_iff (provision : IUPACNormativeProvision) :
    (primitive35Kind? provision).isSome = true ↔ provision ∈ primitive35Provisions := by
  rw [← primitive35Classification_exact]
  simp only [primitive35Kind?, List.mem_append]
  by_cases p92 : provision ∈ primitiveP92SequenceRuleProvisions
  · simp [p92]
  by_cases p93 : provision ∈ primitiveP93SpatialDescriptorProvisions
  · simp [p92, p93]
  by_cases ir9 : provision ∈ primitiveIR9SpatialDescriptorProvisions <;>
    simp [p92, p93, ir9]


theorem primitive35_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ primitive35Provisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : primitive35Provisions.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

/-- One human-reviewed row of independent authority semantics.  This data is deliberately
separate from both the production interpreter and the corpus being checked against it. -/
structure ReviewedProvisionSemantics where
  kind : ProvisionKind
  sourceSuppliesRule : Bool
  reference : ProvisionReference

/-- Human-reviewed source semantics for every manifest row.  Constructing this table is the
global transcription trust boundary; production code is not a field and cannot define it. -/
structure ReviewedProvisionSemanticsTable where
  ChemicallyAdmitted : AuthoritativeChemicalInput → Prop
  row : IUPACNormativeProvision → ReviewedProvisionSemantics

/-- Exact agreement between a candidate frozen corpus and the independently reviewed global
table.  This is the 2,452-row analogue of `ProvisionBatchReferenceFaithful`. -/
structure ReviewedCorpusFaithful
    (reviewed : ReviewedProvisionSemanticsTable)
    (corpus : FrozenProvisionCorpus) : Prop where
  admitted_exact : ∀ input : AuthoritativeChemicalInput,
    corpus.ChemicallyAdmitted input ↔ reviewed.ChemicallyAdmitted input
  exact : ∀ provision : IUPACNormativeProvision,
    corpus.kind provision = (reviewed.row provision).kind ∧
    (corpus.SourceSuppliesRule provision ↔
      (reviewed.row provision).sourceSuppliesRule = true) ∧
    corpus.reference provision = (reviewed.row provision).reference

/-! ## Generic finite reviewed batches -/

/-- Independently reviewed authority semantics for any finite compiler work unit.  The provision
index and membership proof preserve dependent observation types without requiring a global table
before the batch can be useful. -/
structure ReviewedProvisionBatch (scope : Finset IUPACNormativeProvision) where
  ChemicallyAdmitted : AuthoritativeChemicalInput → Prop
  row : (provision : IUPACNormativeProvision) →
    provision ∈ scope → ReviewedProvisionSemantics
  sourceAudited : ∀ {provision : IUPACNormativeProvision}
    (_member : provision ∈ scope),
      IUPACNormativeSource.ProvisionAuditComplete provision.source

/-- Exact agreement between a frozen corpus and one independently reviewed finite work unit. -/
structure ProvisionBatchReferenceFaithful
    {scope : Finset IUPACNormativeProvision}
    (reviewed : ReviewedProvisionBatch scope)
    (corpus : FrozenProvisionCorpus) : Prop where
  admitted_exact : ∀ input : AuthoritativeChemicalInput,
    corpus.ChemicallyAdmitted input ↔ reviewed.ChemicallyAdmitted input
  exact : ∀ {provision : IUPACNormativeProvision} (member : provision ∈ scope),
    corpus.kind provision = (reviewed.row provision member).kind ∧
    (corpus.SourceSuppliesRule provision ↔
      (reviewed.row provision member).sourceSuppliesRule = true) ∧
    corpus.reference provision = (reviewed.row provision member).reference

/-- Reusable adequacy boundary for any finite reviewed batch.  Conformant intent remains
proof-bearing and nonvacuous through `ProvisionDisposition.conformant`. -/
structure ProvisionBatchAdequacy
    {scope : Finset IUPACNormativeProvision}
    (reviewed : ReviewedProvisionBatch scope)
    (corpus : FrozenProvisionCorpus)
    (compiler : ScopedProvisionCompiler corpus scope) : Prop where
  referenceFaithful : ProvisionBatchReferenceFaithful reviewed corpus
  conformant : ∀ {provision : IUPACNormativeProvision} (member : provision ∈ scope),
    (compiler.spec provision member).disposition.IsConformant

namespace ProvisionBatchAdequacy

theorem admitted_exact {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    {reviewed : ReviewedProvisionBatch scope}
    {compiler : ScopedProvisionCompiler corpus scope}
    (adequate : ProvisionBatchAdequacy reviewed corpus compiler)
    (input : AuthoritativeChemicalInput) :
    corpus.ChemicallyAdmitted input ↔ reviewed.ChemicallyAdmitted input :=
  adequate.referenceFaithful.admitted_exact input

theorem kind_exact {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    {reviewed : ReviewedProvisionBatch scope}
    {compiler : ScopedProvisionCompiler corpus scope}
    (adequate : ProvisionBatchAdequacy reviewed corpus compiler)
    {provision : IUPACNormativeProvision} (member : provision ∈ scope) :
    corpus.kind provision = (reviewed.row provision member).kind :=
  (adequate.referenceFaithful.exact member).1

theorem sourceRulePresent {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    {reviewed : ReviewedProvisionBatch scope}
    {compiler : ScopedProvisionCompiler corpus scope}
    (adequate : ProvisionBatchAdequacy reviewed corpus compiler)
    {provision : IUPACNormativeProvision} (member : provision ∈ scope) :
    corpus.SourceSuppliesRule provision :=
  ProvisionDisposition.source_present_of_conformant (adequate.conformant member)

theorem reference_nonvacuous {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    {reviewed : ReviewedProvisionBatch scope}
    {compiler : ScopedProvisionCompiler corpus scope}
    (adequate : ProvisionBatchAdequacy reviewed corpus compiler)
    {provision : IUPACNormativeProvision} (member : provision ∈ scope) :
    ∃ input, ∃ observation,
      corpus.ChemicallyAdmitted input ∧
        (corpus.reference provision).Applicable input ∧
          (corpus.reference provision).Judges input observation :=
  ProvisionDisposition.nonvacuous_of_conformant (adequate.conformant member)

theorem reference_exact {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    {reviewed : ReviewedProvisionBatch scope}
    {compiler : ScopedProvisionCompiler corpus scope}
    (adequate : ProvisionBatchAdequacy reviewed corpus compiler)
    {provision : IUPACNormativeProvision} (member : provision ∈ scope) :
    corpus.reference provision = (reviewed.row provision member).reference :=
  (adequate.referenceFaithful.exact member).2.2

/-- One scoped seven-family theorem closes every member of an arbitrary reviewed batch. -/
theorem endToEndConforms {corpus : FrozenProvisionCorpus}
    {scope : Finset IUPACNormativeProvision}
    {reviewed : ReviewedProvisionBatch scope}
    {compiler : ScopedProvisionCompiler corpus scope}
    {interpreter : ProvisionInterpreter corpus}
    (adequate : ProvisionBatchAdequacy reviewed corpus compiler)
    (correct : ScopedProvisionCompilerCorrect compiler interpreter)
    {provision : IUPACNormativeProvision} (member : provision ∈ scope) :
    (interpreter.scopedToClosureSemantics compiler).EndToEndConforms provision := by
  exact ⟨member, adequate.conformant member,
    correct.every_provision_correct provision member⟩

end ProvisionBatchAdequacy

/-- The explicit trust-boundary artifact for the first 35 provisions.  A later source-data module
must construct this table by spelling out all 11/8/16 rows from the reviewed P-92/P-93/IR-9
judgments.  There is intentionally no default table in this generic compiler module. -/
structure Primitive35ReviewedSemanticsTable where
  ChemicallyAdmitted : AuthoritativeChemicalInput → Prop
  row : (provision : IUPACNormativeProvision) →
    provision ∈ primitive35Provisions → ReviewedProvisionSemantics
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ primitive35Provisions),
      primitive35Kind? provision = some (row provision member).kind
  sourceAudited : ∀ {provision : IUPACNormativeProvision}
    (_member : provision ∈ primitive35Provisions),
      IUPACNormativeSource.ProvisionAuditComplete provision.source
  primitiveCoverage : CurrentPrimitiveCoverageCertificate

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionDisposition.source_present_of_conformant
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionDisposition.nonvacuous_of_conformant
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionDisposition.inapplicable_of_sourceAbsent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionDisposition.inapplicable_of_notApplicable
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCompiler.mem_provisionsOfKind_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCompiler.kind_partition_exhaustive
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCompiler.kind_partitions_disjoint
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCompilerCorrect.every_provision_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCompilerCorrect.every_conformant_provision_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ScopedProvisionCompilerCorrect.every_provision_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ScopedProvisionCompilerCorrect.every_conformant_provision_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCompilerCorrect.restrict
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionBatchAdequacy.admitted_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionBatchAdequacy.kind_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionBatchAdequacy.sourceRulePresent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionBatchAdequacy.reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionBatchAdequacy.reference_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionBatchAdequacy.endToEndConforms
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35Kind?_isSome_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35_sourceAuditComplete
