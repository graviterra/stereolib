import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCanonicalSourceProgram
import TetraStereo.OneCenter.IUPACNext54P91ReviewedSemantics
import TetraStereo.OneCenter.IUPACNext54IR9ReviewedSemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Source entries for the ten non-graphical core-negative provisions

This module packages the P-90 scope row, all seven independently reviewed P-91 rows, and the two
source-scope IR-9 rows as a composable source-entry batch.  Its references retain the actual
authority-side relations: P-90 routing and descriptor admission, the reviewed P-91 dependent
relations, and the IR-9 clause/domain inventory and configuration-factor rule.  No provision is
judged merely by membership in the manifest or by its empty descriptor-assignment projection.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## P-90 scope reference -/

/-- One simultaneous observation of P-90's two routing decisions and its preferred/general
descriptor-admission boundary. -/
structure P90ScopeAuthorityObservation where
  syntheticAuthority : BlueBookP90.ConfigurationAuthority
  naturalProductAuthority : BlueBookP90.ConfigurationAuthority
  preferredInPIN : BlueBookP90.RecommendationStatus
  generalOnlyInGeneralNomenclature : BlueBookP90.RecommendationStatus

def P90ScopeAuthorityJudged (observation : P90ScopeAuthorityObservation) : Prop :=
  BlueBookP90.configurationAuthority .syntheticCompound = observation.syntheticAuthority ∧
    BlueBookP90.configurationAuthority .naturalProduct = observation.naturalProductAuthority ∧
    BlueBookP90.DescriptorAdmitted .preferredIUPACName observation.preferredInPIN ∧
    BlueBookP90.DescriptorAdmitted .general
      observation.generalOnlyInGeneralNomenclature ∧
    ¬BlueBookP90.DescriptorAdmitted .preferredIUPACName
      observation.generalOnlyInGeneralNomenclature

def p90ScopeAuthorityReference : ProvisionReference where
  Observation := P90ScopeAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P90ScopeAuthorityJudged observation

def p90ScopeAuthorityWitness : P90ScopeAuthorityObservation where
  syntheticAuthority := .chapterP93
  naturalProductAuthority := .chapterP10
  preferredInPIN := .preferred
  generalOnlyInGeneralNomenclature := .appropriateGeneral

theorem p90ScopeAuthorityWitness_judged :
    p90ScopeAuthorityReference.Judges next54IR9WitnessInput p90ScopeAuthorityWitness := by
  simp [p90ScopeAuthorityReference, P90ScopeAuthorityJudged, p90ScopeAuthorityWitness,
    BlueBookP90.DescriptorAdmitted]

/-! ## IR-9 umbrella reference -/

/-- IR-9.3's source-scope row owns the exact clause inventory and the semantic domain assigned to
every clause.  The child configuration-introduction row separately retains the executable
`requiredFactors` relation. -/
structure IR9PolyhedralConfigurationScopeObservation where
  clauses : List RedBookIR9.Provision
  semanticDomains : List RedBookIR9.SemanticDomain

def IR9PolyhedralConfigurationScopeJudged
    (observation : IR9PolyhedralConfigurationScopeObservation) : Prop :=
  observation.clauses = RedBookIR9.Provision.all ∧
    observation.semanticDomains =
      RedBookIR9.Provision.all.map RedBookIR9.Provision.semanticDomain

def ir9PolyhedralConfigurationScopeReference : ProvisionReference where
  Observation := IR9PolyhedralConfigurationScopeObservation
  Applicable := fun _input => True
  Judges := fun _input observation => IR9PolyhedralConfigurationScopeJudged observation

def ir9PolyhedralConfigurationScopeWitness : IR9PolyhedralConfigurationScopeObservation where
  clauses := RedBookIR9.Provision.all
  semanticDomains := RedBookIR9.Provision.all.map RedBookIR9.Provision.semanticDomain

theorem ir9PolyhedralConfigurationScopeWitness_judged :
    ir9PolyhedralConfigurationScopeReference.Judges next54IR9WitnessInput
      ir9PolyhedralConfigurationScopeWitness := by
  simp [ir9PolyhedralConfigurationScopeReference,
    IR9PolyhedralConfigurationScopeJudged, ir9PolyhedralConfigurationScopeWitness]

/-! ## Concrete P-91 nonvacuity -/

/-- Every reviewed P-91 source relation has a concrete judged observation. -/
theorem Next54P91AuthorityRow.reference_nonvacuous
    (row : Next54P91AuthorityRow) :
    ∃ observation : row.reference.Observation,
      row.reference.Applicable next54IR9WitnessInput ∧
        row.reference.Judges next54IR9WitnessInput observation := by
  cases row with
  | configurationDepiction =>
      exact ⟨
        { bond := { narrowEndpoint := 0, otherEndpoint := 1, style := .plain }
          representedDepth := .approximatelyInPlane }, by trivial, rfl⟩
  | descriptorVocabulary =>
      exact ⟨.preferred .capitalR, by trivial, by trivial⟩
  | otherAcceptableDescriptors =>
      exact ⟨.substitutive
        { descriptor := .capitalR
          unitKind := .quadriligantChiralityCenter }, by trivial, by trivial⟩
  | substitutiveNomenclatureDescriptors =>
      exact ⟨
        { descriptor := .capitalR
          unitKind := .quadriligantChiralityCenter }, by trivial, by trivial⟩
  | naturalProductDescriptors =>
      exact ⟨
        { family := .dAndL
          delegatedAuthority := .p102 }, by trivial, by trivial⟩
  | descriptorOmission =>
      exact ⟨
        { context :=
            { system := .simpleAlicyclic
              ringSize := 8
              doubleBondCount := 1
              everyDoubleBondConfigurationFixed := False }
          disposition := .required }, by trivial,
        BlueBookP91.simple_eight_monoene_requires⟩
  | namingOfStereoisomers =>
      exact ⟨
        { canonicalCitations :=
            [{ unit := 42
               descriptor := .capitalR
               locant := 1
               target := .parent
               position := .frontOfCompleteName
               parenthesizedAndHyphenated := true }]
          perceivedUnits := [42]
          permissiblyOmittedUnits := [] }, by trivial, by
        simp [Next54P91AuthorityRow.reference, p91NamingOfStereoisomersReference,
          P91NamingOfStereoisomersJudged, P91CanonicalUnitCitation.citation,
          P91CanonicalUnitCitation.locatedCitation, BlueBookP91.CorrectCitationPlacement,
          BlueBookP91.InIncreasingLocantOrder,
          BlueBookP91.EveryUnitSpecifiedUnlessOmitted]⟩

/-! ## Exact composable ten-row batch -/

inductive GlobalNonDescriptorCoreAuxiliarySourceRow where
  | p90Scope
  | p91 (row : Next54P91AuthorityRow)
  | ir9PolyhedralConfiguration
  | ir9ConfigurationIntroduction
  deriving DecidableEq, Repr

namespace GlobalNonDescriptorCoreAuxiliarySourceRow

def all : List GlobalNonDescriptorCoreAuxiliarySourceRow :=
  [.p90Scope] ++ Next54P91AuthorityRow.all.map .p91 ++
    [.ir9PolyhedralConfiguration, .ir9ConfigurationIntroduction]

/-- The eight rows preceding the graphical corpus in canonical core order. -/
def leadingRows : List GlobalNonDescriptorCoreAuxiliarySourceRow :=
  [.p90Scope] ++ Next54P91AuthorityRow.all.map .p91

/-- The two rows following the graphical corpus in canonical core order. -/
def trailingRows : List GlobalNonDescriptorCoreAuxiliarySourceRow :=
  [.ir9PolyhedralConfiguration, .ir9ConfigurationIntroduction]

def provision : GlobalNonDescriptorCoreAuxiliarySourceRow → IUPACNormativeProvision
  | .p90Scope => .p90ScopeAndTerminology
  | .p91 row => row.provision
  | .ir9PolyhedralConfiguration => .ir9PolyhedralConfiguration
  | .ir9ConfigurationIntroduction => .ir9ConfigurationIntroduction

def reference : GlobalNonDescriptorCoreAuxiliarySourceRow →
    OperationProvisionReference .sourceMeaning
  | .p90Scope => ⟨p90ScopeAuthorityReference⟩
  | .p91 row => ⟨row.reference⟩
  | .ir9PolyhedralConfiguration => ⟨ir9PolyhedralConfigurationScopeReference⟩
  | .ir9ConfigurationIntroduction =>
      ⟨Next54IR9AuthorityRow.configurationIntroduction.reference⟩

theorem reference_nonvacuous
    (row : GlobalNonDescriptorCoreAuxiliarySourceRow) :
    ∃ input, ∃ observation : row.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        row.reference.toReference.Applicable input ∧
          row.reference.toReference.Judges input observation := by
  cases row with
  | p90Scope =>
      exact ⟨next54IR9WitnessInput, p90ScopeAuthorityWitness,
        next54IR9WitnessInput_structurallyWellFormed, by trivial,
        p90ScopeAuthorityWitness_judged⟩
  | p91 child =>
      rcases child.reference_nonvacuous with ⟨observation, applicable, judged⟩
      exact ⟨next54IR9WitnessInput, observation,
        next54IR9WitnessInput_structurallyWellFormed, applicable, judged⟩
  | ir9PolyhedralConfiguration =>
      exact ⟨next54IR9WitnessInput, ir9PolyhedralConfigurationScopeWitness,
        next54IR9WitnessInput_structurallyWellFormed, by trivial,
        ir9PolyhedralConfigurationScopeWitness_judged⟩
  | ir9ConfigurationIntroduction =>
      rcases Next54IR9AuthorityRow.configurationIntroduction.reference_nonvacuous with
        ⟨observation, applicable, judged⟩
      exact ⟨next54IR9WitnessInput, observation,
        next54IR9WitnessInput_structurallyWellFormed, applicable, judged⟩

def entry (row : GlobalNonDescriptorCoreAuxiliarySourceRow) :
    GlobalNonDescriptorSourceMeaningEntry where
  provision := row.provision
  reference := row.reference
  admittedJudgment := row.reference_nonvacuous

def provisions : List IUPACNormativeProvision :=
  [ .p90ScopeAndTerminology
  , .p91ConfigurationDepiction
  , .p91DescriptorVocabulary
  , .p91OtherAcceptableDescriptors
  , .p91SubstitutiveNomenclatureDescriptors
  , .p91NaturalProductDescriptors
  , .p91DescriptorOmission
  , .p91NamingOfStereoisomers
  , .ir9PolyhedralConfiguration
  , .ir9ConfigurationIntroduction
  ]

def leadingProvisions : List IUPACNormativeProvision :=
  [ .p90ScopeAndTerminology
  , .p91ConfigurationDepiction
  , .p91DescriptorVocabulary
  , .p91OtherAcceptableDescriptors
  , .p91SubstitutiveNomenclatureDescriptors
  , .p91NaturalProductDescriptors
  , .p91DescriptorOmission
  , .p91NamingOfStereoisomers
  ]

def trailingProvisions : List IUPACNormativeProvision :=
  [.ir9PolyhedralConfiguration, .ir9ConfigurationIntroduction]

def entries : List GlobalNonDescriptorSourceMeaningEntry := all.map entry

def leadingEntries : List GlobalNonDescriptorSourceMeaningEntry := leadingRows.map entry

def trailingEntries : List GlobalNonDescriptorSourceMeaningEntry := trailingRows.map entry

@[simp] theorem all_count : all.length = 10 := by rfl

@[simp] theorem entry_count : entries.length = 10 := by rfl

@[simp] theorem leading_entry_count : leadingEntries.length = 8 := by rfl

@[simp] theorem trailing_entry_count : trailingEntries.length = 2 := by rfl

@[simp] theorem all_provisions_exact : all.map provision = provisions := by rfl

@[simp] theorem entry_provisions_exact :
    entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions := by
  rfl

@[simp] theorem leading_entry_provisions_exact :
    leadingEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = leadingProvisions := by
  rfl

@[simp] theorem trailing_entry_provisions_exact :
    trailingEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = trailingProvisions := by
  rfl

theorem provisions_nodup : provisions.Nodup := by decide

theorem entry_provisions_nodup :
    (entries.map GlobalNonDescriptorSourceMeaningEntry.provision).Nodup := by
  rw [entry_provisions_exact]
  exact provisions_nodup

set_option maxRecDepth 32768 in
private theorem row_mem_globalNonDescriptor
    (row : GlobalNonDescriptorCoreAuxiliarySourceRow) :
    row.provision ∈ globalNonDescriptorProvisions := by
  cases row with
  | p90Scope => decide
  | p91 child => cases child <;> decide
  | ir9PolyhedralConfiguration => decide
  | ir9ConfigurationIntroduction => decide

/-- The source-order prefix batch, designed to compose immediately before the graphical batch. -/
def leadingBatch : GlobalNonDescriptorSourceMeaningBatch leadingProvisions where
  entries := leadingEntries
  provisions_exact := leading_entry_provisions_exact
  scope := by
    intro provision member
    rw [← leading_entry_provisions_exact] at member
    obtain ⟨entryValue, entryMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp entryMember
    exact row_mem_globalNonDescriptor row

/-- The source-order suffix batch, designed to compose immediately after the graphical batch. -/
def trailingBatch : GlobalNonDescriptorSourceMeaningBatch trailingProvisions where
  entries := trailingEntries
  provisions_exact := trailing_entry_provisions_exact
  scope := by
    intro provision member
    rw [← trailing_entry_provisions_exact] at member
    obtain ⟨entryValue, entryMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp entryMember
    exact row_mem_globalNonDescriptor row

/-- The ten-row inventory as one batch.  Canonical core assembly uses `leadingBatch` and
`trailingBatch` separately so the 82 graphical rows remain between them. -/
def batch : GlobalNonDescriptorSourceMeaningBatch provisions where
  entries := entries
  provisions_exact := entry_provisions_exact
  scope := by
    intro provision member
    rw [← entry_provisions_exact] at member
    obtain ⟨entryValue, entryMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp entryMember
    exact row_mem_globalNonDescriptor row


theorem source_audit_complete
    (row : GlobalNonDescriptorCoreAuxiliarySourceRow) :
    IUPACNormativeSource.ProvisionAuditComplete row.provision.source := by
  cases row with
  | p90Scope => exact ⟨rfl, rfl, rfl, rfl⟩
  | p91 child => cases child <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | ir9PolyhedralConfiguration => exact ⟨rfl, rfl, rfl, rfl⟩
  | ir9ConfigurationIntroduction => exact ⟨rfl, rfl, rfl, rfl⟩

end GlobalNonDescriptorCoreAuxiliarySourceRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P91AuthorityRow.reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCoreAuxiliarySourceRow.reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCoreAuxiliarySourceRow.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCoreAuxiliarySourceRow.entry_provisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCoreAuxiliarySourceRow.source_audit_complete
