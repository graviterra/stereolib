import TetraStereo.OneCenter.IUPACNext54ProvisionInventory
import TetraStereo.OneCenter.P91DescriptorSyntax

set_option autoImplicit false

/-!
# Independent reviewed targets for all seven P-91 provisions

The seven-row table below does not treat nomenclature prose as descriptor-pipeline output.  It
separates depiction, vocabulary/applicability, delegated natural-product authority, omission, and
name-placement judgments, then binds every judgment to the exact provision classifier.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

structure P91ConfigurationDepictionAuthorityObservation where
  bond : BlueBookP91.DirectedDepictionBond Nat
  representedDepth : BlueBookP91.DrawingDepth

def P91ConfigurationDepictionJudged
    (observation : P91ConfigurationDepictionAuthorityObservation) : Prop :=
  BlueBookP91.representedDepth observation.bond = observation.representedDepth

def p91ConfigurationDepictionReference : ProvisionReference where
  Observation := P91ConfigurationDepictionAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P91ConfigurationDepictionJudged observation

structure P91SubstitutiveDescriptorAuthorityObservation where
  descriptor : BlueBookP91.Descriptor
  unitKind : BlueBookP91.StereogenicUnitKind

def P91SubstitutiveDescriptorJudged
    (observation : P91SubstitutiveDescriptorAuthorityObservation) : Prop :=
  BlueBookP91.DescriptorApplies observation.descriptor observation.unitKind

def p91SubstitutiveNomenclatureDescriptorsReference : ProvisionReference where
  Observation := P91SubstitutiveDescriptorAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P91SubstitutiveDescriptorJudged observation

structure P91NaturalProductDescriptorAuthorityObservation where
  family : BlueBookP91.NaturalProductDescriptorFamily
  delegatedAuthority : BlueBookP91.DelegatedAuthoritySection

def P91NaturalProductDescriptorJudged
    (observation : P91NaturalProductDescriptorAuthorityObservation) : Prop :=
  BlueBookP91.DelegatedTo observation.family observation.delegatedAuthority

def p91NaturalProductDescriptorsReference : ProvisionReference where
  Observation := P91NaturalProductDescriptorAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P91NaturalProductDescriptorJudged observation

/-- P-91.2.1.2 is exactly the umbrella over its substitutive and delegated-natural-product
subclauses; the sum prevents either source branch from disappearing. -/
inductive P91OtherAcceptableDescriptorAuthorityObservation where
  | substitutive (observation : P91SubstitutiveDescriptorAuthorityObservation)
  | naturalProduct (observation : P91NaturalProductDescriptorAuthorityObservation)

def P91OtherAcceptableDescriptorJudged :
    P91OtherAcceptableDescriptorAuthorityObservation → Prop
  | .substitutive observation => P91SubstitutiveDescriptorJudged observation
  | .naturalProduct observation => P91NaturalProductDescriptorJudged observation

def p91OtherAcceptableDescriptorsReference : ProvisionReference where
  Observation := P91OtherAcceptableDescriptorAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P91OtherAcceptableDescriptorJudged observation

/-- P-91.2.1 contains preferred descriptors, its complete "other acceptable" umbrella, scope
qualifiers, stated reflection pairs, and the source's explicit unknown-configuration examples. -/
inductive P91DescriptorVocabularyAuthorityObservation where
  | preferred (descriptor : BlueBookP91.Descriptor)
  | otherAcceptable (observation : P91OtherAcceptableDescriptorAuthorityObservation)
  | scopeQualifier (qualifier : BlueBookP91.ScopeQualifier)
  | reflection (descriptor reflected : BlueBookP91.Descriptor)
  | unknownReplacement
      (symbol : BlueBookP91.UnknownConfigurationSymbol)
      (descriptor : BlueBookP91.Descriptor)

def P91DescriptorVocabularyJudged : P91DescriptorVocabularyAuthorityObservation → Prop
  | .preferred descriptor => descriptor.IsPreferredCIP
  | .otherAcceptable observation => P91OtherAcceptableDescriptorJudged observation
  | .scopeQualifier _ => True
  | .reflection descriptor reflected => BlueBookP91.ReflectionResult descriptor reflected
  | .unknownReplacement symbol descriptor =>
      BlueBookP91.ExplicitUnknownReplacementExample symbol descriptor

def p91DescriptorVocabularyReference : ProvisionReference where
  Observation := P91DescriptorVocabularyAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P91DescriptorVocabularyJudged observation

structure P91DescriptorOmissionAuthorityObservation where
  context : BlueBookP91.DoubleBondNamingContext
  disposition : BlueBookP91.DescriptorDisposition

def P91DescriptorOmissionJudged
    (observation : P91DescriptorOmissionAuthorityObservation) : Prop :=
  BlueBookP91.DoubleBondDescriptorDisposition observation.context observation.disposition

def p91DescriptorOmissionReference : ProvisionReference where
  Observation := P91DescriptorOmissionAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P91DescriptorOmissionJudged observation

structure P91CanonicalUnitCitation where
  unit : Nat
  descriptor : BlueBookP91.Descriptor
  locant : Nat
  target : BlueBookP91.NameTarget Nat
  position : BlueBookP91.CitationPosition Nat
  parenthesizedAndHyphenated : Bool

def P91CanonicalUnitCitation.citation
    (entry : P91CanonicalUnitCitation) : BlueBookP91.DescriptorCitation Nat Nat where
  descriptor := entry.descriptor
  locant := some entry.locant
  target := entry.target
  position := entry.position
  parenthesizedAndHyphenated := entry.parenthesizedAndHyphenated

def P91CanonicalUnitCitation.locatedCitation
    (entry : P91CanonicalUnitCitation) : BlueBookP91.LocatedDescriptorCitation Nat Nat where
  descriptor := entry.descriptor
  locant := entry.locant
  target := entry.target

structure P91NamingOfStereoisomersAuthorityObservation where
  canonicalCitations : List P91CanonicalUnitCitation
  perceivedUnits : List Nat
  permissiblyOmittedUnits : List Nat

def P91NamingOfStereoisomersJudged
    (observation : P91NamingOfStereoisomersAuthorityObservation) : Prop :=
  (observation.canonicalCitations.map P91CanonicalUnitCitation.unit).Nodup ∧
    (∀ entry ∈ observation.canonicalCitations,
      BlueBookP91.CorrectCitationPlacement entry.citation) ∧
    BlueBookP91.InIncreasingLocantOrder
      (observation.canonicalCitations.map P91CanonicalUnitCitation.locatedCitation) ∧
    BlueBookP91.EveryUnitSpecifiedUnlessOmitted observation.perceivedUnits
      (observation.canonicalCitations.map P91CanonicalUnitCitation.unit)
      observation.permissiblyOmittedUnits

def p91NamingOfStereoisomersReference : ProvisionReference where
  Observation := P91NamingOfStereoisomersAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P91NamingOfStereoisomersJudged observation

inductive Next54P91AuthorityRow where
  | configurationDepiction
  | descriptorVocabulary
  | otherAcceptableDescriptors
  | substitutiveNomenclatureDescriptors
  | naturalProductDescriptors
  | descriptorOmission
  | namingOfStereoisomers
  deriving DecidableEq, Repr

namespace Next54P91AuthorityRow

def all : List Next54P91AuthorityRow :=
  [ .configurationDepiction
  , .descriptorVocabulary
  , .otherAcceptableDescriptors
  , .substitutiveNomenclatureDescriptors
  , .naturalProductDescriptors
  , .descriptorOmission
  , .namingOfStereoisomers
  ]

def provision : Next54P91AuthorityRow → IUPACNormativeProvision
  | .configurationDepiction => .p91ConfigurationDepiction
  | .descriptorVocabulary => .p91DescriptorVocabulary
  | .otherAcceptableDescriptors => .p91OtherAcceptableDescriptors
  | .substitutiveNomenclatureDescriptors => .p91SubstitutiveNomenclatureDescriptors
  | .naturalProductDescriptors => .p91NaturalProductDescriptors
  | .descriptorOmission => .p91DescriptorOmission
  | .namingOfStereoisomers => .p91NamingOfStereoisomers

def kind : Next54P91AuthorityRow → ProvisionKind
  | .configurationDepiction => .depiction
  | .naturalProductDescriptors => .sourceOnly
  | _ => .nomenclature

def reference : Next54P91AuthorityRow → ProvisionReference
  | .configurationDepiction => p91ConfigurationDepictionReference
  | .descriptorVocabulary => p91DescriptorVocabularyReference
  | .otherAcceptableDescriptors => p91OtherAcceptableDescriptorsReference
  | .substitutiveNomenclatureDescriptors => p91SubstitutiveNomenclatureDescriptorsReference
  | .naturalProductDescriptors => p91NaturalProductDescriptorsReference
  | .descriptorOmission => p91DescriptorOmissionReference
  | .namingOfStereoisomers => p91NamingOfStereoisomersReference

def semantics (row : Next54P91AuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference

@[simp] theorem all_length : all.length = 7 := by rfl

theorem all_nodup : all.Nodup := by decide

@[simp] theorem all_provisions_exact : all.map provision = next54P91Provisions := by rfl

@[simp] theorem classifier_exact (row : Next54P91AuthorityRow) :
    next54Kind? row.provision = some row.kind := by
  cases row <;>
    simp [next54Kind?, next54SequenceRuleProvisions, next54PerceptionProvisions,
      next54SpatialDescriptorProvisions, next54DepictionProvisions,
      next54NomenclatureProvisions, next54SourceOnlyProvisions, provision, kind]

end Next54P91AuthorityRow

theorem next54P91_sourceAuditComplete
    {provision : IUPACNormativeProvision} (member : provision ∈ next54P91Provisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : next54P91Provisions.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem next54P91_mem_next54
    {provision : IUPACNormativeProvision} (member : provision ∈ next54P91Provisions) :
    provision ∈ next54Provisions := by
  simp only [next54Provisions, next54BlueBookProvisions, List.mem_append]
  exact Or.inl (Or.inl (Or.inl member))

theorem exists_next54P91AuthorityRow
    {provision : IUPACNormativeProvision} (member : provision ∈ next54P91Provisions) :
    ∃ row, row ∈ Next54P91AuthorityRow.all ∧ row.provision = provision := by
  rw [← Next54P91AuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def next54P91AuthorityRowOf
    (provision : IUPACNormativeProvision) (member : provision ∈ next54P91Provisions) :
    Next54P91AuthorityRow :=
  Classical.choose (exists_next54P91AuthorityRow member)

theorem next54P91AuthorityRowOf_provision
    (provision : IUPACNormativeProvision) (member : provision ∈ next54P91Provisions) :
    (next54P91AuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_next54P91AuthorityRow member)).2

structure Next54P91ReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch next54P91Provisions.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P91Provisions.toFinset),
      (reviewed.row provision member).kind =
        next54Kind provision (next54P91_mem_next54 (by simpa using member))

noncomputable def next54P91ReviewedSemantics : Next54P91ReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        (next54P91AuthorityRowOf provision (by simpa using member)).semantics
      sourceAudited := by
        intro provision member
        exact next54P91_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := next54P91AuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      next54P91AuthorityRowOf_provision provision (by simpa using member)
    have rowClassifier := Next54P91AuthorityRow.classifier_exact row
    have totalClassifier := next54Kind?_eq_some provision
      (next54P91_mem_next54 (by simpa using member))
    rw [rowProvision] at rowClassifier
    change row.kind = next54Kind provision _
    exact Option.some.inj (rowClassifier.symm.trans totalClassifier)

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P91AuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P91_sourceAuditComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P91AuthorityRow.classifier_exact
