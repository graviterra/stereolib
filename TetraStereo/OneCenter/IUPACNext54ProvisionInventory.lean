import TetraStereo.OneCenter.IUPACProvisionSemantics

set_option autoImplicit false

/-!
# Exact second provision-compiler work unit

The first compiler family contains 35 primitive-backed P-92/P-93/IR-9 rows.  This module freezes
the next 54-row promotion queue without assigning unaudited dispositions or semantic references:

* all 7 P-91 rows;
* the 32 P-92 foundational/digraph rows outside the primitive rule family;
* the 3 P-93 polyhedral rows outside the primitive polyhedral family; and
* 12 IR-9 descriptor rows outside the primitive IR-9 family.

The IR-9.3 overview row is retained separately because it is an umbrella/source-scope provision,
not one of the 12 descriptor-bearing residuals.  The exactness theorems below prevent either row
loss or overlap with the initial 35 while the reviewed references are constructed.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def next54P91Provisions : List IUPACNormativeProvision :=
  p91SemanticsSlice

def next54P92ResidualProvisions : List IUPACNormativeProvision :=
  p92FoundationalSemanticsSlice ++ p92DigraphAndRule1aSemanticsSlice

def next54P93PolyhedralResidualProvisions : List IUPACNormativeProvision :=
  [ .p93NontetrahedralGeneralMethodology
  , .p93PolyhedralGeometryRecognition
  , .p93TrigonalPyramid
  ]

def next54IR9ResidualProvisions : List IUPACNormativeProvision :=
  [ .ir9ConfigurationIntroduction
  , .ir9GeometryChoice
  , .ir9DiastereoisomerGeneral
  , .ir9ConfigurationIndex
  , .ir9AbsoluteConfigurationGeneral
  , .ir9RSTetrahedral
  , .ir9CATrigonalPrismatic
  , .ir9SkewLines
  , .ir9SkewLinesTrisBidentate
  , .ir9SkewLinesBisBidentate
  , .ir9SkewLinesChelateConformations
  , .ir9LigandPriorityGeneral
  ]

/-- The IR-9.3 umbrella is deliberately outside the descriptor-bearing second batch. -/
def deferredIR9UmbrellaProvision : IUPACNormativeProvision :=
  .ir9PolyhedralConfiguration

def next54BlueBookProvisions : List IUPACNormativeProvision :=
  next54P91Provisions ++ next54P92ResidualProvisions ++
    next54P93PolyhedralResidualProvisions

def next54Provisions : List IUPACNormativeProvision :=
  next54BlueBookProvisions ++ next54IR9ResidualProvisions

/-! ## Exact seven-family routing -/

def next54DepictionProvisions : List IUPACNormativeProvision :=
  [ .p91ConfigurationDepiction ]

def next54NomenclatureProvisions : List IUPACNormativeProvision :=
  [ .p91DescriptorVocabulary
  , .p91OtherAcceptableDescriptors
  , .p91SubstitutiveNomenclatureDescriptors
  , .p91DescriptorOmission
  , .p91NamingOfStereoisomers
  ]

/-- Delegated natural-product authority and the IR-9 configuration-factor introduction are
source-ownership rows, not executable descriptor relations. -/
def next54SourceOnlyProvisions : List IUPACNormativeProvision :=
  [ .p91NaturalProductDescriptors
  , .ir9ConfigurationIntroduction
  ]

def next54PerceptionProvisions : List IUPACNormativeProvision :=
  [ .p92StereogenicUnits
  , .p92ChiralityDefinition
  , .p92ChiralityCenterDefinition
  , .p92ChiralityAxisDefinition
  , .p92ChiralityPlaneDefinition
  , .p92PseudoasymmetricUnitDefinition
  , .p92CisTransDoubleBondUnitDefinition
  , .p92EnantiomorphicDoubleBondUnitDefinition
  , .p92BondingNumberScope
  , .p92AcyclicDigraph
  , .p92MultipleBondDigraph
  , .p92CyclicDigraph
  , .p92MancudeDigraph
  , .p92SphereExploration
  , .p93PolyhedralGeometryRecognition
  , .ir9GeometryChoice
  , .ir9DiastereoisomerGeneral
  ]

def next54SequenceRuleProvisions : List IUPACNormativeProvision :=
  [ .p92SequenceRulePropertyClasses
  , .p92SequenceRuleReflectionBehavior
  , .p92LigandDentateKinds
  , .p92SequenceRuleHierarchy
  , .p92RuleExhaustivity
  , .p92Rule1aMultipleBondDuplicates
  , .p92Rule1aMancude
  , .p92Rule1aSaturatedCompounds
  , .p92Rule1aDoubleTripleBonds
  , .p92Rule1aSaturatedRings
  , .ir9LigandPriorityGeneral
  ]

def next54SpatialDescriptorProvisions : List IUPACNormativeProvision :=
  [ .p92ChiralityRuleGeneral
  , .p92CenterChiralityRule
  , .p92AxisChiralityRule
  , .p92PlaneChiralityRule
  , .p92HelicityRule
  , .p92HelicityAxis
  , .p92HelicityPlane
  , .p92RSMPDescriptorCorrespondence
  , .p93NontetrahedralGeneralMethodology
  , .p93TrigonalPyramid
  , .ir9ConfigurationIndex
  , .ir9AbsoluteConfigurationGeneral
  , .ir9RSTetrahedral
  , .ir9CATrigonalPrismatic
  , .ir9SkewLines
  , .ir9SkewLinesTrisBidentate
  , .ir9SkewLinesBisBidentate
  , .ir9SkewLinesChelateConformations
  ]

def next54ClassifiedProvisions : List IUPACNormativeProvision :=
  next54SequenceRuleProvisions ++ next54PerceptionProvisions ++
    next54SpatialDescriptorProvisions ++ next54DepictionProvisions ++
      next54NomenclatureProvisions ++ next54SourceOnlyProvisions

/-- Exact semantic-family classifier for the second work unit.  `none` is reserved for manifest
rows outside this batch; authority-data is absent because this 54-row slice contains no such row. -/
def next54Kind? (provision : IUPACNormativeProvision) : Option ProvisionKind :=
  if provision ∈ next54SequenceRuleProvisions then some .sequenceRule
  else if provision ∈ next54PerceptionProvisions then some .perception
  else if provision ∈ next54SpatialDescriptorProvisions then some .spatialDescriptor
  else if provision ∈ next54DepictionProvisions then some .depiction
  else if provision ∈ next54NomenclatureProvisions then some .nomenclature
  else if provision ∈ next54SourceOnlyProvisions then some .sourceOnly
  else none

@[simp] theorem next54SequenceRuleProvisionCount :
    next54SequenceRuleProvisions.length = 11 := by rfl

@[simp] theorem next54PerceptionProvisionCount :
    next54PerceptionProvisions.length = 17 := by rfl

@[simp] theorem next54SpatialDescriptorProvisionCount :
    next54SpatialDescriptorProvisions.length = 18 := by rfl

@[simp] theorem next54DepictionProvisionCount :
    next54DepictionProvisions.length = 1 := by rfl

@[simp] theorem next54NomenclatureProvisionCount :
    next54NomenclatureProvisions.length = 5 := by rfl

@[simp] theorem next54AuthorityDataProvisionCount :
    ([] : List IUPACNormativeProvision).length = 0 := by rfl

@[simp] theorem next54SourceOnlyProvisionCount :
    next54SourceOnlyProvisions.length = 2 := by rfl

@[simp] theorem next54ClassifiedProvisionCount :
    next54ClassifiedProvisions.length = 54 := by rfl

theorem next54ClassifiedProvisions_nodup : next54ClassifiedProvisions.Nodup := by
  decide

/-- The seven semantic-family work queues cover exactly the second 54-row inventory. -/
theorem next54KindClassification_exact :
    next54ClassifiedProvisions.toFinset = next54Provisions.toFinset := by
  decide

theorem next54Kind?_isSome_iff (provision : IUPACNormativeProvision) :
    (next54Kind? provision).isSome = true ↔ provision ∈ next54Provisions := by
  have memberExact := Finset.ext_iff.mp next54KindClassification_exact provision
  rw [next54Kind?]
  split_ifs <;> simp_all [next54ClassifiedProvisions]

/-- Total family routing for a proof-relevant member of the exact 54-row scope. -/
def next54Kind (provision : IUPACNormativeProvision)
    (member : provision ∈ next54Provisions) : ProvisionKind :=
  (next54Kind? provision).get ((next54Kind?_isSome_iff provision).2 member)

theorem next54Kind?_eq_some (provision : IUPACNormativeProvision)
    (member : provision ∈ next54Provisions) :
    next54Kind? provision = some (next54Kind provision member) := by
  have present := (next54Kind?_isSome_iff provision).2 member
  cases kindEq : next54Kind? provision with
  | none => simp [kindEq] at present
  | some kind => simp [next54Kind, kindEq]

/-! ## Reviewed-table routing boundary -/

/-- The source-faithful table required for the second batch.  Unlike an unconstrained generic
batch, every dependent reviewed row is forced to use the exact audited family classifier above. -/
structure Next54ReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch next54Provisions.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ next54Provisions.toFinset),
      (reviewed.row provision member).kind =
        next54Kind provision (by simpa using member)

/-- Exact corpus agreement with the classifier-bound next-54 reviewed table. -/
structure Next54ReferenceFaithful
    (reviewed : Next54ReviewedSemanticsTable)
    (corpus : FrozenProvisionCorpus) : Prop where
  batch : ProvisionBatchReferenceFaithful reviewed.reviewed corpus

namespace Next54ReferenceFaithful

/-- A faithful corpus cannot silently reroute any next-54 row to a different family theorem. -/
theorem kind_exact {reviewed : Next54ReviewedSemanticsTable}
    {corpus : FrozenProvisionCorpus}
    (faithful : Next54ReferenceFaithful reviewed corpus)
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54Provisions) :
    corpus.kind provision = next54Kind provision member := by
  let finMember : provision ∈ next54Provisions.toFinset := by simpa using member
  calc
    corpus.kind provision = (reviewed.reviewed.row provision finMember).kind :=
      (faithful.batch.exact finMember).1
    _ = next54Kind provision member := by
      simpa using reviewed.classifier_exact finMember

/-- The optional inventory classifier and corpus-owned total classifier agree on every member. -/
theorem classifier_eq_corpus_kind {reviewed : Next54ReviewedSemanticsTable}
    {corpus : FrozenProvisionCorpus}
    (faithful : Next54ReferenceFaithful reviewed corpus)
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54Provisions) :
    next54Kind? provision = some (corpus.kind provision) := by
  rw [faithful.kind_exact member]
  exact next54Kind?_eq_some provision member

end Next54ReferenceFaithful

/-- The batch has no authority-data row; all remaining kinds have the exact counts above. -/
theorem next54KindCount_total : 11 + 17 + 18 + 1 + 5 + 0 + 2 = 54 := by
  decide

@[simp] theorem next54P91ProvisionCount : next54P91Provisions.length = 7 := by
  rfl

@[simp] theorem next54P92ResidualProvisionCount :
    next54P92ResidualProvisions.length = 32 := by
  rfl

@[simp] theorem next54P93PolyhedralResidualProvisionCount :
    next54P93PolyhedralResidualProvisions.length = 3 := by
  rfl

@[simp] theorem next54IR9ResidualProvisionCount :
    next54IR9ResidualProvisions.length = 12 := by
  rfl

@[simp] theorem next54ProvisionCount : next54Provisions.length = 54 := by
  rfl

theorem next54Provisions_nodup : next54Provisions.Nodup := by
  decide

/-- The second batch shares no row with the primitive 35. -/
theorem next54Provisions_disjoint_primitive35 :
    List.Disjoint next54Provisions primitive35Provisions := by
  rw [List.disjoint_left]
  decide

/-- The residual P-92 rows plus the initial rule rows recover all 43 P-92 source provisions. -/
theorem next54P92Residual_union_primitive_exact :
    (next54P92ResidualProvisions ++ primitiveP92SequenceRuleProvisions).toFinset =
      p92SourceProvisions.toFinset := by
  decide

/-- The residual and primitive P-93 rows recover the complete 11-row polyhedral slice. -/
theorem next54P93Residual_union_primitive_exact :
    (next54P93PolyhedralResidualProvisions ++
      primitiveP93SpatialDescriptorProvisions).toFinset =
        p93PolyhedralSemanticsSlice.toFinset := by
  decide

/-- The 12 residuals, initial 16, and deferred umbrella recover every one of the 29 IR-9 rows. -/
theorem next54IR9Residual_union_primitive_and_umbrella_exact :
    (next54IR9ResidualProvisions ++ primitiveIR9SpatialDescriptorProvisions ++
      [deferredIR9UmbrellaProvision]).toFinset = ir9SemanticsSlice.toFinset := by
  decide

/-- Every row in the queue is already honestly recorded as partially formalized.  This is an
inventory theorem only; it cannot promote any row to `provisionComplete`. -/
theorem next54Provisions_semantics_honestly_partial
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54Provisions) :
    currentSemanticsMaturity provision = .partiallyFormalized := by
  rcases List.mem_append.mp member with blueBookMember | ir9Member
  · apply every_blueBookP9_provision_has_partial_independent_semantics provision
    have included : next54BlueBookProvisions.Forall
        (fun row => row ∈ sourceProvisions .blueBook2013P9) := by
      decide
    exact (List.forall_iff_forall_mem.mp included) provision blueBookMember
  · apply every_ir9_provision_has_partial_independent_semantics provision
    have included : next54IR9ResidualProvisions.Forall
        (fun row => row ∈ sourceProvisions .redBook2005IR9) := by
      decide
    exact (List.forall_iff_forall_mem.mp included) provision ir9Member

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54Provisions_disjoint_primitive35
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54ClassifiedProvisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54KindClassification_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54Kind?_isSome_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54Kind?_eq_some
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54ReferenceFaithful.kind_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54ReferenceFaithful.classifier_eq_corpus_kind
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54KindCount_total
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92Residual_union_primitive_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P93Residual_union_primitive_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9Residual_union_primitive_and_umbrella_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54Provisions_semantics_honestly_partial
