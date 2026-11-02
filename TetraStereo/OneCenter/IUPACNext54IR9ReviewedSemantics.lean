import TetraStereo.OneCenter.IUPACNext54ProvisionInventory
import TetraStereo.OneCenter.IUPACPrimitive35ReviewedSemantics

set_option autoImplicit false

/-!
# Independent reviewed targets for the 12 residual IR-9 provisions

This module transcribes the Red Book relations already formalized in `IR9PolyhedralSemantics`
into provision-indexed references for the IR-9 component of the second compiler batch. It does
not define production by reference, promote maturity, or claim that the remaining P-91/P-92/P-93
rows have been reviewed.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def ir9ConfigurationIntroductionReference : ProvisionReference :=
  unaryAuthorityReference Bool (List RedBookIR9.ConfigurationFactor)
    RedBookIR9.requiredFactors

def ir9GeometryChoiceReference : ProvisionReference :=
  unaryAuthorityReference RedBookIR9.GeometryRecognitionObservation
    (Option RedBookIR9.Geometry)
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?

def ir9DiastereoisomerGeneralReference : ProvisionReference where
  Observation := RedBookIR9.StereoisomerObservation
  Applicable := fun _input => True
  Judges := fun _input observation => RedBookIR9.Diastereomeric observation

/-! ## Source-level relations for the descriptor-forming residual rows

The observations below retain the premises which make a computed label meaningful.  In
particular, a bare equality with `configurationIndex`, `tetrahedralRS`, or
`trigonalPrismCASymbol` would accept malformed inputs or an output obtained under the wrong
viewpoint.
-/

def configurationIndexPriorities :
    RedBookIR9.ConfigurationIndexInput → List RedBookIR9.PriorityNumber
  | .squarePlanar opposite => [opposite]
  | .octahedral transToOne transToPlane => [transToOne, transToPlane]
  | .squarePyramid4 opposite => [opposite]
  | .squarePyramid5 apical opposite => [apical, opposite]
  | .bipyramidal _ first second perpendicular => first :: second :: perpendicular
  | .tShape stem => [stem]
  | .seeSaw first second => [first, second]
  | .trigonalPrism firstFace secondFace => firstFace ++ secondFace

/-- Geometry-specific input arity required before an IR-9.3.3 configuration index is formed. -/
def configurationIndexArityValid : RedBookIR9.ConfigurationIndexInput → Prop
  | .bipyramidal .trigonal5 _ _ perpendicular => perpendicular.length = 3
  | .bipyramidal .pentagonal7 _ _ perpendicular => perpendicular.length = 5
  | .bipyramidal .hexagonal8 _ _ perpendicular => perpendicular.length = 6
  | .bipyramidal .heptagonal9 _ _ perpendicular => perpendicular.length = 7
  | .trigonalPrism firstFace secondFace => firstFace.length = 3 ∧ secondFace.length = 3
  | _ => True

/-- One position-indexed donor frame. Base priority and prime grouping are validated separately,
then rejoined into the full P-93 priority number actually consumed by configuration rules. -/
structure IR9FiniteDonorPriorityFrame where
  numbering : PriorityNumberingAuthorityObservation
  priming : PrimingAuthorityObservation

def IR9FiniteDonorPriorityFrame.priorityAt
    (frame : IR9FiniteDonorPriorityFrame) (position : Nat) : RedBookIR9.PriorityNumber :=
  { number := frame.numbering.numbers[position]?.getD 0
    primes := frame.priming.primeCounts[position]?.getD 0 }

def FiniteDonorPriorityFrameJudged (frame : IR9FiniteDonorPriorityFrame) : Prop :=
  frame.numbering.count = frame.priming.donorCount ∧
    RedBookIR9.FinitePriorityNumbering frame.numbering.count
      frame.numbering.compareAt frame.numbering.numbers ∧
    RedBookIR9.FinitePrimingAssignment frame.priming.donorCount
      frame.priming.memberships frame.priming.primeCounts

/-- Geometry-specific index input together with the exact donor occupying every selected spatial
position. The full `(number, primes)` value must equal the value at that donor position; loose
number membership is insufficient. -/
structure IR9PositionedConfigurationIndexInput where
  input : RedBookIR9.ConfigurationIndexInput
  donorAtIndexPosition : List Nat

def PositionedConfigurationIndexInputWellFormed
    (frame : IR9FiniteDonorPriorityFrame)
    (positioned : IR9PositionedConfigurationIndexInput) : Prop :=
  configurationIndexArityValid positioned.input ∧
    positioned.donorAtIndexPosition.length =
      (configurationIndexPriorities positioned.input).length ∧
    positioned.donorAtIndexPosition.Nodup ∧
    (∀ position ∈ positioned.donorAtIndexPosition,
      position < frame.numbering.count) ∧
    configurationIndexPriorities positioned.input =
      positioned.donorAtIndexPosition.map frame.priorityAt ∧
    ∀ priority ∈ configurationIndexPriorities positioned.input,
      priority.validFor positioned.input.geometry.coordinationNumber = true

/-- Independent finite perception carrier. It contains no configuration index or priority
number: constitution, spatial distribution, and absolute orientation are classified before a
separate encoding supplies geometry-specific index positions. -/
structure IR9IndependentSpatialArrangement where
  constitution : Nat
  spatialDistribution : List Nat
  absoluteOrientation : Bool
  deriving DecidableEq, Repr

def IR9IndependentSpatialArrangement.mirror
    (arrangement : IR9IndependentSpatialArrangement) : IR9IndependentSpatialArrangement :=
  { arrangement with absoluteOrientation := !arrangement.absoluteOrientation }

def independentStereoisomerObservation
    (left right : IR9IndependentSpatialArrangement) : RedBookIR9.StereoisomerObservation where
  sameConstitution := left.constitution = right.constitution
  spatialDistributionsDiffer :=
    left.spatialDistribution ≠ right.spatialDistribution ∨
      left.absoluteOrientation ≠ right.absoluteOrientation
  mirrorImages := right = left.mirror
  superimposable :=
    left.spatialDistribution = right.spatialDistribution ∧
      left.absoluteOrientation = right.absoluteOrientation

def IndependentMirrorImage
    (left right : IR9IndependentSpatialArrangement) : Prop :=
  right = left.mirror

def IndependentDiastereoisomer
    (left right : IR9IndependentSpatialArrangement) : Prop :=
  RedBookIR9.Diastereomeric (independentStereoisomerObservation left right)

/-- The perception-to-index encoding is data under test. Classification relations remain fixed
on the independent arrangement carrier and do not mention this encoding. -/
structure IR9ConfigurationIndexPerceptionModel where
  domain : List IR9IndependentSpatialArrangement
  encode : IR9IndependentSpatialArrangement → IR9PositionedConfigurationIndexInput

/-- A concrete mirror and a concrete diastereoisomer make the IR-9.3.3 invariants nonvacuous.
The final two clauses quantify over the complete finite perception domain, so correctness cannot
be discharged by selecting empty relations or one favorable example. -/
structure IR9ConfigurationIndexAuthorityObservation where
  frame : IR9FiniteDonorPriorityFrame
  perception : IR9ConfigurationIndexPerceptionModel
  arrangement : IR9IndependentSpatialArrangement
  output : List (List RedBookIR9.PriorityNumber)
  diastereoisomer : IR9IndependentSpatialArrangement

def ir9ConfigurationIndexReference : ProvisionReference where
  Observation := IR9ConfigurationIndexAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    FiniteDonorPriorityFrameJudged observation.frame ∧
    observation.perception.domain.Nodup ∧
    observation.arrangement ∈ observation.perception.domain ∧
    (∀ arrangement ∈ observation.perception.domain,
      observation.frame.numbering.count =
          (observation.perception.encode arrangement).input.geometry.coordinationNumber ∧
        PositionedConfigurationIndexInputWellFormed observation.frame
          (observation.perception.encode arrangement)) ∧
    RedBookIR9.configurationIndex
      (observation.perception.encode observation.arrangement).input = observation.output ∧
    observation.arrangement.mirror ≠ observation.arrangement ∧
    observation.arrangement.mirror ∈ observation.perception.domain ∧
    IndependentMirrorImage observation.arrangement observation.arrangement.mirror ∧
    observation.diastereoisomer ∈ observation.perception.domain ∧
    IndependentDiastereoisomer observation.arrangement observation.diastereoisomer ∧
    RedBookIR9.configurationIndex
      (observation.perception.encode observation.diastereoisomer).input ≠ observation.output ∧
    (∀ arrangement ∈ observation.perception.domain,
      arrangement.mirror ∈ observation.perception.domain ∧
        RedBookIR9.configurationIndex
          (observation.perception.encode arrangement.mirror).input =
        RedBookIR9.configurationIndex (observation.perception.encode arrangement).input) ∧
    ∀ left ∈ observation.perception.domain,
      ∀ right ∈ observation.perception.domain,
        IndependentDiastereoisomer left right →
          RedBookIR9.configurationIndex (observation.perception.encode right).input ≠
            RedBookIR9.configurationIndex (observation.perception.encode left).input

/-- IR-9.3.4.1 permits constitution-based `R/S` or `A/C` conventions and, where applicable,
the geometry-based skew-lines convention. -/
inductive IR9AbsoluteConfigurationGeneralAuthorityObservation where
  | constitutionBased
      (geometry : RedBookIR9.Geometry) (convention : RedBookIR9.AbsoluteConvention)
  | geometryBasedSkewLines
      (application : RedBookIR9.ChelateApplication)
      (handedness : RedBookIR9.HelixHandedness)
      (convention : RedBookIR9.AbsoluteConvention)
      (descriptor : RedBookIR9.SkewDescriptor)

def ir9AbsoluteConfigurationGeneralReference : ProvisionReference where
  Observation := IR9AbsoluteConfigurationGeneralAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    match observation with
    | .constitutionBased geometry convention =>
        RedBookIR9.constitutionBasedConvention geometry = convention
    | .geometryBasedSkewLines application handedness convention descriptor =>
        (application = .trisBidentateOctahedral ∨
          application = .cisBisBidentateOctahedral) ∧
          convention = .skewLines ∧
          RedBookIR9.configurationSkewDescriptor handedness = descriptor

def ir9RSTetrahedralReference : ProvisionReference where
  Observation := UnaryAuthorityObservation RedBookIR9.TetrahedralRSObservation RS
  Applicable := fun _input => True
  Judges := fun _input observation =>
    observation.input.viewedFromCenterTowardLeastPreferred ∧
      RedBookIR9.tetrahedralRS observation.input = observation.output

def ir9CATrigonalPrismaticReference : ProvisionReference where
  Observation := UnaryAuthorityObservation RedBookIR9.TrigonalPrismCAObservation
    BlueBookP93.ChiralitySymbol
  Applicable := fun _input => True
  Judges := fun _input observation =>
    observation.input.preferredFaceHasGreaterHighPriorityCount ∧
      observation.input.viewedFromAbovePreferredFace ∧
      RedBookIR9.trigonalPrismCASymbol observation.input = observation.output

def ir9SkewLinesReference : ProvisionReference :=
  unaryAuthorityReference RedBookIR9.HelixHandedness RedBookIR9.SkewDescriptor
    RedBookIR9.configurationSkewDescriptor

structure IR9ChelateConfigurationAuthorityObservation where
  application : RedBookIR9.ChelateApplication
  availableRingPairCount : Nat
  selectedRingPair : Nat
  skewLineRoles : List RedBookIR9.ChelateLineRole
  handedness : RedBookIR9.HelixHandedness
  skewLineStatus : RedBookIR9.SkewLineStatus
  descriptor : RedBookIR9.SkewDescriptor

/-- The tris- and cis-bis(bidentate) rows differ in the number of available ring pairs, but both
still require selection of a pair, two donor-atom skew lines, handedness evidence, and the
resulting capital Delta/Lambda configuration descriptor. -/
def chelateConfigurationReference
    (expectedApplication : RedBookIR9.ChelateApplication) : ProvisionReference where
  Observation := IR9ChelateConfigurationAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    observation.application = expectedApplication ∧
      RedBookIR9.availableChelateRingPairs observation.application =
        some observation.availableRingPairCount ∧
      observation.selectedRingPair < observation.availableRingPairCount ∧
      observation.skewLineRoles =
        [.betweenDonorAtoms, .betweenDonorAtoms] ∧
      observation.skewLineStatus = .helical observation.handedness ∧
      RedBookIR9.configurationSkewDescriptor observation.handedness = observation.descriptor

def ir9SkewLinesTrisBidentateReference : ProvisionReference :=
  chelateConfigurationReference .trisBidentateOctahedral

def ir9SkewLinesBisBidentateReference : ProvisionReference :=
  chelateConfigurationReference .cisBisBidentateOctahedral

def ir9SkewLinesChelateConformationsReference : ProvisionReference :=
  unaryAuthorityReference RedBookIR9.HelixHandedness
    (List RedBookIR9.ChelateLineRole × RedBookIR9.SkewDescriptor) fun handedness =>
      (RedBookIR9.chelateConformationLines,
        RedBookIR9.conformationSkewDescriptor handedness)

/-! An oriented progression is geometric evidence: its constructor records which cyclic direction
the concrete donor-position sequence follows. The rotation sense consumed by the descriptor rule
is derived from that constructor rather than supplied independently. -/
inductive IR9OrientedDonorProgression where
  | clockwise (donorPositions : List Nat)
  | counterclockwise (donorPositions : List Nat)

def IR9OrientedDonorProgression.donorPositions : IR9OrientedDonorProgression → List Nat
  | .clockwise positions | .counterclockwise positions => positions

def IR9OrientedDonorProgression.sense :
    IR9OrientedDonorProgression → BlueBookP93.RotationSense
  | .clockwise _ => .clockwise
  | .counterclockwise _ => .counterclockwise

/-- A geometric progression is backed position-by-position by one finite donor frame and lists
the donors in strict CIP priority order. -/
def PriorityProgressionBackedByFrame
    (frame : IR9FiniteDonorPriorityFrame)
    (progression : IR9OrientedDonorProgression) : Prop :=
  progression.donorPositions ≠ [] ∧
    progression.donorPositions.Nodup ∧
    (∀ position ∈ progression.donorPositions, position < frame.numbering.count) ∧
    (progression.donorPositions.map frame.priorityAt).Pairwise fun senior junior =>
      senior.seniorTo junior = true

inductive IR9AbsolutePriorityUseAuthorityObservation where
  | tetrahedral
      (progression : IR9OrientedDonorProgression)
      (leastPreferredDonor : Nat)
      (viewedFromCenterTowardLeastPreferred : Prop)
      (descriptor : RS)
  | polyhedral
      (progression : IR9OrientedDonorProgression)
      (geometrySpecificViewAndSelectionHold : Prop)
      (descriptor : BlueBookP93.ChiralitySymbol)

def AbsolutePriorityUseJudged
    (frame : IR9FiniteDonorPriorityFrame)
    (observation : IR9AbsolutePriorityUseAuthorityObservation) : Prop :=
  match observation with
  | .tetrahedral progression leastPreferred viewed descriptor =>
      frame.numbering.count = 4 ∧
        progression.donorPositions.length = 3 ∧
        PriorityProgressionBackedByFrame frame progression ∧
        leastPreferred < frame.numbering.count ∧
        leastPreferred ∉ progression.donorPositions ∧
        (∀ position ∈ progression.donorPositions,
          (frame.priorityAt position).seniorTo (frame.priorityAt leastPreferred) = true) ∧
        viewed ∧
        RedBookIR9.tetrahedralRS
          { sequenceFromPriorityOne := progression.sense
            viewedFromCenterTowardLeastPreferred := viewed } = descriptor
  | .polyhedral progression framePremises descriptor =>
      PriorityProgressionBackedByFrame frame progression ∧
        framePremises ∧ RedBookIR9.caSymbol progression.sense = descriptor

structure IR9LigandPriorityGeneralAuthorityObservation where
  frame : IR9FiniteDonorPriorityFrame
  relativeInput : IR9PositionedConfigurationIndexInput
  relativeOutput : List (List RedBookIR9.PriorityNumber)
  absoluteUse : IR9AbsolutePriorityUseAuthorityObservation

def ir9LigandPriorityGeneralReference : ProvisionReference where
  Observation := IR9LigandPriorityGeneralAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    FiniteDonorPriorityFrameJudged observation.frame ∧
      observation.frame.numbering.count =
        observation.relativeInput.input.geometry.coordinationNumber ∧
      PositionedConfigurationIndexInputWellFormed observation.frame observation.relativeInput ∧
      RedBookIR9.configurationIndex observation.relativeInput.input = observation.relativeOutput ∧
      AbsolutePriorityUseJudged observation.frame observation.absoluteUse

/-- Exact row enumeration for the 12 residual IR-9 provisions. -/
inductive Next54IR9AuthorityRow where
  | configurationIntroduction
  | geometryChoice
  | diastereoisomerGeneral
  | configurationIndex
  | absoluteConfigurationGeneral
  | rsTetrahedral
  | caTrigonalPrismatic
  | skewLines
  | skewLinesTrisBidentate
  | skewLinesBisBidentate
  | skewLinesChelateConformations
  | ligandPriorityGeneral
  deriving DecidableEq, Repr

namespace Next54IR9AuthorityRow

def all : List Next54IR9AuthorityRow :=
  [ .configurationIntroduction
  , .geometryChoice
  , .diastereoisomerGeneral
  , .configurationIndex
  , .absoluteConfigurationGeneral
  , .rsTetrahedral
  , .caTrigonalPrismatic
  , .skewLines
  , .skewLinesTrisBidentate
  , .skewLinesBisBidentate
  , .skewLinesChelateConformations
  , .ligandPriorityGeneral
  ]

def provision : Next54IR9AuthorityRow → IUPACNormativeProvision
  | .configurationIntroduction => .ir9ConfigurationIntroduction
  | .geometryChoice => .ir9GeometryChoice
  | .diastereoisomerGeneral => .ir9DiastereoisomerGeneral
  | .configurationIndex => .ir9ConfigurationIndex
  | .absoluteConfigurationGeneral => .ir9AbsoluteConfigurationGeneral
  | .rsTetrahedral => .ir9RSTetrahedral
  | .caTrigonalPrismatic => .ir9CATrigonalPrismatic
  | .skewLines => .ir9SkewLines
  | .skewLinesTrisBidentate => .ir9SkewLinesTrisBidentate
  | .skewLinesBisBidentate => .ir9SkewLinesBisBidentate
  | .skewLinesChelateConformations => .ir9SkewLinesChelateConformations
  | .ligandPriorityGeneral => .ir9LigandPriorityGeneral

def kind : Next54IR9AuthorityRow → ProvisionKind
  | .configurationIntroduction => .sourceOnly
  | .geometryChoice | .diastereoisomerGeneral => .perception
  | .ligandPriorityGeneral => .sequenceRule
  | _ => .spatialDescriptor

def reference : Next54IR9AuthorityRow → ProvisionReference
  | .configurationIntroduction => ir9ConfigurationIntroductionReference
  | .geometryChoice => ir9GeometryChoiceReference
  | .diastereoisomerGeneral => ir9DiastereoisomerGeneralReference
  | .configurationIndex => ir9ConfigurationIndexReference
  | .absoluteConfigurationGeneral => ir9AbsoluteConfigurationGeneralReference
  | .rsTetrahedral => ir9RSTetrahedralReference
  | .caTrigonalPrismatic => ir9CATrigonalPrismaticReference
  | .skewLines => ir9SkewLinesReference
  | .skewLinesTrisBidentate => ir9SkewLinesTrisBidentateReference
  | .skewLinesBisBidentate => ir9SkewLinesBisBidentateReference
  | .skewLinesChelateConformations => ir9SkewLinesChelateConformationsReference
  | .ligandPriorityGeneral => ir9LigandPriorityGeneralReference

def semantics (row : Next54IR9AuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference

@[simp] theorem all_length : all.length = 12 := by rfl

theorem all_nodup : all.Nodup := by decide

@[simp] theorem all_provisions_exact : all.map provision = next54IR9ResidualProvisions := by
  rfl

@[simp] theorem classifier_exact (row : Next54IR9AuthorityRow) :
    next54Kind? row.provision = some row.kind := by
  cases row <;>
    simp [next54Kind?, next54SequenceRuleProvisions, next54PerceptionProvisions,
      next54SpatialDescriptorProvisions, next54DepictionProvisions,
      next54NomenclatureProvisions, next54SourceOnlyProvisions, provision, kind]

end Next54IR9AuthorityRow

theorem next54IR9_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54IR9ResidualProvisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : next54IR9ResidualProvisions.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_next54IR9AuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54IR9ResidualProvisions) :
    ∃ row, row ∈ Next54IR9AuthorityRow.all ∧ row.provision = provision := by
  rw [← Next54IR9AuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def next54IR9AuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54IR9ResidualProvisions) : Next54IR9AuthorityRow :=
  Classical.choose (exists_next54IR9AuthorityRow member)

theorem next54IR9AuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54IR9ResidualProvisions) :
    (next54IR9AuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_next54IR9AuthorityRow member)).2

/-- The reviewed IR-9 subset preserves the exact global next-54 classifier. -/
structure Next54IR9ReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch next54IR9ResidualProvisions.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ next54IR9ResidualProvisions.toFinset),
      (reviewed.row provision member).kind =
        next54Kind provision (by
          apply List.mem_append_right next54BlueBookProvisions
          simpa using member)

noncomputable def next54IR9ReviewedSemantics : Next54IR9ReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        (next54IR9AuthorityRowOf provision (by simpa using member)).semantics
      sourceAudited := by
        intro provision member
        exact next54IR9_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := next54IR9AuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      next54IR9AuthorityRowOf_provision provision (by simpa using member)
    have rowClassifier := Next54IR9AuthorityRow.classifier_exact row
    have memberList : provision ∈ next54Provisions := by
      apply List.mem_append_right next54BlueBookProvisions
      simpa using member
    have totalClassifier := next54Kind?_eq_some provision memberList
    rw [rowProvision] at rowClassifier
    change row.kind = next54Kind provision _
    exact Option.some.inj (rowClassifier.symm.trans totalClassifier)

/-! ## Nonvacuity of every independent row -/

def next54IR9WitnessInput : AuthoritativeChemicalInput where
  molecule := { atoms := [], interactions := [] }

@[simp] theorem next54IR9WitnessInput_structurallyWellFormed :
    next54IR9WitnessInput.StructurallyWellFormed := by
  simp [next54IR9WitnessInput, AuthoritativeChemicalInput.StructurallyWellFormed,
    SemanticMolecule.StructurallyWellFormed,
    AuthoritativeChemicalInput.SpatialIndicesWellFormed,
    AuthoritativeChemicalInput.DiagramIndicesWellFormed]

theorem next54UnaryAuthorityReference_nonvacuous
    {Input Output : Type} (reference : Input → Output) (input : Input) :
    ∃ observation,
      (unaryAuthorityReference Input Output reference).Applicable next54IR9WitnessInput ∧
      (unaryAuthorityReference Input Output reference).Judges next54IR9WitnessInput observation :=
  ⟨{ input := input, output := reference input }, trivial, rfl⟩

def next54IR9EqualDonorCompareAt (_left _right : Nat) : Option Ordering :=
  some .eq

def next54IR9PriorityNumberingWitness : PriorityNumberingAuthorityObservation where
  count := 4
  compareAt := next54IR9EqualDonorCompareAt
  numbers := [1, 1, 1, 1]

theorem next54IR9PriorityNumberingWitness_valid :
    RedBookIR9.FinitePriorityNumbering next54IR9PriorityNumberingWitness.count
      next54IR9PriorityNumberingWitness.compareAt
      next54IR9PriorityNumberingWitness.numbers := by
  refine
    { length_eq := rfl
      positive := ?_
      comparison := ?_
      highest_number_one := ?_
      no_gaps := ?_ }
  · intro position bound
    change position < 4 at bound
    have cases : position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      decide
  · intro left right leftBound rightBound
    change left < 4 at leftBound
    change right < 4 at rightBound
    have leftCases : left = 0 ∨ left = 1 ∨ left = 2 ∨ left = 3 := by omega
    have rightCases : right = 0 ∨ right = 1 ∨ right = 2 ∨ right = 3 := by omega
    rcases leftCases with rfl | rfl | rfl | rfl <;>
      rcases rightCases with rfl | rfl | rfl | rfl <;>
      norm_num [next54IR9PriorityNumberingWitness, next54IR9EqualDonorCompareAt,
        RedBookIR9.PriorityDecisionAgrees]
  · intro position bound _highest
    change position < 4 at bound
    have cases : position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      rfl
  · intro position bound number positive smaller
    change position < 4 at bound
    have cases : position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      change number < 1 at smaller <;> omega

def next54IR9PrimingMembership (group : Nat) : RedBookIR9.PrimingMembership where
  family := 0
  group := group

def next54IR9PrimingWitness : PrimingAuthorityObservation where
  donorCount := 4
  memberships :=
    [ some (next54IR9PrimingMembership 0)
    , some (next54IR9PrimingMembership 1)
    , some (next54IR9PrimingMembership 2)
    , some (next54IR9PrimingMembership 3)
    ]
  primeCounts := [0, 1, 2, 3]

/-- Source-level mathematical content of the concrete finite witness: four distinct occurrence
groups of one family receive the dense prime-count assignment `0,1,2,3`.  This theorem exposes
constancy, separation, an unprimed group, and gap-freedom independently of the executable checker. -/
def next54IR9AdmissiblePrimingAssignment :
    RedBookIR9.AdmissiblePrimingAssignment [0, 1, 2, 3] (fun donor : Nat => donor) where
  primeCount := fun donor => donor
  constantOnGroup := by
    intro left right _leftMember _rightMember sameGroup
    exact sameGroup
  separatesGroups := by
    intro left right _leftMember _rightMember differentGroups
    exact differentGroups
  hasUnprimed := by
    intro _nonempty
    exact ⟨0, by simp, rfl⟩
  noGaps := by
    intro donor donorMember count smaller
    have donorAtMostThree : donor ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at donorMember
      rcases donorMember with rfl | rfl | rfl | rfl <;> omega
    have countCases : count = 0 ∨ count = 1 ∨ count = 2 := by omega
    refine ⟨count, ?_, rfl⟩
    rcases countCases with rfl | rfl | rfl <;> simp

/-- The executable finite checker agrees with the explicit mathematical witness above.  `rfl`
is kernel reduction of this frozen four-row table, not a VM decision procedure or trusted axiom. -/
theorem next54IR9PrimingWitness_valid :
    RedBookIR9.FinitePrimingAssignment next54IR9PrimingWitness.donorCount
      next54IR9PrimingWitness.memberships next54IR9PrimingWitness.primeCounts := by
  rfl

def next54IR9DonorFrameWitness : IR9FiniteDonorPriorityFrame where
  numbering := next54IR9PriorityNumberingWitness
  priming := next54IR9PrimingWitness

theorem next54IR9DonorFrameWitness_valid :
    FiniteDonorPriorityFrameJudged next54IR9DonorFrameWitness :=
  ⟨rfl, next54IR9PriorityNumberingWitness_valid, next54IR9PrimingWitness_valid⟩

def next54IR9ArrangementA : IR9IndependentSpatialArrangement where
  constitution := 0
  spatialDistribution := [0]
  absoluteOrientation := false

def next54IR9ArrangementB : IR9IndependentSpatialArrangement where
  constitution := 0
  spatialDistribution := [1]
  absoluteOrientation := false

def next54IR9PerceptionDomain : List IR9IndependentSpatialArrangement :=
  [ next54IR9ArrangementA
  , next54IR9ArrangementA.mirror
  , next54IR9ArrangementB
  , next54IR9ArrangementB.mirror
  ]

def next54IR9EncodeArrangement
    (arrangement : IR9IndependentSpatialArrangement) :
    IR9PositionedConfigurationIndexInput :=
  if arrangement.spatialDistribution = [0] then
    { input := .squarePlanar (next54IR9DonorFrameWitness.priorityAt 0)
      donorAtIndexPosition := [0] }
  else
    { input := .squarePlanar (next54IR9DonorFrameWitness.priorityAt 1)
      donorAtIndexPosition := [1] }

def next54IR9PerceptionWitness : IR9ConfigurationIndexPerceptionModel where
  domain := next54IR9PerceptionDomain
  encode := next54IR9EncodeArrangement

theorem Next54IR9AuthorityRow.reference_nonvacuous (row : Next54IR9AuthorityRow) :
    ∃ observation,
      row.reference.Applicable next54IR9WitnessInput ∧
        row.reference.Judges next54IR9WitnessInput observation := by
  cases row with
  | configurationIntroduction =>
      exact next54UnaryAuthorityReference_nonvacuous RedBookIR9.requiredFactors false
  | geometryChoice =>
      exact next54UnaryAuthorityReference_nonvacuous
        RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?
        (.twoCoordinate .linearDisposition)
  | diastereoisomerGeneral =>
      let observation : RedBookIR9.StereoisomerObservation :=
        { sameConstitution := True
          spatialDistributionsDiffer := True
          mirrorImages := False
          superimposable := False }
      exact ⟨observation, trivial,
        by simp [Next54IR9AuthorityRow.reference, ir9DiastereoisomerGeneralReference,
          RedBookIR9.Diastereomeric, observation]⟩
  | configurationIndex =>
      let observation : IR9ConfigurationIndexAuthorityObservation :=
        { frame := next54IR9DonorFrameWitness
          perception := next54IR9PerceptionWitness
          arrangement := next54IR9ArrangementA
          output := RedBookIR9.configurationIndex
            (next54IR9PerceptionWitness.encode next54IR9ArrangementA).input
          diastereoisomer := next54IR9ArrangementB }
      refine ⟨observation, trivial, ?_⟩
      dsimp [Next54IR9AuthorityRow.reference, ir9ConfigurationIndexReference, observation]
      refine ⟨next54IR9DonorFrameWitness_valid, ?_⟩
      simp [next54IR9PerceptionWitness, next54IR9PerceptionDomain,
        next54IR9EncodeArrangement, next54IR9ArrangementA, next54IR9ArrangementB,
        IR9IndependentSpatialArrangement.mirror, IndependentMirrorImage,
        IndependentDiastereoisomer, independentStereoisomerObservation,
        RedBookIR9.Diastereomeric, PositionedConfigurationIndexInputWellFormed,
        configurationIndexArityValid, configurationIndexPriorities,
        RedBookIR9.ConfigurationIndexInput.geometry,
        RedBookIR9.configurationIndex, BlueBookP93.Geometry.coordinationNumber,
        BlueBookP93.PriorityNumber.validFor, IR9FiniteDonorPriorityFrame.priorityAt,
        next54IR9DonorFrameWitness, next54IR9PriorityNumberingWitness,
        next54IR9PrimingWitness]
  | absoluteConfigurationGeneral =>
      let observation : IR9AbsoluteConfigurationGeneralAuthorityObservation :=
        .constitutionBased .tetrahedron .rs
      exact ⟨observation, trivial, by
        simp [Next54IR9AuthorityRow.reference, ir9AbsoluteConfigurationGeneralReference,
          observation, RedBookIR9.constitutionBasedConvention]⟩
  | rsTetrahedral =>
      let input : RedBookIR9.TetrahedralRSObservation :=
        { sequenceFromPriorityOne := .clockwise
          viewedFromCenterTowardLeastPreferred := True }
      let observation : UnaryAuthorityObservation RedBookIR9.TetrahedralRSObservation RS :=
        { input := input, output := .R }
      exact ⟨observation, trivial, by
        simp [Next54IR9AuthorityRow.reference, ir9RSTetrahedralReference, observation,
          input, RedBookIR9.tetrahedralRS]⟩
  | caTrigonalPrismatic =>
      let input : RedBookIR9.TrigonalPrismCAObservation :=
        { preferredFaceHasGreaterHighPriorityCount := True
          viewedFromAbovePreferredFace := True
          oppositeFacePriorityProgression := .clockwise }
      let observation : UnaryAuthorityObservation RedBookIR9.TrigonalPrismCAObservation
          BlueBookP93.ChiralitySymbol :=
        { input := input, output := .C }
      exact ⟨observation, trivial, by
        simp [Next54IR9AuthorityRow.reference, ir9CATrigonalPrismaticReference,
          observation, input, RedBookIR9.trigonalPrismCASymbol, RedBookIR9.caSymbol,
          BlueBookP93.chiralitySymbol]⟩
  | skewLines =>
      exact next54UnaryAuthorityReference_nonvacuous
        RedBookIR9.configurationSkewDescriptor .rightHanded
  | skewLinesTrisBidentate =>
      let observation : IR9ChelateConfigurationAuthorityObservation :=
        { application := .trisBidentateOctahedral
          availableRingPairCount := 3
          selectedRingPair := 0
          skewLineRoles := [.betweenDonorAtoms, .betweenDonorAtoms]
          handedness := .rightHanded
          skewLineStatus := .helical .rightHanded
          descriptor := .capitalDelta }
      exact ⟨observation, trivial, by
        simp [Next54IR9AuthorityRow.reference, ir9SkewLinesTrisBidentateReference,
          chelateConfigurationReference, observation, RedBookIR9.availableChelateRingPairs,
          RedBookIR9.configurationSkewDescriptor]⟩
  | skewLinesBisBidentate =>
      let observation : IR9ChelateConfigurationAuthorityObservation :=
        { application := .cisBisBidentateOctahedral
          availableRingPairCount := 1
          selectedRingPair := 0
          skewLineRoles := [.betweenDonorAtoms, .betweenDonorAtoms]
          handedness := .leftHanded
          skewLineStatus := .helical .leftHanded
          descriptor := .capitalLambda }
      exact ⟨observation, trivial, by
        simp [Next54IR9AuthorityRow.reference, ir9SkewLinesBisBidentateReference,
          chelateConfigurationReference, observation, RedBookIR9.availableChelateRingPairs,
          RedBookIR9.configurationSkewDescriptor]⟩
  | skewLinesChelateConformations =>
      exact next54UnaryAuthorityReference_nonvacuous
        (fun handedness =>
          (RedBookIR9.chelateConformationLines,
            RedBookIR9.conformationSkewDescriptor handedness))
        RedBookIR9.HelixHandedness.rightHanded
  | ligandPriorityGeneral =>
      let relativeInput : IR9PositionedConfigurationIndexInput :=
        { input := .squarePlanar (next54IR9DonorFrameWitness.priorityAt 0)
          donorAtIndexPosition := [0] }
      let observation : IR9LigandPriorityGeneralAuthorityObservation :=
        { frame := next54IR9DonorFrameWitness
          relativeInput := relativeInput
          relativeOutput := RedBookIR9.configurationIndex relativeInput.input
          absoluteUse := .tetrahedral (.clockwise [0, 1, 2]) 3 True .R }
      refine ⟨observation, trivial, ?_⟩
      dsimp [Next54IR9AuthorityRow.reference, ir9LigandPriorityGeneralReference, observation]
      refine ⟨next54IR9DonorFrameWitness_valid, rfl, ?_⟩
      simp [relativeInput, PositionedConfigurationIndexInputWellFormed,
        configurationIndexArityValid, configurationIndexPriorities,
        RedBookIR9.ConfigurationIndexInput.geometry, RedBookIR9.configurationIndex,
        AbsolutePriorityUseJudged, PriorityProgressionBackedByFrame,
        IR9OrientedDonorProgression.donorPositions, IR9OrientedDonorProgression.sense,
        IR9FiniteDonorPriorityFrame.priorityAt, next54IR9DonorFrameWitness,
        next54IR9PriorityNumberingWitness, next54IR9PrimingWitness,
        RedBookIR9.tetrahedralRS, BlueBookP93.Geometry.coordinationNumber,
        BlueBookP93.PriorityNumber.validFor, BlueBookP93.PriorityNumber.seniorTo]

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54IR9AuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54IR9AuthorityRow.classifier_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9_sourceAuditComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9AuthorityRowOf_provision
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9ReviewedSemantics
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54IR9AuthorityRow.reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9PriorityNumberingWitness_valid
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9AdmissiblePrimingAssignment
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9PrimingWitness_valid
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9DonorFrameWitness_valid
