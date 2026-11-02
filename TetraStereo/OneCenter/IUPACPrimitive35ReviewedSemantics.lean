import TetraStereo.OneCenter.IUPACRule45CanonicalProvisionFamily

set_option autoImplicit false
















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## Reusable source-relation shapes -/

structure UnaryAuthorityObservation (Input Output : Type) where
  input : Input
  output : Output

structure BinaryAuthorityObservation (Input Output : Type) where
  left : Input
  right : Input
  output : Output

structure TernaryAuthorityObservation (First Second Third Output : Type) where
  first : First
  second : Second
  third : Third
  output : Output

def unaryAuthorityReference (Input Output : Type) (reference : Input → Output) :
    ProvisionReference where
  Observation := UnaryAuthorityObservation Input Output
  Applicable := fun _input => True
  Judges := fun _input observation => reference observation.input = observation.output

def binaryAuthorityReference (Input Output : Type) (reference : Input → Input → Output) :
    ProvisionReference where
  Observation := BinaryAuthorityObservation Input Output
  Applicable := fun _input => True
  Judges := fun _input observation =>
    reference observation.left observation.right = observation.output

def binaryAuthorityRelation (Input Output : Type)
    (reference : Input → Input → Output → Prop) : ProvisionReference where
  Observation := BinaryAuthorityObservation Input Output
  Applicable := fun _input => True
  Judges := fun _input observation =>
    reference observation.left observation.right observation.output

def ternaryAuthorityReference (First Second Third Output : Type)
    (reference : First → Second → Third → Output) : ProvisionReference where
  Observation := TernaryAuthorityObservation First Second Third Output
  Applicable := fun _input => True
  Judges := fun _input observation =>
    reference observation.first observation.second observation.third = observation.output

/-! ## P-92 reference rows -/

def p92Rule1aAtomicNumberReference : ProvisionReference :=
  binaryAuthorityRelation DeclarativeCIP.ExactAtomicNumber Ordering
    DeclarativeCIP.ExactAtomicNumber.Outcome

def p92Rule1bDuplicateProximityReference : ProvisionReference :=
  binaryAuthorityReference Nat Ordering BlueBookP92.rule1bDecision

def p92Rule2IsotopeMassReference : ProvisionReference :=
  binaryAuthorityReference Nat Ordering BlueBookP92.rule2Decision

def p92Rule3GeometryReference : ProvisionReference :=
  unaryAuthorityReference OfficialRule3Geometry BlueBookP92.Rule3Class
    BlueBookP92.rule3ClassOfOfficial

def p92Rule3SeqCisTransReference : ProvisionReference :=
  unaryAuthorityReference OfficialRule3Geometry Nat fun geometry =>
    BlueBookP92.rule3Priority (BlueBookP92.rule3ClassOfOfficial geometry)

def p92Rule3PriorityReference : ProvisionReference :=
  binaryAuthorityReference OfficialRule3Geometry Ordering fun left right =>
    BlueBookP92.rule3Decision (BlueBookP92.rule3ClassOfOfficial left)
      (BlueBookP92.rule3ClassOfOfficial right)

def p92Rule4aUnitKindReference : ProvisionReference :=
  binaryAuthorityReference OfficialStereogenicUnitKind Ordering fun left right =>
    BlueBookP92.rule4aDecision (BlueBookP92.rule4aClassOfOfficial left)
      (BlueBookP92.rule4aClassOfOfficial right)

def p92Rule4cPseudoasymmetryReference : ProvisionReference :=
  binaryAuthorityReference OfficialPseudoasymmetricDescriptor (Option Ordering) fun left right =>
    BlueBookP92.rule4cDecision? (BlueBookP92.rule4cSymbolOfOfficial left)
      (BlueBookP92.rule4cSymbolOfOfficial right)

/-! ## P-93 and IR-9 reference rows -/

/-- The eight geometries printed in Blue Book P-93.3.2, Table 9.1.  This is deliberately not the
25-row Red Book IR-9.2 vocabulary. -/
def p93CommonPolyhedralGeometries : List PolyhedralGeometry :=
  [ .trigonalPyramid
  , .tShape
  , .tetrahedron
  , .squarePlanar
  , .seeSaw
  , .trigonalBipyramid
  , .squarePyramid
  , .octahedron
  ]

@[simp] theorem p93CommonPolyhedralGeometries_length :
    p93CommonPolyhedralGeometries.length = 8 := by decide

theorem p93CommonPolyhedralGeometries_nodup :
    p93CommonPolyhedralGeometries.Nodup := by decide

/-- P-93.3.2/Table 9.1 is restricted to the eight common organic geometries. -/
def p93PolyhedralSymbolReference : ProvisionReference where
  Observation := UnaryAuthorityObservation PolyhedralGeometry String
  Applicable := fun _input => True
  Judges := fun _input observation =>
    observation.input ∈ p93CommonPolyhedralGeometries ∧
      (BlueBookP93.geometryOfProduction observation.input).symbol = observation.output

/-- IR-9.3.2.1/Table IR-9.2 supplies the full 25-geometry vocabulary. -/
def ir9PolyhedralSymbolReference : ProvisionReference :=
  unaryAuthorityReference PolyhedralGeometry String fun geometry =>
    (BlueBookP93.geometryOfProduction geometry).symbol

def unaryPolyhedralPriorityIndexReference (coordination : Nat)
    (reference : BlueBookP93.PriorityNumber → List BlueBookP93.PriorityNumber) :
    ProvisionReference where
  Observation := UnaryAuthorityObservation PolyhedralPriorityNumber
    (List BlueBookP93.PriorityNumber)
  Applicable := fun _input => True
  Judges := fun _input observation =>
    (BlueBookP93.priorityOfProduction observation.input).validFor coordination = true ∧
      reference (BlueBookP93.priorityOfProduction observation.input) = observation.output

def binaryPolyhedralPriorityIndexReference (coordination : Nat)
    (reference : BlueBookP93.PriorityNumber → BlueBookP93.PriorityNumber →
      List BlueBookP93.PriorityNumber) : ProvisionReference where
  Observation := BinaryAuthorityObservation PolyhedralPriorityNumber
    (List BlueBookP93.PriorityNumber)
  Applicable := fun _input => True
  Judges := fun _input observation =>
    (BlueBookP93.priorityOfProduction observation.left).validFor coordination = true ∧
    (BlueBookP93.priorityOfProduction observation.right).validFor coordination = true ∧
      reference (BlueBookP93.priorityOfProduction observation.left)
        (BlueBookP93.priorityOfProduction observation.right) = observation.output

def tShapeIndexReference : ProvisionReference :=
  unaryPolyhedralPriorityIndexReference 3 BlueBookP93.tShapeIndex

def squarePlanarIndexReference : ProvisionReference :=
  unaryPolyhedralPriorityIndexReference 4 BlueBookP93.squarePlanarIndex

def squarePyramid4IndexReference : ProvisionReference :=
  unaryPolyhedralPriorityIndexReference 4 BlueBookP93.squarePyramid4Index

def seeSawIndexReference : ProvisionReference :=
  binaryPolyhedralPriorityIndexReference 4 BlueBookP93.seeSawIndex

def trigonalBipyramidIndexReference : ProvisionReference :=
  binaryPolyhedralPriorityIndexReference 5 BlueBookP93.trigonalBipyramidIndex

def squarePyramidIndexReference : ProvisionReference :=
  binaryPolyhedralPriorityIndexReference 5 BlueBookP93.squarePyramidIndex

def octahedronIndexReference : ProvisionReference :=
  binaryPolyhedralPriorityIndexReference 6 BlueBookP93.octahedronIndex

def blueBookBipyramidalPriorityFrameValid
    (first second : PolyhedralPriorityNumber) (plane : List PolyhedralPriorityNumber) : Prop :=
  let coordination := plane.length + 2
  3 ≤ plane.length ∧
  (BlueBookP93.priorityOfProduction first).validFor coordination = true ∧
  (BlueBookP93.priorityOfProduction second).validFor coordination = true ∧
  ∀ priority ∈ plane,
    (BlueBookP93.priorityOfProduction priority).validFor coordination = true

def bipyramidalIndexReference : ProvisionReference where
  Observation := TernaryAuthorityObservation PolyhedralPriorityNumber
    PolyhedralPriorityNumber (List PolyhedralPriorityNumber)
    (List (List BlueBookP93.PriorityNumber))
  Applicable := fun _input => True
  Judges := fun _input observation =>
    blueBookBipyramidalPriorityFrameValid observation.first observation.second
      observation.third ∧
    BlueBookP93.bipyramidalIndex (BlueBookP93.priorityOfProduction observation.first)
        (BlueBookP93.priorityOfProduction observation.second)
        (observation.third.map BlueBookP93.priorityOfProduction) = observation.output

def trigonalPyramidalRSReference : ProvisionReference :=
  unaryAuthorityReference PolyhedralRotationSense RS fun sense =>
    RedBookIR9.trigonalPyramidalRS
      { sequenceFromPriorityOne := BlueBookP93.rotationOfProduction sense
        viewedFromCenterTowardLeastPreferred := True
        phantomSite := .lonePairSite
        phantomHasLowestPriority := True }

structure CAAuthorityObservation where
  frame : RedBookIR9.CAReferenceFrame
  sense : PolyhedralRotationSense
  symbol : BlueBookP93.ChiralitySymbol

def caAuthorityReference (allowedFrame : RedBookIR9.CAReferenceFrame → Prop) :
    ProvisionReference where
  Observation := CAAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    allowedFrame observation.frame ∧
      RedBookIR9.caSymbol (BlueBookP93.rotationOfProduction observation.sense) =
        observation.symbol

def genericCAReference : ProvisionReference :=
  caAuthorityReference fun _frame => True

def trigonalBipyramidalCAReference : ProvisionReference :=
  caAuthorityReference fun frame => frame = .trigonalBipyramidSeniorAxialNear

def squarePyramidalCAReference : ProvisionReference :=
  caAuthorityReference fun frame =>
    frame = .squarePyramid5AxialNear ∨ frame = .squarePyramid4CenterNear

def seeSawCAReference : ProvisionReference :=
  unaryAuthorityReference PolyhedralRotationSense BlueBookP93.ChiralitySymbol fun sense =>
    RedBookIR9.seeSawCASymbol
      { largestAnglePair := ({ number := 1 }, { number := 2 })
        viewedFromSeniorMemberOfLargestAnglePair := True
        remainingPairThroughSmallerAngle := True
        senseFromSeniorToJuniorRemainingLigand := BlueBookP93.rotationOfProduction sense }

def octahedralCAReference : ProvisionReference :=
  caAuthorityReference fun frame => frame = .octahedronPriorityOneNearAndLowestTransFar

def otherBipyramidalCAReference : ProvisionReference :=
  caAuthorityReference fun frame => ∃ kind, frame = .otherBipyramidSeniorAxialNear kind

/-- P-93.3.4 contains both the trigonal-pyramidal `R/S` exception and the general polyhedral
`A/C` convention.  Keeping both observations in one row prevents the provision-level reference
from silently dropping P-93.3.4.1. -/
structure P93PolyhedralChiralityAuthorityObservation where
  trigonalPyramidal : UnaryAuthorityObservation PolyhedralRotationSense RS
  polyhedral : CAAuthorityObservation

def p93PolyhedralChiralityReference : ProvisionReference where
  Observation := P93PolyhedralChiralityAuthorityObservation
  Applicable := fun _input => True
  Judges := fun input observation =>
    trigonalPyramidalRSReference.Judges input observation.trigonalPyramidal ∧
      genericCAReference.Judges input observation.polyhedral

structure PriorityNumberingAuthorityObservation where
  count : Nat
  compareAt : Nat → Nat → Option Ordering
  numbers : List Nat

def priorityNumberingReference : ProvisionReference where
  Observation := PriorityNumberingAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    RedBookIR9.FinitePriorityNumbering observation.count observation.compareAt
      observation.numbers

structure PrimingAuthorityObservation where
  donorCount : Nat
  memberships : List (Option RedBookIR9.PrimingMembership)
  primeCounts : List Nat

def primingConventionReference : ProvisionReference where
  Observation := PrimingAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    RedBookIR9.FinitePrimingAssignment observation.donorCount observation.memberships
      observation.primeCounts

/-- One operation-level observation for all four normative components of P-93.3.3.1: dense base
priority numbering, the repeated-ligand priming convention, preference for fewer primes, and the
trans-maximum-difference tie breaker. -/
structure P93PriorityNumberingAuthorityObservation where
  numbering : PriorityNumberingAuthorityObservation
  priming : PrimingAuthorityObservation
  left : PolyhedralPriorityNumber
  right : PolyhedralPriorityNumber
  priorityOutput : Ordering
  leftOpposite : PolyhedralPriorityNumber
  rightOpposite : PolyhedralPriorityNumber
  transMaximumOutput : Ordering

/-- Independent composite semantics for P-93.3.3.1.  It reuses the separately transcribed IR-9
numbering/priming relations because P-93 explicitly delegates those clauses to IR-9.3.3 and
IR-9.3.5, while retaining the independent Blue Book priority and trans-maximum functions. -/
def p93PolyhedralPriorityNumberingReference : ProvisionReference where
  Observation := P93PriorityNumberingAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    observation.numbering.count = observation.priming.donorCount ∧
    RedBookIR9.FinitePriorityNumbering observation.numbering.count
      observation.numbering.compareAt observation.numbering.numbers ∧
    RedBookIR9.FinitePrimingAssignment observation.priming.donorCount
      observation.priming.memberships observation.priming.primeCounts ∧
    BlueBookP93.priorityDecision (BlueBookP93.priorityOfProduction observation.left)
        (BlueBookP93.priorityOfProduction observation.right) = observation.priorityOutput ∧
    BlueBookP93.transMaximumDecision
        (BlueBookP93.priorityOfProduction observation.leftOpposite)
        (BlueBookP93.priorityOfProduction observation.rightOpposite) =
      observation.transMaximumOutput

/-! ## Exhaustive, named 11/8/16 source table -/

inductive Primitive35AuthorityRow where
  | p92Rule1aAtomicNumber
  | p92Rule1bDuplicateProximity
  | p92Rule2IsotopeMass
  | p92Rule3Geometry
  | p92Rule3SeqCisTrans
  | p92Rule3Priority
  | p92Rule4aUnitKind
  | p92Rule45 (family : Rule45CanonicalProvisionFamily)
  | p92Rule4cPseudoasymmetry
  | p93PolyhedralSymbols
  | p93PolyhedralPriorityNumbering
  | p93TShape
  | p93SeeSaw
  | p93TrigonalBipyramid
  | p93SquarePyramid
  | p93Octahedron
  | p93PolyhedralChirality
  | ir9PolyhedralSymbols
  | ir9SquarePlanar
  | ir9Octahedral
  | ir9SquarePyramidal
  | ir9Bipyramidal
  | ir9TShape
  | ir9SeeSaw
  | ir9RSTrigonalPyramidal
  | ir9CAPolyhedral
  | ir9CATrigonalBipyramidal
  | ir9CASquarePyramidal
  | ir9CASeeSaw
  | ir9CAOctahedral
  | ir9CAOtherBipyramidal
  | ir9PriorityNumbers
  | ir9PrimingConvention
  deriving DecidableEq, Repr, Fintype

namespace Primitive35AuthorityRow

def all : List Primitive35AuthorityRow :=
  [ .p92Rule1aAtomicNumber
  , .p92Rule1bDuplicateProximity
  , .p92Rule2IsotopeMass
  , .p92Rule3Geometry
  , .p92Rule3SeqCisTrans
  , .p92Rule3Priority
  , .p92Rule4aUnitKind
  , .p92Rule45 .rule4bLikeUnlike
  , .p92Rule45 .rule4bPairingMethodology
  , .p92Rule4cPseudoasymmetry
  , .p92Rule45 .rule5Enantiomorph
  , .p93PolyhedralSymbols
  , .p93PolyhedralPriorityNumbering
  , .p93TShape
  , .p93SeeSaw
  , .p93TrigonalBipyramid
  , .p93SquarePyramid
  , .p93Octahedron
  , .p93PolyhedralChirality
  , .ir9PolyhedralSymbols
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

def provision : Primitive35AuthorityRow → IUPACNormativeProvision
  | .p92Rule1aAtomicNumber => .p92Rule1aAtomicNumber
  | .p92Rule1bDuplicateProximity => .p92Rule1bDuplicateProximity
  | .p92Rule2IsotopeMass => .p92Rule2IsotopeMass
  | .p92Rule3Geometry => .p92Rule3Geometry
  | .p92Rule3SeqCisTrans => .p92Rule3SeqCisTrans
  | .p92Rule3Priority => .p92Rule3Priority
  | .p92Rule4aUnitKind => .p92Rule4aUnitKind
  | .p92Rule45 family => family.provision
  | .p92Rule4cPseudoasymmetry => .p92Rule4cPseudoasymmetry
  | .p93PolyhedralSymbols => .p93PolyhedralSymbols
  | .p93PolyhedralPriorityNumbering => .p93PolyhedralPriorityNumbering
  | .p93TShape => .p93TShape
  | .p93SeeSaw => .p93SeeSaw
  | .p93TrigonalBipyramid => .p93TrigonalBipyramid
  | .p93SquarePyramid => .p93SquarePyramid
  | .p93Octahedron => .p93Octahedron
  | .p93PolyhedralChirality => .p93PolyhedralChirality
  | .ir9PolyhedralSymbols => .ir9PolyhedralSymbols
  | .ir9SquarePlanar => .ir9SquarePlanar
  | .ir9Octahedral => .ir9Octahedral
  | .ir9SquarePyramidal => .ir9SquarePyramidal
  | .ir9Bipyramidal => .ir9Bipyramidal
  | .ir9TShape => .ir9TShape
  | .ir9SeeSaw => .ir9SeeSaw
  | .ir9RSTrigonalPyramidal => .ir9RSTrigonalPyramidal
  | .ir9CAPolyhedral => .ir9CAPolyhedral
  | .ir9CATrigonalBipyramidal => .ir9CATrigonalBipyramidal
  | .ir9CASquarePyramidal => .ir9CASquarePyramidal
  | .ir9CASeeSaw => .ir9CASeeSaw
  | .ir9CAOctahedral => .ir9CAOctahedral
  | .ir9CAOtherBipyramidal => .ir9CAOtherBipyramidal
  | .ir9PriorityNumbers => .ir9PriorityNumbers
  | .ir9PrimingConvention => .ir9PrimingConvention

def kind : Primitive35AuthorityRow → ProvisionKind
  | .p92Rule1aAtomicNumber
  | .p92Rule1bDuplicateProximity
  | .p92Rule2IsotopeMass
  | .p92Rule3Geometry
  | .p92Rule3SeqCisTrans
  | .p92Rule3Priority
  | .p92Rule4aUnitKind
  | .p92Rule45 _
  | .p92Rule4cPseudoasymmetry
      => .sequenceRule
  | _ => .spatialDescriptor

def reference : Primitive35AuthorityRow → ProvisionReference
  | .p92Rule1aAtomicNumber => p92Rule1aAtomicNumberReference
  | .p92Rule1bDuplicateProximity => p92Rule1bDuplicateProximityReference
  | .p92Rule2IsotopeMass => p92Rule2IsotopeMassReference
  | .p92Rule3Geometry => p92Rule3GeometryReference
  | .p92Rule3SeqCisTrans => p92Rule3SeqCisTransReference
  | .p92Rule3Priority => p92Rule3PriorityReference
  | .p92Rule4aUnitKind => p92Rule4aUnitKindReference
  | .p92Rule45 family => family.completeReference
  | .p92Rule4cPseudoasymmetry => p92Rule4cPseudoasymmetryReference
  | .p93PolyhedralSymbols => p93PolyhedralSymbolReference
  | .p93PolyhedralPriorityNumbering => p93PolyhedralPriorityNumberingReference
  | .p93TShape => tShapeIndexReference
  | .p93SeeSaw => seeSawIndexReference
  | .p93TrigonalBipyramid => trigonalBipyramidIndexReference
  | .p93SquarePyramid => squarePyramidIndexReference
  | .p93Octahedron => octahedronIndexReference
  | .p93PolyhedralChirality => p93PolyhedralChiralityReference
  | .ir9PolyhedralSymbols => ir9PolyhedralSymbolReference
  | .ir9SquarePlanar => squarePlanarIndexReference
  | .ir9Octahedral => octahedronIndexReference
  | .ir9SquarePyramidal => squarePyramid4IndexReference
  | .ir9Bipyramidal => bipyramidalIndexReference
  | .ir9TShape => tShapeIndexReference
  | .ir9SeeSaw => seeSawIndexReference
  | .ir9RSTrigonalPyramidal => trigonalPyramidalRSReference
  | .ir9CAPolyhedral => genericCAReference
  | .ir9CATrigonalBipyramidal => trigonalBipyramidalCAReference
  | .ir9CASquarePyramidal => squarePyramidalCAReference
  | .ir9CASeeSaw => seeSawCAReference
  | .ir9CAOctahedral => octahedralCAReference
  | .ir9CAOtherBipyramidal => otherBipyramidalCAReference
  | .ir9PriorityNumbers => priorityNumberingReference
  | .ir9PrimingConvention => primingConventionReference

def semantics (row : Primitive35AuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference

@[simp] theorem all_length : all.length = 35 := by decide

theorem all_nodup : all.Nodup := by decide

theorem provision_injective : Function.Injective provision := by
  decide

theorem all_provisions_exact : all.map provision = primitive35Provisions := by
  rfl

@[simp] theorem classifier_exact (row : Primitive35AuthorityRow) :
    primitive35Kind? row.provision = some row.kind := by
  cases row <;>
    simp [primitive35Kind?, primitiveP92SequenceRuleProvisions,
      primitiveP93SpatialDescriptorProvisions, primitiveIR9SpatialDescriptorProvisions,
      provision, kind]
  case p92Rule45 family => cases family <;> decide

end Primitive35AuthorityRow

theorem exists_primitive35AuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ primitive35Provisions) :
    ∃ row, row ∈ Primitive35AuthorityRow.all ∧ row.provision = provision := by
  rw [← Primitive35AuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def primitive35AuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ primitive35Provisions) : Primitive35AuthorityRow :=
  Classical.choose (exists_primitive35AuthorityRow member)

theorem primitive35AuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ primitive35Provisions) :
    (primitive35AuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_primitive35AuthorityRow member)).2

/-- The concrete reviewed 35-row source program.  Its admitted domain is frozen independently of
the eventual production interpreter, and every manifest row is recovered through the exact enum
map rather than a default/fallback semantic record. -/
noncomputable def primitive35ReviewedSemantics : Primitive35ReviewedSemanticsTable where
  ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
  row := fun provision member =>
    (primitive35AuthorityRowOf provision member).semantics
  classifier_exact := by
    intro provision member
    let row := primitive35AuthorityRowOf provision member
    have rowProvision : row.provision = provision :=
      primitive35AuthorityRowOf_provision provision member
    change primitive35Kind? provision = some row.kind
    rw [← rowProvision]
    exact Primitive35AuthorityRow.classifier_exact row
  sourceAudited := fun {_provision} member => primitive35_sourceAuditComplete member
  primitiveCoverage := currentPrimitiveCoverage

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93CommonPolyhedralGeometries_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93CommonPolyhedralGeometries_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Primitive35AuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Primitive35AuthorityRow.classifier_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.exists_primitive35AuthorityRow
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35AuthorityRowOf_provision
