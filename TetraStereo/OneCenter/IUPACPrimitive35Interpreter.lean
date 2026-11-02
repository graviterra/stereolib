import TetraStereo.OneCenter.IUPACPrimitive35Compiler
import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance

set_option autoImplicit false

/-!
# Concrete production/reference bridges for the primitive 35

The first completed bridge is the eleven-row P-92 sequence-rule family.  Production propositions
below mention the actual executable/official comparator functions.  The family theorem proves
that each operation graph is exactly the independently reviewed reference graph.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## Concrete P-92 production operation graphs -/

def p92Rule1aAtomicNumberProduces
    (observation : BinaryAuthorityObservation DeclarativeCIP.ExactAtomicNumber Ordering) : Prop :=
  compareOfLessAndEq observation.left.value observation.right.value = observation.output

def p92Rule1bDuplicateProximityProduces
    (observation : BinaryAuthorityObservation Nat Ordering) : Prop :=
  OfficialRuleMajorKey.compareRule1b observation.left observation.right = observation.output

def p92Rule2IsotopeMassProduces
    (observation : BinaryAuthorityObservation Nat Ordering) : Prop :=
  compare observation.left observation.right = observation.output

def p92Rule3GeometryProduces
    (observation : UnaryAuthorityObservation OfficialRule3Geometry BlueBookP92.Rule3Class) : Prop :=
  BlueBookP92.rule3ClassOfOfficial observation.input = observation.output

def p92Rule3SeqCisTransProduces
    (observation : UnaryAuthorityObservation OfficialRule3Geometry Nat) : Prop :=
  observation.input.priority = observation.output

def p92Rule3PriorityProduces
    (observation : BinaryAuthorityObservation OfficialRule3Geometry Ordering) : Prop :=
  OfficialRule3Geometry.compare observation.left observation.right = observation.output

def p92Rule4aUnitKindProduces
    (observation : BinaryAuthorityObservation OfficialStereogenicUnitKind Ordering) : Prop :=
  OfficialStereogenicUnitKind.compare observation.left observation.right = observation.output

def p92Rule4cPseudoasymmetryProduces
    (observation : BinaryAuthorityObservation OfficialPseudoasymmetricDescriptor
      (Option Ordering)) : Prop :=
  OfficialPseudoasymmetricDescriptor.compare? observation.left observation.right =
    observation.output

/-! ## Exact row-level refinement -/

theorem p92Rule1aAtomicNumber_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation DeclarativeCIP.ExactAtomicNumber Ordering) :
    p92Rule1aAtomicNumberProduces observation ↔
      p92Rule1aAtomicNumberReference.Judges source observation := by
  change compareOfLessAndEq observation.left.value observation.right.value =
      observation.output ↔
    DeclarativeCIP.ExactAtomicNumber.Outcome observation.left observation.right
      observation.output
  unfold DeclarativeCIP.ExactAtomicNumber.Outcome
  rw [← LinearOrder.compare_eq_compareOfLessAndEq]

theorem p92Rule1bDuplicateProximity_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation Nat Ordering) :
    p92Rule1bDuplicateProximityProduces observation ↔
      p92Rule1bDuplicateProximityReference.Judges source observation := by
  change OfficialRuleMajorKey.compareRule1b observation.left observation.right =
      observation.output ↔
    BlueBookP92.rule1bDecision observation.left observation.right = observation.output
  unfold OfficialRuleMajorKey.compareRule1b BlueBookP92.rule1bDecision
  change OfficialRuleMajorKey.compareNat observation.right observation.left =
      observation.output ↔
    BlueBookP92.higherNatDecision observation.right observation.left = observation.output
  rw [show OfficialRuleMajorKey.compareNat observation.right observation.left =
      BlueBookP92.higherNatDecision observation.right observation.left by
    exact compareNat_conforms_blueBookP92_higher observation.right observation.left]

theorem p92Rule2IsotopeMass_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation Nat Ordering) :
    p92Rule2IsotopeMassProduces observation ↔
      p92Rule2IsotopeMassReference.Judges source observation := by
  unfold p92Rule2IsotopeMassProduces p92Rule2IsotopeMassReference
    binaryAuthorityReference BlueBookP92.rule2Decision
  rw [compareNat_conforms_blueBookP92_higher]

theorem p92Rule3Geometry_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : UnaryAuthorityObservation OfficialRule3Geometry BlueBookP92.Rule3Class) :
    p92Rule3GeometryProduces observation ↔
      p92Rule3GeometryReference.Judges source observation := by
  rfl

theorem p92Rule3SeqCisTrans_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : UnaryAuthorityObservation OfficialRule3Geometry Nat) :
    p92Rule3SeqCisTransProduces observation ↔
      p92Rule3SeqCisTransReference.Judges source observation := by
  change observation.input.priority = observation.output ↔
    BlueBookP92.rule3Priority (BlueBookP92.rule3ClassOfOfficial observation.input) =
      observation.output
  cases observation.input <;> rfl

theorem p92Rule3Priority_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation OfficialRule3Geometry Ordering) :
    p92Rule3PriorityProduces observation ↔
      p92Rule3PriorityReference.Judges source observation := by
  unfold p92Rule3PriorityProduces p92Rule3PriorityReference binaryAuthorityReference
  rw [currentPrimitiveCoverage.p92.descriptors.rule3]

theorem p92Rule4aUnitKind_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation OfficialStereogenicUnitKind Ordering) :
    p92Rule4aUnitKindProduces observation ↔
      p92Rule4aUnitKindReference.Judges source observation := by
  unfold p92Rule4aUnitKindProduces p92Rule4aUnitKindReference binaryAuthorityReference
  rw [currentPrimitiveCoverage.p92.descriptors.rule4a]

theorem p92Rule4cPseudoasymmetry_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation OfficialPseudoasymmetricDescriptor
      (Option Ordering)) :
    p92Rule4cPseudoasymmetryProduces observation ↔
      p92Rule4cPseudoasymmetryReference.Judges source observation := by
  unfold p92Rule4cPseudoasymmetryProduces p92Rule4cPseudoasymmetryReference
    binaryAuthorityReference
  rw [currentPrimitiveCoverage.p92.descriptors.rule4c]

/-! ## Concrete P-93 / IR-9 production operation graphs -/

def p93PolyhedralSymbolProduces
    (observation : UnaryAuthorityObservation PolyhedralGeometry String) : Prop :=
  observation.input ∈ p93CommonPolyhedralGeometries ∧
    observation.input.symbol = observation.output

def ir9PolyhedralSymbolProduces
    (observation : UnaryAuthorityObservation PolyhedralGeometry String) : Prop :=
  observation.input.symbol = observation.output

def tShapeIndexProduces
    (observation : UnaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) : Prop :=
  observation.input.validFor 3 = true ∧
    (tShapeConfigurationIndex observation.input).map BlueBookP93.priorityOfProduction =
      observation.output

def squarePlanarIndexProduces
    (observation : UnaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) : Prop :=
  observation.input.validFor 4 = true ∧
    (squarePlanarConfigurationIndex observation.input).map BlueBookP93.priorityOfProduction =
      observation.output

def squarePyramid4IndexProduces
    (observation : UnaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) : Prop :=
  observation.input.validFor 4 = true ∧
    (squarePyramid4ConfigurationIndex observation.input).map BlueBookP93.priorityOfProduction =
      observation.output

def seeSawIndexProduces
    (observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) : Prop :=
  observation.left.validFor 4 = true ∧ observation.right.validFor 4 = true ∧
    (seeSawConfigurationIndex observation.left observation.right).map
      BlueBookP93.priorityOfProduction = observation.output

def trigonalBipyramidIndexProduces
    (observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) : Prop :=
  observation.left.validFor 5 = true ∧ observation.right.validFor 5 = true ∧
    (trigonalBipyramidConfigurationIndex observation.left observation.right).map
      BlueBookP93.priorityOfProduction = observation.output

def squarePyramidIndexProduces
    (observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) : Prop :=
  observation.left.validFor 5 = true ∧ observation.right.validFor 5 = true ∧
    (squarePyramidConfigurationIndex observation.left observation.right).map
      BlueBookP93.priorityOfProduction = observation.output

def octahedronIndexProduces
    (observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) : Prop :=
  observation.left.validFor 6 = true ∧ observation.right.validFor 6 = true ∧
    (octahedronConfigurationIndex observation.left observation.right).map
      BlueBookP93.priorityOfProduction = observation.output

def bipyramidalIndexProduces
    (observation : TernaryAuthorityObservation PolyhedralPriorityNumber
      PolyhedralPriorityNumber (List PolyhedralPriorityNumber)
      (List (List BlueBookP93.PriorityNumber))) : Prop :=
  let coordination := observation.third.length + 2
  3 ≤ observation.third.length ∧
  observation.first.validFor coordination = true ∧
  observation.second.validFor coordination = true ∧
  (∀ priority ∈ observation.third, priority.validFor coordination = true) ∧
    (bipyramidalConfigurationIndex observation.first observation.second observation.third).map
      (List.map BlueBookP93.priorityOfProduction) = observation.output

def trigonalPyramidalRSProduces
    (observation : UnaryAuthorityObservation PolyhedralRotationSense RS) : Prop :=
  trigonalPyramidDescriptorOfRotation observation.input = observation.output

def caAuthorityProduces (allowedFrame : RedBookIR9.CAReferenceFrame → Prop)
    (observation : CAAuthorityObservation) : Prop :=
  allowedFrame observation.frame ∧
    BlueBookP93.chiralityOfProduction
      (PolyhedralChiralitySymbol.ofRotation observation.sense) = observation.symbol

def seeSawCAProduces
    (observation : UnaryAuthorityObservation PolyhedralRotationSense
      BlueBookP93.ChiralitySymbol) : Prop :=
  BlueBookP93.chiralityOfProduction
      (PolyhedralChiralitySymbol.ofRotation observation.input) = observation.output

def p93PolyhedralChiralityProduces
    (observation : P93PolyhedralChiralityAuthorityObservation) : Prop :=
  trigonalPyramidalRSProduces observation.trigonalPyramidal ∧
    caAuthorityProduces (fun _frame => True) observation.polyhedral

def priorityNumberingProduces (observation : PriorityNumberingAuthorityObservation) : Prop :=
  densePolyhedralPriorityNumberingOK? observation.count observation.compareAt
    observation.numbers = true

def primingConventionProduces (observation : PrimingAuthorityObservation) : Prop :=
  familyPolyhedralPrimeCountsOK? observation.donorCount observation.memberships
    observation.primeCounts = true

/-- Concrete production predicate for all four P-93.3.3.1 clauses represented by the composite
authority observation. -/
def p93PolyhedralPriorityNumberingProduces
    (observation : P93PriorityNumberingAuthorityObservation) : Prop :=
  observation.numbering.count = observation.priming.donorCount ∧
  priorityNumberingProduces observation.numbering ∧
  primingConventionProduces observation.priming ∧
  comparePolyhedralPriority observation.left observation.right = observation.priorityOutput ∧
  polyhedralTransMaximumDecision observation.leftOpposite observation.rightOpposite =
    observation.transMaximumOutput

/-! ## Exact spatial-family refinement -/

@[simp] theorem polyhedralPriority_validFor_conforms_P93
    (coordination : Nat) (priority : PolyhedralPriorityNumber) :
    priority.validFor coordination =
      (BlueBookP93.priorityOfProduction priority).validFor coordination := by
  cases priority with
  | mk number primes =>
      cases number <;>
        simp [PolyhedralPriorityNumber.validFor, BlueBookP93.PriorityNumber.validFor,
          BlueBookP93.priorityOfProduction]

theorem bipyramidalPriorityFrameValid_conforms_IR9
    (first second : PolyhedralPriorityNumber) (plane : List PolyhedralPriorityNumber) :
    (3 ≤ plane.length ∧
      first.validFor (plane.length + 2) = true ∧
      second.validFor (plane.length + 2) = true ∧
      (∀ priority ∈ plane, priority.validFor (plane.length + 2) = true)) ↔
      blueBookBipyramidalPriorityFrameValid first second plane := by
  simp [blueBookBipyramidalPriorityFrameValid, polyhedralPriority_validFor_conforms_P93]

theorem p93PolyhedralSymbol_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : UnaryAuthorityObservation PolyhedralGeometry String) :
    p93PolyhedralSymbolProduces observation ↔
      p93PolyhedralSymbolReference.Judges source observation := by
  unfold p93PolyhedralSymbolProduces p93PolyhedralSymbolReference
  rw [polyhedral_geometry_symbol_conforms_P93]

theorem ir9PolyhedralSymbol_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : UnaryAuthorityObservation PolyhedralGeometry String) :
    ir9PolyhedralSymbolProduces observation ↔
      ir9PolyhedralSymbolReference.Judges source observation := by
  unfold ir9PolyhedralSymbolProduces ir9PolyhedralSymbolReference unaryAuthorityReference
  rw [polyhedral_geometry_symbol_conforms_P93]

theorem tShapeIndex_production_eq_reference
    (source : AuthoritativeChemicalInput)
  (observation : UnaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) :
    tShapeIndexProduces observation ↔ tShapeIndexReference.Judges source observation := by
  unfold tShapeIndexProduces tShapeIndexReference unaryPolyhedralPriorityIndexReference
  rw [polyhedralPriority_validFor_conforms_P93, tShapeConfigurationIndex_conforms_P93]

theorem squarePlanarIndex_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : UnaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) :
    squarePlanarIndexProduces observation ↔
      squarePlanarIndexReference.Judges source observation := by
  unfold squarePlanarIndexProduces squarePlanarIndexReference
    unaryPolyhedralPriorityIndexReference
  rw [polyhedralPriority_validFor_conforms_P93, squarePlanarConfigurationIndex_conforms_IR9]

theorem squarePyramid4Index_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : UnaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) :
    squarePyramid4IndexProduces observation ↔
      squarePyramid4IndexReference.Judges source observation := by
  unfold squarePyramid4IndexProduces squarePyramid4IndexReference
    unaryPolyhedralPriorityIndexReference
  rw [polyhedralPriority_validFor_conforms_P93, squarePyramid4ConfigurationIndex_conforms_IR9]

theorem seeSawIndex_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) :
    seeSawIndexProduces observation ↔ seeSawIndexReference.Judges source observation := by
  unfold seeSawIndexProduces seeSawIndexReference binaryPolyhedralPriorityIndexReference
  rw [polyhedralPriority_validFor_conforms_P93, polyhedralPriority_validFor_conforms_P93,
    seeSawConfigurationIndex_conforms_P93]

theorem trigonalBipyramidIndex_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) :
    trigonalBipyramidIndexProduces observation ↔
      trigonalBipyramidIndexReference.Judges source observation := by
  unfold trigonalBipyramidIndexProduces trigonalBipyramidIndexReference
    binaryPolyhedralPriorityIndexReference
  rw [polyhedralPriority_validFor_conforms_P93, polyhedralPriority_validFor_conforms_P93,
    trigonalBipyramidConfigurationIndex_conforms_P93]

theorem squarePyramidIndex_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) :
    squarePyramidIndexProduces observation ↔
      squarePyramidIndexReference.Judges source observation := by
  unfold squarePyramidIndexProduces squarePyramidIndexReference
    binaryPolyhedralPriorityIndexReference
  rw [polyhedralPriority_validFor_conforms_P93, polyhedralPriority_validFor_conforms_P93,
    squarePyramidConfigurationIndex_conforms_P93]

theorem octahedronIndex_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber)) :
    octahedronIndexProduces observation ↔
      octahedronIndexReference.Judges source observation := by
  unfold octahedronIndexProduces octahedronIndexReference
    binaryPolyhedralPriorityIndexReference
  rw [polyhedralPriority_validFor_conforms_P93, polyhedralPriority_validFor_conforms_P93,
    octahedronConfigurationIndex_conforms_P93]

theorem bipyramidalIndex_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : TernaryAuthorityObservation PolyhedralPriorityNumber
      PolyhedralPriorityNumber (List PolyhedralPriorityNumber)
      (List (List BlueBookP93.PriorityNumber))) :
    bipyramidalIndexProduces observation ↔
      bipyramidalIndexReference.Judges source observation := by
  unfold bipyramidalIndexProduces bipyramidalIndexReference
  simp only [blueBookBipyramidalPriorityFrameValid,
    polyhedralPriority_validFor_conforms_P93]
  rw [bipyramidalConfigurationIndex_conforms_IR9]
  tauto

theorem trigonalPyramidalRS_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : UnaryAuthorityObservation PolyhedralRotationSense RS) :
    trigonalPyramidalRSProduces observation ↔
      trigonalPyramidalRSReference.Judges source observation := by
  unfold trigonalPyramidalRSProduces trigonalPyramidalRSReference unaryAuthorityReference
  rw [trigonalPyramidDescriptorOfRotation_conforms_IR9]

theorem caProductionSymbol_eq_reference (sense : PolyhedralRotationSense) :
    BlueBookP93.chiralityOfProduction (PolyhedralChiralitySymbol.ofRotation sense) =
      RedBookIR9.caSymbol (BlueBookP93.rotationOfProduction sense) := by
  simpa [RedBookIR9.caSymbol] using polyhedral_chirality_conforms_P93 sense

theorem caAuthority_production_eq_reference
    (allowedFrame : RedBookIR9.CAReferenceFrame → Prop)
    (source : AuthoritativeChemicalInput) (observation : CAAuthorityObservation) :
    caAuthorityProduces allowedFrame observation ↔
      (caAuthorityReference allowedFrame).Judges source observation := by
  unfold caAuthorityProduces caAuthorityReference
  rw [caProductionSymbol_eq_reference]

theorem p93PolyhedralChirality_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : P93PolyhedralChiralityAuthorityObservation) :
    p93PolyhedralChiralityProduces observation ↔
      p93PolyhedralChiralityReference.Judges source observation := by
  exact and_congr
    (trigonalPyramidalRS_production_eq_reference source observation.trigonalPyramidal)
    (by simpa [genericCAReference] using
      caAuthority_production_eq_reference (fun _frame => True) source observation.polyhedral)

theorem seeSawCA_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : UnaryAuthorityObservation PolyhedralRotationSense
      BlueBookP93.ChiralitySymbol) :
    seeSawCAProduces observation ↔ seeSawCAReference.Judges source observation := by
  unfold seeSawCAProduces seeSawCAReference unaryAuthorityReference
    RedBookIR9.seeSawCASymbol
  rw [caProductionSymbol_eq_reference]

theorem priorityNumbering_production_eq_reference
    (source : AuthoritativeChemicalInput) (observation : PriorityNumberingAuthorityObservation) :
    priorityNumberingProduces observation ↔
      priorityNumberingReference.Judges source observation := by
  exact densePolyhedralPriorityNumberingOK?_eq_true_iff_IR9
    observation.count observation.compareAt observation.numbers

theorem primingConvention_production_eq_reference
    (source : AuthoritativeChemicalInput) (observation : PrimingAuthorityObservation) :
    primingConventionProduces observation ↔
      primingConventionReference.Judges source observation := by
  exact familyPolyhedralPrimeCountsOK?_eq_true_iff_IR9
    observation.donorCount observation.memberships observation.primeCounts

theorem p93PolyhedralPriorityNumbering_production_eq_reference
    (source : AuthoritativeChemicalInput)
    (observation : P93PriorityNumberingAuthorityObservation) :
    p93PolyhedralPriorityNumberingProduces observation ↔
      p93PolyhedralPriorityNumberingReference.Judges source observation := by
  unfold p93PolyhedralPriorityNumberingProduces priorityNumberingProduces
    primingConventionProduces p93PolyhedralPriorityNumberingReference
  rw [densePolyhedralPriorityNumberingOK?_eq_true_iff_IR9,
    familyPolyhedralPrimeCountsOK?_eq_true_iff_IR9,
    polyhedral_priority_conforms_P93, polyhedral_transMaximum_conforms_P93]

/-- One spatial-descriptor theorem covers the eight P-93 and sixteen IR-9 reviewed rows. -/
structure PrimitiveP93IR9ReviewedProductionCorrect : Prop where
  p93Symbol : ∀ source observation,
    p93PolyhedralSymbolProduces observation ↔
      p93PolyhedralSymbolReference.Judges source observation
  ir9Symbol : ∀ source observation,
    ir9PolyhedralSymbolProduces observation ↔
      ir9PolyhedralSymbolReference.Judges source observation
  p93PriorityNumbering : ∀ source observation,
    p93PolyhedralPriorityNumberingProduces observation ↔
      p93PolyhedralPriorityNumberingReference.Judges source observation
  tShape : ∀ source observation,
    tShapeIndexProduces observation ↔ tShapeIndexReference.Judges source observation
  squarePlanar : ∀ source observation,
    squarePlanarIndexProduces observation ↔
      squarePlanarIndexReference.Judges source observation
  squarePyramid4 : ∀ source observation,
    squarePyramid4IndexProduces observation ↔
      squarePyramid4IndexReference.Judges source observation
  seeSaw : ∀ source observation,
    seeSawIndexProduces observation ↔ seeSawIndexReference.Judges source observation
  trigonalBipyramid : ∀ source observation,
    trigonalBipyramidIndexProduces observation ↔
      trigonalBipyramidIndexReference.Judges source observation
  squarePyramid : ∀ source observation,
    squarePyramidIndexProduces observation ↔
      squarePyramidIndexReference.Judges source observation
  octahedron : ∀ source observation,
    octahedronIndexProduces observation ↔ octahedronIndexReference.Judges source observation
  bipyramidal : ∀ source observation,
    bipyramidalIndexProduces observation ↔ bipyramidalIndexReference.Judges source observation
  chirality : ∀ source observation,
    p93PolyhedralChiralityProduces observation ↔
      p93PolyhedralChiralityReference.Judges source observation
  trigonalPyramidalRS : ∀ source observation,
    trigonalPyramidalRSProduces observation ↔
      trigonalPyramidalRSReference.Judges source observation
  ca : ∀ allowedFrame source observation,
    caAuthorityProduces allowedFrame observation ↔
      (caAuthorityReference allowedFrame).Judges source observation
  seeSawCA : ∀ source observation,
    seeSawCAProduces observation ↔ seeSawCAReference.Judges source observation
  priorityNumbering : ∀ source observation,
    priorityNumberingProduces observation ↔
      priorityNumberingReference.Judges source observation
  priming : ∀ source observation,
    primingConventionProduces observation ↔
      primingConventionReference.Judges source observation

theorem primitiveP93IR9ReviewedProduction_correct :
    PrimitiveP93IR9ReviewedProductionCorrect where
  p93Symbol := p93PolyhedralSymbol_production_eq_reference
  ir9Symbol := ir9PolyhedralSymbol_production_eq_reference
  p93PriorityNumbering := p93PolyhedralPriorityNumbering_production_eq_reference
  tShape := tShapeIndex_production_eq_reference
  squarePlanar := squarePlanarIndex_production_eq_reference
  squarePyramid4 := squarePyramid4Index_production_eq_reference
  seeSaw := seeSawIndex_production_eq_reference
  trigonalBipyramid := trigonalBipyramidIndex_production_eq_reference
  squarePyramid := squarePyramidIndex_production_eq_reference
  octahedron := octahedronIndex_production_eq_reference
  bipyramidal := bipyramidalIndex_production_eq_reference
  chirality := p93PolyhedralChirality_production_eq_reference
  trigonalPyramidalRS := trigonalPyramidalRS_production_eq_reference
  ca := caAuthority_production_eq_reference
  seeSawCA := seeSawCA_production_eq_reference
  priorityNumbering := priorityNumbering_production_eq_reference
  priming := primingConvention_production_eq_reference

/-! ## Exhaustive row-indexed production program -/

def Primitive35AuthorityRow.ProductionJudges :
    (row : Primitive35AuthorityRow) → AuthoritativeChemicalInput →
      row.reference.Observation → Prop
  | .p92Rule1aAtomicNumber, _source, observation => p92Rule1aAtomicNumberProduces observation
  | .p92Rule1bDuplicateProximity, _source, observation =>
      p92Rule1bDuplicateProximityProduces observation
  | .p92Rule2IsotopeMass, _source, observation => p92Rule2IsotopeMassProduces observation
  | .p92Rule3Geometry, _source, observation => p92Rule3GeometryProduces observation
  | .p92Rule3SeqCisTrans, _source, observation => p92Rule3SeqCisTransProduces observation
  | .p92Rule3Priority, _source, observation => p92Rule3PriorityProduces observation
  | .p92Rule4aUnitKind, _source, observation => p92Rule4aUnitKindProduces observation
  | .p92Rule45 family, source, observation =>
      Rule45CanonicalFamilyProductionJudged family source observation
  | .p92Rule4cPseudoasymmetry, _source, observation => p92Rule4cPseudoasymmetryProduces observation
  | .p93PolyhedralSymbols, _source, observation => p93PolyhedralSymbolProduces observation
  | .p93PolyhedralPriorityNumbering, _source, observation =>
      p93PolyhedralPriorityNumberingProduces observation
  | .p93TShape, _source, observation => tShapeIndexProduces observation
  | .p93SeeSaw, _source, observation => seeSawIndexProduces observation
  | .p93TrigonalBipyramid, _source, observation => trigonalBipyramidIndexProduces observation
  | .p93SquarePyramid, _source, observation => squarePyramidIndexProduces observation
  | .p93Octahedron, _source, observation => octahedronIndexProduces observation
  | .p93PolyhedralChirality, _source, observation => p93PolyhedralChiralityProduces observation
  | .ir9PolyhedralSymbols, _source, observation => ir9PolyhedralSymbolProduces observation
  | .ir9SquarePlanar, _source, observation => squarePlanarIndexProduces observation
  | .ir9Octahedral, _source, observation => octahedronIndexProduces observation
  | .ir9SquarePyramidal, _source, observation => squarePyramid4IndexProduces observation
  | .ir9Bipyramidal, _source, observation => bipyramidalIndexProduces observation
  | .ir9TShape, _source, observation => tShapeIndexProduces observation
  | .ir9SeeSaw, _source, observation => seeSawIndexProduces observation
  | .ir9RSTrigonalPyramidal, _source, observation => trigonalPyramidalRSProduces observation
  | .ir9CAPolyhedral, _source, observation => caAuthorityProduces (fun _frame => True) observation
  | .ir9CATrigonalBipyramidal, _source, observation =>
      caAuthorityProduces (fun frame => frame = .trigonalBipyramidSeniorAxialNear) observation
  | .ir9CASquarePyramidal, _source, observation =>
      caAuthorityProduces (fun frame =>
        frame = .squarePyramid5AxialNear ∨ frame = .squarePyramid4CenterNear) observation
  | .ir9CASeeSaw, _source, observation => seeSawCAProduces observation
  | .ir9CAOctahedral, _source, observation =>
      caAuthorityProduces (fun frame =>
        frame = .octahedronPriorityOneNearAndLowestTransFar) observation
  | .ir9CAOtherBipyramidal, _source, observation =>
      caAuthorityProduces (fun frame =>
        ∃ kind, frame = .otherBipyramidSeniorAxialNear kind) observation
  | .ir9PriorityNumbers, _source, observation => priorityNumberingProduces observation
  | .ir9PrimingConvention, _source, observation => primingConventionProduces observation

theorem Primitive35AuthorityRow.production_eq_reference
    (row : Primitive35AuthorityRow) (source : AuthoritativeChemicalInput)
    (observation : row.reference.Observation) :
    row.ProductionJudges source observation ↔
      row.reference.Judges source observation := by
  cases row with
  | p92Rule1aAtomicNumber =>
      simpa [ProductionJudges] using
        p92Rule1aAtomicNumber_production_eq_reference source observation
  | p92Rule1bDuplicateProximity =>
      simpa [ProductionJudges] using
        p92Rule1bDuplicateProximity_production_eq_reference source observation
  | p92Rule2IsotopeMass =>
      simpa [ProductionJudges] using
        p92Rule2IsotopeMass_production_eq_reference source observation
  | p92Rule3Geometry =>
      simpa [ProductionJudges] using
        p92Rule3Geometry_production_eq_reference source observation
  | p92Rule3SeqCisTrans =>
      simpa [ProductionJudges] using
        p92Rule3SeqCisTrans_production_eq_reference source observation
  | p92Rule3Priority =>
      simpa [ProductionJudges] using
        p92Rule3Priority_production_eq_reference source observation
  | p92Rule4aUnitKind =>
      simpa [ProductionJudges] using
        p92Rule4aUnitKind_production_eq_reference source observation
  | p92Rule45 family =>
      simpa [ProductionJudges, Primitive35AuthorityRow.reference] using
        rule45CanonicalFamilyProduction_iff_canonicalComplete family source observation
  | p92Rule4cPseudoasymmetry =>
      simpa [ProductionJudges] using
        p92Rule4cPseudoasymmetry_production_eq_reference source observation
  | p93PolyhedralSymbols =>
      simpa [ProductionJudges] using
        p93PolyhedralSymbol_production_eq_reference source observation
  | ir9PolyhedralSymbols =>
      simpa [ProductionJudges] using
        ir9PolyhedralSymbol_production_eq_reference source observation
  | p93PolyhedralPriorityNumbering =>
      simpa [ProductionJudges] using
        p93PolyhedralPriorityNumbering_production_eq_reference source observation
  | p93TShape | ir9TShape =>
      simpa [ProductionJudges] using tShapeIndex_production_eq_reference source observation
  | p93SeeSaw | ir9SeeSaw =>
      simpa [ProductionJudges] using seeSawIndex_production_eq_reference source observation
  | p93TrigonalBipyramid =>
      simpa [ProductionJudges] using
        trigonalBipyramidIndex_production_eq_reference source observation
  | p93SquarePyramid =>
      simpa [ProductionJudges] using squarePyramidIndex_production_eq_reference source observation
  | p93Octahedron | ir9Octahedral =>
      simpa [ProductionJudges] using octahedronIndex_production_eq_reference source observation
  | p93PolyhedralChirality =>
      simpa [ProductionJudges] using
        p93PolyhedralChirality_production_eq_reference source observation
  | ir9SquarePlanar =>
      simpa [ProductionJudges] using squarePlanarIndex_production_eq_reference source observation
  | ir9SquarePyramidal =>
      simpa [ProductionJudges] using
        squarePyramid4Index_production_eq_reference source observation
  | ir9Bipyramidal =>
      simpa [ProductionJudges] using bipyramidalIndex_production_eq_reference source observation
  | ir9RSTrigonalPyramidal =>
      simpa [ProductionJudges] using
        trigonalPyramidalRS_production_eq_reference source observation
  | ir9CAPolyhedral =>
      simpa [ProductionJudges, genericCAReference] using
        caAuthority_production_eq_reference (fun _frame => True) source observation
  | ir9CATrigonalBipyramidal =>
      simpa [ProductionJudges, trigonalBipyramidalCAReference] using
        caAuthority_production_eq_reference
          (fun frame => frame = RedBookIR9.CAReferenceFrame.trigonalBipyramidSeniorAxialNear)
          source observation
  | ir9CASquarePyramidal =>
      simpa [ProductionJudges, squarePyramidalCAReference] using
        caAuthority_production_eq_reference
          (fun frame => frame = RedBookIR9.CAReferenceFrame.squarePyramid5AxialNear ∨
            frame = RedBookIR9.CAReferenceFrame.squarePyramid4CenterNear)
          source observation
  | ir9CASeeSaw =>
      simpa [ProductionJudges] using seeSawCA_production_eq_reference source observation
  | ir9CAOctahedral =>
      simpa [ProductionJudges, octahedralCAReference] using
        caAuthority_production_eq_reference
          (fun frame =>
            frame = RedBookIR9.CAReferenceFrame.octahedronPriorityOneNearAndLowestTransFar)
          source observation
  | ir9CAOtherBipyramidal =>
      simpa [ProductionJudges, otherBipyramidalCAReference] using
        caAuthority_production_eq_reference
          (fun frame => ∃ kind, frame = RedBookIR9.CAReferenceFrame.otherBipyramidSeniorAxialNear kind)
          source observation
  | ir9PriorityNumbers =>
      simpa [ProductionJudges] using
        priorityNumbering_production_eq_reference source observation
  | ir9PrimingConvention =>
      simpa [ProductionJudges] using
        primingConvention_production_eq_reference source observation

theorem Primitive35AuthorityRow.reference_applicable_of_judged
    (row : Primitive35AuthorityRow) (source : AuthoritativeChemicalInput)
    (observation : row.reference.Observation)
    (judged : row.reference.Judges source observation) :
    row.reference.Applicable source := by
  cases row with
  | p92Rule45 _ => exact ⟨observation, judged⟩
  | _ => trivial

/-! ## Dependent reference transport used by the global production adapter -/

namespace ProvisionReference

theorem applicable_congr {left right : ProvisionReference} (equal : left = right)
    (source : AuthoritativeChemicalInput) :
    left.Applicable source ↔ right.Applicable source := by
  cases equal
  rfl

theorem judges_cast_congr {left right : ProvisionReference} (equal : left = right)
    (source : AuthoritativeChemicalInput) (observation : left.Observation) :
    left.Judges source observation ↔
      right.Judges source
        (cast (congrArg ProvisionReference.Observation equal) observation) := by
  cases equal
  rfl

end ProvisionReference

namespace ProvisionCorrect

/-- Transport a local family production/reference theorem into the provision corpus once.  The
family supplies only its exact production relation, judgment equivalence, and the semantic fact
that a judged observation witnesses applicability; all dependent reference casts are discharged
generically here. -/
theorem of_transported_judgment
    {corpus : FrozenProvisionCorpus}
    {interpreter : ProvisionInterpreter corpus}
    {provision : IUPACNormativeProvision}
    {reference : ProvisionReference}
    (production : AuthoritativeChemicalInput → reference.Observation → Prop)
    (referenceEq : corpus.reference provision = reference)
    (produces_exact : ∀ (source : AuthoritativeChemicalInput)
      (observation : (corpus.reference provision).Observation),
        interpreter.Produces provision source observation ↔
          production source
            (cast (congrArg ProvisionReference.Observation referenceEq) observation))
    (production_eq_reference : ∀ (source : AuthoritativeChemicalInput)
      (observation : reference.Observation),
        production source observation ↔ reference.Judges source observation)
    (reference_applicable_of_judged : ∀ (source : AuthoritativeChemicalInput)
      (observation : reference.Observation),
        reference.Judges source observation → reference.Applicable source) :
    ProvisionCorrect corpus interpreter provision := by
  intro source _admitted observation
  let localObservation : reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have judgment := production_eq_reference source localObservation
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport := ProvisionReference.judges_cast_congr
    referenceEq source observation
  rw [produces_exact source observation]
  change production source localObservation ↔
    (corpus.reference provision).Applicable source ∧
      (corpus.reference provision).Judges source observation
  constructor
  · intro produced
    have judged := judgment.mp produced
    exact ⟨applicableTransport.mpr
      (reference_applicable_of_judged source localObservation judged),
        judgmentTransport.mpr judged⟩
  · rintro ⟨_applicable, judged⟩
    exact judgment.mpr (judgmentTransport.mp judged)

end ProvisionCorrect

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule1aAtomicNumber_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule1bDuplicateProximity_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule2IsotopeMass_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule3Priority_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule4aUnitKind_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule4cPseudoasymmetry_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93PolyhedralSymbol_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ir9PolyhedralSymbol_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93PolyhedralPriorityNumbering_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93PolyhedralChirality_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.polyhedralPriority_validFor_conforms_P93
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.bipyramidalPriorityFrameValid_conforms_IR9
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.bipyramidalIndex_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.trigonalPyramidalRS_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.caAuthority_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.priorityNumbering_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primingConvention_production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitiveP93IR9ReviewedProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Primitive35AuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Primitive35AuthorityRow.reference_applicable_of_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionReference.applicable_congr
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionReference.judges_cast_congr
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCorrect.of_transported_judgment
