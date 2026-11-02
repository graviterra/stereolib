import TetraStereo.OneCenter.IUPACPrimitive35ReviewedSemantics
import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyNonvacuitySeed

set_option autoImplicit false

/-!
# Proof-bearing compiler for the reviewed primitive 35

This module proves genuine nonvacuity for every reviewed primitive row.  The 32 noncanonical rows
retain concrete local witnesses; the three canonical Rules-4b/5 rows are projections of the one
kernel-checked molecular trace in `IUPACRule45CanonicalFamilyNonvacuitySeed`.  Production
correctness is supplied only by the global compiler adapter, not by a parallel local corpus.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## A concrete admitted witness for the 32 noncanonical rows -/

def primitive35WitnessInput : AuthoritativeChemicalInput where
  molecule := { atoms := [], interactions := [] }

@[simp] theorem primitive35WitnessInput_structurallyWellFormed :
    primitive35WitnessInput.StructurallyWellFormed := by
  simp [primitive35WitnessInput, AuthoritativeChemicalInput.StructurallyWellFormed,
    SemanticMolecule.StructurallyWellFormed,
    AuthoritativeChemicalInput.SpatialIndicesWellFormed,
    AuthoritativeChemicalInput.DiagramIndicesWellFormed]

/-- Lift a row witnessed on the fixed inert source into the source-owning witness shape used by
the compiler.  The canonical Rules-4b/5 family is routed through the molecular boundary instead. -/
theorem primitive35WitnessInput_lift_nonvacuous
    {reference : ProvisionReference}
    (nonvacuous : ∃ observation,
      reference.Applicable primitive35WitnessInput ∧
        reference.Judges primitive35WitnessInput observation) :
    ∃ source, ∃ observation : reference.Observation,
      source.StructurallyWellFormed ∧ reference.Applicable source ∧
        reference.Judges source observation := by
  obtain ⟨observation, applicable, judged⟩ := nonvacuous
  exact ⟨primitive35WitnessInput, observation,
    primitive35WitnessInput_structurallyWellFormed, applicable, judged⟩

/-! ## Generic witnesses for the independent operation graphs -/

theorem unaryAuthorityReference_nonvacuous
    {Input Output : Type} (reference : Input → Output) (input : Input)
    (source : AuthoritativeChemicalInput) :
    ∃ observation,
      (unaryAuthorityReference Input Output reference).Applicable source ∧
      (unaryAuthorityReference Input Output reference).Judges source observation := by
  exact ⟨{ input := input, output := reference input }, trivial, rfl⟩

theorem binaryAuthorityReference_nonvacuous
    {Input Output : Type} (reference : Input → Input → Output)
    (left right : Input) (source : AuthoritativeChemicalInput) :
    ∃ observation,
      (binaryAuthorityReference Input Output reference).Applicable source ∧
      (binaryAuthorityReference Input Output reference).Judges source observation := by
  exact ⟨{ left := left, right := right, output := reference left right }, trivial, rfl⟩

theorem binaryAuthorityRelation_nonvacuous
    {Input Output : Type} (reference : Input → Input → Output → Prop)
    (left right : Input) (output : Output) (judged : reference left right output)
    (source : AuthoritativeChemicalInput) :
    ∃ observation,
      (binaryAuthorityRelation Input Output reference).Applicable source ∧
      (binaryAuthorityRelation Input Output reference).Judges source observation := by
  exact ⟨{ left := left, right := right, output := output }, trivial, judged⟩

theorem ternaryAuthorityReference_nonvacuous
    {First Second Third Output : Type}
    (reference : First → Second → Third → Output)
    (first : First) (second : Second) (third : Third)
    (source : AuthoritativeChemicalInput) :
    ∃ observation,
      (ternaryAuthorityReference First Second Third Output reference).Applicable source ∧
      (ternaryAuthorityReference First Second Third Output reference).Judges source observation := by
  let observation : TernaryAuthorityObservation First Second Third Output :=
    { first := first
      second := second
      third := third
      output := reference first second third }
  exact ⟨observation, trivial, rfl⟩

theorem unaryPolyhedralPriorityIndexReference_nonvacuous
    (coordination : Nat)
    (reference : BlueBookP93.PriorityNumber → List BlueBookP93.PriorityNumber)
    (input : PolyhedralPriorityNumber)
    (valid : (BlueBookP93.priorityOfProduction input).validFor coordination = true)
    (source : AuthoritativeChemicalInput) :
    ∃ observation,
      (unaryPolyhedralPriorityIndexReference coordination reference).Applicable source ∧
      (unaryPolyhedralPriorityIndexReference coordination reference).Judges source observation :=
  ⟨{ input := input, output := reference (BlueBookP93.priorityOfProduction input) },
    trivial, valid, rfl⟩

theorem binaryPolyhedralPriorityIndexReference_nonvacuous
    (coordination : Nat)
    (reference : BlueBookP93.PriorityNumber → BlueBookP93.PriorityNumber →
      List BlueBookP93.PriorityNumber)
    (left right : PolyhedralPriorityNumber)
    (leftValid : (BlueBookP93.priorityOfProduction left).validFor coordination = true)
    (rightValid : (BlueBookP93.priorityOfProduction right).validFor coordination = true)
    (source : AuthoritativeChemicalInput) :
    ∃ observation,
      (binaryPolyhedralPriorityIndexReference coordination reference).Applicable source ∧
      (binaryPolyhedralPriorityIndexReference coordination reference).Judges source observation := by
  let observation : BinaryAuthorityObservation PolyhedralPriorityNumber
      (List BlueBookP93.PriorityNumber) :=
    { left := left
      right := right
      output := reference (BlueBookP93.priorityOfProduction left)
        (BlueBookP93.priorityOfProduction right) }
  exact ⟨observation, trivial, leftValid, rightValid, rfl⟩

/-! ## Positive finite witnesses for the P-93/IR-9 numbering clauses -/

def primitive35TwoDonorCompareAt (left right : Nat) : Option Ordering :=
  if left = 0 ∧ right = 1 then some .gt
  else if left = 1 ∧ right = 0 then some .lt
  else some .eq

def primitive35PriorityNumberingWitness : PriorityNumberingAuthorityObservation where
  count := 2
  compareAt := primitive35TwoDonorCompareAt
  numbers := [1, 2]

theorem primitive35PriorityNumberingWitness_valid :
    RedBookIR9.FinitePriorityNumbering primitive35PriorityNumberingWitness.count
      primitive35PriorityNumberingWitness.compareAt
      primitive35PriorityNumberingWitness.numbers := by
  refine
    { length_eq := rfl
      positive := ?_
      comparison := ?_
      highest_number_one := ?_
      no_gaps := ?_ }
  · intro position bound
    change position < 2 at bound
    have cases : position = 0 ∨ position = 1 := by omega
    rcases cases with rfl | rfl <;>
      norm_num [primitive35PriorityNumberingWitness]
  · intro left right leftBound rightBound
    change left < 2 at leftBound
    change right < 2 at rightBound
    have leftCases : left = 0 ∨ left = 1 := by omega
    have rightCases : right = 0 ∨ right = 1 := by omega
    rcases leftCases with rfl | rfl <;> rcases rightCases with rfl | rfl <;>
      norm_num [primitive35PriorityNumberingWitness, primitive35TwoDonorCompareAt,
        RedBookIR9.PriorityDecisionAgrees]
  · intro position bound highest
    change position < 2 at bound
    have cases : position = 0 ∨ position = 1 := by omega
    rcases cases with rfl | rfl
    · rfl
    · have contradicted := highest 0 (by decide)
      simp [primitive35PriorityNumberingWitness, primitive35TwoDonorCompareAt] at contradicted
  · intro position bound number positive smaller
    change position < 2 at bound
    have cases : position = 0 ∨ position = 1 := by omega
    rcases cases with rfl | rfl
    · change number < 1 at smaller
      omega
    · change number < 2 at smaller
      have numberOne : number = 1 := by omega
      subst number
      exact ⟨0, by decide, rfl⟩

def primitive35PrimingWitness : PrimingAuthorityObservation where
  donorCount := 2
  memberships :=
    [ some { family := 0, group := 0 }
    , some { family := 0, group := 1 }
    ]
  primeCounts := [0, 1]

theorem primitive35PrimingWitness_valid :
    RedBookIR9.FinitePrimingAssignment primitive35PrimingWitness.donorCount
      primitive35PrimingWitness.memberships primitive35PrimingWitness.primeCounts := by
  rfl

/-! ## Every reviewed row has a genuine judged observation -/

theorem Primitive35AuthorityRow.reference_nonvacuous
    (row : Primitive35AuthorityRow) :
    ∃ source, ∃ observation : row.reference.Observation,
      source.StructurallyWellFormed ∧ row.reference.Applicable source ∧
        row.reference.Judges source observation := by
  cases row with
  | p92Rule1aAtomicNumber =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      obtain ⟨outcome, judged⟩ :=
        DeclarativeCIP.ExactAtomicNumber.Outcome.total
          DeclarativeCIP.ExactAtomicNumber.zero DeclarativeCIP.ExactAtomicNumber.zero
      exact binaryAuthorityRelation_nonvacuous
        DeclarativeCIP.ExactAtomicNumber.Outcome
        DeclarativeCIP.ExactAtomicNumber.zero DeclarativeCIP.ExactAtomicNumber.zero
        outcome judged primitive35WitnessInput
  | p92Rule1bDuplicateProximity =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryAuthorityReference_nonvacuous BlueBookP92.rule1bDecision 0 0
        primitive35WitnessInput
  | p92Rule2IsotopeMass =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryAuthorityReference_nonvacuous BlueBookP92.rule2Decision 1 1
        primitive35WitnessInput
  | p92Rule3Geometry =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact unaryAuthorityReference_nonvacuous BlueBookP92.rule3ClassOfOfficial
        OfficialRule3Geometry.seqcis primitive35WitnessInput
  | p92Rule3SeqCisTrans =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact unaryAuthorityReference_nonvacuous
        (fun geometry => BlueBookP92.rule3Priority
          (BlueBookP92.rule3ClassOfOfficial geometry))
        OfficialRule3Geometry.seqcis primitive35WitnessInput
  | p92Rule3Priority =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryAuthorityReference_nonvacuous
        (fun left right => BlueBookP92.rule3Decision
          (BlueBookP92.rule3ClassOfOfficial left)
          (BlueBookP92.rule3ClassOfOfficial right))
        OfficialRule3Geometry.seqcis OfficialRule3Geometry.seqtrans
        primitive35WitnessInput
  | p92Rule4aUnitKind =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryAuthorityReference_nonvacuous
        (fun left right => BlueBookP92.rule4aDecision
          (BlueBookP92.rule4aClassOfOfficial left)
          (BlueBookP92.rule4aClassOfOfficial right))
        OfficialStereogenicUnitKind.chiral OfficialStereogenicUnitKind.pseudoasymmetric
        primitive35WitnessInput
  | p92Rule45 family =>
      exact Rule45CanonicalFamilyNonvacuity.familyNonvacuityWitnesses.nonvacuous family
  | p92Rule4cPseudoasymmetry =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryAuthorityReference_nonvacuous
        (fun left right => BlueBookP92.rule4cDecision?
          (BlueBookP92.rule4cSymbolOfOfficial left)
          (BlueBookP92.rule4cSymbolOfOfficial right))
        OfficialPseudoasymmetricDescriptor.r OfficialPseudoasymmetricDescriptor.s
        primitive35WitnessInput
  | p93PolyhedralSymbols =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let observation : UnaryAuthorityObservation PolyhedralGeometry String :=
        { input := PolyhedralGeometry.tetrahedron
          output := (BlueBookP93.geometryOfProduction PolyhedralGeometry.tetrahedron).symbol }
      exact ⟨observation, trivial,
        by simp [Primitive35AuthorityRow.reference, observation,
          p93PolyhedralSymbolReference, p93CommonPolyhedralGeometries]⟩
  | ir9PolyhedralSymbols =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact unaryAuthorityReference_nonvacuous
        (fun geometry => (BlueBookP93.geometryOfProduction geometry).symbol)
        PolyhedralGeometry.tetrahedron primitive35WitnessInput
  | p93PolyhedralPriorityNumbering =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let numbering := primitive35PriorityNumberingWitness
      let priming := primitive35PrimingWitness
      let left : PolyhedralPriorityNumber := { number := 1, primes := 0 }
      let right : PolyhedralPriorityNumber := { number := 1, primes := 1 }
      let observation : P93PriorityNumberingAuthorityObservation :=
        { numbering := numbering
          priming := priming
          left := left
          right := right
          priorityOutput := BlueBookP93.priorityDecision
            (BlueBookP93.priorityOfProduction left) (BlueBookP93.priorityOfProduction right)
          leftOpposite := left
          rightOpposite := right
          transMaximumOutput := BlueBookP93.transMaximumDecision
            (BlueBookP93.priorityOfProduction left) (BlueBookP93.priorityOfProduction right) }
      refine ⟨observation, trivial, ?_⟩
      change numbering.count = priming.donorCount ∧
        RedBookIR9.FinitePriorityNumbering numbering.count numbering.compareAt numbering.numbers ∧
        RedBookIR9.FinitePrimingAssignment priming.donorCount priming.memberships
          priming.primeCounts ∧ _ ∧ _
      exact ⟨rfl, primitive35PriorityNumberingWitness_valid,
        primitive35PrimingWitness_valid, rfl, rfl⟩
  | p93TShape | ir9TShape =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact unaryPolyhedralPriorityIndexReference_nonvacuous 3 BlueBookP93.tShapeIndex
        { number := 1 } rfl primitive35WitnessInput
  | p93SeeSaw | ir9SeeSaw =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryPolyhedralPriorityIndexReference_nonvacuous 4 BlueBookP93.seeSawIndex
        { number := 1 } { number := 2 } rfl rfl primitive35WitnessInput
  | p93TrigonalBipyramid =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryPolyhedralPriorityIndexReference_nonvacuous 5
        BlueBookP93.trigonalBipyramidIndex
        { number := 1 } { number := 2 } rfl rfl primitive35WitnessInput
  | p93SquarePyramid =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryPolyhedralPriorityIndexReference_nonvacuous 5 BlueBookP93.squarePyramidIndex
        { number := 1 } { number := 2 } rfl rfl primitive35WitnessInput
  | p93Octahedron | ir9Octahedral =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact binaryPolyhedralPriorityIndexReference_nonvacuous 6 BlueBookP93.octahedronIndex
        { number := 1 } { number := 2 } rfl rfl primitive35WitnessInput
  | p93PolyhedralChirality =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let trigonalPyramidal : UnaryAuthorityObservation PolyhedralRotationSense RS :=
        { input := .clockwise
          output := RedBookIR9.trigonalPyramidalRS
            { sequenceFromPriorityOne := BlueBookP93.rotationOfProduction .clockwise
              viewedFromCenterTowardLeastPreferred := True
              phantomSite := .lonePairSite
              phantomHasLowestPriority := True } }
      let polyhedral : CAAuthorityObservation :=
        { frame := .trigonalBipyramidSeniorAxialNear
          sense := .clockwise
          symbol := RedBookIR9.caSymbol (BlueBookP93.rotationOfProduction .clockwise) }
      exact ⟨{ trigonalPyramidal := trigonalPyramidal, polyhedral := polyhedral },
        trivial, rfl, trivial, rfl⟩
  | ir9SquarePlanar =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact unaryPolyhedralPriorityIndexReference_nonvacuous 4 BlueBookP93.squarePlanarIndex
        { number := 1 } rfl primitive35WitnessInput
  | ir9SquarePyramidal =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact unaryPolyhedralPriorityIndexReference_nonvacuous 4 BlueBookP93.squarePyramid4Index
        { number := 1 } rfl primitive35WitnessInput
  | ir9Bipyramidal =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let first : PolyhedralPriorityNumber := { number := 1 }
      let second : PolyhedralPriorityNumber := { number := 2 }
      let plane : List PolyhedralPriorityNumber :=
        [{ number := 3 }, { number := 4 }, { number := 5 }]
      let observation : TernaryAuthorityObservation PolyhedralPriorityNumber
          PolyhedralPriorityNumber (List PolyhedralPriorityNumber)
          (List (List BlueBookP93.PriorityNumber)) :=
        { first := first
          second := second
          third := plane
          output := BlueBookP93.bipyramidalIndex (BlueBookP93.priorityOfProduction first)
            (BlueBookP93.priorityOfProduction second)
            (plane.map BlueBookP93.priorityOfProduction) }
      refine ⟨observation, trivial, ?_⟩
      simp [Primitive35AuthorityRow.reference, observation, first, second, plane,
        bipyramidalIndexReference, blueBookBipyramidalPriorityFrameValid,
        BlueBookP93.PriorityNumber.validFor, BlueBookP93.priorityOfProduction]
  | ir9RSTrigonalPyramidal =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact unaryAuthorityReference_nonvacuous
        (fun sense => RedBookIR9.trigonalPyramidalRS
          { sequenceFromPriorityOne := BlueBookP93.rotationOfProduction sense
            viewedFromCenterTowardLeastPreferred := True
            phantomSite := .lonePairSite
            phantomHasLowestPriority := True })
        PolyhedralRotationSense.clockwise primitive35WitnessInput
  | ir9CAPolyhedral =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let observation : CAAuthorityObservation :=
        { frame := .trigonalBipyramidSeniorAxialNear
          sense := .clockwise
          symbol := RedBookIR9.caSymbol (BlueBookP93.rotationOfProduction .clockwise) }
      exact ⟨observation, trivial, trivial, rfl⟩
  | ir9CATrigonalBipyramidal =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let observation : CAAuthorityObservation :=
        { frame := .trigonalBipyramidSeniorAxialNear
          sense := .clockwise
          symbol := RedBookIR9.caSymbol (BlueBookP93.rotationOfProduction .clockwise) }
      exact ⟨observation, trivial, rfl, rfl⟩
  | ir9CASquarePyramidal =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let observation : CAAuthorityObservation :=
        { frame := .squarePyramid5AxialNear
          sense := .clockwise
          symbol := RedBookIR9.caSymbol (BlueBookP93.rotationOfProduction .clockwise) }
      exact ⟨observation, trivial, Or.inl rfl, rfl⟩
  | ir9CASeeSaw =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact unaryAuthorityReference_nonvacuous
        (fun sense => RedBookIR9.seeSawCASymbol
          { largestAnglePair := ({ number := 1 }, { number := 2 })
            viewedFromSeniorMemberOfLargestAnglePair := True
            remainingPairThroughSmallerAngle := True
            senseFromSeniorToJuniorRemainingLigand := BlueBookP93.rotationOfProduction sense })
        PolyhedralRotationSense.clockwise primitive35WitnessInput
  | ir9CAOctahedral =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let observation : CAAuthorityObservation :=
        { frame := .octahedronPriorityOneNearAndLowestTransFar
          sense := .clockwise
          symbol := RedBookIR9.caSymbol (BlueBookP93.rotationOfProduction .clockwise) }
      exact ⟨observation, trivial, rfl, rfl⟩
  | ir9CAOtherBipyramidal =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      let observation : CAAuthorityObservation :=
        { frame := .otherBipyramidSeniorAxialNear .trigonal5
          sense := .clockwise
          symbol := RedBookIR9.caSymbol (BlueBookP93.rotationOfProduction .clockwise) }
      exact ⟨observation, trivial,
        ⟨RedBookIR9.BipyramidKind.trigonal5, rfl⟩, rfl⟩
  | ir9PriorityNumbers =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact ⟨primitive35PriorityNumberingWitness, trivial,
        primitive35PriorityNumberingWitness_valid⟩
  | ir9PrimingConvention =>
      refine primitive35WitnessInput_lift_nonvacuous ?_
      exact ⟨primitive35PrimingWitness, trivial, primitive35PrimingWitness_valid⟩

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35PriorityNumberingWitness_valid
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35PrimingWitness_valid
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Primitive35AuthorityRow.reference_nonvacuous
