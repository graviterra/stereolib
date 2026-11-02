import TetraStereo.OneCenter.IUPACNext54P93ResidualReviewedSemantics
import TetraStereo.OneCenter.IUPACPrimitive35Interpreter

set_option autoImplicit false

/-!
# Concrete production adapter for the three residual P-93 rows

This module implements the residual P-93 outputs with the executable polyhedral surface from
`PolyhedralConfiguration`.  Source predicates remain independent reviewed input invariants;
production computes geometry recognition, configuration indices, chirality-stage selection, the
trigonal-pyramidal phantom, and the empty trigonal-pyramidal index.  No reviewed `Judges` relation
is used as a production definition.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## Production-side geometry recognition -/

/-- Total conversion from the independent authority geometry vocabulary to the executable
polyhedral geometry vocabulary. -/
def p93ResidualGeometryToProduction : BlueBookP93.Geometry → PolyhedralGeometry
  | .linear => .linear
  | .angular => .angular
  | .trigonalPlanar => .trigonalPlanar
  | .trigonalPyramid => .trigonalPyramid
  | .tShape => .tShape
  | .tetrahedron => .tetrahedron
  | .squarePlanar => .squarePlanar
  | .squarePyramid4 => .squarePyramid4
  | .seeSaw => .seeSaw
  | .trigonalBipyramid => .trigonalBipyramid
  | .squarePyramid => .squarePyramid
  | .octahedron => .octahedron
  | .trigonalPrism => .trigonalPrism
  | .pentagonalBipyramid => .pentagonalBipyramid
  | .faceMonocappedOctahedron => .faceMonocappedOctahedron
  | .squareFaceMonocappedTrigonalPrism => .squareFaceMonocappedTrigonalPrism
  | .cube => .cube
  | .squareAntiprism => .squareAntiprism
  | .dodecahedron => .dodecahedron
  | .hexagonalBipyramid => .hexagonalBipyramid
  | .transBicappedOctahedron => .transBicappedOctahedron
  | .triangularFaceBicappedTrigonalPrism => .triangularFaceBicappedTrigonalPrism
  | .squareFaceBicappedTrigonalPrism => .squareFaceBicappedTrigonalPrism
  | .squareFaceTricappedTrigonalPrism => .squareFaceTricappedTrigonalPrism
  | .heptagonalBipyramid => .heptagonalBipyramid

@[simp] theorem p93ResidualGeometryToProduction_roundtrip
    (geometry : BlueBookP93.Geometry) :
    BlueBookP93.geometryOfProduction (p93ResidualGeometryToProduction geometry) = geometry := by
  cases geometry <;> rfl

/-- Executable recognition decision on the qualitative IR-9 evidence.  This is deliberately a
separate pattern match from `GeometryRecognitionObservation.recognizedGeometry?`. -/
def p93ResidualProductionRecognizedGeometry? :
    RedBookIR9.GeometryRecognitionObservation → Option PolyhedralGeometry
  | .twoCoordinate .linearDisposition => some .linear
  | .twoCoordinate .bentDisposition => some .angular
  | .threeCoordinate .centerCoplanarAnglesApproximatelyEqual => some .trigonalPlanar
  | .threeCoordinate .centerCoplanarOneAngleMuchLarger => some .tShape
  | .threeCoordinate .centerSignificantlyOutOfDonorPlane => some .trigonalPyramid
  | .fourCoordinate .allFiveCoplanar => some .squarePlanar
  | .fourCoordinate .donorsCoplanarCenterDisplaced => some .squarePyramid4
  | .fourCoordinate .donorsNoncoplanarCenterInsideDonorPolyhedron => some .tetrahedron
  | .fourCoordinate .donorsNoncoplanarCenterOutsideDonorPolyhedron => some .seeSaw
  | .higherCoordinationNearestIdealized geometry =>
      if 5 ≤ (p93ResidualGeometryToProduction geometry).coordinationNumber then
        some (p93ResidualGeometryToProduction geometry)
      else none

theorem p93ResidualProductionRecognition_conforms
    (evidence : RedBookIR9.GeometryRecognitionObservation)
    (geometry : BlueBookP93.Geometry) :
    p93ResidualProductionRecognizedGeometry? evidence =
        some (p93ResidualGeometryToProduction geometry) ↔
      RedBookIR9.GeometryRecognized evidence geometry := by
  cases evidence with
  | twoCoordinate observation =>
      cases observation <;> cases geometry <;>
        simp [p93ResidualProductionRecognizedGeometry?,
          p93ResidualGeometryToProduction, RedBookIR9.GeometryRecognized,
          RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
          RedBookIR9.geometryOfTwoCoordinateObservation]
  | threeCoordinate observation =>
      cases observation <;> cases geometry <;>
        simp [p93ResidualProductionRecognizedGeometry?,
          p93ResidualGeometryToProduction, RedBookIR9.GeometryRecognized,
          RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
          RedBookIR9.geometryOfThreeCoordinateObservation]
  | fourCoordinate observation =>
      cases observation <;> cases geometry <;>
        simp [p93ResidualProductionRecognizedGeometry?,
          p93ResidualGeometryToProduction, RedBookIR9.GeometryRecognized,
          RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
          RedBookIR9.geometryOfFourCoordinateObservation]
  | higherCoordinationNearestIdealized sourceGeometry =>
      cases sourceGeometry <;> cases geometry <;>
        simp [p93ResidualProductionRecognizedGeometry?,
          p93ResidualGeometryToProduction, RedBookIR9.GeometryRecognized,
          RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
          PolyhedralGeometry.coordinationNumber, BlueBookP93.Geometry.coordinationNumber]

def P93ResidualProductionGeometryRecognized
    (evidence : RedBookIR9.GeometryRecognitionObservation)
    (geometry : BlueBookP93.Geometry) : Prop :=
  p93ResidualProductionRecognizedGeometry? evidence =
    some (p93ResidualGeometryToProduction geometry)

/-! ## Production-side priority and index computation -/

def p93ResidualPriorityToProduction
    (priority : BlueBookP93.PriorityNumber) : PolyhedralPriorityNumber :=
  { number := priority.number, primes := priority.primes }

@[simp] theorem p93ResidualPriorityToProduction_roundtrip
    (priority : BlueBookP93.PriorityNumber) :
    BlueBookP93.priorityOfProduction (p93ResidualPriorityToProduction priority) = priority := by
  cases priority
  rfl

theorem p93ResidualProductionPriority_validFor_conforms
    (coordination : Nat) (priority : BlueBookP93.PriorityNumber) :
    (p93ResidualPriorityToProduction priority).validFor coordination =
      priority.validFor coordination := by
  simp

theorem p93ResidualProductionPriority_outranks_conforms
    (left right : BlueBookP93.PriorityNumber) :
    (p93ResidualPriorityToProduction left).outranks
        (p93ResidualPriorityToProduction right) = left.seniorTo right := by
  simpa using polyhedral_priority_outranks_conforms_P93
    (p93ResidualPriorityToProduction left)
    (p93ResidualPriorityToProduction right)

def P93PositionPriorityFrame.productionPriorityAt
    (frame : P93PositionPriorityFrame) (position : Nat) : PolyhedralPriorityNumber :=
  p93ResidualPriorityToProduction (frame.priorityAt position)

/-- Executable configuration-index compiler.  Each nonempty branch calls the corresponding
production function over `PolyhedralPriorityNumber`; conversion back to the authority vocabulary
happens only at the adapter boundary. -/
def p93ResidualProductionIndex
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) :
    List (List PolyhedralPriorityNumber) :=
  match construction with
  | .trigonalPyramid => []
  | .tShape stem => [tShapeConfigurationIndex (frame.productionPriorityAt stem)]
  | .seeSaw first second =>
      [seeSawConfigurationIndex (frame.productionPriorityAt first)
        (frame.productionPriorityAt second)]
  | .trigonalBipyramid first second =>
      [trigonalBipyramidConfigurationIndex (frame.productionPriorityAt first)
        (frame.productionPriorityAt second)]
  | .squarePyramid apical =>
      match p93SquareTransToSeniorBasePosition? frame with
      | some transToSeniorBase =>
          [squarePyramidConfigurationIndex (frame.productionPriorityAt apical)
            (frame.productionPriorityAt transToSeniorBase)]
      | none => []
  | .octahedron =>
      match p93OctahedralIndexPositions? frame with
      | some (transToOne, transToSeniorPlane) =>
          [octahedronConfigurationIndex (frame.productionPriorityAt transToOne)
            (frame.productionPriorityAt transToSeniorPlane)]
      | none => []

def p93ResidualProductionIndexToAuthority
    (index : List (List PolyhedralPriorityNumber)) :
    List (List BlueBookP93.PriorityNumber) :=
  index.map (List.map BlueBookP93.priorityOfProduction)

theorem p93ResidualProductionIndex_conforms
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) :
    p93ResidualProductionIndexToAuthority
        (p93ResidualProductionIndex construction frame) =
      construction.index frame := by
  cases construction with
  | trigonalPyramid => rfl
  | tShape stem =>
      simp [p93ResidualProductionIndexToAuthority, p93ResidualProductionIndex,
        P93RelativeIndexConstruction.index,
        P93PositionPriorityFrame.productionPriorityAt,
        tShapeConfigurationIndex_conforms_P93]
  | seeSaw first second =>
      simp [p93ResidualProductionIndexToAuthority, p93ResidualProductionIndex,
        P93RelativeIndexConstruction.index,
        P93PositionPriorityFrame.productionPriorityAt,
        seeSawConfigurationIndex_conforms_P93]
  | trigonalBipyramid first second =>
      simp [p93ResidualProductionIndexToAuthority, p93ResidualProductionIndex,
        P93RelativeIndexConstruction.index,
        P93PositionPriorityFrame.productionPriorityAt,
        trigonalBipyramidConfigurationIndex_conforms_P93]
  | squarePyramid apical =>
      cases selected : p93SquareTransToSeniorBasePosition? frame with
      | none => simp [p93ResidualProductionIndexToAuthority, p93ResidualProductionIndex,
          P93RelativeIndexConstruction.index, selected]
      | some transToSeniorBase =>
          simp [p93ResidualProductionIndexToAuthority, p93ResidualProductionIndex,
            P93RelativeIndexConstruction.index, selected,
            P93PositionPriorityFrame.productionPriorityAt,
            squarePyramidConfigurationIndex_conforms_P93]
  | octahedron =>
      cases selected : p93OctahedralIndexPositions? frame with
      | none => simp [p93ResidualProductionIndexToAuthority, p93ResidualProductionIndex,
          P93RelativeIndexConstruction.index, selected]
      | some pair =>
          rcases pair with ⟨transToOne, transToSeniorPlane⟩
          simp [p93ResidualProductionIndexToAuthority, p93ResidualProductionIndex,
            P93RelativeIndexConstruction.index, selected,
            P93PositionPriorityFrame.productionPriorityAt,
            octahedronConfigurationIndex_conforms_P93]

/-! ## Production-side mirror classification -/

def P93PositionPriorityFrame.productionLabelsAlong
    (frame : P93PositionPriorityFrame) (positions : List Nat) :
    List PolyhedralPriorityNumber :=
  positions.map frame.productionPriorityAt

def p93ResidualProductionProperLabelings
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) :
    List (List PolyhedralPriorityNumber) :=
  (p93CanonicalProperPermutations construction frame).map frame.productionLabelsAlong

def p93ResidualProductionHasNonsuperimposableMirror
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) : Bool :=
  !((p93ResidualProductionProperLabelings construction frame).map
      (List.map BlueBookP93.priorityOfProduction)).contains
    ((frame.productionLabelsAlong
      (p93CanonicalMirrorPermutation construction frame)).map
        BlueBookP93.priorityOfProduction)

theorem P93PositionPriorityFrame.productionLabelsAlong_conforms
    (frame : P93PositionPriorityFrame) (positions : List Nat) :
    (frame.productionLabelsAlong positions).map BlueBookP93.priorityOfProduction =
      frame.labelsAlong positions := by
  simp [P93PositionPriorityFrame.productionLabelsAlong,
    P93PositionPriorityFrame.productionPriorityAt,
    P93PositionPriorityFrame.labelsAlong, List.map_map]

theorem p93ResidualProductionProperLabelings_conforms
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) :
    (p93ResidualProductionProperLabelings construction frame).map
        (List.map BlueBookP93.priorityOfProduction) =
      p93CanonicalProperLabelings construction frame := by
  simp [p93ResidualProductionProperLabelings, p93CanonicalProperLabelings,
    P93PositionPriorityFrame.productionLabelsAlong_conforms, List.map_map]

theorem p93ResidualProductionHasNonsuperimposableMirror_conforms
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) :
    p93ResidualProductionHasNonsuperimposableMirror construction frame =
      p93HasNonsuperimposableMirror construction frame := by
  simp [p93ResidualProductionHasNonsuperimposableMirror,
    p93HasNonsuperimposableMirror,
    p93ResidualProductionProperLabelings_conforms,
    P93PositionPriorityFrame.productionLabelsAlong_conforms]

def p93ResidualProductionRequiredDescriptorStages
    (hasNonsuperimposableMirror : Bool) : List P93DescriptorStage :=
  if hasNonsuperimposableMirror then
    [ .coordinationGeometry, .relativeConfigurationIndex, .absoluteConfiguration ]
  else
    [ .coordinationGeometry, .relativeConfigurationIndex ]

theorem p93ResidualProductionRequiredDescriptorStages_conforms
    (hasNonsuperimposableMirror : Bool) :
    p93ResidualProductionRequiredDescriptorStages hasNonsuperimposableMirror =
      p93RequiredDescriptorStages hasNonsuperimposableMirror := by
  cases hasNonsuperimposableMirror <;> rfl

/-! ## Three concrete production relations -/

def P93NontetrahedralMethodologyProductionJudged
    (observation : P93NontetrahedralMethodologyAuthorityObservation) : Prop :=
  P93ResidualProductionGeometryRecognized observation.recognition
      observation.construction.geometry ∧
    observation.frame.ValidFor observation.construction.geometry ∧
    observation.construction.CanonicalRolesIn observation.frame ∧
    P93CanonicalGeometryActionValid observation.construction observation.frame ∧
    observation.stages =
      p93ResidualProductionRequiredDescriptorStages
        (p93ResidualProductionHasNonsuperimposableMirror
          observation.construction observation.frame) ∧
    observation.configurationIndex =
      p93ResidualProductionIndexToAuthority
        (p93ResidualProductionIndex observation.construction observation.frame)

theorem p93NontetrahedralMethodology_production_eq_reference
    (observation : P93NontetrahedralMethodologyAuthorityObservation) :
    P93NontetrahedralMethodologyProductionJudged observation ↔
      P93NontetrahedralMethodologyJudged observation := by
  simp only [P93NontetrahedralMethodologyProductionJudged,
    P93ResidualProductionGeometryRecognized,
    P93NontetrahedralMethodologyJudged]
  rw [p93ResidualProductionRecognition_conforms,
    p93ResidualProductionHasNonsuperimposableMirror_conforms,
    p93ResidualProductionRequiredDescriptorStages_conforms,
    p93ResidualProductionIndex_conforms]

def P93PolyhedralGeometryRecognitionProductionJudged
    (observation : P93PolyhedralGeometryRecognitionAuthorityObservation) : Prop :=
  P93ResidualProductionGeometryRecognized observation.evidence observation.geometry

theorem p93PolyhedralGeometryRecognition_production_eq_reference
    (observation : P93PolyhedralGeometryRecognitionAuthorityObservation) :
    P93PolyhedralGeometryRecognitionProductionJudged observation ↔
      P93PolyhedralGeometryRecognitionJudged observation :=
  p93ResidualProductionRecognition_conforms observation.evidence observation.geometry

def p93TrigonalPyramidProductionPhantom : PolyhedralPriorityNumber :=
  { number := 4, primes := 0 }

theorem p93PriorityNumber_eq_four_unprimed
    (priority : BlueBookP93.PriorityNumber)
    (number : priority.number = 4) (primes : priority.primes = 0) :
    priority = BlueBookP93.priorityOfProduction p93TrigonalPyramidProductionPhantom := by
  cases priority
  simp_all [p93TrigonalPyramidProductionPhantom, BlueBookP93.priorityOfProduction]

def P93TrigonalPyramidProductionJudged
    (observation : P93TrigonalPyramidAuthorityObservation) : Prop :=
  P93ResidualProductionGeometryRecognized (.threeCoordinate observation.geometryEvidence)
      .trigonalPyramid ∧
    observation.positionFrame.Valid ∧
    observation.physicalPriorities.map Prod.fst = observation.positionFrame.donorPositions ∧
    (observation.physicalPriorities.map Prod.snd).Nodup ∧
    (∀ priority ∈ observation.physicalPriorities.map Prod.snd,
      (p93ResidualPriorityToProduction priority).validFor 4 = true) ∧
    observation.assignedPhantomPosition = observation.positionFrame.vacantPosition ∧
    observation.phantomPriority =
      BlueBookP93.priorityOfProduction p93TrigonalPyramidProductionPhantom ∧
    (∀ priority ∈ observation.physicalPriorities.map Prod.snd,
      (p93ResidualPriorityToProduction priority).outranks
        p93TrigonalPyramidProductionPhantom = true) ∧
    observation.configurationIndex =
      trigonalPyramidConfigurationIndex.map BlueBookP93.priorityOfProduction

theorem p93TrigonalPyramid_production_eq_reference
    (observation : P93TrigonalPyramidAuthorityObservation) :
    P93TrigonalPyramidProductionJudged observation ↔
      P93TrigonalPyramidJudged observation := by
  constructor
  · rintro ⟨geometry, frame, positions, nodup, physicalValid, phantomPosition,
      phantomExact, senior, index⟩
    refine ⟨(p93ResidualProductionRecognition_conforms _ _).mp geometry,
      frame, positions, nodup, ?_, phantomPosition, ?_, ?_, ?_, ?_, ?_⟩
    · intro priority member
      exact (p93ResidualProductionPriority_validFor_conforms 4 priority) ▸
        physicalValid priority member
    · rw [phantomExact]
      decide
    · intro priority member
      rw [phantomExact]
      exact (p93ResidualProductionPriority_outranks_conforms priority
        (BlueBookP93.priorityOfProduction p93TrigonalPyramidProductionPhantom)) ▸
          senior priority member
    · simpa [p93TrigonalPyramidProductionPhantom] using
        congrArg BlueBookP93.PriorityNumber.number phantomExact
    · simpa [p93TrigonalPyramidProductionPhantom] using
        congrArg BlueBookP93.PriorityNumber.primes phantomExact
    · simpa [trigonalPyramidConfigurationIndex,
        BlueBookP93.trigonalPyramidIndex] using index
  · rintro ⟨geometry, frame, positions, nodup, physicalValid, phantomPosition,
      phantomValid, senior, phantomNumber, phantomPrimes, index⟩
    have phantomExact : observation.phantomPriority =
        BlueBookP93.priorityOfProduction p93TrigonalPyramidProductionPhantom :=
      p93PriorityNumber_eq_four_unprimed observation.phantomPriority
        phantomNumber phantomPrimes
    refine ⟨(p93ResidualProductionRecognition_conforms _ _).mpr geometry,
      frame, positions, nodup, ?_, phantomPosition, phantomExact, ?_, ?_⟩
    · intro priority member
      exact (p93ResidualProductionPriority_validFor_conforms 4 priority).symm ▸
        physicalValid priority member
    · intro priority member
      have seniorExact := senior priority member
      rw [phantomExact] at seniorExact
      simpa [p93ResidualPriorityToProduction, p93TrigonalPyramidProductionPhantom,
        BlueBookP93.priorityOfProduction] using seniorExact
    · simpa [trigonalPyramidConfigurationIndex,
        BlueBookP93.trigonalPyramidIndex] using index

/-! ## One dependent three-row production program -/

def Next54P93ResidualAuthorityRow.ProductionJudges :
    (row : Next54P93ResidualAuthorityRow) → row.reference.Observation → Prop
  | .nontetrahedralGeneralMethodology => P93NontetrahedralMethodologyProductionJudged
  | .polyhedralGeometryRecognition => P93PolyhedralGeometryRecognitionProductionJudged
  | .trigonalPyramid => P93TrigonalPyramidProductionJudged

theorem Next54P93ResidualAuthorityRow.production_eq_reference
    (row : Next54P93ResidualAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : row.reference.Observation) :
    row.ProductionJudges observation ↔ row.reference.Judges source observation := by
  cases row with
  | nontetrahedralGeneralMethodology =>
      exact p93NontetrahedralMethodology_production_eq_reference observation
  | polyhedralGeometryRecognition =>
      exact p93PolyhedralGeometryRecognition_production_eq_reference observation
  | trigonalPyramid => exact p93TrigonalPyramid_production_eq_reference observation

theorem Next54P93ResidualAuthorityRow.reference_applicable
    (row : Next54P93ResidualAuthorityRow) (source : AuthoritativeChemicalInput) :
    row.reference.Applicable source := by
  cases row <;> trivial

theorem Next54P93ResidualAuthorityRow.provision_injective :
    Function.Injective Next54P93ResidualAuthorityRow.provision := by
  intro left right same
  cases left <;> cases right <;>
    simp_all [Next54P93ResidualAuthorityRow.provision]

theorem Next54P93ResidualAuthorityRow.provision_mem
    (row : Next54P93ResidualAuthorityRow) :
    row.provision ∈ next54P93PolyhedralResidualProvisions := by
  cases row <;> simp [Next54P93ResidualAuthorityRow.provision,
    next54P93PolyhedralResidualProvisions]

theorem next54P93ResidualReviewedSemantics_row_exact
    (row : Next54P93ResidualAuthorityRow) :
    next54P93ResidualReviewedSemantics.reviewed.row row.provision
        (by simpa using row.provision_mem) = row.semantics := by
  change (next54P93ResidualAuthorityRowOf row.provision row.provision_mem).semantics =
    row.semantics
  congr 1
  exact Next54P93ResidualAuthorityRow.provision_injective
    (next54P93ResidualAuthorityRowOf_provision row.provision row.provision_mem)

theorem next54P93ResidualCorpusReference_eq
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      next54P93ResidualReviewedSemantics.reviewed corpus)
    (row : Next54P93ResidualAuthorityRow) :
    corpus.reference row.provision = row.reference := by
  have exactRow := faithful.exact (by simpa using row.provision_mem)
  rw [next54P93ResidualReviewedSemantics_row_exact row] at exactRow
  exact exactRow.2.2

theorem next54P93ResidualCorpusReference_eq_of_member
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      next54P93ResidualReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P93PolyhedralResidualProvisions) :
    corpus.reference provision =
      (next54P93ResidualAuthorityRowOf provision member).reference := by
  have exactRow := faithful.exact (by simpa using member)
  simpa [next54P93ResidualReviewedSemantics,
    Next54P93ResidualAuthorityRow.semantics] using exactRow.2.2

/-- Concrete interpreter for exactly the residual P-93 scope.  Its false branch is only the
out-of-scope totalization required by `ProvisionInterpreter`; no correctness claim is made there. -/
noncomputable def next54P93ResidualProductionInterpreter
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      next54P93ResidualReviewedSemantics.reviewed corpus) :
    ProvisionInterpreter corpus where
  Produces := fun provision _source observation =>
    if member : provision ∈ next54P93PolyhedralResidualProvisions then
      let row := next54P93ResidualAuthorityRowOf provision member
      let referenceEq := next54P93ResidualCorpusReference_eq_of_member
        faithful provision member
      row.ProductionJudges
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

@[simp] theorem next54P93ResidualProductionInterpreter_exact
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      next54P93ResidualReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P93PolyhedralResidualProvisions)
    (source : AuthoritativeChemicalInput)
    (observation : (corpus.reference provision).Observation) :
    (next54P93ResidualProductionInterpreter faithful).Produces
        provision source observation ↔
      (next54P93ResidualAuthorityRowOf provision member).ProductionJudges
        (cast (congrArg ProvisionReference.Observation
          (next54P93ResidualCorpusReference_eq_of_member faithful provision member))
            observation) := by
  simp only [next54P93ResidualProductionInterpreter, dif_pos member]

/-- One dependent theorem closes production/reference correctness for all three residual rows. -/
theorem next54P93ResidualProductionInterpreter_provisionCorrect
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      next54P93ResidualReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P93PolyhedralResidualProvisions) :
    ProvisionCorrect corpus (next54P93ResidualProductionInterpreter faithful) provision := by
  intro source _admitted observation
  let row := next54P93ResidualAuthorityRowOf provision member
  let referenceEq := next54P93ResidualCorpusReference_eq_of_member
    faithful provision member
  let rowObservation : row.reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have judgment := row.production_eq_reference source rowObservation
  have applicable := row.reference_applicable source
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport :=
    ProvisionReference.judges_cast_congr referenceEq source observation
  rw [next54P93ResidualProductionInterpreter_exact
    faithful provision member source observation]
  change row.ProductionJudges rowObservation ↔
    (corpus.reference provision).Applicable source ∧
      (corpus.reference provision).Judges source observation
  constructor
  · intro produced
    exact ⟨applicableTransport.mpr applicable,
      judgmentTransport.mpr (judgment.mp produced)⟩
  · rintro ⟨_applicable, judged⟩
    exact judgment.mpr (judgmentTransport.mp judged)

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93ResidualProductionRecognition_conforms
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93ResidualProductionIndex_conforms
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93ResidualProductionHasNonsuperimposableMirror_conforms
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P93ResidualAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P93ResidualProductionInterpreter_provisionCorrect
