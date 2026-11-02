import TetraStereo.OneCenter.IUPACNext54ProvisionInventory
import TetraStereo.OneCenter.IR9PolyhedralSemantics

set_option autoImplicit false

/-!
# Independent reviewed targets for the three residual P-93 polyhedral provisions

The general methodology is represented as one typed construction language covering every
P-93.3.3 index form in this source slice.  Geometry recognition is independent, and the
trigonal-pyramidal clause proves its phantom is least priority and its index is empty.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

inductive P93DescriptorStage where
  | coordinationGeometry
  | relativeConfigurationIndex
  | absoluteConfiguration
  deriving DecidableEq, Repr

def p93RequiredDescriptorStages (hasNonsuperimposableMirror : Bool) : List P93DescriptorStage :=
  if hasNonsuperimposableMirror then
    [ .coordinationGeometry, .relativeConfigurationIndex, .absoluteConfiguration ]
  else
    [ .coordinationGeometry, .relativeConfigurationIndex ]

/-- One authoritative priority label at each concrete position.  This single frame is consumed by
both the configuration-index compiler and the finite symmetry action. -/
structure P93PositionPriorityFrame where
  positions : List Nat
  assignments : List (Nat × BlueBookP93.PriorityNumber)

def P93PositionPriorityFrame.priorityAt
    (frame : P93PositionPriorityFrame) (position : Nat) : BlueBookP93.PriorityNumber :=
  match frame.assignments.find? fun assignment => assignment.1 == position with
  | some assignment => assignment.2
  | none => { number := 0 }

def P93PositionPriorityFrame.labelsAlong
    (frame : P93PositionPriorityFrame) (positions : List Nat) :
    List BlueBookP93.PriorityNumber :=
  positions.map frame.priorityAt

def P93PositionPriorityFrame.ValidFor
    (frame : P93PositionPriorityFrame) (geometry : BlueBookP93.Geometry) : Prop :=
  frame.positions.length = geometry.coordinationNumber ∧
    frame.positions.Nodup ∧
    frame.assignments.map Prod.fst = frame.positions ∧
    (frame.assignments.map Prod.snd).Nodup ∧
    ∀ priority ∈ frame.assignments.map Prod.snd,
      BlueBookP93.PriorityNumber.validFor geometry.coordinationNumber priority = true

def p93MostSeniorPosition?
    (frame : P93PositionPriorityFrame) : List Nat → Option Nat
  | [] => none
  | first :: remaining =>
      some (remaining.foldl (fun best candidate =>
        if BlueBookP93.priorityDecision (frame.priorityAt candidate)
            (frame.priorityAt best) == .gt then candidate else best) first)

def p93SquareBaseOppositePosition?
    (frame : P93PositionPriorityFrame) (position : Nat) : Option Nat :=
  match frame.positions with
  | _apical :: first :: second :: third :: fourth :: [] =>
      if position = first then some third
      else if position = third then some first
      else if position = second then some fourth
      else if position = fourth then some second
      else none
  | _ => none

def p93SquareTransToSeniorBasePosition? (frame : P93PositionPriorityFrame) : Option Nat :=
  match p93MostSeniorPosition? frame frame.positions.tail with
  | some seniorBase => p93SquareBaseOppositePosition? frame seniorBase
  | none => none

def p93OctahedralOppositePosition?
    (frame : P93PositionPriorityFrame) (position : Nat) : Option Nat :=
  match frame.positions with
  | first :: firstOpposite :: second :: secondOpposite :: third :: thirdOpposite :: [] =>
      if position = first then some firstOpposite
      else if position = firstOpposite then some first
      else if position = second then some secondOpposite
      else if position = secondOpposite then some second
      else if position = third then some thirdOpposite
      else if position = thirdOpposite then some third
      else none
  | _ => none

def p93PriorityOnePosition? (frame : P93PositionPriorityFrame) : Option Nat :=
  (frame.assignments.find? fun assignment =>
    assignment.2.number == 1 && assignment.2.primes == 0).map Prod.fst

def p93OctahedralIndexPositions? (frame : P93PositionPriorityFrame) : Option (Nat × Nat) :=
  match p93PriorityOnePosition? frame with
  | none => none
  | some priorityOne =>
      match p93OctahedralOppositePosition? frame priorityOne with
      | none => none
      | some transToOne =>
          let perpendicularPlane := frame.positions.filter fun position =>
            position != priorityOne && position != transToOne
          match p93MostSeniorPosition? frame perpendicularPlane with
          | none => none
          | some seniorPlane =>
              match p93OctahedralOppositePosition? frame seniorPlane with
              | none => none
              | some transToSeniorPlane => some (transToOne, transToSeniorPlane)

/-- Exact index constructors named in P-93.3.3.2--P-93.3.3.7.  Constructors carry geometric
role positions only; every priority number is looked up from the shared frame. -/
inductive P93RelativeIndexConstruction where
  | trigonalPyramid
  | tShape (stemPosition : Nat)
  | seeSaw (firstWidePosition secondWidePosition : Nat)
  | trigonalBipyramid (firstApicalPosition secondApicalPosition : Nat)
  | squarePyramid (apicalPosition : Nat)
  | octahedron
  deriving DecidableEq, Repr

def P93RelativeIndexConstruction.geometry : P93RelativeIndexConstruction → BlueBookP93.Geometry
  | .trigonalPyramid => .trigonalPyramid
  | .tShape _ => .tShape
  | .seeSaw _ _ => .seeSaw
  | .trigonalBipyramid _ _ => .trigonalBipyramid
  | .squarePyramid _ => .squarePyramid
  | .octahedron => .octahedron

def P93RelativeIndexConstruction.rolePositions : P93RelativeIndexConstruction → List Nat
  | .trigonalPyramid => []
  | .tShape stem => [stem]
  | .seeSaw first second | .trigonalBipyramid first second => [first, second]
  | .squarePyramid apical => [apical]
  | .octahedron => []

/-- Connect irreducible geometric roles to the canonical position order consumed by the fixed
action.  Square-pyramidal and octahedral trans roles are deliberately absent from the constructor:
they are derived from the shared priority frame below. -/
def P93RelativeIndexConstruction.CanonicalRolesIn
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) : Prop :=
  match construction with
  | .trigonalPyramid => True
  | .tShape stem => frame.positions.head? = some stem
  | .seeSaw firstWide secondWide => frame.positions.take 2 = [firstWide, secondWide]
  | .trigonalBipyramid firstApical secondApical =>
      frame.positions.take 2 = [firstApical, secondApical]
  | .squarePyramid apical =>
      frame.positions.head? = some apical ∧
        (p93SquareTransToSeniorBasePosition? frame).isSome = true
  | .octahedron => (p93OctahedralIndexPositions? frame).isSome = true

def P93RelativeIndexConstruction.index
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) :
    List (List BlueBookP93.PriorityNumber) :=
  match construction with
  | .trigonalPyramid => []
  | .tShape stem => [BlueBookP93.tShapeIndex (frame.priorityAt stem)]
  | .seeSaw first second =>
      [BlueBookP93.seeSawIndex (frame.priorityAt first) (frame.priorityAt second)]
  | .trigonalBipyramid first second =>
      [BlueBookP93.trigonalBipyramidIndex (frame.priorityAt first) (frame.priorityAt second)]
  | .squarePyramid apical =>
      match p93SquareTransToSeniorBasePosition? frame with
      | some transToSeniorBase =>
          [BlueBookP93.squarePyramidIndex (frame.priorityAt apical)
            (frame.priorityAt transToSeniorBase)]
      | none => []
  | .octahedron =>
      match p93OctahedralIndexPositions? frame with
      | some (transToOne, transToSeniorPlane) =>
          [BlueBookP93.octahedronIndex (frame.priorityAt transToOne)
            (frame.priorityAt transToSeniorPlane)]
      | none => []

def P93PermutationValidFor (positions permutation : List Nat) : Prop :=
  permutation.length = positions.length ∧
    permutation.Nodup ∧
    ∀ position ∈ permutation, position ∈ positions

def p93PermutationImage
    (positions permutation : List Nat) (position : Nat) : Nat :=
  match (positions.zip permutation).find? fun assignment => assignment.1 == position with
  | some assignment => assignment.2
  | none => position

def p93ComposePermutation
    (positions first second : List Nat) : List Nat :=
  positions.map fun position =>
    p93PermutationImage positions second
      (p93PermutationImage positions first position)

def p93ExpectedProperActionOrder : P93RelativeIndexConstruction → Nat
  | .trigonalPyramid => 3
  | .tShape _ => 2
  | .seeSaw _ _ => 2
  | .trigonalBipyramid _ _ => 6
  | .squarePyramid _ => 4
  | .octahedron => 24

def p93CanonicalProperIndexPermutations :
    P93RelativeIndexConstruction → List (List Nat)
  | .trigonalPyramid =>
      [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
  | .tShape _ =>
      [[0, 1, 2], [0, 2, 1]]
  | .seeSaw _ _ =>
      [[0, 1, 2, 3], [1, 0, 3, 2]]
  | .trigonalBipyramid _ _ =>
      [[0, 1, 2, 3, 4], [0, 1, 3, 4, 2], [0, 1, 4, 2, 3],
       [1, 0, 2, 4, 3], [1, 0, 4, 3, 2], [1, 0, 3, 2, 4]]
  | .squarePyramid _ =>
      [[0, 1, 2, 3, 4], [0, 2, 3, 4, 1],
       [0, 3, 4, 1, 2], [0, 4, 1, 2, 3]]
  | .octahedron =>
      [[0,1,2,3,4,5], [0,1,3,2,5,4], [0,1,4,5,3,2], [0,1,5,4,2,3],
       [1,0,2,3,5,4], [1,0,3,2,4,5], [1,0,4,5,2,3], [1,0,5,4,3,2],
       [2,3,0,1,5,4], [2,3,1,0,4,5], [2,3,4,5,0,1], [2,3,5,4,1,0],
       [3,2,0,1,4,5], [3,2,1,0,5,4], [3,2,4,5,1,0], [3,2,5,4,0,1],
       [4,5,0,1,2,3], [4,5,1,0,3,2], [4,5,2,3,1,0], [4,5,3,2,0,1],
       [5,4,0,1,3,2], [5,4,1,0,2,3], [5,4,2,3,0,1], [5,4,3,2,1,0]]

def p93CanonicalMirrorIndexPermutation : P93RelativeIndexConstruction → List Nat
  | .trigonalPyramid => [0, 2, 1]
  | .tShape _ => [0, 2, 1]
  | .seeSaw _ _ => [1, 0, 2, 3]
  | .trigonalBipyramid _ _ => [0, 1, 2, 4, 3]
  | .squarePyramid _ => [0, 1, 4, 3, 2]
  | .octahedron => [1, 0, 2, 3, 4, 5]

def p93PositionPermutationFromIndices
    (positions indices : List Nat) : List Nat :=
  indices.map fun index => positions[index]?.getD 0

/-- Proper and mirror actions are fixed by the idealized geometry; observations cannot add or
remove a superposition.  Only the concrete position labels are substituted into this action. -/
def p93CanonicalProperPermutations
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) :
    List (List Nat) :=
  (p93CanonicalProperIndexPermutations construction).map
    (p93PositionPermutationFromIndices frame.positions)

def p93CanonicalMirrorPermutation
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) : List Nat :=
  p93PositionPermutationFromIndices frame.positions
    (p93CanonicalMirrorIndexPermutation construction)

def P93CanonicalGeometryActionValid
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) : Prop :=
  (p93CanonicalProperPermutations construction frame).length =
      p93ExpectedProperActionOrder construction ∧
    (p93CanonicalProperPermutations construction frame).Nodup ∧
    (∀ permutation ∈ p93CanonicalProperPermutations construction frame,
      P93PermutationValidFor frame.positions permutation) ∧
    frame.positions ∈ p93CanonicalProperPermutations construction frame ∧
    (∀ first ∈ p93CanonicalProperPermutations construction frame,
      ∀ second ∈ p93CanonicalProperPermutations construction frame,
        p93ComposePermutation frame.positions first second ∈
          p93CanonicalProperPermutations construction frame) ∧
    P93PermutationValidFor frame.positions
      (p93CanonicalMirrorPermutation construction frame) ∧
    p93ComposePermutation frame.positions
        (p93CanonicalMirrorPermutation construction frame)
        (p93CanonicalMirrorPermutation construction frame) = frame.positions ∧
    ∀ proper ∈ p93CanonicalProperPermutations construction frame,
      p93ComposePermutation frame.positions
          (p93CanonicalMirrorPermutation construction frame)
          (p93ComposePermutation frame.positions proper
            (p93CanonicalMirrorPermutation construction frame)) ∈
        p93CanonicalProperPermutations construction frame

def p93CanonicalProperLabelings
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) :
    List (List BlueBookP93.PriorityNumber) :=
  (p93CanonicalProperPermutations construction frame).map frame.labelsAlong

def p93HasNonsuperimposableMirror
    (construction : P93RelativeIndexConstruction) (frame : P93PositionPriorityFrame) : Bool :=
  !(p93CanonicalProperLabelings construction frame).contains
    (frame.labelsAlong (p93CanonicalMirrorPermutation construction frame))

structure P93NontetrahedralMethodologyAuthorityObservation where
  recognition : RedBookIR9.GeometryRecognitionObservation
  construction : P93RelativeIndexConstruction
  frame : P93PositionPriorityFrame
  stages : List P93DescriptorStage
  configurationIndex : List (List BlueBookP93.PriorityNumber)

def P93NontetrahedralMethodologyJudged
    (observation : P93NontetrahedralMethodologyAuthorityObservation) : Prop :=
  RedBookIR9.GeometryRecognized observation.recognition observation.construction.geometry ∧
    observation.frame.ValidFor observation.construction.geometry ∧
    observation.construction.CanonicalRolesIn observation.frame ∧
    P93CanonicalGeometryActionValid observation.construction observation.frame ∧
    observation.stages =
      p93RequiredDescriptorStages
        (p93HasNonsuperimposableMirror observation.construction observation.frame) ∧
    observation.configurationIndex = observation.construction.index observation.frame

def p93NontetrahedralGeneralMethodologyReference : ProvisionReference where
  Observation := P93NontetrahedralMethodologyAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P93NontetrahedralMethodologyJudged observation

structure P93PolyhedralGeometryRecognitionAuthorityObservation where
  evidence : RedBookIR9.GeometryRecognitionObservation
  geometry : BlueBookP93.Geometry

def P93PolyhedralGeometryRecognitionJudged
    (observation : P93PolyhedralGeometryRecognitionAuthorityObservation) : Prop :=
  RedBookIR9.GeometryRecognized observation.evidence observation.geometry

def p93PolyhedralGeometryRecognitionReference : ProvisionReference where
  Observation := P93PolyhedralGeometryRecognitionAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P93PolyhedralGeometryRecognitionJudged observation

structure P93TrigonalPyramidPositionFrame where
  tetrahedralPositions : List Nat
  donorPositions : List Nat
  vacantPosition : Nat

def P93TrigonalPyramidPositionFrame.Valid
    (frame : P93TrigonalPyramidPositionFrame) : Prop :=
  frame.tetrahedralPositions.length = 4 ∧
    frame.tetrahedralPositions.Nodup ∧
    frame.donorPositions.length = 3 ∧
    frame.donorPositions.Nodup ∧
    (∀ position ∈ frame.donorPositions, position ∈ frame.tetrahedralPositions) ∧
    frame.vacantPosition ∈ frame.tetrahedralPositions ∧
    frame.vacantPosition ∉ frame.donorPositions ∧
    ∀ position ∈ frame.tetrahedralPositions,
      position ∈ frame.donorPositions ∨ position = frame.vacantPosition

structure P93TrigonalPyramidAuthorityObservation where
  geometryEvidence : RedBookIR9.ThreeCoordinateObservation
  positionFrame : P93TrigonalPyramidPositionFrame
  physicalPriorities : List (Nat × BlueBookP93.PriorityNumber)
  assignedPhantomPosition : Nat
  phantomPriority : BlueBookP93.PriorityNumber
  configurationIndex : List BlueBookP93.PriorityNumber

def P93TrigonalPyramidJudged
    (observation : P93TrigonalPyramidAuthorityObservation) : Prop :=
  RedBookIR9.GeometryRecognized (.threeCoordinate observation.geometryEvidence)
      .trigonalPyramid ∧
    observation.positionFrame.Valid ∧
    observation.physicalPriorities.map Prod.fst = observation.positionFrame.donorPositions ∧
    (observation.physicalPriorities.map Prod.snd).Nodup ∧
    (∀ priority ∈ observation.physicalPriorities.map Prod.snd,
      BlueBookP93.PriorityNumber.validFor 4 priority = true) ∧
    observation.assignedPhantomPosition = observation.positionFrame.vacantPosition ∧
    BlueBookP93.PriorityNumber.validFor 4 observation.phantomPriority = true ∧
    (∀ priority ∈ observation.physicalPriorities.map Prod.snd,
      priority.seniorTo observation.phantomPriority = true) ∧
    observation.phantomPriority.number = 4 ∧
    observation.phantomPriority.primes = 0 ∧
    observation.configurationIndex = BlueBookP93.trigonalPyramidIndex

def p93TrigonalPyramidReference : ProvisionReference where
  Observation := P93TrigonalPyramidAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P93TrigonalPyramidJudged observation

inductive Next54P93ResidualAuthorityRow where
  | nontetrahedralGeneralMethodology
  | polyhedralGeometryRecognition
  | trigonalPyramid
  deriving DecidableEq, Repr

namespace Next54P93ResidualAuthorityRow

def all : List Next54P93ResidualAuthorityRow :=
  [ .nontetrahedralGeneralMethodology
  , .polyhedralGeometryRecognition
  , .trigonalPyramid
  ]

def provision : Next54P93ResidualAuthorityRow → IUPACNormativeProvision
  | .nontetrahedralGeneralMethodology => .p93NontetrahedralGeneralMethodology
  | .polyhedralGeometryRecognition => .p93PolyhedralGeometryRecognition
  | .trigonalPyramid => .p93TrigonalPyramid

def kind : Next54P93ResidualAuthorityRow → ProvisionKind
  | .polyhedralGeometryRecognition => .perception
  | _ => .spatialDescriptor

def reference : Next54P93ResidualAuthorityRow → ProvisionReference
  | .nontetrahedralGeneralMethodology => p93NontetrahedralGeneralMethodologyReference
  | .polyhedralGeometryRecognition => p93PolyhedralGeometryRecognitionReference
  | .trigonalPyramid => p93TrigonalPyramidReference

def semantics (row : Next54P93ResidualAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference

@[simp] theorem all_length : all.length = 3 := by rfl

theorem all_nodup : all.Nodup := by decide

@[simp] theorem all_provisions_exact :
    all.map provision = next54P93PolyhedralResidualProvisions := by rfl

@[simp] theorem classifier_exact (row : Next54P93ResidualAuthorityRow) :
    next54Kind? row.provision = some row.kind := by
  cases row <;>
    simp [next54Kind?, next54SequenceRuleProvisions, next54PerceptionProvisions,
      next54SpatialDescriptorProvisions, provision, kind]

/-! ## Abstract satisfiability of the input-invariant residual references -/

/-- These three methodology references are conceptual and do not inspect their molecular input.
The empty carrier packages structural admission; it is not asserted to realize the observations. -/
def witnessInput : AuthoritativeChemicalInput where
  molecule := { atoms := [], interactions := [] }

@[simp] theorem witnessInput_structurallyWellFormed :
    witnessInput.StructurallyWellFormed := by
  simp [witnessInput, AuthoritativeChemicalInput.StructurallyWellFormed,
    SemanticMolecule.StructurallyWellFormed,
    AuthoritativeChemicalInput.SpatialIndicesWellFormed,
    AuthoritativeChemicalInput.DiagramIndicesWellFormed]

def witnessThreePositionPriorityFrame : P93PositionPriorityFrame where
  positions := [0, 1, 2]
  assignments :=
    [(0, { number := 1 }), (1, { number := 2 }), (2, { number := 3 })]

def methodologyWitness : P93NontetrahedralMethodologyAuthorityObservation where
  recognition := .threeCoordinate .centerCoplanarOneAngleMuchLarger
  construction := .tShape 0
  frame := witnessThreePositionPriorityFrame
  stages := [.coordinationGeometry, .relativeConfigurationIndex]
  configurationIndex := [[{ number := 1 }]]

theorem methodologyWitness_judged :
    P93NontetrahedralMethodologyJudged methodologyWitness := by
  simp [P93NontetrahedralMethodologyJudged, methodologyWitness,
    witnessThreePositionPriorityFrame, P93PositionPriorityFrame.ValidFor,
    P93PositionPriorityFrame.priorityAt, P93CanonicalGeometryActionValid,
    p93HasNonsuperimposableMirror, p93CanonicalProperLabelings,
    p93CanonicalProperPermutations, p93CanonicalMirrorPermutation,
    p93CanonicalProperIndexPermutations, p93CanonicalMirrorIndexPermutation,
    p93PositionPermutationFromIndices, P93PositionPriorityFrame.labelsAlong,
    P93PermutationValidFor, p93ComposePermutation, p93PermutationImage,
    p93ExpectedProperActionOrder, P93RelativeIndexConstruction.CanonicalRolesIn,
    P93RelativeIndexConstruction.geometry, P93RelativeIndexConstruction.index,
    p93RequiredDescriptorStages, RedBookIR9.GeometryRecognized,
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
    RedBookIR9.geometryOfThreeCoordinateObservation, BlueBookP93.tShapeIndex,
    BlueBookP93.Geometry.coordinationNumber, BlueBookP93.PriorityNumber.validFor]

def geometryRecognitionWitness : P93PolyhedralGeometryRecognitionAuthorityObservation where
  evidence := .threeCoordinate .centerSignificantlyOutOfDonorPlane
  geometry := .trigonalPyramid

theorem geometryRecognitionWitness_judged :
    P93PolyhedralGeometryRecognitionJudged geometryRecognitionWitness := by
  rfl

def trigonalPyramidPositionFrameWitness : P93TrigonalPyramidPositionFrame where
  tetrahedralPositions := [0, 1, 2, 3]
  donorPositions := [0, 1, 2]
  vacantPosition := 3

def trigonalPyramidWitness : P93TrigonalPyramidAuthorityObservation where
  geometryEvidence := .centerSignificantlyOutOfDonorPlane
  positionFrame := trigonalPyramidPositionFrameWitness
  physicalPriorities :=
    [(0, { number := 1 }), (1, { number := 2 }), (2, { number := 3 })]
  assignedPhantomPosition := 3
  phantomPriority := { number := 4 }
  configurationIndex := []

theorem trigonalPyramidWitness_judged :
    P93TrigonalPyramidJudged trigonalPyramidWitness := by
  simp [P93TrigonalPyramidJudged, trigonalPyramidWitness,
    trigonalPyramidPositionFrameWitness, P93TrigonalPyramidPositionFrame.Valid,
    RedBookIR9.GeometryRecognized,
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
    RedBookIR9.geometryOfThreeCoordinateObservation,
    BlueBookP93.PriorityNumber.validFor, BlueBookP93.PriorityNumber.seniorTo,
    BlueBookP93.trigonalPyramidIndex]

/-- Molecular input is definitionally irrelevant to these three conceptual source references. -/
theorem reference_input_invariant
    (row : Next54P93ResidualAuthorityRow)
    (first second : AuthoritativeChemicalInput) :
    (row.reference.Applicable first ↔ row.reference.Applicable second) ∧
      ∀ observation,
        row.reference.Judges first observation ↔
          row.reference.Judges second observation := by
  cases row <;> exact ⟨Iff.rfl, fun _observation => Iff.rfl⟩

/-- Satisfiability of the three independent methodology relations.  This is not a claim that the
empty carrier molecule realizes the geometry observation. -/
theorem reference_nonvacuous (row : Next54P93ResidualAuthorityRow) :
    ∃ observation,
      row.reference.Applicable witnessInput ∧
        row.reference.Judges witnessInput observation := by
  cases row with
  | nontetrahedralGeneralMethodology =>
      exact ⟨methodologyWitness, trivial, methodologyWitness_judged⟩
  | polyhedralGeometryRecognition =>
      exact ⟨geometryRecognitionWitness, trivial, geometryRecognitionWitness_judged⟩
  | trigonalPyramid =>
      exact ⟨trigonalPyramidWitness, trivial, trigonalPyramidWitness_judged⟩

theorem reference_nonvacuous_at
    (row : Next54P93ResidualAuthorityRow)
    (input : AuthoritativeChemicalInput) :
    ∃ observation,
      row.reference.Applicable input ∧
        row.reference.Judges input observation := by
  rcases row.reference_nonvacuous with ⟨observation, applicable, judged⟩
  have invariant := row.reference_input_invariant witnessInput input
  exact ⟨observation, invariant.1.mp applicable, (invariant.2 observation).mp judged⟩

end Next54P93ResidualAuthorityRow

theorem next54P93Residual_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P93PolyhedralResidualProvisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : next54P93PolyhedralResidualProvisions.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem next54P93Residual_mem_next54
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P93PolyhedralResidualProvisions) :
    provision ∈ next54Provisions := by
  apply List.mem_append_left next54IR9ResidualProvisions
  apply List.mem_append_right next54P91Provisions
  apply List.mem_append_right next54P92ResidualProvisions
  exact member

theorem exists_next54P93ResidualAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P93PolyhedralResidualProvisions) :
    ∃ row, row ∈ Next54P93ResidualAuthorityRow.all ∧ row.provision = provision := by
  rw [← Next54P93ResidualAuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def next54P93ResidualAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P93PolyhedralResidualProvisions) :
    Next54P93ResidualAuthorityRow :=
  Classical.choose (exists_next54P93ResidualAuthorityRow member)

theorem next54P93ResidualAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P93PolyhedralResidualProvisions) :
    (next54P93ResidualAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_next54P93ResidualAuthorityRow member)).2

structure Next54P93ResidualReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch next54P93PolyhedralResidualProvisions.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P93PolyhedralResidualProvisions.toFinset),
      (reviewed.row provision member).kind =
        next54Kind provision (next54P93Residual_mem_next54 (by simpa using member))

noncomputable def next54P93ResidualReviewedSemantics :
    Next54P93ResidualReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        (next54P93ResidualAuthorityRowOf provision (by simpa using member)).semantics
      sourceAudited := by
        intro provision member
        exact next54P93Residual_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := next54P93ResidualAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      next54P93ResidualAuthorityRowOf_provision provision (by simpa using member)
    have rowClassifier := Next54P93ResidualAuthorityRow.classifier_exact row
    have totalClassifier := next54Kind?_eq_some provision
      (next54P93Residual_mem_next54 (by simpa using member))
    rw [rowProvision] at rowClassifier
    change row.kind = next54Kind provision _
    exact Option.some.inj (rowClassifier.symm.trans totalClassifier)

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P93ResidualAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P93Residual_sourceAuditComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P93ResidualAuthorityRow.classifier_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P93ResidualAuthorityRow.reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P93ResidualAuthorityRow.reference_nonvacuous_at
