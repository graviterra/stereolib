import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance
import TetraStereo.OneCenter.IR9BipyramidalSourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.BipyramidalSourceIndexCompleteness

namespace RedBookIR9.BipyramidKind

/-- Production geometry corresponding to one source-level bipyramid family. -/
def productionGeometry : BipyramidKind → PolyhedralGeometry
  | .trigonal5 => .trigonalBipyramid
  | .pentagonal7 => .pentagonalBipyramid
  | .hexagonal8 => .hexagonalBipyramid
  | .heptagonal9 => .heptagonalBipyramid

/-- Number of entries consumed by the public configuration-index router.  TBPY-5 consumes only
the two axial entries because IR-9 omits its equatorial triangular segment. -/
def configurationArity : BipyramidKind → Nat
  | .trigonal5 => 2
  | .pentagonal7 => 7
  | .hexagonal8 => 8
  | .heptagonal9 => 9

/-- Typed spatial-role observation selected by a bipyramid family. -/
def positionObservation (kind : BipyramidKind) (first second : Nat)
    (perpendicular : List Nat) : ConfigurationPositionObservation :=
  match kind with
  | .trigonal5 => .trigonalBipyramid first second
  | .pentagonal7 => .pentagonalBipyramid first second perpendicular
  | .hexagonal8 => .hexagonalBipyramid first second perpendicular
  | .heptagonal9 => .heptagonalBipyramid first second perpendicular

/-- Flattened distinguished positions actually consumed by production. -/
def positions (kind : BipyramidKind) (first second : Nat)
    (perpendicular : List Nat) : List Nat :=
  match kind with
  | .trigonal5 => [first, second]
  | .pentagonal7 | .hexagonal8 | .heptagonal9 => first :: second :: perpendicular

/-- Typed absolute-orientation observation selected by a bipyramid family. -/
def absoluteObservation (kind : BipyramidKind)
    (sense : BlueBookP93.RotationSense) : AbsoluteOrientationObservation :=
  match kind with
  | .trigonal5 => .trigonalBipyramidAC sense
  | .pentagonal7 => .pentagonalBipyramidAC sense
  | .hexagonal8 => .hexagonalBipyramidAC sense
  | .heptagonal9 => .heptagonalBipyramidAC sense

/-- Priority entries expected after looking up the distinguished positions. -/
def entries (kind : BipyramidKind)
    (first second : PolyhedralPriorityNumber)
    (perpendicular : List PolyhedralPriorityNumber) : List PolyhedralPriorityNumber :=
  match kind with
  | .trigonal5 => [first, second]
  | .pentagonal7 | .hexagonal8 | .heptagonal9 => first :: second :: perpendicular

/-- Relative configuration index prescribed for the family. -/
def expectedIndex (kind : BipyramidKind)
    (first second : PolyhedralPriorityNumber)
    (perpendicular : List PolyhedralPriorityNumber) :
    List (List PolyhedralPriorityNumber) :=
  match kind with
  | .trigonal5 => [trigonalBipyramidConfigurationIndex first second]
  | .pentagonal7 | .hexagonal8 | .heptagonal9 =>
      bipyramidalConfigurationIndex first second perpendicular

@[simp] theorem productionGeometry_sourceGeometry (kind : BipyramidKind) :
    BlueBookP93.geometryOfProduction kind.productionGeometry = kind.geometry := by
  cases kind <;> rfl

@[simp] theorem productionGeometry_configurationIndexArity (kind : BipyramidKind) :
    kind.productionGeometry.configurationIndexArity? = some kind.configurationArity := by
  cases kind <;> rfl

@[simp] theorem positionObservation_positionsFor (kind : BipyramidKind)
    (first second : Nat) (perpendicular : List Nat) :
    (kind.positionObservation first second perpendicular).positionsFor? kind.geometry =
      some (kind.positions first second perpendicular) := by
  cases kind <;> rfl

@[simp] theorem absoluteObservation_rotationFor (kind : BipyramidKind)
    (sense : BlueBookP93.RotationSense) :
    (kind.absoluteObservation sense).rotationFor? kind.geometry = some (some sense) := by
  cases kind <;> rfl

end RedBookIR9.BipyramidKind

/-- Exact success boundary of the pure public bipyramidal index router, uniformly for TBPY-5,
PBPY-7, HBPY-8, and HBPY-9. -/
theorem bipyramidalConfigurationIndex?_exact
    (kind : BipyramidKind)
    (priorities : List PolyhedralPriorityNumber)
    (firstPosition secondPosition : Nat)
    (perpendicularPositions : List Nat)
    (firstPriority secondPriority : PolyhedralPriorityNumber)
    (perpendicularPriorities : List PolyhedralPriorityNumber)
    (positionLength :
      (kind.positions firstPosition secondPosition perpendicularPositions).length =
        kind.configurationArity)
    (positionsDistinct :
      (kind.positions firstPosition secondPosition perpendicularPositions).eraseDups.length =
        (kind.positions firstPosition secondPosition perpendicularPositions).length)
    (lookups :
      (kind.positions firstPosition secondPosition perpendicularPositions).mapM
          (fun position => priorities[position]?) =
        some (kind.entries firstPriority secondPriority perpendicularPriorities)) :
    polyhedralConfigurationIndex? kind.productionGeometry priorities
        (kind.positions firstPosition secondPosition perpendicularPositions) =
      some (kind.expectedIndex firstPriority secondPriority perpendicularPriorities) := by
  unfold polyhedralConfigurationIndex?
  rw [kind.productionGeometry_configurationIndexArity]
  have guardFalse :
      ((kind.positions firstPosition secondPosition perpendicularPositions).length !=
          kind.configurationArity ||
        (kind.positions firstPosition secondPosition perpendicularPositions).eraseDups.length !=
          (kind.positions firstPosition secondPosition perpendicularPositions).length) = false := by
    simp [positionLength, positionsDistinct]
  change
    (if
        ((kind.positions firstPosition secondPosition perpendicularPositions).length !=
            kind.configurationArity ||
          (kind.positions firstPosition secondPosition perpendicularPositions).eraseDups.length !=
            (kind.positions firstPosition secondPosition perpendicularPositions).length) = true
      then none
      else
        (kind.positions firstPosition secondPosition perpendicularPositions).mapM
            (fun position => priorities[position]?) >>= fun entries =>
          polyhedralConfigurationIndexOfEntries? kind.productionGeometry entries) =
      some (kind.expectedIndex firstPriority secondPriority perpendicularPriorities)
  rw [guardFalse]
  simp only [Bool.false_eq_true, ↓reduceIte, lookups]
  cases kind <;> rfl

/-- Exact end-to-end public assignment theorem for every represented bipyramidal family.

The observation supplies only an admitted nearest idealized bipyramid, its typed axial/equatorial
positions, and the source rotation sense.  The molecule-derived CIP layer supplies all priority
numbers.  Subject to the exact arity, distinct-position, successful-lookup, and absolute-priority
conditions used by production, the public analyzer emits precisely the source relative index and
the source `A/C` symbol. -/
theorem bipyramidalGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult)
    (kind : BipyramidKind)
    (center : Nat) (ligands : List Nat)
    (sense : PolyhedralRotationSense)
    (priorities : List PolyhedralPriorityNumber)
    (firstPosition secondPosition : Nat)
    (perpendicularPositions : List Nat)
    (firstPriority secondPriority : PolyhedralPriorityNumber)
    (perpendicularPriorities : List PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center kind.productionGeometry ligands =
        some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length)
    (positionLength :
      (kind.positions firstPosition secondPosition perpendicularPositions).length =
        kind.configurationArity)
    (positionsDistinct :
      (kind.positions firstPosition secondPosition perpendicularPositions).eraseDups.length =
        (kind.positions firstPosition secondPosition perpendicularPositions).length)
    (lookups :
      (kind.positions firstPosition secondPosition perpendicularPositions).mapM
          (fun position => priorities[position]?) =
        some (kind.entries firstPriority secondPriority perpendicularPriorities)) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := kind.productionGeometry
          recognition := .higherCoordinationNearestIdealized kind.geometry
          ligands := ligands
          configurationPositions :=
            kind.positionObservation firstPosition secondPosition perpendicularPositions
          absoluteOrientation := kind.absoluteObservation
            (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := kind.productionGeometry
              configurationIndex :=
                kind.expectedIndex firstPriority secondPriority perpendicularPriorities
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have indexEq := bipyramidalConfigurationIndex?_exact kind priorities
    firstPosition secondPosition perpendicularPositions
    firstPriority secondPriority perpendicularPriorities
    positionLength positionsDistinct lookups
  cases kind <;> cases sense <;>
    simp_all [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
      IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
      RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
      BlueBookP93.Geometry.coordinationNumber,
      RedBookIR9.BipyramidKind.productionGeometry,
      RedBookIR9.BipyramidKind.positionObservation,
      RedBookIR9.BipyramidKind.positions,
      RedBookIR9.BipyramidKind.entries,
      RedBookIR9.BipyramidKind.expectedIndex,
      RedBookIR9.BipyramidKind.configurationArity,
      RedBookIR9.BipyramidKind.geometry,
      RedBookIR9.ConfigurationPositionObservation.positionsFor?,
      RedBookIR9.BipyramidKind.absoluteObservation,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
      BlueBookP93.geometryOfProduction,
      PolyhedralRotationSense.ofIndependent,
      ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?,
      polyhedralAbsoluteConfiguration?, PolyhedralChiralitySymbol.ofRotation,
      BlueBookP93.rotationOfProduction]

/-- A successful nontrigonal public bipyramidal assignment necessarily supplied the exact
equatorial polygon length: five for PBPY-7, six for HBPY-8, and seven for HBPY-9. -/
theorem bipyramidalGeometryObservationAssignment_success_perpendicular_length
    (result : ChemistryNormalizationResult)
    (kind : BipyramidKind) (notTrigonal : kind ≠ .trigonal5)
    (center : Nat) (ligands : List Nat)
    (recognition : GeometryRecognitionObservation)
    (firstPosition secondPosition : Nat) (perpendicularPositions : List Nat)
    (absoluteOrientation : AbsoluteOrientationObservation)
    (priming : IndexedPolyhedralPrimingObservation)
    (assignment : StereoAssignment)
    (produced :
      result.polyhedralGeometryObservationAssignment?
          { center := center
            geometry := kind.productionGeometry
            recognition := recognition
            ligands := ligands
            configurationPositions :=
              kind.positionObservation firstPosition secondPosition perpendicularPositions
            absoluteOrientation := absoluteOrientation
            priming := priming } = some assignment) :
    perpendicularPositions.length + 2 = kind.configurationArity := by
  obtain ⟨priorities, memberships, independentRotation?, rotation?, positions, index, absolute,
      recognitionOK, recognitionValid, priorityEq, validFrame, finiteCertificate,
      positionsRecognized, orientationRecognized, rotationEq, guardFalse, indexEq,
      absoluteEq, assignmentEq⟩ :=
    result.polyhedralGeometryObservationAssignment?_sound_IR9 _ assignment produced
  have positionsEq : positions =
      kind.positions firstPosition secondPosition perpendicularPositions := by
    change
      (kind.positionObservation firstPosition secondPosition perpendicularPositions).positionsFor?
          (BlueBookP93.geometryOfProduction kind.productionGeometry) = some positions
      at positionsRecognized
    rw [kind.productionGeometry_sourceGeometry,
      kind.positionObservation_positionsFor] at positionsRecognized
    exact Option.some.inj positionsRecognized.symm
  have requiredArity : positions.length = kind.configurationArity := by
    change polyhedralConfigurationIndex? kind.productionGeometry priorities positions =
      some index at indexEq
    unfold polyhedralConfigurationIndex? at indexEq
    rw [kind.productionGeometry_configurationIndexArity] at indexEq
    simp at indexEq
    exact indexEq.1.1
  rw [positionsEq] at requiredArity
  cases kind <;> simp_all [RedBookIR9.BipyramidKind.positions,
    RedBookIR9.BipyramidKind.configurationArity]

end TetraStereo.OneCenter
