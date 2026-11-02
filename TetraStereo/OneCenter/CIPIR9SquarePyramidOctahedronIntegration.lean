import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance
import TetraStereo.OneCenter.IR9SquarePyramidAbsoluteSymmetry
import TetraStereo.OneCenter.IR9OctahedronAbsoluteSymmetry

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecular observation integration for SPY-5 and OC-6

The symmetry modules close the idealized source-index and absolute-class mathematics.  This file
connects the literal two-entry indices to the public molecule-backed observation constructor.  The
observations remain typed nearest-idealized geometry and rotation evidence; ligand priority numbers
are derived by the molecular CIP layer before the exact descriptor is emitted.
-/

/-- Exact success of the public SPY-5 two-position index router. -/
theorem squarePyramidConfigurationIndex?_exact
    (priorities : List PolyhedralPriorityNumber)
    (apicalPosition transPosition : Nat)
    (apicalPriority transPriority : PolyhedralPriorityNumber)
    (positionsDistinct : [apicalPosition, transPosition].eraseDups.length = 2)
    (lookups : [apicalPosition, transPosition].mapM
        (fun position => priorities[position]?) =
      some [apicalPriority, transPriority]) :
    polyhedralConfigurationIndex? .squarePyramid priorities
        [apicalPosition, transPosition] =
      some [[apicalPriority, transPriority]] := by
  simp [polyhedralConfigurationIndex?,
    PolyhedralGeometry.configurationIndexArity?, positionsDistinct, lookups,
    polyhedralConfigurationIndexOfEntries?, squarePyramidConfigurationIndex]

/-- Exact success of the public OC-6 two-position index router. -/
theorem octahedronConfigurationIndex?_exact
    (priorities : List PolyhedralPriorityNumber)
    (transToOnePosition transToSeniorPlanePosition : Nat)
    (transToOnePriority transToSeniorPlanePriority : PolyhedralPriorityNumber)
    (positionsDistinct :
      [transToOnePosition, transToSeniorPlanePosition].eraseDups.length = 2)
    (lookups : [transToOnePosition, transToSeniorPlanePosition].mapM
        (fun position => priorities[position]?) =
      some [transToOnePriority, transToSeniorPlanePriority]) :
    polyhedralConfigurationIndex? .octahedron priorities
        [transToOnePosition, transToSeniorPlanePosition] =
      some [[transToOnePriority, transToSeniorPlanePriority]] := by
  simp [polyhedralConfigurationIndex?,
    PolyhedralGeometry.configurationIndexArity?, positionsDistinct, lookups,
    polyhedralConfigurationIndexOfEntries?, octahedronConfigurationIndex]

/-- Exact molecule-backed SPY-5 descriptor after typed geometry, spatial-role, and rotation
observations have been supplied. -/
theorem squarePyramidGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (sense : PolyhedralRotationSense) (priorities : List PolyhedralPriorityNumber)
    (apicalPosition transPosition : Nat)
    (apicalPriority transPriority : PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .squarePyramid ligands = some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length)
    (positionsDistinct : [apicalPosition, transPosition].eraseDups.length = 2)
    (lookups : [apicalPosition, transPosition].mapM
        (fun position => priorities[position]?) =
      some [apicalPriority, transPriority]) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .squarePyramid
          recognition := .higherCoordinationNearestIdealized .squarePyramid
          ligands := ligands
          configurationPositions := .squarePyramid apicalPosition transPosition
          absoluteOrientation := .squarePyramidAC
            (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .squarePyramid
              configurationIndex := [[apicalPriority, transPriority]]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have indexEq := squarePyramidConfigurationIndex?_exact priorities
    apicalPosition transPosition apicalPriority transPriority positionsDistinct lookups
  cases sense <;>
    simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
      IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
      RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
      BlueBookP93.Geometry.coordinationNumber,
      RedBookIR9.ConfigurationPositionObservation.positionsFor?,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
      BlueBookP93.geometryOfProduction,
      PolyhedralRotationSense.ofIndependent,
      ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
      prioritiesDistinct, indexEq,
      polyhedralAbsoluteConfiguration?, PolyhedralChiralitySymbol.ofRotation,
      BlueBookP93.rotationOfProduction]

/-- Exact molecule-backed OC-6 descriptor after typed geometry, spatial-role, and rotation
observations have been supplied. -/
theorem octahedronGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (sense : PolyhedralRotationSense) (priorities : List PolyhedralPriorityNumber)
    (transToOnePosition transToSeniorPlanePosition : Nat)
    (transToOnePriority transToSeniorPlanePriority : PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .octahedron ligands = some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length)
    (positionsDistinct :
      [transToOnePosition, transToSeniorPlanePosition].eraseDups.length = 2)
    (lookups : [transToOnePosition, transToSeniorPlanePosition].mapM
        (fun position => priorities[position]?) =
      some [transToOnePriority, transToSeniorPlanePriority]) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .octahedron
          recognition := .higherCoordinationNearestIdealized .octahedron
          ligands := ligands
          configurationPositions :=
            .octahedron transToOnePosition transToSeniorPlanePosition
          absoluteOrientation := .octahedronAC
            (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .octahedron
              configurationIndex :=
                [[transToOnePriority, transToSeniorPlanePriority]]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have indexEq := octahedronConfigurationIndex?_exact priorities
    transToOnePosition transToSeniorPlanePosition
    transToOnePriority transToSeniorPlanePriority positionsDistinct lookups
  cases sense <;>
    simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
      IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
      RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
      BlueBookP93.Geometry.coordinationNumber,
      RedBookIR9.ConfigurationPositionObservation.positionsFor?,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
      BlueBookP93.geometryOfProduction,
      PolyhedralRotationSense.ofIndependent,
      ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
      prioritiesDistinct, indexEq,
      polyhedralAbsoluteConfiguration?, PolyhedralChiralitySymbol.ofRotation,
      BlueBookP93.rotationOfProduction]

end TetraStereo.OneCenter
