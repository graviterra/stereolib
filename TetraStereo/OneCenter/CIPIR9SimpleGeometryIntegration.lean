import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance
import TetraStereo.OneCenter.IR9SimpleGeometryProductionCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-backed integration for T-3, SP-4, SPY-4, and SS-4

These exact theorems connect the newly proved source/production symmetry boundaries to the public
observation constructor.  Three- and four-coordinate geometry evidence uses the qualitative
IR-9.3.2 decision-tree constructors, so no invented numerical distortion threshold is introduced.
-/

theorem tShapeConfigurationIndex?_exact
    (priorities : List PolyhedralPriorityNumber) (stemPosition : Nat)
    (stemPriority : PolyhedralPriorityNumber)
    (lookup : priorities[stemPosition]? = some stemPriority) :
    polyhedralConfigurationIndex? .tShape priorities [stemPosition] =
      some [[stemPriority]] := by
  simp [polyhedralConfigurationIndex?,
    PolyhedralGeometry.configurationIndexArity?, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop, lookup,
    polyhedralConfigurationIndexOfEntries?, tShapeConfigurationIndex]

theorem squarePlanarConfigurationIndex?_exact
    (priorities : List PolyhedralPriorityNumber) (transPosition : Nat)
    (transPriority : PolyhedralPriorityNumber)
    (lookup : priorities[transPosition]? = some transPriority) :
    polyhedralConfigurationIndex? .squarePlanar priorities [transPosition] =
      some [[transPriority]] := by
  simp [polyhedralConfigurationIndex?,
    PolyhedralGeometry.configurationIndexArity?, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop, lookup,
    polyhedralConfigurationIndexOfEntries?, squarePlanarConfigurationIndex]

theorem squarePyramid4ConfigurationIndex?_exact
    (priorities : List PolyhedralPriorityNumber) (transPosition : Nat)
    (transPriority : PolyhedralPriorityNumber)
    (lookup : priorities[transPosition]? = some transPriority) :
    polyhedralConfigurationIndex? .squarePyramid4 priorities [transPosition] =
      some [[transPriority]] := by
  simp [polyhedralConfigurationIndex?,
    PolyhedralGeometry.configurationIndexArity?, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop, lookup,
    polyhedralConfigurationIndexOfEntries?, squarePyramid4ConfigurationIndex]

theorem seeSawConfigurationIndex?_exact
    (priorities : List PolyhedralPriorityNumber)
    (firstPosition secondPosition : Nat)
    (firstPriority secondPriority : PolyhedralPriorityNumber)
    (positionsDistinct : [firstPosition, secondPosition].eraseDups.length = 2)
    (lookups : [firstPosition, secondPosition].mapM
        (fun position => priorities[position]?) = some [firstPriority, secondPriority]) :
    polyhedralConfigurationIndex? .seeSaw priorities [firstPosition, secondPosition] =
      some [seeSawConfigurationIndex firstPriority secondPriority] := by
  simp [polyhedralConfigurationIndex?,
    PolyhedralGeometry.configurationIndexArity?, positionsDistinct, lookups,
    polyhedralConfigurationIndexOfEntries?]

theorem tShapeGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (priorities : List PolyhedralPriorityNumber)
    (stemPosition : Nat) (stemPriority : PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .tShape ligands = some priorities)
    (lookup : priorities[stemPosition]? = some stemPriority) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .tShape
          recognition := .threeCoordinate .centerCoplanarOneAngleMuchLarger
          ligands := ligands
          configurationPositions := .tShape stemPosition
          absoluteOrientation := .none } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .tShape
              configurationIndex := [[stemPriority]]
              absolute? := none } } := by
  have indexEq := tShapeConfigurationIndex?_exact priorities stemPosition stemPriority lookup
  simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
    IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
    RedBookIR9.geometryOfThreeCoordinateObservation,
    RedBookIR9.ConfigurationPositionObservation.positionsFor?,
    RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
    BlueBookP93.geometryOfProduction,
    ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
    indexEq, polyhedralAbsoluteConfiguration?]

theorem squarePlanarGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (priorities : List PolyhedralPriorityNumber)
    (transPosition : Nat) (transPriority : PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .squarePlanar ligands = some priorities)
    (lookup : priorities[transPosition]? = some transPriority) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .squarePlanar
          recognition := .fourCoordinate .allFiveCoplanar
          ligands := ligands
          configurationPositions := .squarePlanar transPosition
          absoluteOrientation := .none } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .squarePlanar
              configurationIndex := [[transPriority]]
              absolute? := none } } := by
  have indexEq := squarePlanarConfigurationIndex?_exact priorities transPosition transPriority lookup
  simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
    IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
    RedBookIR9.geometryOfFourCoordinateObservation,
    RedBookIR9.ConfigurationPositionObservation.positionsFor?,
    RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
    BlueBookP93.geometryOfProduction,
    ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
    indexEq, polyhedralAbsoluteConfiguration?]

theorem squarePyramid4GeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (sense : PolyhedralRotationSense) (priorities : List PolyhedralPriorityNumber)
    (transPosition : Nat) (transPriority : PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .squarePyramid4 ligands = some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length)
    (lookup : priorities[transPosition]? = some transPriority) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .squarePyramid4
          recognition := .fourCoordinate .donorsCoplanarCenterDisplaced
          ligands := ligands
          configurationPositions := .squarePyramid4 transPosition
          absoluteOrientation := .squarePyramid4AC
            (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .squarePyramid4
              configurationIndex := [[transPriority]]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have indexEq := squarePyramid4ConfigurationIndex?_exact priorities transPosition transPriority lookup
  cases sense <;>
    simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
      IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
      RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
      RedBookIR9.geometryOfFourCoordinateObservation,
      RedBookIR9.ConfigurationPositionObservation.positionsFor?,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
      BlueBookP93.geometryOfProduction,
      PolyhedralRotationSense.ofIndependent,
      ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
      prioritiesDistinct, indexEq,
      polyhedralAbsoluteConfiguration?, PolyhedralChiralitySymbol.ofRotation,
      BlueBookP93.rotationOfProduction]

theorem seeSawGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (sense : PolyhedralRotationSense) (priorities : List PolyhedralPriorityNumber)
    (firstPosition secondPosition : Nat)
    (firstPriority secondPriority : PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .seeSaw ligands = some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length)
    (positionsDistinct : [firstPosition, secondPosition].eraseDups.length = 2)
    (lookups : [firstPosition, secondPosition].mapM
        (fun position => priorities[position]?) = some [firstPriority, secondPriority]) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .seeSaw
          recognition := .fourCoordinate .donorsNoncoplanarCenterOutsideDonorPolyhedron
          ligands := ligands
          configurationPositions := .seeSaw firstPosition secondPosition
          absoluteOrientation := .seeSawAC (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .seeSaw
              configurationIndex := [seeSawConfigurationIndex firstPriority secondPriority]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have indexEq := seeSawConfigurationIndex?_exact priorities firstPosition secondPosition
    firstPriority secondPriority positionsDistinct lookups
  cases sense <;>
    simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
      IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
      RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
      RedBookIR9.geometryOfFourCoordinateObservation,
      RedBookIR9.ConfigurationPositionObservation.positionsFor?,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
      BlueBookP93.geometryOfProduction,
      PolyhedralRotationSense.ofIndependent,
      ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
      prioritiesDistinct, indexEq,
      polyhedralAbsoluteConfiguration?, PolyhedralChiralitySymbol.ofRotation,
      BlueBookP93.rotationOfProduction]

end TetraStereo.OneCenter
