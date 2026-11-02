import TetraStereo.OneCenter.IR9FourCoordinateSpatialPerception
import TetraStereo.OneCenter.CIPIR9SimpleGeometryIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.FourCoordinateSpatialPerception

/-!
# Molecule-backed exact four-coordinate spatial integration

This ingress omits the formerly supplied qualitative recognition label.  It collects the center
and exactly four ligand coordinates, computes the determinate IR-9.3.2.2 branch, constructs the
typed recognition record, and only then invokes the existing molecule-derived CIP priority and
descriptor route.
-/

/-- A four-coordinate observation with no caller-supplied geometry-recognition answer. -/
structure IndexedFourCoordinateSpatialGeometryObservation where
  center : ℕ
  geometry : PolyhedralGeometry
  ligands : List ℕ
  configurationPositions : RedBookIR9.ConfigurationPositionObservation
  absoluteOrientation : RedBookIR9.AbsoluteOrientationObservation
  priming : IndexedPolyhedralPrimingObservation := .repeatedPolydentateLigands
  deriving DecidableEq, Repr

namespace IndexedFourCoordinateSpatialGeometryObservation

/-- Insert the recognition branch computed from coordinates. -/
def withRecognition (record : IndexedFourCoordinateSpatialGeometryObservation)
    (observation : RedBookIR9.FourCoordinateObservation) :
    IndexedPolyhedralGeometryObservation :=
  { center := record.center
    geometry := record.geometry
    recognition := .fourCoordinate observation
    ligands := record.ligands
    configurationPositions := record.configurationPositions
    absoluteOrientation := record.absoluteOrientation
    priming := record.priming }

end IndexedFourCoordinateSpatialGeometryObservation

/-- Collect a center and exactly four donor points.  Missing coordinates and every other ligand
arity are rejected. -/
def SpatialConfiguration.fourCoordinateFrame?
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : List ℕ) :
    Option FourCoordinateSpatialPerception.Frame :=
  match ligands with
  | [donor0, donor1, donor2, donor3] => do
      let centerPoint ← spatial.positions[center]?
      let donorPoint0 ← spatial.positions[donor0]?
      let donorPoint1 ← spatial.positions[donor1]?
      let donorPoint2 ← spatial.positions[donor2]?
      let donorPoint3 ← spatial.positions[donor3]?
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3 }
  | _ => none

theorem SpatialConfiguration.fourCoordinateFrame?_explicit
    (spatial : SpatialConfiguration) (center donor0 donor1 donor2 donor3 : ℕ)
    (centerPoint donorPoint0 donorPoint1 donorPoint2 donorPoint3 : CartesianPoint3)
    (centerEq : spatial.positions[center]? = some centerPoint)
    (donorEq0 : spatial.positions[donor0]? = some donorPoint0)
    (donorEq1 : spatial.positions[donor1]? = some donorPoint1)
    (donorEq2 : spatial.positions[donor2]? = some donorPoint2)
    (donorEq3 : spatial.positions[donor3]? = some donorPoint3) :
    spatial.fourCoordinateFrame? center [donor0, donor1, donor2, donor3] =
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3 } := by
  simp [SpatialConfiguration.fourCoordinateFrame?, centerEq, donorEq0, donorEq1,
    donorEq2, donorEq3]

/-- Compute and insert the coordinate-derived recognition branch. -/
def IndexedFourCoordinateSpatialGeometryObservation.derivedRecord?
    (record : IndexedFourCoordinateSpatialGeometryObservation)
    (spatial : SpatialConfiguration) : Option IndexedPolyhedralGeometryObservation := do
  let frame ← spatial.fourCoordinateFrame? record.center record.ligands
  let observation ← FourCoordinateSpatialPerception.observe? frame
  some (record.withRecognition observation)

/-- Public descriptor construction after exact coordinate-derived four-coordinate recognition. -/
def ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedFourCoordinateSpatialGeometryObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? spatial
  result.polyhedralGeometryObservationAssignment? derived

/-- Exact success/refusal characterization of the coordinate-derived public route. -/
theorem ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedFourCoordinateSpatialGeometryObservation)
    (assignment : StereoAssignment) :
    result.fourCoordinateSpatialGeometryAssignment? spatial record = some assignment ↔
      ∃ frame observation,
        spatial.fourCoordinateFrame? record.center record.ligands = some frame ∧
        FourCoordinateSpatialPerception.Judgment frame observation ∧
        result.polyhedralGeometryObservationAssignment?
            (record.withRecognition observation) = some assignment := by
  constructor
  · intro produced
    unfold ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment? at produced
    unfold IndexedFourCoordinateSpatialGeometryObservation.derivedRecord? at produced
    cases frameEq : spatial.fourCoordinateFrame? record.center record.ligands with
    | none => simp [frameEq] at produced
    | some frame =>
        cases observationEq : FourCoordinateSpatialPerception.observe? frame with
        | none => simp [frameEq, observationEq] at produced
        | some observation =>
            refine ⟨frame, observation, rfl,
              (FourCoordinateSpatialPerception.observe?_eq_some_iff frame observation).mp
                observationEq, ?_⟩
            simpa [frameEq, observationEq] using produced
  · rintro ⟨frame, observation, frameEq, judgment, produced⟩
    have observationEq : FourCoordinateSpatialPerception.observe? frame = some observation :=
      (FourCoordinateSpatialPerception.observe?_eq_some_iff frame observation).mpr judgment
    simp [ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?,
      IndexedFourCoordinateSpatialGeometryObservation.derivedRecord?, frameEq, observationEq,
      produced]

/-- Every emitted descriptor carries the exact coordinate judgment and its geometry label is the
one forced by that judgment. -/
theorem ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?_sound
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedFourCoordinateSpatialGeometryObservation)
    (assignment : StereoAssignment)
    (produced :
      result.fourCoordinateSpatialGeometryAssignment? spatial record = some assignment) :
    ∃ frame observation,
      spatial.fourCoordinateFrame? record.center record.ligands = some frame ∧
      FourCoordinateSpatialPerception.Judgment frame observation ∧
      RedBookIR9.geometryOfFourCoordinateObservation observation =
        BlueBookP93.geometryOfProduction record.geometry ∧
      result.polyhedralGeometryObservationAssignment?
          (record.withRecognition observation) = some assignment := by
  obtain ⟨frame, observation, frameEq, judgment, publicProduced⟩ :=
    (result.fourCoordinateSpatialGeometryAssignment?_eq_some_iff
      spatial record assignment).mp produced
  obtain ⟨_, _, _, _, _, _, _, _, recognition, _⟩ :=
    result.polyhedralGeometryObservationAssignment?_sound_IR9
      (record.withRecognition observation) assignment publicProduced
  refine ⟨frame, observation, frameEq, judgment, ?_, publicProduced⟩
  simpa [RedBookIR9.GeometryRecognized,
    IndexedFourCoordinateSpatialGeometryObservation.withRecognition,
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?] using recognition

/-- Exact refusal occurs precisely when coordinate collection/perception fails or when the
already-certified molecule/CIP descriptor constructor refuses the computed branch. -/
theorem ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedFourCoordinateSpatialGeometryObservation) :
    result.fourCoordinateSpatialGeometryAssignment? spatial record = none ↔
      record.derivedRecord? spatial = none ∨
        ∃ derived, record.derivedRecord? spatial = some derived ∧
          result.polyhedralGeometryObservationAssignment? derived = none := by
  unfold ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?
  cases derivedEq : record.derivedRecord? spatial with
  | none => simp
  | some derived =>
      cases producedEq : result.polyhedralGeometryObservationAssignment? derived <;>
        simp [producedEq]

/-! ## Exact final assignments for each computed branch -/

theorem tetrahedronGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (priorities : List PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .tetrahedron ligands = some priorities) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .tetrahedron
          recognition := .fourCoordinate
            .donorsNoncoplanarCenterInsideDonorPolyhedron
          ligands := ligands
          configurationPositions := .noDistinguishedPositions
          absoluteOrientation := .none } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .tetrahedron
              configurationIndex := []
              absolute? := none } } := by
  simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
    IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
    RedBookIR9.geometryOfFourCoordinateObservation,
    RedBookIR9.ConfigurationPositionObservation.positionsFor?,
    RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
    BlueBookP93.geometryOfProduction,
    ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
    polyhedralConfigurationIndex?, PolyhedralGeometry.configurationIndexArity?,
    polyhedralConfigurationIndexOfEntries?, polyhedralAbsoluteConfiguration?]

theorem ChemistryNormalizationResult.fourCoordinateSpatial_squarePlanar_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat) (frame : FourCoordinateSpatialPerception.Frame)
    (priorities : List PolyhedralPriorityNumber)
    (transPosition : Nat) (transPriority : PolyhedralPriorityNumber)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (coplanar : frame.AllFiveCoplanar)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .squarePlanar ligands = some priorities)
    (lookup : priorities[transPosition]? = some transPriority) :
    result.fourCoordinateSpatialGeometryAssignment? spatial
        { center := center
          geometry := .squarePlanar
          ligands := ligands
          configurationPositions := .squarePlanar transPosition
          absoluteOrientation := .none } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .squarePlanar
              configurationIndex := [[transPriority]]
              absolute? := none } } := by
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .allFiveCoplanar :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame .allFiveCoplanar).mpr
      (.allFiveCoplanar coplanar)
  simp [ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?,
    IndexedFourCoordinateSpatialGeometryObservation.derivedRecord?, frameEq, observationEq,
    IndexedFourCoordinateSpatialGeometryObservation.withRecognition,
    squarePlanarGeometryObservationAssignment_exact result center ligands priorities
      transPosition transPriority priorityEq lookup]

theorem ChemistryNormalizationResult.fourCoordinateSpatial_squarePyramid4_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat) (frame : FourCoordinateSpatialPerception.Frame)
    (sense : PolyhedralRotationSense) (priorities : List PolyhedralPriorityNumber)
    (transPosition : Nat) (transPriority : PolyhedralPriorityNumber)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (displaced : frame.DonorsCoplanarCenterDisplaced)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .squarePyramid4 ligands = some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length)
    (lookup : priorities[transPosition]? = some transPriority) :
    result.fourCoordinateSpatialGeometryAssignment? spatial
        { center := center
          geometry := .squarePyramid4
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
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .donorsCoplanarCenterDisplaced :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame
      .donorsCoplanarCenterDisplaced).mpr
        (.donorsCoplanarCenterDisplaced displaced)
  simp [ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?,
    IndexedFourCoordinateSpatialGeometryObservation.derivedRecord?, frameEq, observationEq,
    IndexedFourCoordinateSpatialGeometryObservation.withRecognition,
    squarePyramid4GeometryObservationAssignment_exact result center ligands sense priorities
      transPosition transPriority priorityEq prioritiesDistinct lookup]

theorem ChemistryNormalizationResult.fourCoordinateSpatial_tetrahedron_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat) (frame : FourCoordinateSpatialPerception.Frame)
    (priorities : List PolyhedralPriorityNumber)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (inside : frame.CenterStrictlyInside)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .tetrahedron ligands = some priorities) :
    result.fourCoordinateSpatialGeometryAssignment? spatial
        { center := center
          geometry := .tetrahedron
          ligands := ligands
          configurationPositions := .noDistinguishedPositions
          absoluteOrientation := .none } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .tetrahedron
              configurationIndex := []
              absolute? := none } } := by
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .donorsNoncoplanarCenterInsideDonorPolyhedron :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame
      .donorsNoncoplanarCenterInsideDonorPolyhedron).mpr
        (.donorsNoncoplanarCenterInside
          (FourCoordinateSpatialPerception.Frame.centerStrictlyInside_donorVolume_ne inside)
          inside)
  simp [ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?,
    IndexedFourCoordinateSpatialGeometryObservation.derivedRecord?, frameEq, observationEq,
    IndexedFourCoordinateSpatialGeometryObservation.withRecognition,
    tetrahedronGeometryObservationAssignment_exact result center ligands priorities priorityEq]

theorem ChemistryNormalizationResult.fourCoordinateSpatial_seeSaw_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat) (frame : FourCoordinateSpatialPerception.Frame)
    (sense : PolyhedralRotationSense) (priorities : List PolyhedralPriorityNumber)
    (firstPosition secondPosition : Nat)
    (firstPriority secondPriority : PolyhedralPriorityNumber)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (outside : frame.CenterStrictlyOutside)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .seeSaw ligands = some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length)
    (positionsDistinct : [firstPosition, secondPosition].eraseDups.length = 2)
    (lookups : [firstPosition, secondPosition].mapM
        (fun position => priorities[position]?) = some [firstPriority, secondPriority]) :
    result.fourCoordinateSpatialGeometryAssignment? spatial
        { center := center
          geometry := .seeSaw
          ligands := ligands
          configurationPositions := .seeSaw firstPosition secondPosition
          absoluteOrientation := .seeSawAC (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .seeSaw
              configurationIndex := [seeSawConfigurationIndex firstPriority secondPriority]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .donorsNoncoplanarCenterOutsideDonorPolyhedron :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame
      .donorsNoncoplanarCenterOutsideDonorPolyhedron).mpr
        (.donorsNoncoplanarCenterOutside outside)
  simp [ChemistryNormalizationResult.fourCoordinateSpatialGeometryAssignment?,
    IndexedFourCoordinateSpatialGeometryObservation.derivedRecord?, frameEq, observationEq,
    IndexedFourCoordinateSpatialGeometryObservation.withRecognition,
    seeSawGeometryObservationAssignment_exact result center ligands sense priorities
      firstPosition secondPosition firstPriority secondPriority priorityEq prioritiesDistinct
      positionsDistinct lookups]

end TetraStereo.OneCenter
