import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance
import TetraStereo.OneCenter.IR9HigherCoordinationGeometryApplicabilityTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9

/-!
# Total typed ingress for the complete IR-9 geometry vocabulary

IR-9 provides explicit qualitative decision trees for coordination numbers two through four and
an explicit nearest-idealized judgment for higher coordination.  The functions below choose a
canonical witness of that source vocabulary for each of the 25 Table IR-9.2 geometries.  They do
not introduce a numerical distortion metric.
-/

/-- Canonical source-supported recognition evidence for each Table IR-9.2 geometry. -/
def canonicalGeometryRecognitionObservation : Geometry → GeometryRecognitionObservation
  | .linear => .twoCoordinate .linearDisposition
  | .angular => .twoCoordinate .bentDisposition
  | .trigonalPlanar => .threeCoordinate .centerCoplanarAnglesApproximatelyEqual
  | .trigonalPyramid => .threeCoordinate .centerSignificantlyOutOfDonorPlane
  | .tShape => .threeCoordinate .centerCoplanarOneAngleMuchLarger
  | .tetrahedron => .fourCoordinate .donorsNoncoplanarCenterInsideDonorPolyhedron
  | .squarePlanar => .fourCoordinate .allFiveCoplanar
  | .squarePyramid4 => .fourCoordinate .donorsCoplanarCenterDisplaced
  | .seeSaw => .fourCoordinate .donorsNoncoplanarCenterOutsideDonorPolyhedron
  | geometry => .higherCoordinationNearestIdealized geometry

/-- The canonical observation recognizes exactly the geometry from which it was constructed. -/
@[simp] theorem canonicalGeometryRecognitionObservation_recognized (geometry : Geometry) :
    GeometryRecognized (canonicalGeometryRecognitionObservation geometry) geometry := by
  cases geometry <;> rfl

/-- Source-level recognition evidence is surjective over the complete 25-geometry vocabulary. -/
theorem every_geometry_has_recognition_observation (geometry : Geometry) :
    ∃ observation, GeometryRecognized observation geometry :=
  ⟨canonicalGeometryRecognitionObservation geometry,
    canonicalGeometryRecognitionObservation_recognized geometry⟩

/-- Recognition evidence cannot entail two different geometry labels. -/
theorem geometryRecognition_functional
    (observation : GeometryRecognitionObservation) (left right : Geometry)
    (leftRecognized : GeometryRecognized observation left)
    (rightRecognized : GeometryRecognized observation right) :
    left = right := by
  unfold GeometryRecognized at leftRecognized rightRecognized
  rw [leftRecognized] at rightRecognized
  exact Option.some.inj rightRecognized

namespace ConfigurationPositionObservation

/-- Geometry-only compatibility of a typed position observation.  The shared
`noDistinguishedPositions` constructor is valid exactly for the five geometries whose relative
index consumes no distinguished positions. -/
def GeometryCompatible
    (observation : ConfigurationPositionObservation) (geometry : Geometry) : Prop :=
  match observation, geometry with
  | .noDistinguishedPositions, .linear
  | .noDistinguishedPositions, .angular
  | .noDistinguishedPositions, .trigonalPlanar
  | .noDistinguishedPositions, .trigonalPyramid
  | .noDistinguishedPositions, .tetrahedron
  | .tShape _, .tShape
  | .squarePlanar _, .squarePlanar
  | .squarePyramid4 _, .squarePyramid4
  | .seeSaw _ _, .seeSaw
  | .trigonalBipyramid _ _, .trigonalBipyramid
  | .squarePyramid _ _, .squarePyramid
  | .octahedron _ _, .octahedron
  | .trigonalPrism _ _, .trigonalPrism
  | .faceMonocappedOctahedron _ _ _, .faceMonocappedOctahedron
  | .squareFaceMonocappedTrigonalPrism _ _ _, .squareFaceMonocappedTrigonalPrism
  | .cube _ _ _ _ _ _ _ _, .cube
  | .squareAntiprism _ _ _ _ _ _ _ _, .squareAntiprism
  | .dodecahedron _ _ _ _ _ _ _ _, .dodecahedron
  | .transBicappedOctahedron _ _ _ _ _ _ _ _, .transBicappedOctahedron
  | .triangularFaceBicappedTrigonalPrism _ _ _ _ _ _ _ _,
      .triangularFaceBicappedTrigonalPrism
  | .squareFaceBicappedTrigonalPrism _ _ _ _ _ _ _ _,
      .squareFaceBicappedTrigonalPrism
  | .squareFaceTricappedTrigonalPrism _ _ _ _ _ _ _ _ _,
      .squareFaceTricappedTrigonalPrism
  | .pentagonalBipyramid _ _ _, .pentagonalBipyramid
  | .hexagonalBipyramid _ _ _, .hexagonalBipyramid
  | .heptagonalBipyramid _ _ _, .heptagonalBipyramid => True
  | _, _ => False

/-- Structural shape checks performed by `positionsFor?` itself.  Final uniqueness, bounds, and
geometry-specific arity remain the responsibility of `polyhedralConfigurationIndex?`. -/
def WellShaped : ConfigurationPositionObservation → Prop
  | .trigonalPrism firstFace secondFace =>
      firstFace.length = 3 ∧ secondFace.length = 3
  | .faceMonocappedOctahedron _ cappedFace oppositeFace =>
      cappedFace.length = 3 ∧ oppositeFace.length = 3
  | .squareFaceMonocappedTrigonalPrism _ firstFace secondFace =>
      firstFace.length = 3 ∧ secondFace.length = 3
  | _ => True

/-- Exact typed-router boundary: a position observation succeeds precisely when its constructor
belongs to the requested geometry and its internally variable faces satisfy the router's shape
checks.  In particular, every wrong-geometry pairing is rejected. -/
theorem positionsFor?_isSome_iff_compatible_and_wellShaped
    (observation : ConfigurationPositionObservation) (geometry : Geometry) :
    (observation.positionsFor? geometry).isSome = true ↔
      GeometryCompatible observation geometry ∧ WellShaped observation := by
  cases observation <;> cases geometry <;>
    simp [ConfigurationPositionObservation.positionsFor?, GeometryCompatible, WellShaped]

end ConfigurationPositionObservation

/-- One canonical, duplicate-free distinguished-position observation for every geometry. -/
def canonicalConfigurationPositionObservation : Geometry → ConfigurationPositionObservation
  | .linear | .angular | .trigonalPlanar | .trigonalPyramid | .tetrahedron =>
      .noDistinguishedPositions
  | .tShape => .tShape 0
  | .squarePlanar => .squarePlanar 0
  | .squarePyramid4 => .squarePyramid4 0
  | .seeSaw => .seeSaw 0 1
  | .trigonalBipyramid => .trigonalBipyramid 0 1
  | .squarePyramid => .squarePyramid 0 1
  | .octahedron => .octahedron 0 1
  | .trigonalPrism => .trigonalPrism [0, 1, 2] [3, 4, 5]
  | .pentagonalBipyramid => .pentagonalBipyramid 0 1 [2, 3, 4, 5, 6]
  | .faceMonocappedOctahedron =>
      .faceMonocappedOctahedron 0 [1, 2, 3] [4, 5, 6]
  | .squareFaceMonocappedTrigonalPrism =>
      .squareFaceMonocappedTrigonalPrism 0 [1, 2, 3] [4, 5, 6]
  | .cube => .cube 0 1 2 3 4 5 6 7
  | .squareAntiprism => .squareAntiprism 0 1 2 3 4 5 6 7
  | .dodecahedron => .dodecahedron 0 1 2 3 4 5 6 7
  | .hexagonalBipyramid => .hexagonalBipyramid 0 1 [2, 3, 4, 5, 6, 7]
  | .transBicappedOctahedron => .transBicappedOctahedron 0 1 2 3 4 5 6 7
  | .triangularFaceBicappedTrigonalPrism =>
      .triangularFaceBicappedTrigonalPrism 0 1 2 3 4 5 6 7
  | .squareFaceBicappedTrigonalPrism =>
      .squareFaceBicappedTrigonalPrism 0 1 2 3 4 5 6 7
  | .squareFaceTricappedTrigonalPrism =>
      .squareFaceTricappedTrigonalPrism 0 1 2 3 4 5 6 7 8
  | .heptagonalBipyramid => .heptagonalBipyramid 0 1 [2, 3, 4, 5, 6, 7, 8]

/-- The canonical typed observation succeeds for every geometry and returns the consecutive
distinguished positions expected by its complete index constructor. -/
@[simp] theorem canonicalConfigurationPositionObservation_positionsFor
    (geometry : Geometry) :
    (canonicalConfigurationPositionObservation geometry).positionsFor? geometry =
      some (List.range (match geometry with
        | .linear | .angular | .trigonalPlanar | .trigonalPyramid | .tetrahedron => 0
        | .tShape | .squarePlanar | .squarePyramid4 => 1
        | .seeSaw | .trigonalBipyramid | .squarePyramid | .octahedron => 2
        | .trigonalPrism => 6
        | .pentagonalBipyramid | .faceMonocappedOctahedron
        | .squareFaceMonocappedTrigonalPrism => 7
        | .cube | .squareAntiprism | .dodecahedron | .hexagonalBipyramid
        | .transBicappedOctahedron | .triangularFaceBicappedTrigonalPrism
        | .squareFaceBicappedTrigonalPrism => 8
        | .squareFaceTricappedTrigonalPrism | .heptagonalBipyramid => 9)) := by
  cases geometry <;> decide

/-- Typed position evidence is total over the complete 25-geometry vocabulary. -/
theorem every_geometry_has_configuration_position_observation (geometry : Geometry) :
    ∃ (observation : ConfigurationPositionObservation) (positions : List Nat),
      observation.positionsFor? geometry = some positions :=
  ⟨canonicalConfigurationPositionObservation geometry, _,
    canonicalConfigurationPositionObservation_positionsFor geometry⟩

end TetraStereo.OneCenter.RedBookIR9

namespace TetraStereo.OneCenter

namespace PolyhedralGeometry

/-- Every production geometry now has a complete configuration-index arity. -/
@[simp] theorem configurationIndexArity?_isSome (geometry : PolyhedralGeometry) :
    geometry.configurationIndexArity?.isSome = true := by
  cases geometry <;> rfl

/-- The 25 normative geometry symbols render without aliases. -/
theorem symbol_injective : Function.Injective PolyhedralGeometry.symbol := by
  intro left right same
  cases left <;> cases right <;> simp_all [PolyhedralGeometry.symbol]

theorem all_symbols_nodup :
    (PolyhedralGeometry.all.map PolyhedralGeometry.symbol).Nodup := by
  decide

end PolyhedralGeometry

namespace BlueBookP93.Geometry

/-- The independent P-93/IR-9 geometry vocabulary likewise has no symbol aliases. -/
theorem symbol_injective : Function.Injective BlueBookP93.Geometry.symbol := by
  intro left right same
  cases left <;> cases right <;> simp_all [BlueBookP93.Geometry.symbol]

end BlueBookP93.Geometry

namespace BlueBookP93

/-- The production-to-independent geometry bridge neither merges nor loses geometry labels. -/
theorem geometryOfProduction_injective : Function.Injective geometryOfProduction := by
  intro left right same
  cases left <;> cases right <;> simp_all [geometryOfProduction]

end BlueBookP93

end TetraStereo.OneCenter
