import TetraStereo.OneCenter.PolyhedralConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent Red Book IR-9.3 semantics

This module transcribes the general semantics of Red Book IR-9.3 independently of coordinate
perception and of the production descriptor renderer.  In particular, it does not assume that a
list of priority numbers has already been put in the right polyhedral positions.  It records:

* the three factors required to describe a coordination entity;
* the source's exhaustive idealized-geometry vocabulary and its explicit three- and
  four-coordinate recognition decision trees;
* the relative-configuration index constructions;
* the distinct `R/S`, `C/A`, and skew-lines absolute-configuration conventions; and
* donor-atom priority numbering and the polydentate-ligand priming convention.

Words such as “close to a plane” and “significantly displaced” require experimental or coordinate
evidence.  The corresponding observations below are therefore inputs to the normative relation;
they are not silently replaced with implementation-specific numerical tolerances.
-/

namespace RedBookIR9



/-- Clause-level IR-9.3 provisions mirrored by the global normative manifest. -/
inductive Provision where
  | polyhedralConfiguration
  | configurationIntroduction
  | polyhedralSymbols
  | geometryChoice
  | diastereoisomerGeneral
  | configurationIndex
  | squarePlanar
  | octahedral
  | squarePyramidal
  | bipyramidal
  | tShape
  | seeSaw
  | absoluteConfigurationGeneral
  | rsTetrahedral
  | rsTrigonalPyramidal
  | caPolyhedral
  | caTrigonalBipyramidal
  | caSquarePyramidal
  | caSeeSaw
  | caOctahedral
  | caTrigonalPrismatic
  | caOtherBipyramidal
  | skewLines
  | skewLinesTrisBidentate
  | skewLinesBisBidentate
  | skewLinesChelateConformations
  | ligandPriorityGeneral
  | priorityNumbers
  | primingConvention
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .polyhedralConfiguration
  , .configurationIntroduction
  , .polyhedralSymbols
  , .geometryChoice
  , .diastereoisomerGeneral
  , .configurationIndex
  , .squarePlanar
  , .octahedral
  , .squarePyramidal
  , .bipyramidal
  , .tShape
  , .seeSaw
  , .absoluteConfigurationGeneral
  , .rsTetrahedral
  , .rsTrigonalPyramidal
  , .caPolyhedral
  , .caTrigonalBipyramidal
  , .caSquarePyramidal
  , .caSeeSaw
  , .caOctahedral
  , .caTrigonalPrismatic
  , .caOtherBipyramidal
  , .skewLines
  , .skewLinesTrisBidentate
  , .skewLinesBisBidentate
  , .skewLinesChelateConformations
  , .ligandPriorityGeneral
  , .priorityNumbers
  , .primingConvention
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_length : all.length = 29 := by
  decide

def sourceSection : Provision → String
  | .polyhedralConfiguration => "IR-9.3"
  | .configurationIntroduction => "IR-9.3.1"
  | .polyhedralSymbols => "IR-9.3.2.1/Tables IR-9.2--IR-9.3"
  | .geometryChoice => "IR-9.3.2.2"
  | .diastereoisomerGeneral => "IR-9.3.3.1"
  | .configurationIndex => "IR-9.3.3.2"
  | .squarePlanar => "IR-9.3.3.3"
  | .octahedral => "IR-9.3.3.4"
  | .squarePyramidal => "IR-9.3.3.5"
  | .bipyramidal => "IR-9.3.3.6"
  | .tShape => "IR-9.3.3.7"
  | .seeSaw => "IR-9.3.3.8"
  | .absoluteConfigurationGeneral => "IR-9.3.4.1"
  | .rsTetrahedral => "IR-9.3.4.2"
  | .rsTrigonalPyramidal => "IR-9.3.4.3"
  | .caPolyhedral => "IR-9.3.4.4"
  | .caTrigonalBipyramidal => "IR-9.3.4.5"
  | .caSquarePyramidal => "IR-9.3.4.6"
  | .caSeeSaw => "IR-9.3.4.7"
  | .caOctahedral => "IR-9.3.4.8"
  | .caTrigonalPrismatic => "IR-9.3.4.9"
  | .caOtherBipyramidal => "IR-9.3.4.10"
  | .skewLines => "IR-9.3.4.11"
  | .skewLinesTrisBidentate => "IR-9.3.4.12"
  | .skewLinesBisBidentate => "IR-9.3.4.13"
  | .skewLinesChelateConformations => "IR-9.3.4.14"
  | .ligandPriorityGeneral => "IR-9.3.5.1"
  | .priorityNumbers => "IR-9.3.5.2"
  | .primingConvention => "IR-9.3.5.3"

end Provision

/-! ## Configuration and stereoisomer foundations -/

inductive ConfigurationFactor where
  | coordinationGeometry
  | relativeConfiguration
  | absoluteConfiguration
  deriving DecidableEq, Repr

namespace ConfigurationFactor

def all : List ConfigurationFactor :=
  [ .coordinationGeometry, .relativeConfiguration, .absoluteConfiguration ]

@[simp] theorem mem_all (factor : ConfigurationFactor) : factor ∈ all := by
  cases factor <;> simp [all]

theorem all_nodup : all.Nodup := by
  decide

end ConfigurationFactor

/-- IR-9.3.1 requires all three factors only when distinct enantiomers exist. -/
def requiredFactors (hasNonsuperimposableMirror : Bool) : List ConfigurationFactor :=
  if hasNonsuperimposableMirror then ConfigurationFactor.all
  else [.coordinationGeometry, .relativeConfiguration]

@[simp] theorem requiredFactors_chiral :
    requiredFactors true = ConfigurationFactor.all :=
  rfl

@[simp] theorem requiredFactors_achiral :
    requiredFactors false = [.coordinationGeometry, .relativeConfiguration] :=
  rfl

/-- Evidence relevant to the Red Book distinction between enantiomers and diastereoisomers. -/
structure StereoisomerObservation where
  sameConstitution : Prop
  spatialDistributionsDiffer : Prop
  mirrorImages : Prop
  superimposable : Prop

def Enantiomeric (observation : StereoisomerObservation) : Prop :=
  observation.sameConstitution ∧ observation.spatialDistributionsDiffer ∧
    observation.mirrorImages ∧ ¬observation.superimposable

def Diastereomeric (observation : StereoisomerObservation) : Prop :=
  observation.sameConstitution ∧ observation.spatialDistributionsDiffer ∧
    ¬observation.mirrorImages

theorem enantiomeric_not_diastereomeric (observation : StereoisomerObservation) :
    Enantiomeric observation → ¬Diastereomeric observation := by
  rintro ⟨_, _, mirror, _⟩ ⟨_, _, notMirror⟩
  exact notMirror mirror

/-! ## Idealized geometry vocabulary and recognition -/

abbrev Geometry := BlueBookP93.Geometry

/-- Red Book Table IR-9.2, transcribed independently of the executable geometry enum. -/
def allGeometries : List Geometry :=
  [ .linear, .angular
  , .trigonalPlanar, .trigonalPyramid, .tShape
  , .tetrahedron, .squarePlanar, .squarePyramid4, .seeSaw
  , .trigonalBipyramid, .squarePyramid
  , .octahedron, .trigonalPrism
  , .pentagonalBipyramid, .faceMonocappedOctahedron, .squareFaceMonocappedTrigonalPrism
  , .cube, .squareAntiprism, .dodecahedron, .hexagonalBipyramid
  , .transBicappedOctahedron, .triangularFaceBicappedTrigonalPrism
  , .squareFaceBicappedTrigonalPrism
  , .squareFaceTricappedTrigonalPrism, .heptagonalBipyramid
  ]

@[simp] theorem geometry_mem_all (geometry : Geometry) : geometry ∈ allGeometries := by
  cases geometry <;> simp [allGeometries]

theorem allGeometries_nodup : allGeometries.Nodup := by
  decide

@[simp] theorem allGeometries_length : allGeometries.length = 25 := by
  decide

/-- Qualitative observations in the explicit IR-9.3.2.2 four-coordinate decision tree. -/
inductive FourCoordinateObservation where
  | allFiveCoplanar
  | donorsCoplanarCenterDisplaced
  | donorsNoncoplanarCenterInsideDonorPolyhedron
  | donorsNoncoplanarCenterOutsideDonorPolyhedron
  deriving DecidableEq, Repr

def geometryOfFourCoordinateObservation : FourCoordinateObservation → Geometry
  | .allFiveCoplanar => .squarePlanar
  | .donorsCoplanarCenterDisplaced => .squarePyramid4
  | .donorsNoncoplanarCenterInsideDonorPolyhedron => .tetrahedron
  | .donorsNoncoplanarCenterOutsideDonorPolyhedron => .seeSaw

theorem fourCoordinateGeometry_injective :
    Function.Injective geometryOfFourCoordinateObservation := by
  intro left right same
  cases left <;> cases right <;> simp_all [geometryOfFourCoordinateObservation]

/-- Qualitative observations in the explicit IR-9.3.2.2 three-coordinate decision tree. -/
inductive ThreeCoordinateObservation where
  | centerCoplanarAnglesApproximatelyEqual
  | centerCoplanarOneAngleMuchLarger
  | centerSignificantlyOutOfDonorPlane
  deriving DecidableEq, Repr

def geometryOfThreeCoordinateObservation : ThreeCoordinateObservation → Geometry
  | .centerCoplanarAnglesApproximatelyEqual => .trigonalPlanar
  | .centerCoplanarOneAngleMuchLarger => .tShape
  | .centerSignificantlyOutOfDonorPlane => .trigonalPyramid

theorem threeCoordinateGeometry_injective :
    Function.Injective geometryOfThreeCoordinateObservation := by
  intro left right same
  cases left <;> cases right <;> simp_all [geometryOfThreeCoordinateObservation]

/-- Qualitative two-coordinate choice stated in IR-9.3.2.1. -/
inductive TwoCoordinateObservation where
  | linearDisposition
  | bentDisposition
  deriving DecidableEq, Repr

def geometryOfTwoCoordinateObservation : TwoCoordinateObservation → Geometry
  | .linearDisposition => .linear
  | .bentDisposition => .angular

/-- Complete typed geometry-recognition evidence supported by IR-9.3.2.  Three- and
four-coordinate choices use the source's explicit qualitative decision trees.  For coordination
numbers 5--9 the source specifies selection of the nearest idealized geometry but supplies no
universal numerical distance or distortion threshold; that experimental/modeling judgment is
therefore represented explicitly and admitted only for a Table IR-9.2 geometry of coordination at
least five. -/
inductive GeometryRecognitionObservation where
  | twoCoordinate (observation : TwoCoordinateObservation)
  | threeCoordinate (observation : ThreeCoordinateObservation)
  | fourCoordinate (observation : FourCoordinateObservation)
  | higherCoordinationNearestIdealized (geometry : Geometry)
  deriving DecidableEq, Repr

/-- Geometry entailed by one IR-9.3.2 observation. -/
def GeometryRecognitionObservation.recognizedGeometry? :
    GeometryRecognitionObservation → Option Geometry
  | .twoCoordinate observation => some (geometryOfTwoCoordinateObservation observation)
  | .threeCoordinate observation => some (geometryOfThreeCoordinateObservation observation)
  | .fourCoordinate observation => some (geometryOfFourCoordinateObservation observation)
  | .higherCoordinationNearestIdealized geometry =>
      if 5 ≤ geometry.coordinationNumber then some geometry else none

/-- Independent source relation between qualitative geometry evidence and the resulting
polyhedral geometry. -/
def GeometryRecognized
    (observation : GeometryRecognitionObservation) (geometry : Geometry) : Prop :=
  observation.recognizedGeometry? = some geometry

@[simp] theorem twoCoordinate_recognized
    (observation : TwoCoordinateObservation) :
    GeometryRecognized (.twoCoordinate observation)
      (geometryOfTwoCoordinateObservation observation) := by
  cases observation <;> rfl

@[simp] theorem threeCoordinate_recognized
    (observation : ThreeCoordinateObservation) :
    GeometryRecognized (.threeCoordinate observation)
      (geometryOfThreeCoordinateObservation observation) := by
  cases observation <;> rfl

@[simp] theorem fourCoordinate_recognized
    (observation : FourCoordinateObservation) :
    GeometryRecognized (.fourCoordinate observation)
      (geometryOfFourCoordinateObservation observation) := by
  cases observation <;> rfl

/-- The polyhedral symbol is assigned before relative or absolute spatial features. -/
def factorPrecedes (left right : ConfigurationFactor) : Prop :=
  match left, right with
  | .coordinationGeometry, .relativeConfiguration
  | .coordinationGeometry, .absoluteConfiguration
  | .relativeConfiguration, .absoluteConfiguration => True
  | _, _ => False

@[simp] theorem geometry_precedes_relative :
    factorPrecedes .coordinationGeometry .relativeConfiguration :=
  trivial

@[simp] theorem geometry_precedes_absolute :
    factorPrecedes .coordinationGeometry .absoluteConfiguration :=
  trivial

/-! ## Relative configuration and configuration indices -/

abbrev PriorityNumber := BlueBookP93.PriorityNumber

inductive FormulaPattern where
  | Ma2b2
  | Ma2b4
  | Ma3b3
  | Ma2bc
  | other
  deriving DecidableEq, Repr

inductive TraditionalRelativeTerm where
  | cis
  | trans
  | fac
  | mer
  deriving DecidableEq, Repr

/-- Exact recommended scope of the simple `cis/trans/fac/mer` terms stated in IR-9.3.3.1,
IR-9.3.3.3, and IR-9.3.3.4.  The possible `SP-4 Ma2bc` extension is not recommended. -/
def traditionalTermApplicable
    (geometry : Geometry) (pattern : FormulaPattern) (term : TraditionalRelativeTerm) : Prop :=
  match geometry, pattern, term with
  | .squarePlanar, .Ma2b2, .cis | .squarePlanar, .Ma2b2, .trans => True
  | .octahedron, .Ma2b4, .cis | .octahedron, .Ma2b4, .trans => True
  | .octahedron, .Ma3b3, .fac | .octahedron, .Ma3b3, .mer => True
  | _, _, _ => False

@[simp] theorem squarePlanar_Ma2bc_not_recommended (term : TraditionalRelativeTerm) :
    ¬traditionalTermApplicable .squarePlanar .Ma2bc term := by
  cases term <;> simp [traditionalTermApplicable]

inductive BipyramidKind where
  | trigonal5
  | pentagonal7
  | hexagonal8
  | heptagonal9
  deriving DecidableEq, Repr

def BipyramidKind.geometry : BipyramidKind → Geometry
  | .trigonal5 => .trigonalBipyramid
  | .pentagonal7 => .pentagonalBipyramid
  | .hexagonal8 => .hexagonalBipyramid
  | .heptagonal9 => .heptagonalBipyramid

/-- Geometry-specific evidence from which IR-9.3.3 constructs a configuration index. -/
inductive ConfigurationIndexInput where
  | squarePlanar (transToPriorityOne : PriorityNumber)
  | octahedral (transToPriorityOne transToSeniorPerpendicular : PriorityNumber)
  | squarePyramid4 (transToSeniorBase : PriorityNumber)
  | squarePyramid5 (apical transToSeniorBase : PriorityNumber)
  | bipyramidal (kind : BipyramidKind) (firstAxial secondAxial : PriorityNumber)
      (perpendicularCycle : List PriorityNumber)
  | tShape (stem : PriorityNumber)
  | seeSaw (firstLargestAngle secondLargestAngle : PriorityNumber)
  | trigonalPrism (firstFace secondFace : List PriorityNumber)
  deriving DecidableEq, Repr

/-- Typed positional evidence used before donor priorities are known.  Constructor names carry the
exact geometry-specific spatial role prescribed by IR-9.3.3; there is no generic untyped position
list which could silently be interpreted under the wrong geometry. -/
inductive ConfigurationPositionObservation where
  | noDistinguishedPositions
  | tShape (stem : Nat)
  | squarePlanar (transToPriorityOne : Nat)
  | squarePyramid4 (transToSeniorBase : Nat)
  | seeSaw (firstLargestAngle secondLargestAngle : Nat)
  | trigonalBipyramid (firstAxial secondAxial : Nat)
  | squarePyramid (apical transToSeniorBase : Nat)
  | octahedron (transToPriorityOne transToSeniorPerpendicular : Nat)
  | trigonalPrism (firstFace secondFace : List Nat)
  | faceMonocappedOctahedron (cap : Nat) (cappedFace oppositeFace : List Nat)
  | squareFaceMonocappedTrigonalPrism (cap : Nat) (firstFace secondFace : List Nat)
  | cube (v000 v001 v010 v011 v100 v101 v110 v111 : Nat)
  | squareAntiprism (v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
  | dodecahedron (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
  | transBicappedOctahedron (cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2 : Nat)
  | triangularFaceBicappedTrigonalPrism
      (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : Nat)
  | squareFaceBicappedTrigonalPrism
      (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : Nat)
  | squareFaceTricappedTrigonalPrism
      (cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : Nat)
  | pentagonalBipyramid (firstAxial secondAxial : Nat) (perpendicularCycle : List Nat)
  | hexagonalBipyramid (firstAxial secondAxial : Nat) (perpendicularCycle : List Nat)
  | heptagonalBipyramid (firstAxial secondAxial : Nat) (perpendicularCycle : List Nat)
  deriving DecidableEq, Repr

/-- Exact IR-9 geometry domain and flattened positional order of a typed observation.  The
geometry-specific router performs bounds, uniqueness, and final arity checks after this step. -/
def ConfigurationPositionObservation.positionsFor?
    (observation : ConfigurationPositionObservation) (geometry : Geometry) :
    Option (List Nat) :=
  match observation, geometry with
  | .noDistinguishedPositions, .linear
  | .noDistinguishedPositions, .angular
  | .noDistinguishedPositions, .trigonalPlanar
  | .noDistinguishedPositions, .trigonalPyramid
  | .noDistinguishedPositions, .tetrahedron => some []
  | .tShape stem, .tShape => some [stem]
  | .squarePlanar transToOne, .squarePlanar => some [transToOne]
  | .squarePyramid4 transToSenior, .squarePyramid4 => some [transToSenior]
  | .seeSaw first second, .seeSaw => some [first, second]
  | .trigonalBipyramid first second, .trigonalBipyramid => some [first, second]
  | .squarePyramid apical transToSenior, .squarePyramid =>
      some [apical, transToSenior]
  | .octahedron transToOne transToSeniorPlane, .octahedron =>
      some [transToOne, transToSeniorPlane]
  | .trigonalPrism firstFace secondFace, .trigonalPrism =>
      if firstFace.length != 3 || secondFace.length != 3 then none
      else some (firstFace ++ secondFace)
  | .faceMonocappedOctahedron cap cappedFace oppositeFace, .faceMonocappedOctahedron =>
      if cappedFace.length != 3 || oppositeFace.length != 3 then none
      else some (cap :: (cappedFace ++ oppositeFace))
  | .squareFaceMonocappedTrigonalPrism cap firstFace secondFace,
      .squareFaceMonocappedTrigonalPrism =>
      if firstFace.length != 3 || secondFace.length != 3 then none
      else some (cap :: (firstFace ++ secondFace))
  | .cube v000 v001 v010 v011 v100 v101 v110 v111, .cube =>
      some [v000, v001, v010, v011, v100, v101, v110, v111]
  | .squareAntiprism v0 v1 v2 v3 v4 v5 v6 v7, .squareAntiprism =>
      some [v0, v1, v2, v3, v4, v5, v6, v7]
  | .dodecahedron a0 a1 a2 a3 b0 b1 b2 b3, .dodecahedron =>
      some [a0, a1, a2, a3, b0, b1, b2, b3]
  | .transBicappedOctahedron cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2,
      .transBicappedOctahedron =>
      some [cap0, cap1, s0p0, s0p1, s0p2, s1p0, s1p1, s1p2]
  | .triangularFaceBicappedTrigonalPrism cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2,
      .triangularFaceBicappedTrigonalPrism =>
      some [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2]
  | .squareFaceBicappedTrigonalPrism cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2,
      .squareFaceBicappedTrigonalPrism =>
      some [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2]
  | .squareFaceTricappedTrigonalPrism cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2,
      .squareFaceTricappedTrigonalPrism =>
      some [cap0, cap1, cap2, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2]
  | .pentagonalBipyramid first second cycle, .pentagonalBipyramid =>
      some (first :: second :: cycle)
  | .hexagonalBipyramid first second cycle, .hexagonalBipyramid =>
      some (first :: second :: cycle)
  | .heptagonalBipyramid first second cycle, .heptagonalBipyramid =>
      some (first :: second :: cycle)
  | _, _ => none

/-- Independent relation between typed spatial-role evidence, geometry, and the position sequence
consumed by configuration-index construction. -/
def ConfigurationPositionsRecognized
    (observation : ConfigurationPositionObservation) (geometry : Geometry)
    (positions : List Nat) : Prop :=
  observation.positionsFor? geometry = some positions

/-- Exact TPR-6 face-shape boundary: a trigonal-prism position observation is recognized exactly
when it supplies two triangular (three-position) faces, and the routed order is their
corresponding-vertex concatenation. -/
theorem trigonalPrism_positionsFor?_eq_some_iff
    (firstFace secondFace positions : List Nat) :
    (ConfigurationPositionObservation.trigonalPrism firstFace secondFace).positionsFor?
        .trigonalPrism = some positions ↔
      firstFace.length = 3 ∧ secondFace.length = 3 ∧
        positions = firstFace ++ secondFace := by
  by_cases firstIsTriangle : firstFace.length = 3
  · by_cases secondIsTriangle : secondFace.length = 3
    · simp [ConfigurationPositionObservation.positionsFor?, firstIsTriangle,
        secondIsTriangle]
      constructor <;> intro same <;> exact same.symm
    · simp [ConfigurationPositionObservation.positionsFor?, firstIsTriangle,
        secondIsTriangle]
  · simp [ConfigurationPositionObservation.positionsFor?, firstIsTriangle]

/-- Exact OCF-7 role-shape boundary: the cap and two typed triangular faces route to all seven
positions exactly when both face observations contain three positions. -/
theorem faceMonocappedOctahedron_positionsFor?_eq_some_iff
    (cap : Nat) (cappedFace oppositeFace positions : List Nat) :
    (ConfigurationPositionObservation.faceMonocappedOctahedron
        cap cappedFace oppositeFace).positionsFor? .faceMonocappedOctahedron =
        some positions ↔
      cappedFace.length = 3 ∧ oppositeFace.length = 3 ∧
        positions = cap :: (cappedFace ++ oppositeFace) := by
  by_cases cappedIsTriangle : cappedFace.length = 3
  · by_cases oppositeIsTriangle : oppositeFace.length = 3
    · simp [ConfigurationPositionObservation.positionsFor?, cappedIsTriangle,
        oppositeIsTriangle]
      constructor <;> intro same <;> exact same.symm
    · simp [ConfigurationPositionObservation.positionsFor?, cappedIsTriangle,
        oppositeIsTriangle]
  · simp [ConfigurationPositionObservation.positionsFor?, cappedIsTriangle]

/-- Exact TPRS-7 role-shape boundary: the cap and two triangular prism faces route to all seven
positions exactly when both face observations contain three positions. -/
theorem squareFaceMonocappedTrigonalPrism_positionsFor?_eq_some_iff
    (cap : Nat) (firstFace secondFace positions : List Nat) :
    (ConfigurationPositionObservation.squareFaceMonocappedTrigonalPrism
        cap firstFace secondFace).positionsFor? .squareFaceMonocappedTrigonalPrism =
        some positions ↔
      firstFace.length = 3 ∧ secondFace.length = 3 ∧
        positions = cap :: (firstFace ++ secondFace) := by
  by_cases firstIsTriangle : firstFace.length = 3
  · by_cases secondIsTriangle : secondFace.length = 3
    · simp [ConfigurationPositionObservation.positionsFor?, firstIsTriangle,
        secondIsTriangle]
      constructor <;> intro same <;> exact same.symm
    · simp [ConfigurationPositionObservation.positionsFor?, firstIsTriangle,
        secondIsTriangle]
  · simp [ConfigurationPositionObservation.positionsFor?, firstIsTriangle]

/-- Exact CU-8 role routing in lexicographic binary-coordinate order. -/
@[simp] theorem cube_positionsFor?_exact
    (v000 v001 v010 v011 v100 v101 v110 v111 : Nat) :
    (ConfigurationPositionObservation.cube
        v000 v001 v010 v011 v100 v101 v110 v111).positionsFor? .cube =
      some [v000, v001, v010, v011, v100, v101, v110, v111] :=
  rfl

/-- Exact SAPR-8 role routing in alternating-rim cyclic order. -/
@[simp] theorem squareAntiprism_positionsFor?_exact
    (v0 v1 v2 v3 v4 v5 v6 v7 : Nat) :
    (ConfigurationPositionObservation.squareAntiprism
        v0 v1 v2 v3 v4 v5 v6 v7).positionsFor? .squareAntiprism =
      some [v0, v1, v2, v3, v4, v5, v6, v7] :=
  rfl

/-- Exact DD-8 role routing with the two four-position A/B families kept distinct. -/
@[simp] theorem dodecahedron_positionsFor?_exact
    (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    (ConfigurationPositionObservation.dodecahedron
        a0 a1 a2 a3 b0 b1 b2 b3).positionsFor? .dodecahedron =
      some [a0, a1, a2, a3, b0, b1, b2, b3] :=
  rfl

/-- Exact OCT-8 role routing: opposite caps, then each cap-incident three-vertex face. -/
@[simp] theorem transBicappedOctahedron_positionsFor?_exact
    (cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2 : Nat) :
    (ConfigurationPositionObservation.transBicappedOctahedron
        cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2).positionsFor?
        .transBicappedOctahedron =
      some [cap0, cap1, s0p0, s0p1, s0p2, s1p0, s1p1, s1p2] :=
  rfl

/-- Exact TPRT-8 role routing: two triangular-face caps followed by the two corresponding
three-corner faces. -/
@[simp] theorem triangularFaceBicappedTrigonalPrism_positionsFor?_exact
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : Nat) :
    (ConfigurationPositionObservation.triangularFaceBicappedTrigonalPrism
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2).positionsFor?
        .triangularFaceBicappedTrigonalPrism =
      some [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] :=
  rfl

/-- Exact TPRS-8 role routing: the two selected-face caps followed by the two triangular-face
triples. -/
@[simp] theorem squareFaceBicappedTrigonalPrism_positionsFor?_exact
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : Nat) :
    (ConfigurationPositionObservation.squareFaceBicappedTrigonalPrism
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2).positionsFor?
        .squareFaceBicappedTrigonalPrism =
      some [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] :=
  rfl

/-- Exact TPRS-9 role routing: the three square-face caps followed by the two triangular-face
triples. -/
@[simp] theorem squareFaceTricappedTrigonalPrism_positionsFor?_exact
    (cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : Nat) :
    (ConfigurationPositionObservation.squareFaceTricappedTrigonalPrism
        cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2).positionsFor?
        .squareFaceTricappedTrigonalPrism =
      some [cap0, cap1, cap2, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] :=
  rfl

/-- Typed absolute-orientation observation for the currently implemented IR-9.3.4 conventions.
Each constructor fixes both the geometry and whether the observation is interpreted by the
trigonal-pyramidal `R/S` construction or a polyhedral `A/C` construction. -/
inductive AbsoluteOrientationObservation where
  | none
  | trigonalPyramidRS (sense : BlueBookP93.RotationSense)
  | seeSawAC (sense : BlueBookP93.RotationSense)
  | trigonalBipyramidAC (sense : BlueBookP93.RotationSense)
  | squarePyramid4AC (sense : BlueBookP93.RotationSense)
  | squarePyramidAC (sense : BlueBookP93.RotationSense)
  | octahedronAC (sense : BlueBookP93.RotationSense)
  | trigonalPrismAC (sense : BlueBookP93.RotationSense)
  | pentagonalBipyramidAC (sense : BlueBookP93.RotationSense)
  | hexagonalBipyramidAC (sense : BlueBookP93.RotationSense)
  | heptagonalBipyramidAC (sense : BlueBookP93.RotationSense)
  deriving DecidableEq, Repr

/-- Geometry check and independent rotation sense entailed by a typed absolute observation. -/
def AbsoluteOrientationObservation.rotationFor?
    (observation : AbsoluteOrientationObservation) (geometry : Geometry) :
    Option (Option BlueBookP93.RotationSense) :=
  match observation, geometry with
  | .none, _ => some (Option.none : Option BlueBookP93.RotationSense)
  | .trigonalPyramidRS sense, .trigonalPyramid => some (some sense)
  | .seeSawAC sense, .seeSaw => some (some sense)
  | .trigonalBipyramidAC sense, .trigonalBipyramid => some (some sense)
  | .squarePyramid4AC sense, .squarePyramid4 => some (some sense)
  | .squarePyramidAC sense, .squarePyramid => some (some sense)
  | .octahedronAC sense, .octahedron => some (some sense)
  | .trigonalPrismAC sense, .trigonalPrism => some (some sense)
  | .pentagonalBipyramidAC sense, .pentagonalBipyramid => some (some sense)
  | .hexagonalBipyramidAC sense, .hexagonalBipyramid => some (some sense)
  | .heptagonalBipyramidAC sense, .heptagonalBipyramid => some (some sense)
  | _, _ => Option.none

def AbsoluteOrientationRecognized
    (observation : AbsoluteOrientationObservation) (geometry : Geometry)
    (rotation? : Option BlueBookP93.RotationSense) : Prop :=
  observation.rotationFor? geometry = some rotation?

def ConfigurationIndexInput.geometry : ConfigurationIndexInput → Geometry
  | .squarePlanar _ => .squarePlanar
  | .octahedral _ _ => .octahedron
  | .squarePyramid4 _ => .squarePyramid4
  | .squarePyramid5 _ _ => .squarePyramid
  | .bipyramidal kind _ _ _ => kind.geometry
  | .tShape _ => .tShape
  | .seeSaw _ _ => .seeSaw
  | .trigonalPrism _ _ => .trigonalPrism

/-- Hyphen-separated index segments.  A trigonal bipyramid omits the equatorial segment exactly as
specified by IR-9.3.3.6. -/
def configurationIndex : ConfigurationIndexInput → List (List PriorityNumber)
  | .squarePlanar opposite => [[opposite]]
  | .octahedral transToOne transToPlane => [[transToOne, transToPlane]]
  | .squarePyramid4 opposite => [[opposite]]
  | .squarePyramid5 apical opposite => [[apical, opposite]]
  | .bipyramidal .trigonal5 first second _ =>
      [BlueBookP93.orderedPair first second]
  | .bipyramidal _ first second perpendicular =>
      [ BlueBookP93.orderedPair first second
      , BlueBookP93.canonicalCycle perpendicular
      ]
  | .tShape stem => [[stem]]
  | .seeSaw first second => [BlueBookP93.orderedPair first second]
  | .trigonalPrism firstFace secondFace =>
      [BlueBookP93.trigonalPrismIndex firstFace secondFace]

@[simp] theorem trigonalBipyramid_omits_perpendicularSegment
    (first second : PriorityNumber) (perpendicular : List PriorityNumber) :
    (configurationIndex (.bipyramidal .trigonal5 first second perpendicular)).length = 1 := by
  simp [configurationIndex]

@[simp] theorem nontrigonalBipyramid_has_two_segments
    (kind : BipyramidKind) (notTrigonal : kind ≠ .trigonal5)
    (first second : PriorityNumber) (perpendicular : List PriorityNumber) :
    (configurationIndex (.bipyramidal kind first second perpendicular)).length = 2 := by
  cases kind <;> simp_all [configurationIndex]

@[simp] theorem seeSaw_index_has_two_digits (first second : PriorityNumber) :
    ((configurationIndex (.seeSaw first second)).headD []).length = 2 := by
  simp [configurationIndex, BlueBookP93.orderedPair]
  split <;> rfl

/-- Configuration indices identify relative placement and distinguish diastereoisomers; they do
not, by themselves, distinguish an enantiomeric pair. -/
structure RelativeConfigurationIndexSemantics (SpatialArrangement : Type*) where
  index : SpatialArrangement → List (List PriorityNumber)
  distinguishesDiastereomers : ∀ {left right}, index left = index right →
    ¬Diastereomeric
      { sameConstitution := True
        spatialDistributionsDiffer := left ≠ right
        mirrorImages := False
        superimposable := False }
  mirrorHasSameIndex : SpatialArrangement → SpatialArrangement
  index_mirror : ∀ arrangement, index (mirrorHasSameIndex arrangement) = index arrangement

/-! ## Absolute configuration: R/S and C/A -/

inductive AbsoluteConvention where
  | rs
  | ca
  | skewLines
  deriving DecidableEq, Repr

def constitutionBasedConvention : Geometry → AbsoluteConvention
  | .tetrahedron | .trigonalPyramid => .rs
  | _ => .ca

@[simp] theorem tetrahedral_convention_is_rs :
    constitutionBasedConvention .tetrahedron = .rs :=
  rfl

@[simp] theorem nonTetrahedral_example_convention_is_ca :
    constitutionBasedConvention .octahedron = .ca :=
  rfl

/-- View direction used by the tetrahedral R/S rule: from the centre toward priority 4. -/
structure TetrahedralRSObservation where
  sequenceFromPriorityOne : BlueBookP93.RotationSense
  viewedFromCenterTowardLeastPreferred : Prop

def tetrahedralRS (observation : TetrahedralRSObservation) : RS :=
  match observation.sequenceFromPriorityOne with
  | .clockwise => .R
  | .counterclockwise => .S

@[simp] theorem tetrahedralRS_clockwise (view : Prop) :
    tetrahedralRS
      { sequenceFromPriorityOne := .clockwise
        viewedFromCenterTowardLeastPreferred := view } = .R :=
  rfl

inductive PhantomSite where
  | vacantCoordinationSite
  | lonePairSite
  deriving DecidableEq, Repr

/-- IR-9.3.4.3 turns a TPY-3 centre into a notional tetrahedron by placing a lowest-priority
phantom atom at the vacant site or, in a lone-pair model, at the lone-pair site. -/
structure TrigonalPyramidalRSObservation extends TetrahedralRSObservation where
  phantomSite : PhantomSite
  phantomHasLowestPriority : Prop

def trigonalPyramidalRS (observation : TrigonalPyramidalRSObservation) : RS :=
  tetrahedralRS observation.toTetrahedralRSObservation

inductive CAReferenceFrame where
  | trigonalBipyramidSeniorAxialNear
  | squarePyramid5AxialNear
  | squarePyramid4CenterNear
  | seeSawFromSeniorLargestAngleLigand
  | octahedronPriorityOneNearAndLowestTransFar
  | trigonalPrismPreferredFaceNear
  | otherBipyramidSeniorAxialNear (kind : BipyramidKind)
  deriving DecidableEq, Repr

def CAReferenceFrame.geometry : CAReferenceFrame → Geometry
  | .trigonalBipyramidSeniorAxialNear => .trigonalBipyramid
  | .squarePyramid5AxialNear => .squarePyramid
  | .squarePyramid4CenterNear => .squarePyramid4
  | .seeSawFromSeniorLargestAngleLigand => .seeSaw
  | .octahedronPriorityOneNearAndLowestTransFar => .octahedron
  | .trigonalPrismPreferredFaceNear => .trigonalPrism
  | .otherBipyramidSeniorAxialNear kind => kind.geometry

/-- The result of applying the geometry-specific reference frame and then choosing the sequence
that is lower at the first point of difference. -/
def caSymbol (selectedSense : BlueBookP93.RotationSense) : BlueBookP93.ChiralitySymbol :=
  BlueBookP93.chiralitySymbol selectedSense

@[simp] theorem caSymbol_clockwise :
    caSymbol .clockwise = .C :=
  rfl

@[simp] theorem caSymbol_counterclockwise :
    caSymbol .counterclockwise = .A :=
  rfl

/-- IR-9.3.4.7 uses the higher-priority member of the largest-angle pair as the viewpoint and
reads the remaining pair through the smaller angle. -/
structure SeeSawCAObservation where
  largestAnglePair : PriorityNumber × PriorityNumber
  viewedFromSeniorMemberOfLargestAnglePair : Prop
  remainingPairThroughSmallerAngle : Prop
  senseFromSeniorToJuniorRemainingLigand : BlueBookP93.RotationSense

def seeSawCASymbol (observation : SeeSawCAObservation) : BlueBookP93.ChiralitySymbol :=
  caSymbol observation.senseFromSeniorToJuniorRemainingLigand

/-- IR-9.3.4.9 selects the triangular face with more high-priority donors and reads the less
preferred opposite face from above it. -/
structure TrigonalPrismCAObservation where
  preferredFaceHasGreaterHighPriorityCount : Prop
  viewedFromAbovePreferredFace : Prop
  oppositeFacePriorityProgression : BlueBookP93.RotationSense

def trigonalPrismCASymbol
    (observation : TrigonalPrismCAObservation) : BlueBookP93.ChiralitySymbol :=
  caSymbol observation.oppositeFacePriorityProgression

/-! ## The skew-lines convention -/

inductive HelixHandedness where
  | rightHanded
  | leftHanded
  deriving DecidableEq, Repr

namespace HelixHandedness

def opposite : HelixHandedness → HelixHandedness
  | .rightHanded => .leftHanded
  | .leftHanded => .rightHanded

@[simp] theorem opposite_opposite (handedness : HelixHandedness) :
    handedness.opposite.opposite = handedness := by
  cases handedness <;> rfl

end HelixHandedness

inductive SkewLineStatus where
  | helical (handedness : HelixHandedness)
  | inversionAtParallel
  | inversionAtPerpendicular
  deriving DecidableEq, Repr

/-- Reversing which of the two skew lines is called axis and which tangent preserves chirality. -/
def swapSkewLineRoles : SkewLineStatus → SkewLineStatus := id

@[simp] theorem swapping_skew_lines_preserves_chirality (status : SkewLineStatus) :
    swapSkewLineRoles status = status :=
  rfl

inductive SkewDescriptor where
  | capitalDelta
  | capitalLambda
  | lowercaseDelta
  | lowercaseLambda
  deriving DecidableEq, Repr

def SkewDescriptor.label : SkewDescriptor → String
  | .capitalDelta => "Delta"
  | .capitalLambda => "Lambda"
  | .lowercaseDelta => "delta"
  | .lowercaseLambda => "lambda"

def configurationSkewDescriptor : HelixHandedness → SkewDescriptor
  | .rightHanded => .capitalDelta
  | .leftHanded => .capitalLambda

def conformationSkewDescriptor : HelixHandedness → SkewDescriptor
  | .rightHanded => .lowercaseDelta
  | .leftHanded => .lowercaseLambda

inductive ChelateApplication where
  | trisBidentateOctahedral
  | cisBisBidentateOctahedral
  | higherPolydentateRequiringAdditionalRules
  | individualChelateRingConformation
  deriving DecidableEq, Repr

def availableChelateRingPairs : ChelateApplication → Option Nat
  | .trisBidentateOctahedral => some 3
  | .cisBisBidentateOctahedral => some 1
  | .higherPolydentateRequiringAdditionalRules => none
  | .individualChelateRingConformation => some 1

@[simp] theorem tris_has_three_ring_pairs :
    availableChelateRingPairs .trisBidentateOctahedral = some 3 :=
  rfl

@[simp] theorem cis_bis_has_one_ring_pair :
    availableChelateRingPairs .cisBisBidentateOctahedral = some 1 :=
  rfl

inductive ChelateLineRole where
  | betweenDonorAtoms
  | betweenNeighboringRingAtoms
  deriving DecidableEq, Repr

/-- The two lines used for an individual chelate-ring conformation. -/
def chelateConformationLines : List ChelateLineRole :=
  [.betweenDonorAtoms, .betweenNeighboringRingAtoms]

theorem chelateConformationLines_nodup : chelateConformationLines.Nodup := by
  decide

/-! ## Donor-atom priority and priming -/

inductive PriorityComparisonProperty where
  | atomicNumber
  | atomicMass
  | subsequentCIPProperty
  deriving DecidableEq, Repr

def PriorityComparisonProperty.rank : PriorityComparisonProperty → Nat
  | .atomicNumber => 0
  | .atomicMass => 1
  | .subsequentCIPProperty => 2

@[simp] theorem atomicNumber_before_atomicMass :
    PriorityComparisonProperty.atomicNumber.rank <
      PriorityComparisonProperty.atomicMass.rank := by
  decide

@[simp] theorem atomicMass_before_subsequent :
    PriorityComparisonProperty.atomicMass.rank <
      PriorityComparisonProperty.subsequentCIPProperty.rank := by
  decide

/-- Abstract independent CIP ranking used by IR-9.3.5.  Full molecular construction of this
relation is a separate P-92 conformance obligation. -/
structure DonorPrioritySemantics (Ligand : Type*) where
  samePriority : Ligand → Ligand → Prop
  outranks : Ligand → Ligand → Prop
  samePriority_refl : ∀ ligand, samePriority ligand ligand
  samePriority_symm : ∀ {left right}, samePriority left right → samePriority right left
  outranks_irrefl : ∀ ligand, ¬outranks ligand ligand
  outranks_trans : ∀ {first second third},
    outranks first second → outranks second third → outranks first third

def DonorPrioritySemantics.IsHighest {Ligand : Type*}
    (semantics : DonorPrioritySemantics Ligand) (ligand : Ligand) : Prop :=
  ∀ other, ¬semantics.outranks other ligand

/-- IR-9.3.5.2 priority-number assignment: identical/equivalent ligands share a number, the
highest tier is numbered 1, strict priority corresponds to smaller numbers, and no number is
skipped before an assigned tier. -/
structure ValidPriorityAssignment {Ligand : Type*}
    (semantics : DonorPrioritySemantics Ligand) where
  number : Ligand → Nat
  positive : ∀ ligand, 0 < number ligand
  same_number : ∀ {left right}, semantics.samePriority left right → number left = number right
  outranks_iff : ∀ {left right}, semantics.outranks left right ↔ number left < number right
  highest_number_one : ∀ {ligand}, semantics.IsHighest ligand → number ligand = 1
  no_gaps : ∀ ligand n, 0 < n → n < number ligand → ∃ higher, number higher = n

theorem identical_ligands_receive_same_number {Ligand : Type*}
    {semantics : DonorPrioritySemantics Ligand}
    (assignment : ValidPriorityAssignment semantics)
    {left right : Ligand} (same : semantics.samePriority left right) :
    assignment.number left = assignment.number right :=
  assignment.same_number same

/-! ### Finite executable donor frames -/

/-- Independent interpretation of one resolved CIP decision against two assigned IR-9.3.5.2
priority numbers. -/
def PriorityDecisionAgrees (decision : Option Ordering) (leftNumber rightNumber : Nat) : Prop :=
  match decision with
  | some .gt => leftNumber < rightNumber
  | some .eq => leftNumber = rightNumber
  | some .lt => leftNumber > rightNumber
  | none => False

/-- IR-9.3.5.2 specialized to the finite, indexed donor frame used by an executable coordination
pipeline.  This is deliberately relational: it says what any accepted numbering must satisfy and
does not prescribe a sorting algorithm.

The conditions transcribe the source requirements that equal ligands share a number, strict CIP
priority is represented by smaller numbers, the highest tier is numbered one, and no tier number
is skipped. -/
structure FinitePriorityNumbering
    (count : Nat) (compareAt : Nat → Nat → Option Ordering) (numbers : List Nat) : Prop where
  length_eq : numbers.length = count
  positive : ∀ position, position < count → 0 < numbers[position]?.getD 0
  comparison : ∀ left right, left < count → right < count →
    PriorityDecisionAgrees (compareAt left right)
      (numbers[left]?.getD 0) (numbers[right]?.getD 0)
  highest_number_one : ∀ position, position < count →
    (∀ other, other < count → compareAt other position ≠ some .gt) →
      numbers[position]?.getD 0 = 1
  no_gaps : ∀ position, position < count → ∀ number,
    0 < number → number < numbers[position]?.getD 0 →
      ∃ higher, higher < count ∧ numbers[higher]?.getD 0 = number

/-! The priming convention is grouping metadata, not an additional CIP comparison.  IR-9.3.5.3
distinguishes two sources of ambiguity: repeated polydentate ligands of the same kind and repeated
coordinating fragments of the same kind within one polydentate ligand. -/

structure DonorOccurrence
    (LigandId LigandKind FragmentId FragmentKind : Type*) where
  basePriority : Nat
  ligand : LigandId
  ligandKind : LigandKind
  coordinatingFragment : FragmentId
  fragmentKind : FragmentKind
  isPolydentate : Prop

/-- Two occurrences belong to different polydentate ligands of the same particular kind. -/
def RepeatedPolydentateLigand
    {LigandId LigandKind FragmentId FragmentKind : Type*}
    (left right : DonorOccurrence LigandId LigandKind FragmentId FragmentKind) : Prop :=
  left.isPolydentate ∧ right.isPolydentate ∧
    left.ligandKind = right.ligandKind ∧ left.ligand ≠ right.ligand

/-- Two occurrences belong to different coordinating fragments of the same particular kind inside
one polydentate ligand. -/
def RepeatedCoordinatingFragment
    {LigandId LigandKind FragmentId FragmentKind : Type*}
    (left right : DonorOccurrence LigandId LigandKind FragmentId FragmentKind) : Prop :=
  left.isPolydentate ∧ right.isPolydentate ∧ left.ligand = right.ligand ∧
    left.fragmentKind = right.fragmentKind ∧
    left.coordinatingFragment ≠ right.coordinatingFragment

/-- Exact two-way applicability boundary stated in IR-9.3.5.3.  Notice that this does not compare
atom identifiers and does not impose a canonical choice of which group is unprimed: the source
explicitly permits that choice to be arbitrary. -/
def NeedsPrimeGrouping
    {LigandId LigandKind FragmentId FragmentKind : Type*}
    (left right : DonorOccurrence LigandId LigandKind FragmentId FragmentKind) : Prop :=
  RepeatedPolydentateLigand left right ∨ RepeatedCoordinatingFragment left right

/-- A source-level grouping frame supplied after ligand identity or symmetry analysis.  A frame is
either grouping whole repeated ligands or grouping repeated coordinating fragments within one
ligand.  This evidence cannot in general be reconstructed from an unordered donor-atom list. -/
inductive PrimingGroupingBasis where
  | repeatedPolydentateLigands
  | repeatedCoordinatingFragments
  deriving DecidableEq, Repr

/-- IR-9.3.5.3 admissibility of prime counts for one family of otherwise indistinguishable groups.
The assignment deliberately contains no ordering on `Group`: any group may receive zero primes.
Counts are constant within a group, distinct between represented groups, start at zero, and have
no gaps. -/
structure AdmissiblePrimingAssignment
    {Donor Group : Type*} [DecidableEq Donor] [DecidableEq Group]
    (donors : List Donor) (groupOf : Donor → Group) where
  primeCount : Donor → Nat
  constantOnGroup : ∀ {left right}, left ∈ donors → right ∈ donors →
    groupOf left = groupOf right → primeCount left = primeCount right
  separatesGroups : ∀ {left right}, left ∈ donors → right ∈ donors →
    groupOf left ≠ groupOf right → primeCount left ≠ primeCount right
  hasUnprimed : donors ≠ [] → ∃ donor ∈ donors, primeCount donor = 0
  noGaps : ∀ {donor}, donor ∈ donors → ∀ count,
    count < primeCount donor → ∃ other ∈ donors, primeCount other = count

/-- Membership of one donor in one IR-9.3.5.3 equivalence family and one occurrence group inside
that family.  A family is a particular ligand kind, or a particular coordinating-fragment kind
inside one ligand.  Its groups are the distinct ligand or fragment occurrences which primes must
distinguish.  The natural-number values are opaque identities: only equality is meaningful. -/
structure PrimingMembership where
  family : Nat
  group : Nat
  deriving DecidableEq, Repr

/-- Membership lookup in a finite donor frame. -/
def finitePrimingMembershipAt
    (memberships : List (Option PrimingMembership)) (position : Nat) :
    Option PrimingMembership :=
  (memberships[position]?).join

/-- Executable finite interpretation of every family-local IR-9.3.5.3 obligation. -/
def finitePrimingAssignmentOK
    (donorCount : Nat) (memberships : List (Option PrimingMembership))
    (primeCounts : List Nat) : Bool :=
  let positions := List.range donorCount
  memberships.length == donorCount &&
  primeCounts.length == donorCount &&
  positions.all (fun position =>
      match finitePrimingMembershipAt memberships position with
      | none => primeCounts[position]?.getD 0 == 0
      | some _ => true) &&
  positions.all (fun position =>
      match finitePrimingMembershipAt memberships position with
      | none => true
      | some member =>
          positions.any (fun other =>
            match finitePrimingMembershipAt memberships other with
            | none => false
            | some otherMember =>
                member.family == otherMember.family && member.group != otherMember.group)) &&
  positions.all (fun left =>
      positions.all fun right =>
        match finitePrimingMembershipAt memberships left,
            finitePrimingMembershipAt memberships right with
        | some leftMember, some rightMember =>
            if leftMember.family == rightMember.family then
              (leftMember.group == rightMember.group) ==
                (primeCounts[left]?.getD 0 == primeCounts[right]?.getD 0)
            else true
        | _, _ => true) &&
  positions.all (fun position =>
      match finitePrimingMembershipAt memberships position with
      | none => true
      | some member =>
          positions.any (fun other =>
            match finitePrimingMembershipAt memberships other with
            | none => false
            | some otherMember =>
                member.family == otherMember.family &&
                  primeCounts[other]?.getD 0 == 0)) &&
  positions.all (fun position =>
      match finitePrimingMembershipAt memberships position with
      | none => true
      | some member =>
          (List.range (primeCounts[position]?.getD 0)).all fun count =>
            positions.any (fun other =>
              match finitePrimingMembershipAt memberships other with
              | none => false
              | some otherMember =>
                  member.family == otherMember.family &&
                    primeCounts[other]?.getD 0 == count))

/-- Complete finite IR-9.3.5.3 assignment, with the source's words "of a particular kind" made
explicit.

Prime counts are dense only *within one applicable family*.  Donors outside every repeated family
remain unprimed.  Within a family, equal occurrence groups have equal counts, different occurrence
groups have different counts, one group is unprimed, and no count is skipped.  Different ligand or
fragment kinds are independent and may reuse the same prime counts.  This is deliberately not one
global partition: such a partition would incorrectly prime an unrelated ligand merely because a
different ligand kind occurs twice. -/
def FinitePrimingAssignment
    (donorCount : Nat) (memberships : List (Option PrimingMembership))
    (primeCounts : List Nat) : Prop :=
  finitePrimingAssignmentOK donorCount memberships primeCounts = true

/-- A base priority plus the number of prime marks assigned by the priming convention. -/
def primedPriority (basePriority primeCount : Nat) : PriorityNumber :=
  { number := basePriority, primes := primeCount }

@[simp] theorem primedPriority_number (base primeCount : Nat) :
    (primedPriority base primeCount).number = base :=
  rfl

@[simp] theorem primedPriority_primes (base primeCount : Nat) :
    (primedPriority base primeCount).primes = primeCount :=
  rfl

theorem fewer_primes_has_higher_priority (base firstPrimes secondPrimes : Nat)
    (fewer : firstPrimes < secondPrimes) :
    (primedPriority base firstPrimes).seniorTo
      (primedPriority base secondPrimes) = true := by
  simp [primedPriority, BlueBookP93.PriorityNumber.seniorTo, fewer]

theorem unprimed_has_priority_over_primed (base primeCount : Nat)
    (positive : 0 < primeCount) :
    (primedPriority base 0).seniorTo (primedPriority base primeCount) = true := by
  exact fewer_primes_has_higher_priority base 0 primeCount positive

/-- Any number of primes remains senior to the next unprimed base priority: for example every
`1`, `1'`, `1''`, ... precedes `2`. -/
theorem primed_has_priority_over_next_base (base primeCount : Nat) :
    (primedPriority base primeCount).seniorTo (primedPriority (base + 1) 0) = true := by
  simp [primedPriority, BlueBookP93.PriorityNumber.seniorTo]

/-! ## Semantic ownership map -/

inductive SemanticDomain where
  | foundations
  | geometry
  | relativeConfiguration
  | absoluteRA
  | skewLines
  | ligandPriority
  deriving DecidableEq, Repr

def Provision.semanticDomain : Provision → SemanticDomain
  | .polyhedralConfiguration | .configurationIntroduction | .diastereoisomerGeneral =>
      .foundations
  | .polyhedralSymbols | .geometryChoice => .geometry
  | .configurationIndex | .squarePlanar | .octahedral | .squarePyramidal
  | .bipyramidal | .tShape | .seeSaw => .relativeConfiguration
  | .absoluteConfigurationGeneral | .rsTetrahedral | .rsTrigonalPyramidal
  | .caPolyhedral | .caTrigonalBipyramidal | .caSquarePyramidal | .caSeeSaw
  | .caOctahedral | .caTrigonalPrismatic | .caOtherBipyramidal => .absoluteRA
  | .skewLines | .skewLinesTrisBidentate | .skewLinesBisBidentate
  | .skewLinesChelateConformations => .skewLines
  | .ligandPriorityGeneral | .priorityNumbers | .primingConvention => .ligandPriority

theorem every_provision_has_semantic_domain (provision : Provision) :
    provision.semanticDomain ∈
      [ .foundations, .geometry, .relativeConfiguration, .absoluteRA, .skewLines,
        .ligandPriority ] := by
  cases provision <;> simp [Provision.semanticDomain]

end RedBookIR9

end TetraStereo.OneCenter
