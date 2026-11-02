import TetraStereo.OneCenter.StereochemicalElements
import TetraStereo.OneCenter.RS

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# IUPAC P-93 / Red Book IR-9.3 polyhedral configuration primitives

This module formalizes the descriptor-forming part of P-93.3 and the full IR-9.3.2.1 polyhedral
symbol vocabulary independently of molecular geometry recognition.  Its inputs are already
identified polyhedral positions carrying CIP-derived priority numbers.  A later perception layer
must prove that a molecular/coordinate frame supplies those positions; this module does not infer
an idealized geometry from connectivity.
-/

namespace BlueBookP93

/-- Independent union of P-93.3/Table 9.1 and Red Book Table IR-9.2. -/
inductive Geometry where
  | linear
  | angular
  | trigonalPlanar
  | trigonalPyramid
  | tShape
  | tetrahedron
  | squarePlanar
  | squarePyramid4
  | seeSaw
  | trigonalBipyramid
  | squarePyramid
  | octahedron
  | trigonalPrism
  | pentagonalBipyramid
  | faceMonocappedOctahedron
  | squareFaceMonocappedTrigonalPrism
  | cube
  | squareAntiprism
  | dodecahedron
  | hexagonalBipyramid
  | transBicappedOctahedron
  | triangularFaceBicappedTrigonalPrism
  | squareFaceBicappedTrigonalPrism
  | squareFaceTricappedTrigonalPrism
  | heptagonalBipyramid
  deriving DecidableEq, Repr

def Geometry.coordinationNumber : Geometry → ℕ
  | .linear | .angular => 2
  | .trigonalPlanar | .trigonalPyramid | .tShape => 3
  | .tetrahedron | .squarePlanar | .squarePyramid4 | .seeSaw => 4
  | .trigonalBipyramid | .squarePyramid => 5
  | .octahedron | .trigonalPrism => 6
  | .pentagonalBipyramid | .faceMonocappedOctahedron
  | .squareFaceMonocappedTrigonalPrism => 7
  | .cube | .squareAntiprism | .dodecahedron | .hexagonalBipyramid
  | .transBicappedOctahedron | .triangularFaceBicappedTrigonalPrism
  | .squareFaceBicappedTrigonalPrism => 8
  | .squareFaceTricappedTrigonalPrism | .heptagonalBipyramid => 9

def Geometry.symbol : Geometry → String
  | .linear => "L-2"
  | .angular => "A-2"
  | .trigonalPlanar => "TP-3"
  | .trigonalPyramid => "TPY-3"
  | .tShape => "TS-3"
  | .tetrahedron => "T-4"
  | .squarePlanar => "SP-4"
  | .squarePyramid4 => "SPY-4"
  | .seeSaw => "SS-4"
  | .trigonalBipyramid => "TBPY-5"
  | .squarePyramid => "SPY-5"
  | .octahedron => "OC-6"
  | .trigonalPrism => "TPR-6"
  | .pentagonalBipyramid => "PBPY-7"
  | .faceMonocappedOctahedron => "OCF-7"
  | .squareFaceMonocappedTrigonalPrism => "TPRS-7"
  | .cube => "CU-8"
  | .squareAntiprism => "SAPR-8"
  | .dodecahedron => "DD-8"
  | .hexagonalBipyramid => "HBPY-8"
  | .transBicappedOctahedron => "OCT-8"
  | .triangularFaceBicappedTrigonalPrism => "TPRT-8"
  | .squareFaceBicappedTrigonalPrism => "TPRS-8"
  | .squareFaceTricappedTrigonalPrism => "TPRS-9"
  | .heptagonalBipyramid => "HBPY-9"

/-- P-93.3.3 priority number with the P-93.3.3.1 priming convention.  Smaller `number` is
higher priority; for otherwise equal entries fewer primes have priority. -/
structure PriorityNumber where
  number : ℕ
  primes : ℕ := 0
  deriving DecidableEq, Repr

def PriorityNumber.seniorTo (left right : PriorityNumber) : Bool :=
  left.number < right.number || (left.number == right.number && left.primes < right.primes)

def PriorityNumber.validFor (coordination : ℕ) (priority : PriorityNumber) : Bool :=
  0 < priority.number && priority.number ≤ coordination

/-- P-93.3.3.1 priority decision, including preference of unprimed over primed numbers. -/
def priorityDecision (left right : PriorityNumber) : Ordering :=
  if left.seniorTo right then .gt else if right.seniorTo left then .lt else .eq

/-- Put a two-entry configuration index in senior-first order. -/
def orderedPair (first second : PriorityNumber) : List PriorityNumber :=
  if second.seniorTo first then [second, first] else [first, second]

/-- P-93.3.3.1(a), trans-maximum-difference: between otherwise tied positions, the position
opposite the more senior ligand has priority. -/
def transMaximumDecision (leftOpposite rightOpposite : PriorityNumber) : Ordering :=
  priorityDecision leftOpposite rightOpposite

/-- P-93.3.3.2: trigonal-pyramidal systems use a phantom fourth position and no configuration
index. -/
def trigonalPyramidIndex : List PriorityNumber := []

/-- P-93.3.3.3: the T-shape index is the priority number on the stem. -/
def tShapeIndex (stem : PriorityNumber) : List PriorityNumber := [stem]

/-- IR-9.3.3.3: the square-planar index is the priority number trans to priority one. -/
def squarePlanarIndex (transToOne : PriorityNumber) : List PriorityNumber := [transToOne]

/-- IR-9.3.3.5: the four-coordinate square-pyramidal index is chosen by the same
trans-to-senior rule as the square-planar index. -/
def squarePyramid4Index (transToSenior : PriorityNumber) : List PriorityNumber :=
  [transToSenior]

/-- P-93.3.3.4: the see-saw index names the two positions separated by the largest angle. -/
def seeSawIndex (firstWide secondWide : PriorityNumber) : List PriorityNumber :=
  orderedPair firstWide secondWide

/-- P-93.3.3.5: the trigonal-bipyramidal index is the senior-first apical pair. -/
def trigonalBipyramidIndex (firstApical secondApical : PriorityNumber) : List PriorityNumber :=
  orderedPair firstApical secondApical

/-- P-93.3.3.6: square-pyramidal index: apical priority, then the base position trans to the
highest-priority base position. -/
def squarePyramidIndex (apical transToSeniorBase : PriorityNumber) : List PriorityNumber :=
  [apical, transToSeniorBase]

/-- P-93.3.3.7: octahedral index: the position trans to priority one, followed by the position
trans to the highest-priority position in the perpendicular plane. -/
def octahedronIndex (transToOne transToSeniorPlane : PriorityNumber) : List PriorityNumber :=
  [transToOne, transToSeniorPlane]

def comparePrioritySequence : List PriorityNumber → List PriorityNumber → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | left :: lefts, right :: rights =>
      match priorityDecision left right with
      | .eq => comparePrioritySequence lefts rights
      | decision => decision

def cyclicRotations (priorities : List PriorityNumber) : List (List PriorityNumber) :=
  (List.range priorities.length).map fun offset =>
    priorities.drop offset ++ priorities.take offset

/-- One aligned trigonal-prism frame.  The first three entries are one triangular face and the
last three are the corresponding opposite vertices. -/
def trigonalPrismFrame (firstFace secondFace : List PriorityNumber) (offset : Nat) :
    List PriorityNumber :=
  firstFace.drop offset ++ firstFace.take offset ++
    secondFace.drop offset ++ secondFace.take offset

/-- All twelve frames of a trigonal prism: three rotations and two directions, viewed from either
triangular face.  `firstFace` and `secondFace` must be supplied in corresponding-vertex order. -/
def trigonalPrismFrameCandidates (firstFace secondFace : List PriorityNumber) :
    List (List PriorityNumber) :=
  let offsets := List.range 3
  (offsets.map (trigonalPrismFrame firstFace secondFace)) ++
  (offsets.map (trigonalPrismFrame firstFace.reverse secondFace.reverse)) ++
  (offsets.map (trigonalPrismFrame secondFace firstFace)) ++
  (offsets.map (trigonalPrismFrame secondFace.reverse firstFace.reverse))

/-- Lexicographically most senior member of a nonempty candidate family, with `[]` as the empty
fallback. -/
def mostSeniorPrioritySequence (candidates : List (List PriorityNumber)) : List PriorityNumber :=
  match candidates with
  | [] => []
  | first :: rest => rest.foldl (fun best candidate =>
      if comparePrioritySequence candidate best == .gt then candidate else best) first

/-- IR-9.3.4.9 trigonal-prismatic configuration index.  The preferred triangular face is selected
internally by comparing the complete aligned face words.  The index is the three-entry word on the
opposite face in the resulting canonical frame. -/
def trigonalPrismIndex (firstFace secondFace : List PriorityNumber) :
    List PriorityNumber :=
  (mostSeniorPrioritySequence
    (trigonalPrismFrameCandidates firstFace secondFace)).drop 3

/-- Independent IR-9.3.3.6 reading of the lowest cyclic numerical sequence. -/
def canonicalCycle (priorities : List PriorityNumber) : List PriorityNumber :=
  let candidates := cyclicRotations priorities ++ cyclicRotations priorities.reverse
  match candidates with
  | [] => []
  | first :: rest => rest.foldl (fun best candidate =>
      if comparePrioritySequence candidate best == .gt then candidate else best) first

def bipyramidalIndex (firstAxial secondAxial : PriorityNumber)
    (perpendicularPlane : List PriorityNumber) : List (List PriorityNumber) :=
  [orderedPair firstAxial secondAxial, canonicalCycle perpendicularPlane]

inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- P-93.3.4.2 polyhedral chirality symbols. -/
inductive ChiralitySymbol where
  | A
  | C
  deriving DecidableEq, Repr

/-- Viewed from the senior end of the reference axis, clockwise is `C` and counterclockwise is
`A`. -/
def chiralitySymbol : RotationSense → ChiralitySymbol
  | .clockwise => .C
  | .counterclockwise => .A

end BlueBookP93

/-! ## Executable descriptor surface -/

inductive PolyhedralGeometry where
  | linear
  | angular
  | trigonalPlanar
  | trigonalPyramid
  | tShape
  | tetrahedron
  | squarePlanar
  | squarePyramid4
  | seeSaw
  | trigonalBipyramid
  | squarePyramid
  | octahedron
  | trigonalPrism
  | pentagonalBipyramid
  | faceMonocappedOctahedron
  | squareFaceMonocappedTrigonalPrism
  | cube
  | squareAntiprism
  | dodecahedron
  | hexagonalBipyramid
  | transBicappedOctahedron
  | triangularFaceBicappedTrigonalPrism
  | squareFaceBicappedTrigonalPrism
  | squareFaceTricappedTrigonalPrism
  | heptagonalBipyramid
  deriving DecidableEq, Repr

namespace PolyhedralGeometry

/-- Exhaustive Red Book Table IR-9.2 geometry list, in coordination-number order. -/
def all : List PolyhedralGeometry :=
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

@[simp] theorem mem_all (geometry : PolyhedralGeometry) : geometry ∈ all := by
  cases geometry <;> simp [all]

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_length : all.length = 25 := by
  decide

def coordinationNumber : PolyhedralGeometry → ℕ
  | .linear | .angular => 2
  | .trigonalPlanar | .trigonalPyramid | .tShape => 3
  | .tetrahedron | .squarePlanar | .squarePyramid4 | .seeSaw => 4
  | .trigonalBipyramid | .squarePyramid => 5
  | .octahedron | .trigonalPrism => 6
  | .pentagonalBipyramid | .faceMonocappedOctahedron
  | .squareFaceMonocappedTrigonalPrism => 7
  | .cube | .squareAntiprism | .dodecahedron | .hexagonalBipyramid
  | .transBicappedOctahedron | .triangularFaceBicappedTrigonalPrism
  | .squareFaceBicappedTrigonalPrism => 8
  | .squareFaceTricappedTrigonalPrism | .heptagonalBipyramid => 9

def symbol : PolyhedralGeometry → String
  | .linear => "L-2"
  | .angular => "A-2"
  | .trigonalPlanar => "TP-3"
  | .trigonalPyramid => "TPY-3"
  | .tShape => "TS-3"
  | .tetrahedron => "T-4"
  | .squarePlanar => "SP-4"
  | .squarePyramid4 => "SPY-4"
  | .seeSaw => "SS-4"
  | .trigonalBipyramid => "TBPY-5"
  | .squarePyramid => "SPY-5"
  | .octahedron => "OC-6"
  | .trigonalPrism => "TPR-6"
  | .pentagonalBipyramid => "PBPY-7"
  | .faceMonocappedOctahedron => "OCF-7"
  | .squareFaceMonocappedTrigonalPrism => "TPRS-7"
  | .cube => "CU-8"
  | .squareAntiprism => "SAPR-8"
  | .dodecahedron => "DD-8"
  | .hexagonalBipyramid => "HBPY-8"
  | .transBicappedOctahedron => "OCT-8"
  | .triangularFaceBicappedTrigonalPrism => "TPRT-8"
  | .squareFaceBicappedTrigonalPrism => "TPRS-8"
  | .squareFaceTricappedTrigonalPrism => "TPRS-9"
  | .heptagonalBipyramid => "HBPY-9"

end PolyhedralGeometry

structure PolyhedralPriorityNumber where
  number : ℕ
  primes : ℕ := 0
  deriving DecidableEq, Repr

namespace PolyhedralPriorityNumber

def outranks (left right : PolyhedralPriorityNumber) : Bool :=
  left.number < right.number || (left.number == right.number && left.primes < right.primes)

def validFor (coordination : ℕ) (priority : PolyhedralPriorityNumber) : Bool :=
  priority.number != 0 && priority.number ≤ coordination

def label (priority : PolyhedralPriorityNumber) : String :=
  toString priority.number ++ String.ofList (List.replicate priority.primes '\'')

end PolyhedralPriorityNumber

inductive PolyhedralRotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

inductive PolyhedralChiralitySymbol where
  | A
  | C
  deriving DecidableEq, Repr

namespace PolyhedralChiralitySymbol

def ofRotation : PolyhedralRotationSense → PolyhedralChiralitySymbol
  | .clockwise => .C
  | .counterclockwise => .A

def mirror : PolyhedralChiralitySymbol → PolyhedralChiralitySymbol
  | .A => .C
  | .C => .A

def label : PolyhedralChiralitySymbol → String
  | .A => "A"
  | .C => "C"

@[simp] theorem mirror_mirror (symbol : PolyhedralChiralitySymbol) :
    mirror (mirror symbol) = symbol := by
  cases symbol <;> rfl

end PolyhedralChiralitySymbol

/-- Absolute-configuration suffix used by P-93.3: trigonal pyramids use `R/S`, while the other
chiral polyhedra use `A/C`. -/
inductive PolyhedralAbsoluteConfiguration where
  | rs (descriptor : RS)
  | ac (descriptor : PolyhedralChiralitySymbol)
  deriving DecidableEq, Repr

namespace PolyhedralAbsoluteConfiguration

def label : PolyhedralAbsoluteConfiguration → String
  | .rs .R => "R"
  | .rs .S => "S"
  | .ac descriptor => descriptor.label

end PolyhedralAbsoluteConfiguration

structure PolyhedralDescriptor where
  geometry : PolyhedralGeometry
  /-- Hyphen-separated configuration-index segments.  Priority numbers within one segment are
  concatenated, e.g. `[[2,5]]` renders `25`, while a pentagonal-bipyramidal index may have the
  two segments `[[3,4],[1,2,3,4,2]]`. -/
  configurationIndex : List (List PolyhedralPriorityNumber) := []
  absolute? : Option PolyhedralAbsoluteConfiguration := none
  deriving DecidableEq, Repr

namespace PolyhedralDescriptor

def label (descriptor : PolyhedralDescriptor) : String :=
  let index := descriptor.configurationIndex.map fun segment =>
    String.join (segment.map PolyhedralPriorityNumber.label)
  let pieces := [descriptor.geometry.symbol] ++ index ++ descriptor.absolute?.toList.map
    PolyhedralAbsoluteConfiguration.label
  String.intercalate "-" pieces

end PolyhedralDescriptor

def comparePolyhedralPriority (left right : PolyhedralPriorityNumber) : Ordering :=
  if left.outranks right then .gt else if right.outranks left then .lt else .eq

def orderPolyhedralPair (first second : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  if second.outranks first then [second, first] else [first, second]

def polyhedralTransMaximumDecision
    (leftOpposite rightOpposite : PolyhedralPriorityNumber) : Ordering :=
  comparePolyhedralPriority leftOpposite rightOpposite

/-- P-93.3.4.1 trigonal-pyramidal `R/S` result after introducing the phantom fourth position. -/
def trigonalPyramidDescriptorOfRotation : PolyhedralRotationSense → RS
  | .clockwise => .R
  | .counterclockwise => .S

def trigonalPyramidConfigurationIndex : List PolyhedralPriorityNumber := []

def tShapeConfigurationIndex (stem : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber := [stem]

def squarePlanarConfigurationIndex (transToOne : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber := [transToOne]

def squarePyramid4ConfigurationIndex (transToSenior : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber := [transToSenior]

def seeSawConfigurationIndex (firstWide secondWide : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber := orderPolyhedralPair firstWide secondWide

def trigonalBipyramidConfigurationIndex (firstApical secondApical : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber := orderPolyhedralPair firstApical secondApical

def squarePyramidConfigurationIndex (apical transToSeniorBase : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber := [apical, transToSeniorBase]

def octahedronConfigurationIndex (transToOne transToSeniorPlane : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber := [transToOne, transToSeniorPlane]

/-- Lexicographic priority for equal-length configuration-index sequences. -/
def comparePolyhedralPrioritySequence :
    List PolyhedralPriorityNumber → List PolyhedralPriorityNumber → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | left :: lefts, right :: rights =>
      match comparePolyhedralPriority left right with
      | .eq => comparePolyhedralPrioritySequence lefts rights
      | decision => decision

def polyhedralCyclicRotations (priorities : List PolyhedralPriorityNumber) :
    List (List PolyhedralPriorityNumber) :=
  (List.range priorities.length).map fun offset =>
    priorities.drop offset ++ priorities.take offset

def polyhedralTrigonalPrismFrame
    (firstFace secondFace : List PolyhedralPriorityNumber) (offset : Nat) :
    List PolyhedralPriorityNumber :=
  firstFace.drop offset ++ firstFace.take offset ++
    secondFace.drop offset ++ secondFace.take offset

def polyhedralTrigonalPrismFrameCandidates
    (firstFace secondFace : List PolyhedralPriorityNumber) :
    List (List PolyhedralPriorityNumber) :=
  let offsets := List.range 3
  (offsets.map (polyhedralTrigonalPrismFrame firstFace secondFace)) ++
  (offsets.map (polyhedralTrigonalPrismFrame firstFace.reverse secondFace.reverse)) ++
  (offsets.map (polyhedralTrigonalPrismFrame secondFace firstFace)) ++
  (offsets.map (polyhedralTrigonalPrismFrame secondFace.reverse firstFace.reverse))

def mostSeniorPolyhedralPrioritySequence
    (candidates : List (List PolyhedralPriorityNumber)) :
    List PolyhedralPriorityNumber :=
  match candidates with
  | [] => []
  | first :: rest => rest.foldl (fun best candidate =>
      if comparePolyhedralPrioritySequence candidate best == .gt then candidate else best) first

/-- Production IR-9.3.4.9 trigonal-prismatic index. -/
def trigonalPrismConfigurationIndex
    (firstFace secondFace : List PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  (mostSeniorPolyhedralPrioritySequence
    (polyhedralTrigonalPrismFrameCandidates firstFace secondFace)).drop 3

/-- IR-9.3.3.6 canonical perpendicular-plane sequence: consider every starting vertex and both
directions, then retain the lexicographically most senior priority-number sequence.  This also
handles repeated and primed priority numbers without an importer-chosen starting point. -/
def canonicalPolyhedralCycle (priorities : List PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  let candidates :=
    polyhedralCyclicRotations priorities ++ polyhedralCyclicRotations priorities.reverse
  match candidates with
  | [] => []
  | first :: rest => rest.foldl (fun best candidate =>
      if comparePolyhedralPrioritySequence candidate best == .gt then candidate else best) first

/-- IR-9.3.3.6 bipyramidal configuration index.  The first segment is the senior-first reference
axis; the second is the canonical cyclic sequence in the perpendicular plane. -/
def bipyramidalConfigurationIndex (firstAxial secondAxial : PolyhedralPriorityNumber)
    (perpendicularPlane : List PolyhedralPriorityNumber) :
    List (List PolyhedralPriorityNumber) :=
  [orderPolyhedralPair firstAxial secondAxial, canonicalPolyhedralCycle perpendicularPlane]

/-! ## Independent conformance bridges -/

namespace BlueBookP93

def geometryOfProduction : PolyhedralGeometry → Geometry
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

def priorityOfProduction (priority : PolyhedralPriorityNumber) : PriorityNumber :=
  { number := priority.number, primes := priority.primes }

def rotationOfProduction : PolyhedralRotationSense → RotationSense
  | .clockwise => .clockwise
  | .counterclockwise => .counterclockwise

def chiralityOfProduction : PolyhedralChiralitySymbol → ChiralitySymbol
  | .A => .A
  | .C => .C

end BlueBookP93

@[simp] theorem polyhedral_priority_outranks_conforms_P93
    (left right : PolyhedralPriorityNumber) :
    (BlueBookP93.priorityOfProduction left).seniorTo
        (BlueBookP93.priorityOfProduction right) = left.outranks right :=
  rfl

@[simp] theorem polyhedral_geometry_symbol_conforms_P93 (geometry : PolyhedralGeometry) :
    geometry.symbol = (BlueBookP93.geometryOfProduction geometry).symbol := by
  cases geometry <;> rfl

@[simp] theorem polyhedral_geometry_coordination_conforms_P93 (geometry : PolyhedralGeometry) :
    geometry.coordinationNumber =
      (BlueBookP93.geometryOfProduction geometry).coordinationNumber := by
  cases geometry <;> rfl

theorem polyhedral_priority_conforms_P93 (left right : PolyhedralPriorityNumber) :
    comparePolyhedralPriority left right =
      BlueBookP93.priorityDecision (BlueBookP93.priorityOfProduction left)
        (BlueBookP93.priorityOfProduction right) :=
  rfl

theorem polyhedral_transMaximum_conforms_P93 (left right : PolyhedralPriorityNumber) :
    polyhedralTransMaximumDecision left right =
      BlueBookP93.transMaximumDecision (BlueBookP93.priorityOfProduction left)
        (BlueBookP93.priorityOfProduction right) :=
  rfl

theorem tShapeConfigurationIndex_conforms_P93 (stem : PolyhedralPriorityNumber) :
    (tShapeConfigurationIndex stem).map BlueBookP93.priorityOfProduction =
      BlueBookP93.tShapeIndex (BlueBookP93.priorityOfProduction stem) :=
  rfl

theorem squarePlanarConfigurationIndex_conforms_IR9 (transToOne : PolyhedralPriorityNumber) :
    (squarePlanarConfigurationIndex transToOne).map BlueBookP93.priorityOfProduction =
      BlueBookP93.squarePlanarIndex (BlueBookP93.priorityOfProduction transToOne) :=
  rfl

theorem squarePyramid4ConfigurationIndex_conforms_IR9
    (transToSenior : PolyhedralPriorityNumber) :
    (squarePyramid4ConfigurationIndex transToSenior).map BlueBookP93.priorityOfProduction =
      BlueBookP93.squarePyramid4Index (BlueBookP93.priorityOfProduction transToSenior) :=
  rfl

theorem seeSawConfigurationIndex_conforms_P93
    (first second : PolyhedralPriorityNumber) :
    (seeSawConfigurationIndex first second).map BlueBookP93.priorityOfProduction =
      BlueBookP93.seeSawIndex (BlueBookP93.priorityOfProduction first)
        (BlueBookP93.priorityOfProduction second) := by
  by_cases h : second.outranks first = true <;>
    simp [seeSawConfigurationIndex, orderPolyhedralPair, BlueBookP93.seeSawIndex,
      BlueBookP93.orderedPair, h]

theorem trigonalBipyramidConfigurationIndex_conforms_P93
    (first second : PolyhedralPriorityNumber) :
    (trigonalBipyramidConfigurationIndex first second).map BlueBookP93.priorityOfProduction =
      BlueBookP93.trigonalBipyramidIndex (BlueBookP93.priorityOfProduction first)
        (BlueBookP93.priorityOfProduction second) := by
  by_cases h : second.outranks first = true <;>
    simp [trigonalBipyramidConfigurationIndex, orderPolyhedralPair,
      BlueBookP93.trigonalBipyramidIndex, BlueBookP93.orderedPair, h]

theorem squarePyramidConfigurationIndex_conforms_P93
    (apical transToSeniorBase : PolyhedralPriorityNumber) :
    (squarePyramidConfigurationIndex apical transToSeniorBase).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.squarePyramidIndex (BlueBookP93.priorityOfProduction apical)
        (BlueBookP93.priorityOfProduction transToSeniorBase) :=
  rfl

theorem octahedronConfigurationIndex_conforms_P93
    (transToOne transToSeniorPlane : PolyhedralPriorityNumber) :
    (octahedronConfigurationIndex transToOne transToSeniorPlane).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.octahedronIndex (BlueBookP93.priorityOfProduction transToOne)
        (BlueBookP93.priorityOfProduction transToSeniorPlane) :=
  rfl

theorem comparePolyhedralPrioritySequence_conforms_IR9
    (left right : List PolyhedralPriorityNumber) :
    comparePolyhedralPrioritySequence left right =
      BlueBookP93.comparePrioritySequence
        (left.map BlueBookP93.priorityOfProduction)
        (right.map BlueBookP93.priorityOfProduction) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons first rest inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons second seconds =>
          simp only [comparePolyhedralPrioritySequence,
            BlueBookP93.comparePrioritySequence, List.map_cons]
          rw [polyhedral_priority_conforms_P93]
          cases BlueBookP93.priorityDecision (BlueBookP93.priorityOfProduction first)
              (BlueBookP93.priorityOfProduction second)
          · rfl
          · exact inductionHypothesis seconds
          · rfl

theorem polyhedralCyclicRotations_conforms_IR9 (priorities : List PolyhedralPriorityNumber) :
    (polyhedralCyclicRotations priorities).map
        (List.map BlueBookP93.priorityOfProduction) =
      BlueBookP93.cyclicRotations (priorities.map BlueBookP93.priorityOfProduction) := by
  simp [polyhedralCyclicRotations, BlueBookP93.cyclicRotations, List.map_drop,
    List.map_take]

private theorem canonicalCycleFold_conforms_IR9
    (candidates : List (List PolyhedralPriorityNumber))
    (best : List PolyhedralPriorityNumber) :
    ((candidates.foldl (fun current candidate =>
        if comparePolyhedralPrioritySequence candidate current == .gt
        then candidate else current) best).map BlueBookP93.priorityOfProduction) =
      ((candidates.map (List.map BlueBookP93.priorityOfProduction)).foldl
        (fun current candidate =>
          if BlueBookP93.comparePrioritySequence candidate current == .gt
          then candidate else current)
        (best.map BlueBookP93.priorityOfProduction)) := by
  induction candidates generalizing best with
  | nil => rfl
  | cons candidate candidates inductionHypothesis =>
      simp only [List.foldl_cons, List.map_cons]
      rw [← comparePolyhedralPrioritySequence_conforms_IR9 candidate best]
      split <;> apply inductionHypothesis

theorem polyhedralTrigonalPrismFrame_conforms_IR9
    (firstFace secondFace : List PolyhedralPriorityNumber) (offset : Nat) :
    (polyhedralTrigonalPrismFrame firstFace secondFace offset).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.trigonalPrismFrame
        (firstFace.map BlueBookP93.priorityOfProduction)
        (secondFace.map BlueBookP93.priorityOfProduction) offset := by
  simp [polyhedralTrigonalPrismFrame, BlueBookP93.trigonalPrismFrame,
    List.map_drop, List.map_take]

theorem polyhedralTrigonalPrismFrameCandidates_conforms_IR9
    (firstFace secondFace : List PolyhedralPriorityNumber) :
    (polyhedralTrigonalPrismFrameCandidates firstFace secondFace).map
        (List.map BlueBookP93.priorityOfProduction) =
      BlueBookP93.trigonalPrismFrameCandidates
        (firstFace.map BlueBookP93.priorityOfProduction)
        (secondFace.map BlueBookP93.priorityOfProduction) := by
  have mapFamily (left right : List PolyhedralPriorityNumber) :
      ((List.range 3).map (polyhedralTrigonalPrismFrame left right)).map
          (List.map BlueBookP93.priorityOfProduction) =
        (List.range 3).map
          (BlueBookP93.trigonalPrismFrame
            (left.map BlueBookP93.priorityOfProduction)
            (right.map BlueBookP93.priorityOfProduction)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro offset _
    exact polyhedralTrigonalPrismFrame_conforms_IR9 left right offset
  simp only [polyhedralTrigonalPrismFrameCandidates,
    BlueBookP93.trigonalPrismFrameCandidates, List.map_append]
  rw [mapFamily firstFace secondFace, mapFamily firstFace.reverse secondFace.reverse,
    mapFamily secondFace firstFace, mapFamily secondFace.reverse firstFace.reverse]
  simp only [List.map_reverse]

theorem mostSeniorPolyhedralPrioritySequence_conforms_IR9
    (candidates : List (List PolyhedralPriorityNumber)) :
    (mostSeniorPolyhedralPrioritySequence candidates).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.mostSeniorPrioritySequence
        (candidates.map (List.map BlueBookP93.priorityOfProduction)) := by
  unfold mostSeniorPolyhedralPrioritySequence BlueBookP93.mostSeniorPrioritySequence
  cases candidates with
  | nil => rfl
  | cons first rest =>
      simpa using canonicalCycleFold_conforms_IR9 rest first

theorem trigonalPrismConfigurationIndex_conforms_IR9
    (firstFace secondFace : List PolyhedralPriorityNumber) :
    (trigonalPrismConfigurationIndex firstFace secondFace).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.trigonalPrismIndex
        (firstFace.map BlueBookP93.priorityOfProduction)
        (secondFace.map BlueBookP93.priorityOfProduction) := by
  unfold trigonalPrismConfigurationIndex BlueBookP93.trigonalPrismIndex
  rw [List.map_drop, mostSeniorPolyhedralPrioritySequence_conforms_IR9,
    polyhedralTrigonalPrismFrameCandidates_conforms_IR9]

theorem canonicalPolyhedralCycle_conforms_IR9 (priorities : List PolyhedralPriorityNumber) :
    (canonicalPolyhedralCycle priorities).map BlueBookP93.priorityOfProduction =
      BlueBookP93.canonicalCycle (priorities.map BlueBookP93.priorityOfProduction) := by
  let candidates :=
    polyhedralCyclicRotations priorities ++ polyhedralCyclicRotations priorities.reverse
  have mappedCandidates :
      candidates.map (List.map BlueBookP93.priorityOfProduction) =
        BlueBookP93.cyclicRotations (priorities.map BlueBookP93.priorityOfProduction) ++
          BlueBookP93.cyclicRotations
            (priorities.map BlueBookP93.priorityOfProduction).reverse := by
    simp only [candidates, List.map_append]
    rw [polyhedralCyclicRotations_conforms_IR9,
      polyhedralCyclicRotations_conforms_IR9, List.map_reverse]
  change
    ((match candidates with
      | [] => []
      | first :: rest => rest.foldl (fun best candidate =>
          if comparePolyhedralPrioritySequence candidate best == Ordering.gt
          then candidate else best) first).map BlueBookP93.priorityOfProduction) =
      (match
        BlueBookP93.cyclicRotations (priorities.map BlueBookP93.priorityOfProduction) ++
          BlueBookP93.cyclicRotations
            (priorities.map BlueBookP93.priorityOfProduction).reverse with
       | [] => []
       | first :: rest => rest.foldl (fun best candidate =>
          if BlueBookP93.comparePrioritySequence candidate best == Ordering.gt
          then candidate else best) first)
  rw [← mappedCandidates]
  cases candidates with
  | nil => rfl
  | cons first rest =>
      simpa using canonicalCycleFold_conforms_IR9 rest first

theorem orderPolyhedralPair_conforms_IR9
    (first second : PolyhedralPriorityNumber) :
    (orderPolyhedralPair first second).map BlueBookP93.priorityOfProduction =
      BlueBookP93.orderedPair (BlueBookP93.priorityOfProduction first)
        (BlueBookP93.priorityOfProduction second) := by
  unfold orderPolyhedralPair BlueBookP93.orderedPair
  rw [show (BlueBookP93.priorityOfProduction second).seniorTo
      (BlueBookP93.priorityOfProduction first) = second.outranks first from rfl]
  cases second.outranks first <;> rfl

theorem bipyramidalConfigurationIndex_conforms_IR9
    (firstAxial secondAxial : PolyhedralPriorityNumber)
    (perpendicularPlane : List PolyhedralPriorityNumber) :
    (bipyramidalConfigurationIndex firstAxial secondAxial perpendicularPlane).map
        (List.map BlueBookP93.priorityOfProduction) =
      BlueBookP93.bipyramidalIndex
        (BlueBookP93.priorityOfProduction firstAxial)
        (BlueBookP93.priorityOfProduction secondAxial)
        (perpendicularPlane.map BlueBookP93.priorityOfProduction) := by
  unfold bipyramidalConfigurationIndex BlueBookP93.bipyramidalIndex
  simp only [List.map_cons, List.map_nil]
  rw [canonicalPolyhedralCycle_conforms_IR9, orderPolyhedralPair_conforms_IR9]

theorem polyhedral_chirality_conforms_P93 (sense : PolyhedralRotationSense) :
    BlueBookP93.chiralityOfProduction (PolyhedralChiralitySymbol.ofRotation sense) =
      BlueBookP93.chiralitySymbol (BlueBookP93.rotationOfProduction sense) := by
  cases sense <;> rfl

/-- Checked package for the descriptor-forming P-93.3 primitives.  Geometry recognition and
CIP-to-priority-number assignment are intentionally separate future obligations. -/
structure PrimitiveP93PolyhedralConformance : Prop where
  geometrySymbol : ∀ geometry, geometry.symbol =
    (BlueBookP93.geometryOfProduction geometry).symbol
  coordinationNumber : ∀ geometry, geometry.coordinationNumber =
    (BlueBookP93.geometryOfProduction geometry).coordinationNumber
  priority : ∀ left right, comparePolyhedralPriority left right =
    BlueBookP93.priorityDecision (BlueBookP93.priorityOfProduction left)
      (BlueBookP93.priorityOfProduction right)
  transMaximum : ∀ left right, polyhedralTransMaximumDecision left right =
    BlueBookP93.transMaximumDecision (BlueBookP93.priorityOfProduction left)
      (BlueBookP93.priorityOfProduction right)
  tShapeIndex : ∀ stem,
    (tShapeConfigurationIndex stem).map BlueBookP93.priorityOfProduction =
      BlueBookP93.tShapeIndex (BlueBookP93.priorityOfProduction stem)
  squarePlanarIndex : ∀ transToOne,
    (squarePlanarConfigurationIndex transToOne).map BlueBookP93.priorityOfProduction =
      BlueBookP93.squarePlanarIndex (BlueBookP93.priorityOfProduction transToOne)
  squarePyramid4Index : ∀ transToSenior,
    (squarePyramid4ConfigurationIndex transToSenior).map BlueBookP93.priorityOfProduction =
      BlueBookP93.squarePyramid4Index (BlueBookP93.priorityOfProduction transToSenior)
  seeSawIndex : ∀ first second,
    (seeSawConfigurationIndex first second).map BlueBookP93.priorityOfProduction =
      BlueBookP93.seeSawIndex (BlueBookP93.priorityOfProduction first)
        (BlueBookP93.priorityOfProduction second)
  trigonalBipyramidIndex : ∀ first second,
    (trigonalBipyramidConfigurationIndex first second).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.trigonalBipyramidIndex (BlueBookP93.priorityOfProduction first)
        (BlueBookP93.priorityOfProduction second)
  squarePyramidIndex : ∀ apical transToSeniorBase,
    (squarePyramidConfigurationIndex apical transToSeniorBase).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.squarePyramidIndex (BlueBookP93.priorityOfProduction apical)
        (BlueBookP93.priorityOfProduction transToSeniorBase)
  octahedronIndex : ∀ transToOne transToSeniorPlane,
    (octahedronConfigurationIndex transToOne transToSeniorPlane).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.octahedronIndex (BlueBookP93.priorityOfProduction transToOne)
        (BlueBookP93.priorityOfProduction transToSeniorPlane)
  trigonalPrismIndex : ∀ firstFace secondFace,
    (trigonalPrismConfigurationIndex firstFace secondFace).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.trigonalPrismIndex
        (firstFace.map BlueBookP93.priorityOfProduction)
        (secondFace.map BlueBookP93.priorityOfProduction)
  bipyramidalIndex : ∀ firstAxial secondAxial perpendicularPlane,
    (bipyramidalConfigurationIndex firstAxial secondAxial perpendicularPlane).map
        (List.map BlueBookP93.priorityOfProduction) =
      BlueBookP93.bipyramidalIndex
        (BlueBookP93.priorityOfProduction firstAxial)
        (BlueBookP93.priorityOfProduction secondAxial)
        (perpendicularPlane.map BlueBookP93.priorityOfProduction)
  chirality : ∀ sense,
    BlueBookP93.chiralityOfProduction (PolyhedralChiralitySymbol.ofRotation sense) =
      BlueBookP93.chiralitySymbol (BlueBookP93.rotationOfProduction sense)

theorem primitiveP93Polyhedral_conforms : PrimitiveP93PolyhedralConformance where
  geometrySymbol := polyhedral_geometry_symbol_conforms_P93
  coordinationNumber := polyhedral_geometry_coordination_conforms_P93
  priority := polyhedral_priority_conforms_P93
  transMaximum := polyhedral_transMaximum_conforms_P93
  tShapeIndex := tShapeConfigurationIndex_conforms_P93
  squarePlanarIndex := squarePlanarConfigurationIndex_conforms_IR9
  squarePyramid4Index := squarePyramid4ConfigurationIndex_conforms_IR9
  seeSawIndex := seeSawConfigurationIndex_conforms_P93
  trigonalBipyramidIndex := trigonalBipyramidConfigurationIndex_conforms_P93
  squarePyramidIndex := squarePyramidConfigurationIndex_conforms_P93
  octahedronIndex := octahedronConfigurationIndex_conforms_P93
  trigonalPrismIndex := trigonalPrismConfigurationIndex_conforms_IR9
  bipyramidalIndex := bipyramidalConfigurationIndex_conforms_IR9
  chirality := polyhedral_chirality_conforms_P93

end TetraStereo.OneCenter
