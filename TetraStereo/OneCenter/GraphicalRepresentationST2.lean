import TetraStereo.OneCenter.GraphicalRepresentationST0
import TetraStereo.OneCenter.PolyhedralConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent IUPAC 2006 graphical semantics: ST-2

ST-2 is about recognizing and unambiguously depicting coordination geometry, not merely printing a
polyhedral symbol.  This module records the thirteen section domains, their exact symbols and
coordination numbers, the element/explicit-ligand applicability exclusions, and the evidence a 2D
drawing must provide.  Detailed coordinate-to-figure recognition remains a later relation carried
by `matchesPreferredFigureGeometry`.
-/

namespace IUPACDrawing2006.ST2

open ST0

inductive GeometrySection where
  | linear
  | angular
  | tShaped
  | trigonalPlanar
  | trigonalPyramidal
  | squarePlanar
  | squarePyramidalFour
  | seeSaw
  | trigonalBipyramidal
  | squarePyramidalFive
  | octahedral
  | trigonalPrismatic
  | higherCoordination
  deriving DecidableEq, Repr

namespace GeometrySection

def all : List GeometrySection :=
  [ .linear, .angular, .tShaped, .trigonalPlanar, .trigonalPyramidal, .squarePlanar
  , .squarePyramidalFour, .seeSaw, .trigonalBipyramidal, .squarePyramidalFive
  , .octahedral, .trigonalPrismatic, .higherCoordination
  ]

@[simp] theorem mem_all (geometry : GeometrySection) : geometry ∈ all := by
  cases geometry <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 13 := by decide

def sourceSection : GeometrySection → String
  | .linear => "ST-2.1"
  | .angular => "ST-2.2"
  | .tShaped => "ST-2.3"
  | .trigonalPlanar => "ST-2.4"
  | .trigonalPyramidal => "ST-2.5"
  | .squarePlanar => "ST-2.6"
  | .squarePyramidalFour => "ST-2.7"
  | .seeSaw => "ST-2.8"
  | .trigonalBipyramidal => "ST-2.9"
  | .squarePyramidalFive => "ST-2.10"
  | .octahedral => "ST-2.11"
  | .trigonalPrismatic => "ST-2.12"
  | .higherCoordination => "ST-2.13"

def polyhedralGeometry? : GeometrySection → Option BlueBookP93.Geometry
  | .linear => some .linear
  | .angular => some .angular
  | .tShaped => some .tShape
  | .trigonalPlanar => some .trigonalPlanar
  | .trigonalPyramidal => some .trigonalPyramid
  | .squarePlanar => some .squarePlanar
  | .squarePyramidalFour => some .squarePyramid4
  | .seeSaw => some .seeSaw
  | .trigonalBipyramidal => some .trigonalBipyramid
  | .squarePyramidalFive => some .squarePyramid
  | .octahedral => some .octahedron
  | .trigonalPrismatic => some .trigonalPrism
  | .higherCoordination => none

def symbol? (geometry : GeometrySection) : Option String :=
  (geometry.polyhedralGeometry?).map BlueBookP93.Geometry.symbol

def fixedCoordination? (geometry : GeometrySection) : Option ℕ :=
  (geometry.polyhedralGeometry?).map BlueBookP93.Geometry.coordinationNumber

@[simp] theorem symbol_table_exact : all.map symbol? =
    [ some "L-2", some "A-2", some "TS-3", some "TP-3", some "TPY-3", some "SP-4"
    , some "SPY-4", some "SS-4", some "TBPY-5", some "SPY-5", some "OC-6"
    , some "TPR-6", none
    ] := by
  decide

def IsPlanar : GeometrySection → Prop
  | .linear | .angular | .tShaped | .trigonalPlanar | .squarePlanar => True
  | _ => False

def RequiresAllLigandsExplicit : GeometrySection → Prop
  | .tShaped | .trigonalPlanar | .trigonalPyramidal => True
  | _ => False

def RejectsCarbonOrNitrogenCenter : GeometrySection → Prop
  | .tShaped => True
  | _ => False

def RejectsCarbonGroupIsoelectronicCenter : GeometrySection → Prop
  | .squarePyramidalFour | .seeSaw => True
  | _ => False

/-- Nonplanar geometries for which an all-plain drawing cannot communicate a known absolute
configuration. -/
def KnownChiralityRequiresStereoBonds : GeometrySection → Prop
  | .trigonalPyramidal | .squarePyramidalFour | .seeSaw | .trigonalBipyramidal
  | .squarePyramidalFive | .octahedral | .trigonalPrismatic => True
  | _ => False

end GeometrySection

structure DrawingObservation where
  geometry : GeometrySection
  ligandCount : ℕ
  allLigandsExplicit : Bool
  centralAtomClearlySingleAndLabeled : Bool
  centralAtomIsSP2Carbon : Bool
  centralAtomIsCarbonOrNitrogen : Bool
  centralAtomIsCarbonGroupIsoelectronic : Bool
  absoluteChiralityKnown : Bool
  usesSolidAndHashedStereoBonds : Bool
  polyhedralSolidWithoutCentralAtom : Bool
  /-- Exact angle, collinearity, bisector, bond-length, and perspective clauses from the preferred
  figure family for the selected section. -/
  matchesPreferredFigureGeometry : Prop

namespace DrawingObservation

def CoordinationCountCorrect (observation : DrawingObservation) : Prop :=
  match observation.geometry.fixedCoordination? with
  | some expected => observation.ligandCount = expected
  | none => 7 ≤ observation.ligandCount

def ExplicitLigandBoundary (observation : DrawingObservation) : Prop :=
  observation.geometry.RequiresAllLigandsExplicit →
    observation.allLigandsExplicit = true ∧
    (observation.centralAtomClearlySingleAndLabeled = true ∨
      (observation.geometry = .trigonalPlanar ∧ observation.centralAtomIsSP2Carbon = true))

def ElementBoundary (observation : DrawingObservation) : Prop :=
  (observation.geometry.RejectsCarbonOrNitrogenCenter →
      observation.centralAtomIsCarbonOrNitrogen = false) ∧
  (observation.geometry.RejectsCarbonGroupIsoelectronicCenter →
      observation.centralAtomIsCarbonGroupIsoelectronic = false)

def ChiralityEvidenceBoundary (observation : DrawingObservation) : Prop :=
  observation.geometry.KnownChiralityRequiresStereoBonds →
    observation.absoluteChiralityKnown = true →
      observation.usesSolidAndHashedStereoBonds = true

def HigherCoordinationBoundary (observation : DrawingObservation) : Prop :=
  observation.geometry = .higherCoordination →
    observation.polyhedralSolidWithoutCentralAtom = true

/-- The conjunction that a production 2D recognizer must establish before calling a drawing a
preferred ST-2 depiction. -/
def Preferred (observation : DrawingObservation) : Prop :=
  observation.CoordinationCountCorrect ∧
  observation.ExplicitLigandBoundary ∧
  observation.ElementBoundary ∧
  observation.ChiralityEvidenceBoundary ∧
  observation.HigherCoordinationBoundary ∧
  observation.matchesPreferredFigureGeometry

theorem known_chiral_nonplanar_preferred_uses_stereobonds
    (observation : DrawingObservation)
    (preferred : observation.Preferred)
    (requires : observation.geometry.KnownChiralityRequiresStereoBonds)
    (known : observation.absoluteChiralityKnown = true) :
    observation.usesSolidAndHashedStereoBonds = true :=
  preferred.2.2.2.1 requires known

theorem higherCoordination_preferred_is_polyhedralSolid
    (observation : DrawingObservation)
    (preferred : observation.Preferred)
    (higher : observation.geometry = .higherCoordination) :
    observation.polyhedralSolidWithoutCentralAtom = true :=
  preferred.2.2.2.2.1 higher

end DrawingObservation

end IUPACDrawing2006.ST2

end TetraStereo.OneCenter
