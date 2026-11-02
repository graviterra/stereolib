import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.OneCenter.P93MolecularFullereneNumberedCageCompiler

set_option autoImplicit false

/-!
# Source-only numbered fullerene face transcriptions

This module is the irreducible source-data boundary for the three P-93.5.6 cage diagrams.  It
contains only typed source identity and executable projections of a coherently oriented face
transcription.  In particular, it has no dependency on the canonical P-93 source-claim inventory
or on the proof-carrying derivative program assembled from these transcriptions.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

namespace P93CanonicalProgramFullerene

/-- The three cage identities actually printed in P-93.5.6.  This is not inferred from vertex
count: it is the typed name attached to the independently reviewed face transcription. -/
inductive CageDesignation where
  | c76D2
  | c60Ih
  | c70D5h6
  deriving DecidableEq, Repr

namespace CageDesignation

def atomCount : CageDesignation → Nat
  | .c76D2 => 76
  | .c60Ih => 60
  | .c70D5h6 => 70

def printedName : CageDesignation → String
  | .c76D2 => "(C76-D2)[5,6]fullerene"
  | .c60Ih => "(C60-Ih)[5,6]fullerene"
  | .c70D5h6 => "(C70-D5h(6))[5,6]fullerene"


def facePage : CageDesignation → Nat
  | .c76D2 => 80
  | .c60Ih => 81
  | .c70D5h6 => 82

end CageDesignation

/-- Irreducible raster-transcription boundary.  Atom `i` is printed locant `i + 1`; the faces are
the complete coherently oriented facial rotation system, expressed with these zero-based atoms. -/
structure NumberedFaceTranscription where
  designation : CageDesignation
  atomCount : Nat
  atomCountExact : atomCount = designation.atomCount
  faces : List (List Nat)
  normativeSource : IUPACNormativeSource
  sourceIsBlueBookP9 : normativeSource = .blueBook2013P9
  artifactSha256 : String
  artifactSha256Exact :
    artifactSha256 = "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  pdfPage : Nat
  pdfPageExact : pdfPage = designation.facePage
  printedDesignation : String
  printedDesignationExact : printedDesignation = designation.printedName
  auditLocator : String
  auditLocatorNonempty : auditLocator ≠ ""
  deriving DecidableEq, Repr

namespace NumberedFaceTranscription

/-- Executable undirected incidence in at least one transcribed face. -/
def hasFaceEdge (transcription : NumberedFaceTranscription) (left right : Nat) : Bool :=
  transcription.faces.any fun face =>
    isForwardMolecularFullereneFaceEdge face left right ||
      isForwardMolecularFullereneFaceEdge face right left

/-- The unique canonical increasing edge table derived from the face transcription.  The
quadratic range is bounded by at most 76 atoms for the three P-93 examples and does not enumerate
paths, permutations, or automorphisms. -/
def edgeTable (transcription : NumberedFaceTranscription) : List (Nat × Nat) :=
  (List.range transcription.atomCount).flatMap fun left =>
    ((List.range transcription.atomCount).filter fun right =>
      decide (left < right) && transcription.hasFaceEdge left right).map fun right =>
        (left, right)

/-- Source locant `i + 1` is represented by raw atom `i`. -/
def atomsByLocant (transcription : NumberedFaceTranscription) : List Nat :=
  List.range transcription.atomCount

def numberedPackage (transcription : NumberedFaceTranscription) :
    MolecularFullereneNumberedCagePackage where
  atomsByLocant := transcription.atomsByLocant
  edgeTable := transcription.edgeTable
  faces := transcription.faces

def carbonAtom : AtomSpec := AtomSpec.aliphatic .C

def singleBond (edge : Nat × Nat) : RawBond where
  source := edge.1
  target := edge.2
  kind := .single

/-- The all-carbon cage core generated from the same face table.  Substituents are intentionally
absent: complete printed derivative molecules enter through the canonical derivative program. -/
def cageMolecule (transcription : NumberedFaceTranscription) : RawMolecule where
  atoms := List.replicate transcription.atomCount carbonAtom
  bonds := transcription.edgeTable.map singleBond

end NumberedFaceTranscription

/-- A single proof-carrying numbered cage.  This source-only carrier is shared by the C60, C70,
and C76 cage packages; derivative observations and source claims live strictly downstream. -/
structure SharedNumberedCage where
  transcription : NumberedFaceTranscription
  certificate : transcription.numberedPackage.Certificate transcription.cageMolecule

namespace SharedNumberedCage

def numberedPackage (cage : SharedNumberedCage) : MolecularFullereneNumberedCagePackage :=
  cage.transcription.numberedPackage

def coreMolecule (cage : SharedNumberedCage) : RawMolecule :=
  cage.transcription.cageMolecule

end SharedNumberedCage
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
