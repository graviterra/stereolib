import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70SourceData
import TetraStereo.OneCenter.P93MolecularFullereneFiniteFaceCertificate

set_option autoImplicit false

/-!
# Frozen P-93 C70 transcription and finite table bridge

This leaf caches the one concrete comparison between the reviewed source edge list and the
lexicographic table generated from its faces.  Downstream certificate assembly consumes only the
kernel-checked equality and structural generic theorems, avoiding repeated normalization.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

/-- Exact typed source record for the numbered C70 cage shared by the P-93.5.6.5 and P-93.5.6.6
figures. -/
def iupacP93CanonicalFullereneC70Transcription : NumberedFaceTranscription where
  designation := .c70D5h6
  atomCount := 70
  atomCountExact := rfl
  faces := iupacP93CanonicalFullereneC70Faces
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 82
  pdfPageExact := rfl
  printedDesignation := "(C70-D5h(6))[5,6]fullerene"
  printedDesignationExact := rfl
  auditLocator :=
    "PDF pages 82-83, P-93.5.6.5 Type-4 and P-93.5.6.6 superimposed numbered C70 figures"
  auditLocatorNonempty := by decide

/-- Both source figures are definitionally tied to the single reviewed C70 topology. -/
theorem iupacP93CanonicalFullereneC70Transcription_shared_pages :
    iupacP93CanonicalFullereneC70Transcription.faces =
        iupacP93CanonicalFullereneC70Page82Faces ∧
      iupacP93CanonicalFullereneC70Transcription.faces =
        iupacP93CanonicalFullereneC70Page83Faces := by
  exact ⟨rfl, rfl⟩

/-- The generated locant carrier is exactly the seventy zero-based printed locants. -/
theorem iupacP93CanonicalFullereneC70Transcription_atomsByLocant :
    iupacP93CanonicalFullereneC70Transcription.atomsByLocant = List.range 70 := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The generated lexicographic edge table and the independently source-derived edge list denote
the same undirected graph.  This is the only concrete generated-table normalization. -/
theorem iupacP93CanonicalFullereneC70_edgeTable_toFinset :
    iupacP93CanonicalFullereneC70Transcription.edgeTable.toFinset =
      iupacP93CanonicalFullereneC70Edges.toFinset := by
  decide

/-- Duplicate-freedom of the generated table is structural for every transcription. -/
def iupacP93CanonicalFullereneC70TableAudit :
    FaceDerivedTableAudit iupacP93CanonicalFullereneC70Transcription :=
  FaceDerivedTableAudit.canonical iupacP93CanonicalFullereneC70Transcription

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70_edgeTable_toFinset
