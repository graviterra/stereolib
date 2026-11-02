import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC60FiniteAudit
import TetraStereo.OneCenter.P93MolecularFullereneFiniteFaceCertificate

set_option autoImplicit false

/-!
# Frozen P-93 C60 transcription and finite table bridge

This leaf caches the concrete source-edge containment and generated-table cardinality checks.
Their symbolic combination proves exact edge-set equality without deciding an ambient pair
Finset equality in the downstream cage certificate.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

/-- Exact typed source record for the numbered C60 cage shared by the Type-2 and Type-3
derivatives on Blue Book page 81. -/
def iupacP93CanonicalFullereneC60Transcription : NumberedFaceTranscription where
  designation := .c60Ih
  atomCount := 60
  atomCountExact := rfl
  faces := iupacP93CanonicalFullereneC60Faces
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 81
  pdfPageExact := rfl
  printedDesignation := "(C60-Ih)[5,6]fullerene"
  printedDesignationExact := rfl
  auditLocator :=
    "PDF page 81, P-93.5.6.3, numbered C60 cage shared by the Type-2 and Type-3 derivatives"
  auditLocatorNonempty := by decide


def iupacP93CanonicalFullereneC60RasterSha256 : String :=
  "aeb461b44214b944af5fd02739403c2f5576784acdcb69bbe5c64ebe5376b1db"

theorem iupacP93CanonicalFullereneC60Transcription_atomsByLocant :
    iupacP93CanonicalFullereneC60Transcription.atomsByLocant = List.range 60 := by
  rfl

theorem iupacP93CanonicalFullereneC60Transcription_faces :
    iupacP93CanonicalFullereneC60Transcription.faces =
      iupacP93CanonicalFullereneC60Faces := by
  rfl

def iupacP93CanonicalFullereneC60NumberedPackage :
    BlueBookP93.Cyclic.MolecularFullereneNumberedCagePackage :=
  iupacP93CanonicalFullereneC60Transcription.numberedPackage

theorem iupacP93CanonicalFullereneC60NumberedPackage_faces :
    iupacP93CanonicalFullereneC60NumberedPackage.faces =
      iupacP93CanonicalFullereneC60Faces := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every reviewed source edge occurs in the generated lexicographic table. -/
theorem iupacP93CanonicalFullereneC60_sourceEdgesInEdgeTable :
    iupacP93CanonicalFullereneC60Edges.all (fun edge =>
      decide (edge ∈ iupacP93CanonicalFullereneC60Transcription.edgeTable)) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The generated table contains exactly the ninety edges of a C60 fullerene cage. -/
theorem iupacP93CanonicalFullereneC60_edgeTableLength :
    iupacP93CanonicalFullereneC60Transcription.edgeTable.length = 90 := by
  decide

/-- Exact generated/source edge-set equality, derived from containment and equal cardinality. -/
theorem iupacP93CanonicalFullereneC60_edgeTable_toFinset :
    iupacP93CanonicalFullereneC60Transcription.edgeTable.toFinset =
      iupacP93CanonicalFullereneC60Edges.toFinset := by
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge edgePresent
    have sourcePresent : edge ∈ iupacP93CanonicalFullereneC60Edges := by
      simpa using edgePresent
    have accepted := (List.all_eq_true.mp
      iupacP93CanonicalFullereneC60_sourceEdgesInEdgeTable) edge sourcePresent
    simpa using of_decide_eq_true accepted
  · rw [List.toFinset_card_of_nodup iupacP93CanonicalFullereneC60_edgesNodup,
      List.toFinset_card_of_nodup
        (numberedFaceTranscription_edgeTable_nodup
          iupacP93CanonicalFullereneC60Transcription),
      iupacP93CanonicalFullereneC60_edge_count,
      iupacP93CanonicalFullereneC60_edgeTableLength]

def iupacP93CanonicalFullereneC60TableAudit :
    FaceDerivedTableAudit iupacP93CanonicalFullereneC60Transcription :=
  FaceDerivedTableAudit.canonical iupacP93CanonicalFullereneC60Transcription

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60_edgeTable_toFinset
