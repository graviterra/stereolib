import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76FiniteAudit
import TetraStereo.OneCenter.P93MolecularFullereneFiniteFaceCertificate

set_option autoImplicit false

/-!
# Frozen P-93 C76 transcription and finite table bridge

This leaf caches the one concrete comparison between the reviewed source edge list and the
lexicographic table generated from its faces.  Downstream certificate assembly consumes only the
kernel-checked equality and structural generic theorems, avoiding repeated normalization.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

/-- Exact typed source record for the right-hand numbered C76 cage in P-93.5.6.2, example II. -/
def iupacP93CanonicalFullereneC76Transcription : NumberedFaceTranscription where
  designation := .c76D2
  atomCount := 76
  atomCountExact := rfl
  faces := iupacP93CanonicalFullereneC76Faces
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 80
  pdfPageExact := rfl
  printedDesignation := "(C76-D2)[5,6]fullerene"
  printedDesignationExact := rfl
  auditLocator :=
    "PDF page 80, P-93.5.6.2 example II, right-hand numbered (f,sC)-(C76-D2)[5,6]fullerene figure"
  auditLocatorNonempty := by decide

theorem iupacP93CanonicalFullereneC76Transcription_atomsByLocant :
    iupacP93CanonicalFullereneC76Transcription.atomsByLocant = List.range 76 := by
  rfl

theorem iupacP93CanonicalFullereneC76Transcription_faces :
    iupacP93CanonicalFullereneC76Transcription.faces =
      iupacP93CanonicalFullereneC76Faces := by
  rfl

theorem iupacP93CanonicalFullereneC76Transcription_start_face_present :
    iupacP93CanonicalFullereneC76FsCStartFace ∈
      iupacP93CanonicalFullereneC76Transcription.faces :=
  iupacP93CanonicalFullereneC76_start_face_present

theorem iupacP93CanonicalFullereneC76Transcription_start_progression :
    iupacP93CanonicalFullereneC76FsCStartFace.take 3 = [0, 1, 2] :=
  iupacP93CanonicalFullereneC76_start_progression

def iupacP93CanonicalFullereneC76NumberedPackage :
    BlueBookP93.Cyclic.MolecularFullereneNumberedCagePackage :=
  iupacP93CanonicalFullereneC76Transcription.numberedPackage

theorem iupacP93CanonicalFullereneC76NumberedPackage_faces :
    iupacP93CanonicalFullereneC76NumberedPackage.faces =
      iupacP93CanonicalFullereneC76Faces := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every reviewed source edge occurs in the face-generated lexicographic table.  This finite
check ranges over the 114 source edges only. -/
theorem iupacP93CanonicalFullereneC76_sourceEdgesInEdgeTable :
    iupacP93CanonicalFullereneC76Edges.all (fun edge =>
      decide (edge ∈ iupacP93CanonicalFullereneC76Transcription.edgeTable)) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The generated table has the Euler-forced 114 edge records.  Kept separate from source
containment so neither proof constructs a concrete Finset equality. -/
theorem iupacP93CanonicalFullereneC76_edgeTableLength :
    iupacP93CanonicalFullereneC76Transcription.edgeTable.length = 114 := by
  decide

/-- The generated lexicographic edge table and independently source-derived edge list denote the
same undirected graph.  Equality follows symbolically from source containment and equal finite
cardinality; it is never decided directly. -/
theorem iupacP93CanonicalFullereneC76_edgeTable_toFinset :
    iupacP93CanonicalFullereneC76Transcription.edgeTable.toFinset =
      iupacP93CanonicalFullereneC76Edges.toFinset := by
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge edgePresent
    have sourcePresent : edge ∈ iupacP93CanonicalFullereneC76Edges := by
      simpa using edgePresent
    have accepted := (List.all_eq_true.mp
      iupacP93CanonicalFullereneC76_sourceEdgesInEdgeTable) edge sourcePresent
    simpa using of_decide_eq_true accepted
  · rw [List.toFinset_card_of_nodup iupacP93CanonicalFullereneC76_edgesNodup,
      List.toFinset_card_of_nodup
        (numberedFaceTranscription_edgeTable_nodup
          iupacP93CanonicalFullereneC76Transcription),
      iupacP93CanonicalFullereneC76_edge_count,
      iupacP93CanonicalFullereneC76_edgeTableLength]

/-- Duplicate-freedom of the generated table is structural for every transcription. -/
def iupacP93CanonicalFullereneC76TableAudit :
    FaceDerivedTableAudit iupacP93CanonicalFullereneC76Transcription :=
  FaceDerivedTableAudit.canonical iupacP93CanonicalFullereneC76Transcription

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC76_edgeTable_toFinset
