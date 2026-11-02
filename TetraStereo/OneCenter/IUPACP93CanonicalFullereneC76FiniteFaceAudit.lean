import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76FiniteAuditCore

set_option autoImplicit false

/-! # Face-local finite audits for the P-93 C76 transcription -/

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

set_option maxRecDepth 10000 in
/- Every transcribed face is induced in the source-derived cage graph.  This checks only pairs
of vertices of that face and never scans the ambient natural numbers or a molecular bond fold. -/
theorem iupacP93CanonicalFullereneC76_facesInduced :
    iupacP93CanonicalFullereneC76Faces.all (fun face =>
      face.all (fun left => face.all (fun right =>
        if left = right then true
        else iupacP93CanonicalFullereneC76HasSourceEdge left right ==
          iupacP93CanonicalFullereneC76HasNamedFaceEdge face left right))) = true := by
  decide

/-- Every closed source face edge belongs to the source cage edge set. -/
theorem iupacP93CanonicalFullereneC76_facesCyclicEdges :
    iupacP93CanonicalFullereneC76Faces.all (fun face =>
      (iupacP93C76DirectedFaceEdges face).all (fun edge =>
        iupacP93CanonicalFullereneC76HasSourceEdge edge.1 edge.2)) = true := by
  decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
