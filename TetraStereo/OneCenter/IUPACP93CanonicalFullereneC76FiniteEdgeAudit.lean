import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76FiniteAuditCore

set_option autoImplicit false

/-! # Edge-incidence finite audits for the P-93 C76 transcription -/

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

/-- Every source cage edge belongs to exactly two named faces. -/
theorem iupacP93CanonicalFullereneC76_twoNamedFacesPerEdge :
    iupacP93CanonicalFullereneC76Edges.all (fun edge =>
      decide (iupacP93CanonicalFullereneC76Faces.countP
        (fun face => iupacP93CanonicalFullereneC76HasNamedFaceEdge
          face edge.1 edge.2) = 2)) = true := by
  decide

set_option maxRecDepth 10000 in
/-- The two incident source faces traverse every canonical edge in opposite directions. -/
theorem iupacP93CanonicalFullereneC76_oppositeNamedFaceOrientations :
    iupacP93CanonicalFullereneC76Edges.all (fun edge =>
      decide (iupacP93CanonicalFullereneC76Faces.countP
          (fun face => iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge
            face edge.1 edge.2) = 1 ∧
        iupacP93CanonicalFullereneC76Faces.countP
          (fun face => iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge
            face edge.2 edge.1) = 1)) = true := by
  decide

/-- All seventy-five consecutive systematic locant edges occur in the source graph. -/
theorem iupacP93CanonicalFullereneC76_consecutiveSourceEdges :
    (List.range 75).all (fun atom =>
      iupacP93CanonicalFullereneC76HasSourceEdge atom (atom + 1)) = true := by
  decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
