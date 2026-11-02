import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70SourceData
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Cycle

set_option autoImplicit false









namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

/-- Executable source-edge incidence, using the already deduplicated canonical edge list. -/
def iupacP93CanonicalFullereneC70HasSourceEdge (left right : Nat) : Bool :=
  iupacP93CanonicalFullereneC70Edges.contains
    (iupacP93C70CanonicalEdge (left, right))

/-- Executable forward adjacency, definitionally aligned with the generic face-map compiler. -/
def iupacP93CanonicalFullereneC70HasForwardNamedFaceEdge
    (face : List Nat) (left right : Nat) : Bool :=
  face.contains left && face.nextOr left (face.head?.getD left) == right

/-- Executable unoriented adjacency in one supplied cyclic face. -/
def iupacP93CanonicalFullereneC70HasNamedFaceEdge
    (face : List Nat) (left right : Nat) : Bool :=
  iupacP93CanonicalFullereneC70HasForwardNamedFaceEdge face left right ||
    iupacP93CanonicalFullereneC70HasForwardNamedFaceEdge face right left

/-- Executable source face-map incidence, definitionally aligned with the generated
transcription's `hasFaceEdge`. -/
def iupacP93CanonicalFullereneC70HasFaceEdge (left right : Nat) : Bool :=
  iupacP93CanonicalFullereneC70Faces.any fun face =>
    iupacP93CanonicalFullereneC70HasNamedFaceEdge face left right

theorem iupacP93CanonicalFullereneC70_facesNodup :
    (iupacP93CanonicalFullereneC70Faces.map List.toFinset).Nodup := by
  decide

theorem iupacP93CanonicalFullereneC70_eachFaceNodup :
    iupacP93CanonicalFullereneC70Faces.all (fun face => decide face.Nodup) = true := by
  decide

theorem iupacP93CanonicalFullereneC70_faceSizes :
    iupacP93CanonicalFullereneC70Faces.all (fun face =>
      decide (face.length = 5 ∨ face.length = 6)) = true := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC70_vertexFinset :
    iupacP93CanonicalFullereneC70Faces.flatten.toFinset = Finset.range 70 := by
  decide

theorem iupacP93CanonicalFullereneC70_edgesNodup :
    iupacP93CanonicalFullereneC70Edges.Nodup := by
  decide

theorem iupacP93CanonicalFullereneC70_edgesCanonicalAndBounded :
    iupacP93CanonicalFullereneC70Edges.all (fun edge =>
      decide (edge.1 < edge.2 ∧ edge.1 < 70 ∧ edge.2 < 70)) = true := by
  decide

set_option maxRecDepth 10000 in
/-- Every transcribed face is induced in the source-derived cage graph.  The equality is checked
only for pairs of vertices of that face; it does not scan the ambient natural numbers. -/
theorem iupacP93CanonicalFullereneC70_facesInduced :
    iupacP93CanonicalFullereneC70Faces.all (fun face =>
      face.all (fun left => face.all (fun right =>
        if left = right then true
        else iupacP93CanonicalFullereneC70HasFaceEdge left right ==
          iupacP93CanonicalFullereneC70HasNamedFaceEdge face left right))) = true := by
  decide

/-- Every directed edge in every closed source face occurs in the source cage edge set. -/
theorem iupacP93CanonicalFullereneC70_facesCyclicEdges :
    iupacP93CanonicalFullereneC70Faces.all (fun face =>
      (iupacP93C70DirectedFaceEdges face).all (fun edge =>
        iupacP93CanonicalFullereneC70HasSourceEdge edge.1 edge.2)) = true := by
  decide

/-- Every source cage edge belongs to exactly two named faces. -/
theorem iupacP93CanonicalFullereneC70_twoNamedFacesPerEdge :
    iupacP93CanonicalFullereneC70Edges.all (fun edge =>
      decide (iupacP93CanonicalFullereneC70Faces.countP
        (fun face => iupacP93CanonicalFullereneC70HasNamedFaceEdge
          face edge.1 edge.2) = 2)) = true := by
  decide

set_option maxRecDepth 10000 in
/-- The two incident source faces traverse every canonical edge in opposite directions. -/
theorem iupacP93CanonicalFullereneC70_oppositeNamedFaceOrientations :
    iupacP93CanonicalFullereneC70Edges.all (fun edge =>
      decide (iupacP93CanonicalFullereneC70Faces.countP
          (fun face => iupacP93CanonicalFullereneC70HasForwardNamedFaceEdge
            face edge.1 edge.2) = 1 ∧
        iupacP93CanonicalFullereneC70Faces.countP
          (fun face => iupacP93CanonicalFullereneC70HasForwardNamedFaceEdge
            face edge.2 edge.1) = 1)) = true := by
  decide

/-- All sixty-nine consecutive systematic locant edges occur in the source graph. -/
theorem iupacP93CanonicalFullereneC70_consecutiveSourceEdges :
    (List.range 69).all (fun atom =>
      iupacP93CanonicalFullereneC70HasSourceEdge atom (atom + 1)) = true := by
  decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
