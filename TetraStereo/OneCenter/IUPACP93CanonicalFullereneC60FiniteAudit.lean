import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC60SourceData
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Cycle
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false









namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

/-- Executable source-edge incidence, using the already deduplicated canonical edge list. -/
def iupacP93CanonicalFullereneC60HasSourceEdge (left right : Nat) : Bool :=
  iupacP93CanonicalFullereneC60Edges.contains
    (iupacP93C60CanonicalEdge (left, right))

/-- Executable forward adjacency, definitionally aligned with the generic face-map compiler. -/
def iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge
    (face : List Nat) (left right : Nat) : Bool :=
  face.contains left && face.nextOr left (face.head?.getD left) == right

/-- Executable unoriented adjacency in one supplied cyclic face. -/
def iupacP93CanonicalFullereneC60HasNamedFaceEdge
    (face : List Nat) (left right : Nat) : Bool :=
  iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge face left right ||
    iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge face right left

/-- Executable incidence in the complete source face map, definitionally aligned with the
generated transcription's `hasFaceEdge`. -/
def iupacP93CanonicalFullereneC60HasFaceEdge (left right : Nat) : Bool :=
  iupacP93CanonicalFullereneC60Faces.any fun face =>
    iupacP93CanonicalFullereneC60HasNamedFaceEdge face left right

theorem iupacP93CanonicalFullereneC60_facesNodup :
    (iupacP93CanonicalFullereneC60Faces.map List.toFinset).Nodup := by
  decide

theorem iupacP93CanonicalFullereneC60_eachFaceNodup :
    iupacP93CanonicalFullereneC60Faces.all (fun face => decide face.Nodup) = true := by
  decide

theorem iupacP93CanonicalFullereneC60_faceSizes :
    iupacP93CanonicalFullereneC60Faces.all (fun face =>
      decide (face.length = 5 ∨ face.length = 6)) = true := by
  decide

/-- Pure face-adjacency neighbors, definitionally aligned with the generic transcription's
forward-or-reverse face predicate. -/
def iupacP93CanonicalFullereneC60FaceAdjacencyNeighbors (atom : Nat) : Finset Nat :=
  (Finset.range 60).filter fun neighbor =>
    neighbor ≠ atom ∧ iupacP93CanonicalFullereneC60HasFaceEdge atom neighbor = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every bounded source locant has exactly three face-adjacent cage neighbors. -/
theorem iupacP93CanonicalFullereneC60_faceAdjacencyDegree
    (atom : Nat) (atomBound : atom < 60) :
    (iupacP93CanonicalFullereneC60FaceAdjacencyNeighbors atom).card = 3 := by
  interval_cases atom <;> decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC60_vertexFinset :
    iupacP93CanonicalFullereneC60Faces.flatten.toFinset = Finset.range 60 := by
  decide

theorem iupacP93CanonicalFullereneC60_edgesNodup :
    iupacP93CanonicalFullereneC60Edges.Nodup := by
  decide

theorem iupacP93CanonicalFullereneC60_edgesCanonicalAndBounded :
    iupacP93CanonicalFullereneC60Edges.all (fun edge =>
      decide (edge.1 < edge.2 ∧ edge.1 < 60 ∧ edge.2 < 60)) = true := by
  decide

set_option maxRecDepth 10000 in
/- Every transcribed face is induced in the source-derived cage graph.  This checks only pairs
of vertices of that face and never scans the ambient natural numbers or a molecular bond fold. -/
theorem iupacP93CanonicalFullereneC60_facesInduced :
    iupacP93CanonicalFullereneC60Faces.all (fun face =>
      face.all (fun left => face.all (fun right =>
        if left = right then true
        else iupacP93CanonicalFullereneC60HasFaceEdge left right ==
          iupacP93CanonicalFullereneC60HasNamedFaceEdge face left right))) = true := by
  decide

/-- Every directed edge in every closed source face occurs in the source cage edge set. -/
theorem iupacP93CanonicalFullereneC60_facesCyclicEdges :
    iupacP93CanonicalFullereneC60Faces.all (fun face =>
      (iupacP93C60DirectedFaceEdges face).all (fun edge =>
        iupacP93CanonicalFullereneC60HasSourceEdge edge.1 edge.2)) = true := by
  decide

/-- Every source cage edge belongs to exactly two named faces. -/
theorem iupacP93CanonicalFullereneC60_twoNamedFacesPerEdge :
    iupacP93CanonicalFullereneC60Edges.all (fun edge =>
      decide (iupacP93CanonicalFullereneC60Faces.countP
        (fun face => iupacP93CanonicalFullereneC60HasNamedFaceEdge
          face edge.1 edge.2) = 2)) = true := by
  decide

set_option maxRecDepth 10000 in
/-- The two incident source faces traverse every canonical edge in opposite directions. -/
theorem iupacP93CanonicalFullereneC60_oppositeNamedFaceOrientations :
    iupacP93CanonicalFullereneC60Edges.all (fun edge =>
      decide (iupacP93CanonicalFullereneC60Faces.countP
          (fun face => iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge
            face edge.1 edge.2) = 1 ∧
        iupacP93CanonicalFullereneC60Faces.countP
          (fun face => iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge
            face edge.2 edge.1) = 1)) = true := by
  decide

/-- All fifty-nine consecutive systematic locant edges occur in the source graph. -/
theorem iupacP93CanonicalFullereneC60_consecutiveSourceEdges :
    (List.range 59).all (fun atom =>
      iupacP93CanonicalFullereneC60HasSourceEdge atom (atom + 1)) = true := by
  decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
