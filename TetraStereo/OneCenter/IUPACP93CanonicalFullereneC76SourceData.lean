import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic




















/-- The complete coherently oriented face map transcribed from the right-hand P-93 C76
figure.  Pentagons precede hexagons; locants are zero-based. -/
def iupacP93CanonicalFullereneC76Faces : List (List Nat) :=
  [ [4, 21, 22, 6, 5]
  , [7, 25, 26, 27, 8]
  , [11, 32, 33, 13, 12]
  , [14, 36, 37, 16, 15]
  , [17, 40, 41, 19, 18]
  , [23, 45, 46, 47, 24]
  , [28, 51, 52, 30, 29]
  , [34, 56, 57, 58, 35]
  , [38, 59, 60, 61, 39]
  , [42, 62, 63, 64, 43]
  , [48, 67, 68, 50, 49]
  , [53, 69, 70, 71, 54]
  , [0, 1, 2, 3, 4, 5]
  , [0, 5, 6, 7, 8, 9]
  , [0, 9, 10, 11, 12, 1]
  , [1, 12, 13, 14, 15, 2]
  , [2, 15, 16, 17, 18, 3]
  , [3, 18, 19, 20, 21, 4]
  , [6, 22, 23, 24, 25, 7]
  , [8, 27, 28, 29, 10, 9]
  , [10, 29, 30, 31, 32, 11]
  , [13, 33, 34, 35, 36, 14]
  , [16, 37, 38, 39, 40, 17]
  , [19, 41, 42, 43, 44, 20]
  , [20, 44, 45, 23, 22, 21]
  , [24, 47, 48, 49, 26, 25]
  , [26, 49, 50, 51, 28, 27]
  , [30, 52, 53, 54, 55, 31]
  , [31, 55, 56, 34, 33, 32]
  , [35, 58, 59, 38, 37, 36]
  , [39, 61, 62, 42, 41, 40]
  , [43, 64, 65, 46, 45, 44]
  , [46, 65, 66, 67, 48, 47]
  , [50, 68, 69, 53, 52, 51]
  , [54, 71, 72, 57, 56, 55]
  , [57, 72, 73, 60, 59, 58]
  , [60, 73, 74, 63, 62, 61]
  , [63, 74, 75, 66, 65, 64]
  , [66, 75, 70, 69, 68, 67]
  , [70, 75, 74, 73, 72, 71]
  ]

/-- The printed `(f,sC)` start face in its clockwise-from-outside `1 -> 2 -> 3`
orientation, converted to zero-based locants. -/
def iupacP93CanonicalFullereneC76FsCStartFace : List Nat :=
  [0, 1, 2, 3, 4, 5]

theorem iupacP93CanonicalFullereneC76_start_face_present :
    iupacP93CanonicalFullereneC76FsCStartFace ∈
      iupacP93CanonicalFullereneC76Faces := by
  decide

theorem iupacP93CanonicalFullereneC76_start_progression :
    iupacP93CanonicalFullereneC76FsCStartFace.take 3 = [0, 1, 2] := by
  decide

/-- Local source-data helper: consecutive directed edges, including the closing edge. -/
def iupacP93C76DirectedFaceEdges (face : List Nat) : List (Nat × Nat) :=
  face.zip (face.tail ++ face.take 1)

/-- Local source-data helper for the canonical representative of an undirected edge. -/
def iupacP93C76CanonicalEdge (edge : Nat × Nat) : Nat × Nat :=
  if edge.1 < edge.2 then edge else (edge.2, edge.1)

/-- All directed face-edge occurrences, retaining multiplicity and orientation. -/
def iupacP93CanonicalFullereneC76DirectedEdgeOccurrences : List (Nat × Nat) :=
  iupacP93CanonicalFullereneC76Faces.flatMap iupacP93C76DirectedFaceEdges

/-- The deduplicated canonical undirected cage edges derived only from the source faces. -/
def iupacP93CanonicalFullereneC76Edges : List (Nat × Nat) :=
  (iupacP93CanonicalFullereneC76DirectedEdgeOccurrences.map
    iupacP93C76CanonicalEdge).eraseDups

/-- Neighbors in the source-derived undirected cage graph. -/
def iupacP93CanonicalFullereneC76Neighbors (atom : Nat) : List Nat :=
  (iupacP93CanonicalFullereneC76Edges.filterMap fun edge =>
    if edge.1 = atom then some edge.2
    else if edge.2 = atom then some edge.1
    else none).eraseDups

/-- One monotone finite reachability expansion in the source-derived cage graph. -/
def iupacP93CanonicalFullereneC76ReachabilityStep (atoms : List Nat) : List Nat :=
  (atoms ++ atoms.flatMap iupacP93CanonicalFullereneC76Neighbors).eraseDups

/-- Iterate a fixed number of monotone reachability expansions. -/
def iupacP93CanonicalFullereneC76Reachable : Nat → List Nat → List Nat
  | 0, atoms => atoms
  | fuel + 1, atoms => iupacP93CanonicalFullereneC76Reachable fuel
      (iupacP93CanonicalFullereneC76ReachabilityStep atoms)

theorem iupacP93CanonicalFullereneC76Faces_length :
    iupacP93CanonicalFullereneC76Faces.length = 40 := by
  decide

theorem iupacP93CanonicalFullereneC76_pentagon_count :
    iupacP93CanonicalFullereneC76Faces.countP
      (fun face => decide (face.length = 5)) = 12 := by
  decide

theorem iupacP93CanonicalFullereneC76_hexagon_count :
    iupacP93CanonicalFullereneC76Faces.countP
      (fun face => decide (face.length = 6)) = 28 := by
  decide

theorem iupacP93CanonicalFullereneC76_vertex_bounds :
    iupacP93CanonicalFullereneC76Faces.all (fun face =>
      face.all (fun atom => atom < 76)) = true := by
  decide

theorem iupacP93CanonicalFullereneC76_vertex_count :
    iupacP93CanonicalFullereneC76Faces.flatten.eraseDups.length = 76 := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC76_directed_occurrence_count :
    iupacP93CanonicalFullereneC76DirectedEdgeOccurrences.length = 228 := by
  decide

theorem iupacP93CanonicalFullereneC76_edge_count :
    iupacP93CanonicalFullereneC76Edges.length = 114 := by
  decide

theorem iupacP93CanonicalFullereneC76_cubic :
    (List.range 76).all (fun atom =>
      (iupacP93CanonicalFullereneC76Neighbors atom).length = 3) = true := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC76_each_edge_twice_oppositely_oriented :
    iupacP93CanonicalFullereneC76Edges.all (fun edge =>
      iupacP93CanonicalFullereneC76DirectedEdgeOccurrences.count edge = 1 &&
        iupacP93CanonicalFullereneC76DirectedEdgeOccurrences.count
          (edge.2, edge.1) = 1) = true := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC76_connected :
    (iupacP93CanonicalFullereneC76Reachable 10 [0]).eraseDups.length = 76 := by
  decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
