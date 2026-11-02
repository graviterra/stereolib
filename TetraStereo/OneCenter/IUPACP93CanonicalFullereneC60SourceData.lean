import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic




















/-- The complete coherently oriented face map transcribed from the numbered P-93 C60 figure.
Pentagons precede hexagons; locants are zero-based. -/
def iupacP93CanonicalFullereneC60Faces : List (List Nat) :=
  [ [0, 1, 2, 3, 4]
  , [19, 20, 21, 6, 5]
  , [24, 25, 9, 8, 7]
  , [28, 29, 12, 11, 10]
  , [32, 33, 15, 14, 13]
  , [36, 37, 18, 17, 16]
  , [41, 42, 43, 23, 22]
  , [44, 45, 46, 27, 26]
  , [47, 48, 49, 31, 30]
  , [50, 51, 52, 35, 34]
  , [53, 54, 40, 39, 38]
  , [59, 58, 57, 56, 55]
  , [8, 9, 10, 11, 1, 0]
  , [0, 4, 5, 6, 7, 8]
  , [11, 12, 13, 14, 2, 1]
  , [14, 15, 16, 17, 3, 2]
  , [17, 18, 19, 5, 4, 3]
  , [21, 22, 23, 24, 7, 6]
  , [25, 26, 27, 28, 10, 9]
  , [29, 30, 31, 32, 13, 12]
  , [33, 34, 35, 36, 16, 15]
  , [37, 38, 39, 20, 19, 18]
  , [39, 40, 41, 22, 21, 20]
  , [43, 44, 26, 25, 24, 23]
  , [46, 47, 30, 29, 28, 27]
  , [49, 50, 34, 33, 32, 31]
  , [52, 53, 38, 37, 36, 35]
  , [54, 55, 56, 42, 41, 40]
  , [56, 57, 45, 44, 43, 42]
  , [57, 58, 48, 47, 46, 45]
  , [58, 59, 51, 50, 49, 48]
  , [59, 55, 54, 53, 52, 51]
  ]

/-- The page-81 `(f,sC)` start face, stored in the printed clockwise-from-outside
`1 -> 2 -> 3` orientation and converted to zero-based locants.  Both Type-2 and Type-3 examples
use this same numbered C60 orientation. -/
def iupacP93CanonicalFullereneC60FsCStartFace : List Nat :=
  [0, 1, 2, 3, 4]

theorem iupacP93CanonicalFullereneC60_fsCStartFace_mem :
    iupacP93CanonicalFullereneC60FsCStartFace ∈
      iupacP93CanonicalFullereneC60Faces := by
  decide

theorem iupacP93CanonicalFullereneC60_fsCStartFace_firstThree :
    iupacP93CanonicalFullereneC60FsCStartFace.take 3 = [0, 1, 2] := by
  decide

/-- Local source-data helper: consecutive directed edges, including the closing edge. -/
def iupacP93C60DirectedFaceEdges (face : List Nat) : List (Nat × Nat) :=
  face.zip (face.tail ++ face.take 1)

/-- Local source-data helper for the canonical representative of an undirected edge. -/
def iupacP93C60CanonicalEdge (edge : Nat × Nat) : Nat × Nat :=
  if edge.1 < edge.2 then edge else (edge.2, edge.1)

/-- All directed face-edge occurrences, retaining multiplicity and orientation. -/
def iupacP93CanonicalFullereneC60DirectedEdgeOccurrences : List (Nat × Nat) :=
  iupacP93CanonicalFullereneC60Faces.flatMap iupacP93C60DirectedFaceEdges

/-- The deduplicated canonical undirected cage edges derived only from the source faces. -/
def iupacP93CanonicalFullereneC60Edges : List (Nat × Nat) :=
  (iupacP93CanonicalFullereneC60DirectedEdgeOccurrences.map
    iupacP93C60CanonicalEdge).eraseDups

/-- Neighbors in the source-derived undirected cage graph. -/
def iupacP93CanonicalFullereneC60Neighbors (atom : Nat) : List Nat :=
  (iupacP93CanonicalFullereneC60Edges.filterMap fun edge =>
    if edge.1 = atom then some edge.2
    else if edge.2 = atom then some edge.1
    else none).eraseDups

/-- One monotone finite reachability expansion in the source-derived cage graph. -/
def iupacP93CanonicalFullereneC60ReachabilityStep (atoms : List Nat) : List Nat :=
  (atoms ++ atoms.flatMap iupacP93CanonicalFullereneC60Neighbors).eraseDups

/-- Iterate reachability a fixed number of times; 60 steps suffice for a 60-vertex graph. -/
def iupacP93CanonicalFullereneC60Reachable : Nat → List Nat → List Nat
  | 0, atoms => atoms
  | fuel + 1, atoms => iupacP93CanonicalFullereneC60Reachable fuel
      (iupacP93CanonicalFullereneC60ReachabilityStep atoms)

theorem iupacP93CanonicalFullereneC60Faces_length :
    iupacP93CanonicalFullereneC60Faces.length = 32 := by
  decide

theorem iupacP93CanonicalFullereneC60_pentagon_count :
    iupacP93CanonicalFullereneC60Faces.countP
      (fun face => decide (face.length = 5)) = 12 := by
  decide

theorem iupacP93CanonicalFullereneC60_hexagon_count :
    iupacP93CanonicalFullereneC60Faces.countP
      (fun face => decide (face.length = 6)) = 20 := by
  decide

theorem iupacP93CanonicalFullereneC60_vertex_bounds :
    iupacP93CanonicalFullereneC60Faces.all (fun face =>
      face.all (fun atom => atom < 60)) = true := by
  decide

theorem iupacP93CanonicalFullereneC60_vertex_count :
    (iupacP93CanonicalFullereneC60Faces.flatten.eraseDups.length = 60) := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC60_directed_occurrence_count :
    iupacP93CanonicalFullereneC60DirectedEdgeOccurrences.length = 180 := by
  decide

theorem iupacP93CanonicalFullereneC60_edge_count :
    iupacP93CanonicalFullereneC60Edges.length = 90 := by
  decide

theorem iupacP93CanonicalFullereneC60_cubic :
    (List.range 60).all (fun atom =>
      (iupacP93CanonicalFullereneC60Neighbors atom).length = 3) = true := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC60_each_edge_twice_oppositely_oriented :
    iupacP93CanonicalFullereneC60Edges.all (fun edge =>
      iupacP93CanonicalFullereneC60DirectedEdgeOccurrences.count edge = 1 &&
        iupacP93CanonicalFullereneC60DirectedEdgeOccurrences.count (edge.2, edge.1) = 1) =
      true := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC60_connected :
    (iupacP93CanonicalFullereneC60Reachable 60 [0]).eraseDups.length = 60 := by
  decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
