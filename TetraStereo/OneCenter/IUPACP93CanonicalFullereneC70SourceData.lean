import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic


























/-- The complete coherently oriented face map shared by the numbered P-93 C70 figures.
Pentagons precede hexagons; locants are zero-based. -/
def iupacP93CanonicalFullereneC70Faces : List (List Nat) :=
  [ [0, 5, 6, 7, 8]
  , [14, 15, 16, 3, 2]
  , [26, 27, 28, 10, 9]
  , [30, 31, 32, 13, 12]
  , [36, 37, 38, 18, 17]
  , [40, 41, 22, 21, 20]
  , [44, 45, 25, 24, 23]
  , [53, 54, 35, 34, 33]
  , [59, 60, 61, 43, 42]
  , [62, 63, 48, 47, 46]
  , [65, 66, 52, 51, 50]
  , [67, 68, 57, 56, 55]
  , [0, 1, 2, 3, 4, 5]
  , [8, 9, 10, 11, 1, 0]
  , [11, 12, 13, 14, 2, 1]
  , [16, 17, 18, 19, 4, 3]
  , [19, 20, 21, 6, 5, 4]
  , [21, 22, 23, 24, 7, 6]
  , [24, 25, 26, 9, 8, 7]
  , [28, 29, 30, 12, 11, 10]
  , [32, 33, 34, 15, 14, 13]
  , [34, 35, 36, 17, 16, 15]
  , [38, 39, 40, 20, 19, 18]
  , [41, 42, 43, 44, 23, 22]
  , [45, 46, 47, 27, 26, 25]
  , [47, 48, 49, 29, 28, 27]
  , [49, 50, 51, 31, 30, 29]
  , [51, 52, 53, 33, 32, 31]
  , [54, 55, 56, 37, 36, 35]
  , [56, 57, 58, 39, 38, 37]
  , [58, 59, 42, 41, 40, 39]
  , [61, 62, 46, 45, 44, 43]
  , [63, 64, 65, 50, 49, 48]
  , [66, 67, 55, 54, 53, 52]
  , [68, 69, 60, 59, 58, 57]
  , [69, 64, 63, 62, 61, 60]
  , [69, 68, 67, 66, 65, 64]
  ]

/-- Page 82 uses the shared C70 face transcription; only its derivative overlay differs. -/
def iupacP93CanonicalFullereneC70Page82Faces : List (List Nat) :=
  iupacP93CanonicalFullereneC70Faces

/-- Page 83 uses the shared C70 face transcription; only its derivative overlay differs. -/
def iupacP93CanonicalFullereneC70Page83Faces : List (List Nat) :=
  iupacP93CanonicalFullereneC70Faces

theorem iupacP93CanonicalFullereneC70_page82_page83_same_cage :
    iupacP93CanonicalFullereneC70Page82Faces =
      iupacP93CanonicalFullereneC70Page83Faces := by
  rfl

/-- The page-83 `(f,sC)` start face, stored in the printed clockwise-from-outside
`1 -> 2 -> 3` orientation and converted to zero-based locants.  This source observation is kept
separate from the shared topological face table. -/
def iupacP93CanonicalFullereneC70Page83FsCStartFace : List Nat :=
  [0, 1, 2, 3, 4, 5]

theorem iupacP93CanonicalFullereneC70_page83_start_face_present :
    iupacP93CanonicalFullereneC70Page83FsCStartFace ∈
      iupacP93CanonicalFullereneC70Faces := by
  decide

theorem iupacP93CanonicalFullereneC70_page83_start_progression :
    iupacP93CanonicalFullereneC70Page83FsCStartFace.take 3 = [0, 1, 2] := by
  decide

/-- Local source-data helper: consecutive directed edges, including the closing edge. -/
def iupacP93C70DirectedFaceEdges (face : List Nat) : List (Nat × Nat) :=
  face.zip (face.tail ++ face.take 1)

/-- Local source-data helper for the canonical representative of an undirected edge. -/
def iupacP93C70CanonicalEdge (edge : Nat × Nat) : Nat × Nat :=
  if edge.1 < edge.2 then edge else (edge.2, edge.1)

/-- All directed face-edge occurrences, retaining multiplicity and orientation. -/
def iupacP93CanonicalFullereneC70DirectedEdgeOccurrences : List (Nat × Nat) :=
  iupacP93CanonicalFullereneC70Faces.flatMap iupacP93C70DirectedFaceEdges

/-- The deduplicated canonical undirected cage edges derived only from the source faces. -/
def iupacP93CanonicalFullereneC70Edges : List (Nat × Nat) :=
  (iupacP93CanonicalFullereneC70DirectedEdgeOccurrences.map
    iupacP93C70CanonicalEdge).eraseDups

/-- Neighbors in the source-derived undirected cage graph. -/
def iupacP93CanonicalFullereneC70Neighbors (atom : Nat) : List Nat :=
  (iupacP93CanonicalFullereneC70Edges.filterMap fun edge =>
    if edge.1 = atom then some edge.2
    else if edge.2 = atom then some edge.1
    else none).eraseDups

/-- One monotone finite reachability expansion in the source-derived cage graph. -/
def iupacP93CanonicalFullereneC70ReachabilityStep (atoms : List Nat) : List Nat :=
  (atoms ++ atoms.flatMap iupacP93CanonicalFullereneC70Neighbors).eraseDups

/-- Iterate a fixed number of monotone reachability expansions. -/
def iupacP93CanonicalFullereneC70Reachable : Nat → List Nat → List Nat
  | 0, atoms => atoms
  | fuel + 1, atoms => iupacP93CanonicalFullereneC70Reachable fuel
      (iupacP93CanonicalFullereneC70ReachabilityStep atoms)

theorem iupacP93CanonicalFullereneC70Faces_length :
    iupacP93CanonicalFullereneC70Faces.length = 37 := by
  decide

theorem iupacP93CanonicalFullereneC70_pentagon_count :
    iupacP93CanonicalFullereneC70Faces.countP
      (fun face => decide (face.length = 5)) = 12 := by
  decide

theorem iupacP93CanonicalFullereneC70_hexagon_count :
    iupacP93CanonicalFullereneC70Faces.countP
      (fun face => decide (face.length = 6)) = 25 := by
  decide

theorem iupacP93CanonicalFullereneC70_vertex_bounds :
    iupacP93CanonicalFullereneC70Faces.all (fun face =>
      face.all (fun atom => atom < 70)) = true := by
  decide

theorem iupacP93CanonicalFullereneC70_vertex_count :
    iupacP93CanonicalFullereneC70Faces.flatten.eraseDups.length = 70 := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC70_directed_occurrence_count :
    iupacP93CanonicalFullereneC70DirectedEdgeOccurrences.length = 210 := by
  decide

theorem iupacP93CanonicalFullereneC70_edge_count :
    iupacP93CanonicalFullereneC70Edges.length = 105 := by
  decide

theorem iupacP93CanonicalFullereneC70_cubic :
    (List.range 70).all (fun atom =>
      (iupacP93CanonicalFullereneC70Neighbors atom).length = 3) = true := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC70_each_edge_twice_oppositely_oriented :
    iupacP93CanonicalFullereneC70Edges.all (fun edge =>
      iupacP93CanonicalFullereneC70DirectedEdgeOccurrences.count edge = 1 &&
        iupacP93CanonicalFullereneC70DirectedEdgeOccurrences.count (edge.2, edge.1) = 1) =
      true := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC70_connected :
    (iupacP93CanonicalFullereneC70Reachable 10 [0]).eraseDups.length = 70 := by
  decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
