import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76SourceData
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Cycle

set_option autoImplicit false

/-!
# Core finite audits for the P-93 C76 face transcription

This low-dependency source leaf defines the executable incidence predicates and certifies the
basic frozen-list invariants without importing the molecular fullerene compiler.
-/

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

/-- Executable source-edge incidence, using the already deduplicated canonical edge list. -/
def iupacP93CanonicalFullereneC76HasSourceEdge (left right : Nat) : Bool :=
  iupacP93CanonicalFullereneC76Edges.contains
    (iupacP93C76CanonicalEdge (left, right))

/-- Local forward-face predicate, definitionally identical to the generic compiler predicate but
kept in this low-dependency source leaf. -/
def iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge
    (face : List Nat) (left right : Nat) : Bool :=
  face.contains left && face.nextOr left (face.head?.getD left) == right

/-- Executable unoriented adjacency in one supplied cyclic face. -/
def iupacP93CanonicalFullereneC76HasNamedFaceEdge
    (face : List Nat) (left right : Nat) : Bool :=
  iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge face left right ||
    iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge face right left

theorem iupacP93CanonicalFullereneC76_facesNodup :
    (iupacP93CanonicalFullereneC76Faces.map List.toFinset).Nodup := by
  decide

theorem iupacP93CanonicalFullereneC76_eachFaceNodup :
    iupacP93CanonicalFullereneC76Faces.all (fun face => decide face.Nodup) = true := by
  decide

theorem iupacP93CanonicalFullereneC76_faceSizes :
    iupacP93CanonicalFullereneC76Faces.all (fun face =>
      decide (face.length = 5 ∨ face.length = 6)) = true := by
  decide

set_option maxRecDepth 10000 in
theorem iupacP93CanonicalFullereneC76_vertexFinset :
    iupacP93CanonicalFullereneC76Faces.flatten.toFinset = Finset.range 76 := by
  decide

theorem iupacP93CanonicalFullereneC76_edgesNodup :
    iupacP93CanonicalFullereneC76Edges.Nodup := by
  decide

theorem iupacP93CanonicalFullereneC76_edgesCanonicalAndBounded :
    iupacP93CanonicalFullereneC76Edges.all (fun edge =>
      decide (edge.1 < edge.2 ∧ edge.1 < 76 ∧ edge.2 < 76)) = true := by
  decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
