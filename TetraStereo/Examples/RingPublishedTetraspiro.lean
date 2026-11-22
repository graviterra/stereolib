import TetraStereo.Engine.CentresRingMirror

set_option autoImplicit false
set_option maxRecDepth 60000
set_option maxHeartbeats 3500000

namespace TetraStereo.Examples.RingPublishedTetraspiro
open OneCenter Engine Engine.CentresRing LocalizedGenericMarkedRecalculation

/-- P-93.5.3.2 example 5. The central four-membered ring shares each
of its four carbons with a three-membered oxirane ring. Lean atom IDs
are one less than the published locants. The hydrogen positions are constructed. -/
def molecule : RawMolecule where
  atoms := [.aliphatic .O,.aliphatic .C,.aliphatic .C,.aliphatic .C,.aliphatic .O,.aliphatic .C,.aliphatic .C,.aliphatic .O,.aliphatic .C,.aliphatic .C,.aliphatic .O,.aliphatic .C] ++ List.replicate 8 (.aliphatic .H)
  bonds := ([(2,3),(3,6),(6,9),(9,2),(2,0),(0,1),(1,2),(1,12),(1,13),(3,4),(4,5),(5,3),(5,14),(5,15),(6,7),(7,8),(8,6),(8,16),(8,17),(9,10),(10,11),(11,9),(11,18),(11,19)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration := ⟨[⟨-1,-5,1⟩,⟨1,-5,-1⟩,⟨0,-3,0⟩,⟨3,0,0⟩,⟨5,-1,-1⟩,⟨5,1,1⟩,⟨0,3,0⟩,⟨-1,5,1⟩,⟨1,5,-1⟩,⟨-3,0,0⟩,⟨-5,1,1⟩,⟨-5,-1,-1⟩,⟨0,-7,-8⟩,⟨8,-7,0⟩,⟨7,8,0⟩,⟨7,0,8⟩,⟨8,7,0⟩,⟨0,7,-8⟩,⟨-7,0,-8⟩,⟨-7,-8,0⟩]⟩
def reflected := MirrorCasing.reflectGeometry spatial
def centers : List Nat := [2,3,6,9]

theorem admitted : (LocalizedChemicalRing.admitRawSpatial? molecule spatial).isSome = true ∧
    (LocalizedChemicalRing.admitRawSpatial? molecule reflected).isSome = true := by decide +kernel

/-- Starting carrier order and coordinate hand sent to the source for the four
annotated centers. Priority ranking occurs after these frame bindings. -/
def frames (s : SpatialConfiguration) := centers.mapM fun root => do
  let ids ← frameAtoms? molecule (canonicalCenterRoot root)
  let hand ← readback? (fun a => s.positions[a]?) ids
  return (ids,hand)

theorem requested_frames :
    frames spatial = some [([3,9,0,1],.S),([2,6,4,5],.S),([3,9,7,8],.R),([6,2,10,11],.R)] ∧
    frames reflected = some [([3,9,0,1],.R),([2,6,4,5],.R),([3,9,7,8],.S),([6,2,10,11],.S)] := by
  decide +kernel

end TetraStereo.Examples.RingPublishedTetraspiro
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiro.admitted
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiro.requested_frames
