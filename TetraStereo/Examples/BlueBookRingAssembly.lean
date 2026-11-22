import TetraStereo.Engine.RingRecursivePriorities

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
namespace TetraStereo.Examples.BlueBookRingAssembly
open OneCenter CertifiedLocalizedCIPInput Engine.RingChemicalPriority Recursive LocalizedGenericMarkedRecalculation

/-- Source locants 1–17 are retained. Atom 0 is the alcohol oxygen. -/
def hydrogenIds : List (List Nat) := [[18],[19],[20,21],[22,23],[24],[25,26],[27,28],[29,30],[31],[32,33],[34],[35,36],[37,38],[39],[40,41],[42,43],[44,45,46],[47,48,49]]

def molecule : RawMolecule where
  atoms := [.aliphatic .O] ++ List.replicate 17 (.aliphatic .C) ++ List.replicate 32 (.aliphatic .H)
  bonds := (([(1,2),(2,3),(3,4),(4,5),(5,6),(6,1),(4,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,10),(13,16),(1,17),(8,0)] : List (Nat × Nat)) ++
    (List.range 18).flatMap (fun i => ((hydrogenIds[i]?).getD []).map (fun h => (i,h)))).map
      (fun (i,j) => ⟨i,j,.single⟩)

/-- Rational rendering of the numbered P-93.6 drawing. The lower arcs of
the rings project towards the viewer, as does the hydroxyl bond at C-8. -/
def spatial : SpatialConfiguration := ⟨[⟨1,-5,1⟩,⟨-11,2,0⟩,⟨-9,0,1⟩,⟨-7,0,1⟩,⟨-5,2,0⟩,⟨-7,4,0⟩,
  ⟨-9,4,0⟩,⟨-4,-1,0⟩,⟨0,-3,0⟩,⟨4,-1,0⟩,⟨5,2,0⟩,⟨7,0,1⟩,
  ⟨9,0,1⟩,⟨11,2,0⟩,⟨9,4,0⟩,⟨7,4,0⟩,⟨13,0,0⟩,⟨-13,4,0⟩,
  ⟨2,-6,1⟩,⟨-13,0,0⟩,⟨-9,1,3⟩,⟨-9,-1,-1⟩,⟨-7,1,3⟩,⟨-7,-1,-1⟩,
  ⟨-3,4,0⟩,⟨-7,5,2⟩,⟨-7,3,-2⟩,⟨-9,5,2⟩,⟨-9,3,-2⟩,⟨-4,0,2⟩,
  ⟨-4,-2,-2⟩,⟨-1,-5,-1⟩,⟨4,0,2⟩,⟨4,-2,-2⟩,⟨3,4,0⟩,⟨7,1,3⟩,
  ⟨7,-1,-1⟩,⟨9,1,3⟩,⟨9,-1,-1⟩,⟨13,4,0⟩,⟨9,5,2⟩,⟨9,3,-2⟩,
  ⟨7,5,2⟩,⟨7,3,-2⟩,⟨13,1,2⟩,⟨13,-1,-2⟩,⟨14,0,1⟩,⟨-13,5,2⟩,
  ⟨-13,3,-2⟩,⟨-12,4,1⟩]⟩
def geometry : Geometry := fun i => spatial.positions[i]?

/-- Extend an explicit correspondence of heavy atoms to their attached H
atoms in local list order. The verifier checks the resulting occurrence map. -/
private def relabel (pairs : List (Nat × Nat)) : Nat → Nat :=
  let heavy (i : Nat) := ((pairs ++ pairs.map Prod.swap).lookup i).getD i
  let table := (List.range 18).map heavy ++
    (List.range 18).flatMap (fun i => (hydrogenIds[heavy i]?).getD [])
  fun i => table[i]?.getD i

private def leftRing := relabel [(3,5),(2,6)]
private def rightRing := relabel [(11,15),(12,14)]
private def rings := relabel [(7,9),(4,10),(3,11),(5,15),(2,12),(6,14),(1,13),(17,16)]



def hints (path : List Nat) : Option Recursive.Frame :=
  match path.getLast? with
  | some 1 => some ⟨.fourB,17,2,6,19,leftRing,true⟩
  | some 13 => some ⟨.fourB,16,12,14,39,rightRing,true⟩
  | some 4 => some ⟨.five,7,3,5,24,leftRing,false⟩
  | some 10 => some ⟨.five,9,11,15,34,rightRing,false⟩
  | some 8 => some ⟨.fourC,0,7,9,31,rings,false⟩
  | _ => none

/-- The source distinguishes the two constitutional paths at C-8 in an
outer-ring-rooted digraph in sphere VI. Sphere IV suffices at the other
auxiliary sites in these derivations. -/
def radius (path : List Nat) := if path.getLast? = some 8 ∧ path.length > 1 then 5 else 3

def atSite (path : List Nat) : Option Reading :=
  (certify molecule geometry hints radius 5 path).map Subtype.val

end TetraStereo.Examples.BlueBookRingAssembly
