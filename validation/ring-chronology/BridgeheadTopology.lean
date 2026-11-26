import TetraStereo.Engine.RingBridgeheadNitrogen

/-! Separate the graph question from whether the three ligands have distinct
priorities. This exhausts a family of subdivided theta graphs, including
fused, large-ring and short bridged systems. The oracle uses only the
subdivision lengths, independently of path search. -/
open TetraStereo.OneCenter TetraStereo.Engine.RingBridgeheadNitrogen

namespace BridgeheadTopology

def graph (n : Nat) (edges : List (Nat × Nat)) : RawMolecule where
  atoms := List.replicate n (AtomSpec.aliphatic .C)
  bonds := edges.map fun (a,b) => ⟨a,b,.single⟩

/-- Atoms 0 and 1 are the junctions. Allocate fresh interior atoms to
each of the three branches. -/
def theta (i j k : Nat) : RawMolecule := Id.run do
  let mut fresh := 2
  let mut edges := []
  for size in [i,j,k] do
    let path := [0] ++ ((List.range size).map (fresh + ·)) ++ [1]
    edges := edges ++ path.zip path.tail
    fresh := fresh + size
  return graph fresh edges

def verify : IO Unit := do
  let mut count := 0
  for i in List.range 6 do
    for j in [1,2,3,4,5] do
      for k in [1,2,3,4,5] do
        let sizes := [i,j,k]
        let expected := i > 0 && sizes.any fun common =>
          (sizes.erase common).all fun other => common + other + 2 ≤ 7
        let m := theta i j k
        for endpoint in [0,1] do
          unless constrainedRaw m endpoint == expected do
            throw (IO.userError s!"theta {sizes}, junction {endpoint}, expected {expected}")
        count := count + 1
  let openAmine := graph 4 [(0,1),(0,2),(0,3)]
  let oneRing := graph 5 [(0,1),(1,2),(2,3),(3,0),(0,4)]
  for m in [openAmine,oneRing] do
    if constrainedRaw m 0 then throw (IO.userError "acyclic or singly cyclic junction accepted")
  IO.println s!"{count} theta graphs, both ends; acyclic and single-ring controls passed."

end BridgeheadTopology

def main := BridgeheadTopology.verify
