import TetraStereo.Engine.RingStereoSphereInventory

/-! Fixed-reference readings on two signings of the same eight-vertex tree.
All earlier edge priorities are empty in this abstract inventory. -/
namespace StereoReferenceSwap
open TetraStereo.OneCenter TetraStereo.Engine.RingStereoSphereInventory

private def path (hands : List (Option RS)) : SignedPath :=
  hands.map fun h => ⟨[],h⟩

-- The root has children u, v, w. The first two extend to u-a-p and v-b-q.
-- Only u and w exchange signs. The root and a are the two invisible positions.
private def tree (u w : RS) : Inventory :=
  let root := [none]
  let v : Option RS := some .S
  [↑[path root],
   ↑[path (root ++ [some u]),path (root ++ [v]),path (root ++ [some w])],
   ↑[path (root ++ [some u,none]),path (root ++ [v,some .R])],
   ↑[path (root ++ [some u,none,some .R]),path (root ++ [v,some .R,some .S])]]

private theorem read_list (seed : RS) (xs : List SignedPath) :
    sphere seed (↑xs) =
      ((xs.map (project seed)).filter (fun k => (TetraStereo.Engine.RingFullPathPairs.bitOf k).isSome)
        |>.insertionSort (· ≥ ·)).filterMap TetraStereo.Engine.RingFullPathPairs.bitOf := by
  apply congrArg (List.filterMap TetraStereo.Engine.RingFullPathPairs.bitOf)
  exact List.mergeSort_eq_insertionSort (· ≥ ·) _

theorem readings :
    reading .R (tree .S .R) = [true,false,false,true,true,false] ∧
    reading .R (tree .R .S) = [true,false,false,true,true,false] ∧
    reading .S (tree .S .R) = [true,true,false,false,false,true] ∧
    reading .S (tree .R .S) = [true,true,false,false,true,false] := by
  simp only [reading,tree,List.flatMap_cons,List.flatMap_nil,List.append_nil,read_list]
  decide +kernel

end StereoReferenceSwap
assert_kernel_only StereoReferenceSwap.readings
