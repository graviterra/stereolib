import TetraStereo.Engine.RingChemicalPriority

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false
namespace TetraStereo.Examples.BlueBookHexachlorocyclohexane
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Engine.RingChemicalPriority Certificate.CanonicalSphereKey

/-- Atoms 0–5 represent C-1 through C-6 of P-92.5.2.2 Example 3. The next
six atoms are their chlorine substituents; the final six are explicit hydrogen. -/
def molecule : RawMolecule where
  atoms := List.replicate 6 (.aliphatic .C) ++ List.replicate 6 (.aliphatic .Cl) ++
    List.replicate 6 (.aliphatic .H)
  bonds := (List.range 6).flatMap fun i =>
    [⟨i,(i+1)%6,.single⟩,⟨i,i+6,.single⟩,⟨i,i+12,.single⟩]

/-- The bold C-4/C-3 edge faces the viewer. Chlorine is above the mean ring
plane at C-1, C-3 and C-6, and below it at C-2, C-4 and C-5. -/
def spatial : SpatialConfiguration := ⟨[
  ⟨1,0,-2⟩,⟨2,0,0⟩,⟨1,0,2⟩,⟨-1,0,2⟩,⟨-2,0,0⟩,⟨-1,0,-2⟩,
  ⟨2,2,-4⟩,⟨4,-2,0⟩,⟨2,2,4⟩,⟨-2,-2,4⟩,⟨-4,-2,0⟩,⟨-2,2,-4⟩,
  ⟨2,-2,-4⟩,⟨4,2,0⟩,⟨2,-2,4⟩,⟨-2,2,4⟩,⟨-4,2,0⟩,⟨-2,-2,-4⟩]⟩

def geometry : Geometry := fun i => spatial.positions[i]?

/-- In one ring direction the first terminal duplicate of the focus stops the
chain. The other direction still has a real chlorinated carbon at that sphere. -/
private def chain : Nat → HTree Nat
  | 0 => .node 6 []
  | d+1 => .node 6 [.node 17 [],chain d,.node 1 []]

private def shapes (d : Nat) : List (HTree Nat) :=
  [.node 17 [],chain d,chain (d-1),.node 1 []]

def site (root : Fin 6) (clockwise : Bool) (offset : Nat) :=
  (root.val + offset * (if clockwise then 1 else 5)) % 6

def path (i : Fin 6) (cw : Bool) (k : Fin 5) :=
  (List.range (k.val+2)).map (site i cw)

def order (i : Fin 6) (cw : Bool) (k : Fin 5) :=
  let c := site i cw (k.val+1)
  [c+6,site i cw k.val,site i cw (k.val+2),c+12]

private def Matches (i : Fin 6) (cw : Bool) (k : Fin 5) : Prop :=
  (checkedShapes? molecule (path i cw k) (order i cw k) (5-k.val)).map Subtype.val =
    some (shapes (5-k.val))

private def checkList {α : Type} (check : (a b : α) → Option (PLift (a = b))) :
    (xs ys : List α) → Option (PLift (xs = ys))
  | [],[] => some ⟨rfl⟩
  | a :: xs,b :: ys => do
    let ⟨h⟩ ← check a b
    let ⟨t⟩ ← checkList check xs ys
    return ⟨congrArg₂ List.cons h t⟩
  | _,_ => none

private def checkTree : Nat → (a b : HTree Nat) → Option (PLift (a = b))
  | 0,_,_ => none
  | n+1,.node a as,.node b bs => do
    if h : a = b then
      let ⟨t⟩ ← checkList (checkTree n) as bs
      return ⟨congrArg₂ HTree.node h t⟩
    else none

private def checkShapes (i : Fin 6) (cw : Bool) (k : Fin 5) : Option (PLift (Matches i cw k)) := do
  let ⟨trees,h⟩ ← ((checkedShapes? molecule (path i cw k) (order i cw k) (5-k.val)).map Subtype.val).attach
  let ⟨eq⟩ ← checkList (checkTree 6) trees (shapes (5-k.val))
  return ⟨h.trans (congrArg some eq)⟩

private theorem matches_of_checked {i cw k} (ok : (checkShapes i cw k).isSome = true) : Matches i cw k :=
  ((checkShapes i cw k).get ok).down

private theorem matches0 (cw : Bool) (k : Fin 5) : Matches 0 cw k := by
  apply matches_of_checked
  cases cw <;> fin_cases k <;> decide +kernel

private theorem matches1 (cw : Bool) (k : Fin 5) : Matches 1 cw k := by
  apply matches_of_checked
  cases cw <;> fin_cases k <;> decide +kernel

private theorem matches2 (cw : Bool) (k : Fin 5) : Matches 2 cw k := by
  apply matches_of_checked
  cases cw <;> fin_cases k <;> decide +kernel

private theorem matches3 (cw : Bool) (k : Fin 5) : Matches 3 cw k := by
  apply matches_of_checked
  cases cw <;> fin_cases k <;> decide +kernel

private theorem matches4 (cw : Bool) (k : Fin 5) : Matches 4 cw k := by
  apply matches_of_checked
  cases cw <;> fin_cases k <;> decide +kernel

private theorem matches5 (cw : Bool) (k : Fin 5) : Matches 5 cw k := by
  apply matches_of_checked
  cases cw <;> fin_cases k <;> decide +kernel

private theorem molecular_shapes (i : Fin 6) (cw : Bool) (k : Fin 5) : Matches i cw k := by
  fin_cases i <;> first | apply matches0 | apply matches1 | apply matches2 |
                          apply matches3 | apply matches4 | apply matches5

private theorem strict_shapes (k : Fin 5) : (shapes (5-k.val)).Pairwise
    (fun a b => ckey 3 (5-k.val) b < ckey 3 (5-k.val) a) := by
  fin_cases k <;> decide +kernel

/-- The four actual incident cursors have this strict Rule 1a order, for
every root and either direction. The witness does not depend on geometry. -/
theorem branch_order (i : Fin 6) (cw : Bool) (k : Fin 5) :
    ∃ ranking : AtomicRanking molecule (path i cw k) (5-k.val),
      ranking.arms.map (·.cursor.node.atom) = order i cw k := by
  obtain ⟨⟨trees,build⟩,_,eq⟩ := Option.map_eq_some_iff.mp (molecular_shapes i cw k)
  change trees = shapes (5-k.val) at eq
  apply build
  rw [eq]
  exact strict_shapes k

end TetraStereo.Examples.BlueBookHexachlorocyclohexane
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexane.branch_order
