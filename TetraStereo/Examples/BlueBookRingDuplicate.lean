import TetraStereo.Engine.RingIsotopePriority

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false

namespace TetraStereo.Examples.BlueBookRingDuplicate
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority

/-- Carbon identifiers follow the P-92.2.2 Example 1 drawing. O is atom 0;
H26 is the wedged hydrogen at C1 and H27 is the hydroxyl hydrogen. -/
def hydrogenParents : List Nat :=
  [1,0,3,3,4,4,5,6,6,7,7,8,8,9,9,11,11,12,12,13,14,14,15,15,
    16,16,17,17,18,19,19,20,20,21,21,22,22,23,24,24,25,25]

def molecule : RawMolecule where
  atoms := [.aliphatic .O] ++ List.replicate 25 (.aliphatic .C) ++
    List.replicate hydrogenParents.length (.aliphatic .H)
  bonds := (([(0,1),(1,2),(1,10),
    (2,3),(3,4),(4,5),(2,8),(8,9),(9,5),(2,7),(7,6),(6,5),
    (10,11),(11,12),(12,13),(13,14),(14,15),(15,13),
    (10,16),(16,17),(17,18),(18,19),(19,20),(20,18),
    (10,21),(21,22),(22,23),(23,24),(24,25),(25,23)] : List (Nat × Nat)) ++
    hydrogenParents.zipIdx.map (fun e : Nat × Nat => (e.1,e.2+26))).map
      (fun (i,j) => ⟨i,j,.single⟩)

/-- C2 lies to the right of C1, C10 down and to the left, H26 toward the
viewer and O0 away. Only C1 and its depicted ligand frame have coordinates.
The frame has positive signed volume in the published priority order. -/
def geometry : Geometry
  | 0 => some ⟨0,1,-1⟩ | 1 => some ⟨0,0,0⟩ | 2 => some ⟨2,0,0⟩
  | 10 => some ⟨-1,-2,0⟩ | 26 => some ⟨-1,1,1⟩ | _ => none

def isotopeControl : RawMolecule :=
  let atoms := molecule.atoms.set 2 {element := .C, isotope? := some 12}
  {molecule with atoms := atoms.set 10 {element := .C, isotope? := some 13}}

/-- Full root-to-closure address and source distance independently read back
from the earlier real occurrence. Exhausting the supplied depth declines. -/
private def closures (m : RawMolecule) : Nat → CanonicalRerootCursor →
    Option (List (List Nat × Nat))
  | 0,_ => none
  | n+1,c => do
    match c.node.provenance with
    | .ringDuplicate _ =>
      let o ← IsotopePriority.observation? m [1] c
      return [(c.node.history.reverse,o.sourceDistanceFromFocus)]
    | .realAtom => return (← (c.children m).mapM (closures m n)).flatten
    | _ => none

def closureInventory? (arm : Nat) : Option (List (List Nat × Nat)) := do
  let f ← occurrence? molecule [1]
  let c ← (occurrenceLigandCursors molecule f).find? (fun c => c.node.atom == arm)
  return (← closures molecule 8 c).insertionSort (· ≤ ·)

/-- The complete cage arm contains six ring closures. Every closure returns
to the bridgehead in sphere I. The cyclopropyl ligands each close in both
directions, always onto their own original CH in sphere IV. -/
theorem complete_closures :
    closureInventory? 2 = some [
      ([1,2,3,4,5,6,7,2],1),([1,2,3,4,5,9,8,2],1),
      ([1,2,7,6,5,4,3,2],1),([1,2,7,6,5,9,8,2],1),
      ([1,2,8,9,5,4,3,2],1),([1,2,8,9,5,6,7,2],1)] ∧
    closureInventory? 10 = some [
      ([1,10,11,12,13,14,15,13],4),([1,10,11,12,13,15,14,13],4),
      ([1,10,16,17,18,19,20,18],4),([1,10,16,17,18,20,19,18],4),
      ([1,10,21,22,23,24,25,23],4),([1,10,21,22,23,25,24,23],4)] := by
  constructor <;> decide +kernel

theorem rule1a_tie : SiblingConstitution.compare? molecule [1,2] [1,10] = some .eq := by
  decide +kernel

theorem source_order : IsotopePriority.order? molecule [1] = some [0,2,10,26] := by
  decide +kernel

theorem rule1b_precedes_isotope :
    IsotopePriority.order? isotopeControl [1] = some [0,2,10,26] := by
  decide +kernel

def descriptor? (m : RawMolecule) (g : Geometry) := do
  let order ← IsotopePriority.order? m [1]
  caseFromMirror? (readback? g order) (readback? (mirror g) order)

theorem published_letter : descriptor? molecule geometry = some (.chiral .S) ∧
    descriptor? molecule (mirror geometry) = some (.chiral .R) ∧
    descriptor? isotopeControl geometry = some (.chiral .S) := by
  simp only [descriptor?,source_order,rule1b_precedes_isotope]
  decide +kernel

end TetraStereo.Examples.BlueBookRingDuplicate

assert_kernel_only TetraStereo.Examples.BlueBookRingDuplicate.complete_closures
assert_kernel_only TetraStereo.Examples.BlueBookRingDuplicate.rule1a_tie
assert_kernel_only TetraStereo.Examples.BlueBookRingDuplicate.source_order
assert_kernel_only TetraStereo.Examples.BlueBookRingDuplicate.rule1b_precedes_isotope
assert_kernel_only TetraStereo.Examples.BlueBookRingDuplicate.published_letter
