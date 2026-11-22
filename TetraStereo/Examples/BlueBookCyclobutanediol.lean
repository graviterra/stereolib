import TetraStereo.Engine.RingEnantiomorphicArms

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

namespace TetraStereo.Examples.BlueBookCyclobutanediol
open OneCenter Engine.RingChemicalPriority CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation

/-- Indices 0–3 are the source locants 1–4. Hydroxyl oxygens are 4,5.
The remaining eight atoms are explicit hydrogens. -/
def molecule : RawMolecule where
  atoms := List.replicate 4 (.aliphatic .C) ++ List.replicate 2 (.aliphatic .O) ++
    List.replicate 8 (.aliphatic .H)
  bonds := ([(0,1),(1,2),(2,3),(3,0),(0,4),(2,5),(0,6),(2,7),
    (1,8),(1,9),(3,10),(3,11),(4,12),(5,13)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

/-- Rational realization of P-92.6 Example 2. The OH and H groups at the
opposite methines have opposite orientations. The two ring methylenes lie
on opposite sides of the plane through the methines and their substituents.
The choice of x sign presents the two occurrences as in the simplified digraph. -/
def spatial : SpatialConfiguration := ⟨[⟨0,-2,0⟩,⟨-1,0,0⟩,⟨0,2,0⟩,⟨1,0,0⟩,
  ⟨0,-3,1⟩,⟨0,3,-1⟩,⟨0,-3,-1⟩,⟨0,3,1⟩,⟨-2,0,1⟩,⟨-2,0,-1⟩,⟨2,0,1⟩,⟨2,0,-1⟩,
  ⟨0,-4,1⟩,⟨0,4,-1⟩]⟩

def geometry : Geometry := fun i => spatial.positions[i]?

/-- Reflection in the methine plane exchanges the two methylene arms
while preserving every atomic specification and every bond. -/
def reflectAtom : Nat → Nat
  | 1 => 3 | 3 => 1 | 8 => 10 | 10 => 8 | 9 => 11 | 11 => 9 | n => n

theorem molecular_reflection :
    (∀ i : Fin 14, reflectAtom (reflectAtom i) = i ∧
      molecule.atoms[reflectAtom i]? = molecule.atoms[i.val]? ∧
      geometry (reflectAtom i) = mirror geometry i) ∧
    ∀ i j : Fin 14, molecule.bondOrder (reflectAtom i) (reflectAtom j) = molecule.bondOrder i j := by
  decide +kernel

/-- The carbon with an onward real copy of the original focus outranks the
carbon leading to its terminal duplicate. Read all four orders independently. -/
theorem auxiliary_orders :
    atomicOrder? molecule [0,1,2] 2 = some [5,1,3,7] ∧
    atomicOrder? molecule [0,3,2] 2 = some [5,3,1,7] ∧
    atomicOrder? molecule [2,1,0] 2 = some [4,1,3,6] ∧
    atomicOrder? molecule [2,3,0] 2 = some [4,3,1,6] := by decide +kernel

/-- The first two spheres coincide. The real copy of C-1 presents O,C,H
in the first sibling group of sphere III; the ring duplicate has no children.
Padding slots use zero, below every real atomic number in this molecule. -/
theorem deciding_spheres :
    ligandRows? molecule [0,1,2] 1 2 = some [[6],[6,1,1],[8,6,1,0,0,0,0,0,0]] ∧
    ligandRows? molecule [0,1,2] 3 2 = some [[6],[6,1,1],[0,0,0,0,0,0,0,0,0]] := by
  decide +kernel

theorem occurrence_auxiliaries :
    atomicAux? molecule geometry [0,1,2] 2 = some .R ∧
    atomicAux? molecule geometry [0,3,2] 2 = some .S ∧
    atomicAux? molecule geometry [2,1,0] 2 = some .R ∧
    atomicAux? molecule geometry [2,3,0] 2 = some .S := by decide +kernel

/-- The independent two-step calculation and its mirror give lowercase r at
both published sites. The paths distinguish repeated occurrences of the same atom. -/
theorem published_centers :
    caseFromMirror? (fromAux molecule geometry 4 1 3 6 [0,1,2] [0,3,2] 2)
      (fromAux molecule (mirror geometry) 4 1 3 6 [0,1,2] [0,3,2] 2) = some (.pseudoasymmetric .r) ∧
    caseFromMirror? (fromAux molecule geometry 5 1 3 7 [2,1,0] [2,3,0] 2)
      (fromAux molecule (mirror geometry) 5 1 3 7 [2,1,0] [2,3,0] 2) = some (.pseudoasymmetric .r) := by
  simp only [fromAux_mirror]
  decide +kernel

/-- Full branch enumeration supplies the auxiliary paths; the reflection check
and the constitutional frame checks establish the applicability of Rule 5. -/
theorem checked_centers :
    enantiomorphicCenter? molecule geometry reflectAtom 0 4 1 3 6 2 = some (.pseudoasymmetric .r) ∧
    enantiomorphicCenter? molecule geometry reflectAtom 2 5 1 3 7 2 = some (.pseudoasymmetric .r) := by
  decide +kernel

theorem discovered_sites :
    singleSite? molecule 0 1 = some [0,1,2] ∧ singleSite? molecule 0 3 = some [0,3,2] ∧
    singleSite? molecule 2 1 = some [2,1,0] ∧ singleSite? molecule 2 3 = some [2,3,0] := by
  decide +kernel

/-- The remaining Rule-1a tie is real through sphere II. The decisive
occupied slot against the ring duplicate's missing children is in sphere III. -/
theorem shallower_insufficient :
    atomicOrder? molecule [0,1,2] 1 = none ∧ atomicOrder? molecule [0,3,2] 1 = none ∧
    atomicOrder? molecule [2,1,0] 1 = none ∧ atomicOrder? molecule [2,3,0] 1 = none := by
  decide +kernel

/-- Invert only the C-3 methine while keeping the constitutional digraph and
its arm-exchanging reflection. This is a constructed stereoisomer control. -/
def invertedThird : Geometry
  | 5 => geometry 7
  | 7 => geometry 5
  | 13 => some ⟨0,4,1⟩
  | i => geometry i

theorem inverted_centers :
    enantiomorphicCenter? molecule invertedThird reflectAtom 0 4 1 3 6 2 = some (.pseudoasymmetric .s) ∧
    enantiomorphicCenter? molecule invertedThird reflectAtom 2 5 1 3 7 2 = some (.pseudoasymmetric .s) := by
  decide +kernel

theorem rejects_unjustified :
    (singlePair? molecule geometry id 0 4 1 3 6 2).isNone = true ∧
    (singlePair? molecule geometry reflectAtom 0 4 1 3 6 1).isNone = true ∧
    (singlePair? molecule (fun i => if i = 5 then none else geometry i) reflectAtom
      0 4 1 3 6 2).isNone = true := by decide +kernel

/-- A second copy of a bond is invalid even if explicit neighbor lists
continue to enumerate the undamaged graph. -/
theorem duplicate_bond_rejected :
    saturatedCHO {molecule with
      bonds := ⟨0,1,.single⟩ :: molecule.bonds
      neighborOrder := (List.range molecule.atomCount).map molecule.writtenNeighbors} = false := by
  decide +kernel

end TetraStereo.Examples.BlueBookCyclobutanediol
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.molecular_reflection
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.auxiliary_orders
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.occurrence_auxiliaries
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.published_centers
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.checked_centers
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.discovered_sites
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.shallower_insufficient
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.deciding_spheres
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.inverted_centers
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.rejects_unjustified
assert_kernel_only TetraStereo.Examples.BlueBookCyclobutanediol.duplicate_bond_rejected
