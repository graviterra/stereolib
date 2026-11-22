import TetraStereo.Engine.RingMolecularPromotion

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option Elab.async false

namespace TetraStereo.Examples.RingRemoteIsotope
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority Recursive

/-- A cyclopentyl group. Its two CH₂ carbons attached to the focus (1 and 4)
have identical atom specifications. Carbons 2 and 3 carry the nuclides. -/
private def atoms (left right : Nat) : List AtomSpec :=
  [.aliphatic .C, .aliphatic .C, {element := .C, isotope? := some left},
   {element := .C, isotope? := some right}, .aliphatic .C] ++
    List.replicate 9 (.aliphatic .H)

private def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),
   (1,6),(1,7),(2,8),(2,9),(3,10),(3,11),(4,12),(4,13)]

private def bond (e : Nat × Nat) : RawBond := ⟨e.1,e.2,.single⟩

/-- The CH fluorinated ring carbon is atom 0, with F at atom 14. -/
def molecule (left right : Nat) : RawMolecule where
  atoms := atoms left right ++ [.aliphatic .F]
  bonds := ((0,14) :: edges).map bond

private def ringPositions : List CartesianPoint3 :=
  [⟨2,1,0⟩,⟨3,3,-2⟩,⟨4,5,-1⟩,⟨4,5,1⟩,⟨3,3,2⟩,⟨2,-2,0⟩,
   ⟨4,2,-3⟩,⟨2,4,-4⟩,⟨6,5,-1⟩,⟨3,7,-2⟩,⟨6,5,1⟩,⟨3,7,2⟩,⟨4,2,3⟩,⟨2,4,4⟩]

/-- A cyclic change of coordinate axes places the plane exchanging the two
ring routes at x = 0. It preserves the orientation of the ligand frame. -/
def geometry : Geometry := fun i =>
  ((ringPositions ++ [⟨0,0,0⟩])[i]?).map fun p => ⟨p.z,p.x,p.y⟩

private def reverseRing : Nat → Nat
  | 1 => 4 | 4 => 1 | 2 => 3 | 3 => 2
  | 6 => 12 | 12 => 6 | 7 => 13 | 13 => 7
  | 8 => 10 | 10 => 8 | 9 => 11 | 11 => 9 | i => i

/-- Equalizing the remote masses restores a molecular reflection exchanging
the two ring directions and preserving every atom and bond. -/
theorem equal_isotope_symmetry : Reflects (molecule 12 12) geometry reverseRing := by
  constructor <;> decide +kernel

/-- The nearer heavy isotope decides. The same two nuclides appear in the
opposite order one sphere farther out along the respective ring routes. -/
theorem remote_orders :
    (molecule 13 12).atoms[1]? = (molecule 13 12).atoms[4]? ∧
    IsotopePriority.order? (molecule 13 12) [0] = some [14,1,4,5] ∧
    IsotopePriority.order? (molecule 12 13) [0] = some [14,4,1,5] ∧
    IsotopePriority.order? (molecule 12 12) [0] = none := by
  refine ⟨?_,?_,?_,?_⟩ <;> decide +kernel

private def derived (m : RawMolecule) (g : Geometry) (p : List Nat) : Option Reading :=
  (Promotion.deriveAt m g (fun _ => none) (fun _ => 1) 1 p).map Subtype.val

/-- The recursive evaluator derives opposite letters on reflection, both
at the ring root and at the retained occurrence reached from fluorine. -/
theorem remote_readings :
    derived (molecule 13 12) geometry [0] = some ⟨.R,.S⟩ ∧
    derived (molecule 13 12) geometry [14,0] = some ⟨.R,.S⟩ ∧
    derived (molecule 13 12) (mirror geometry) [0] = some ⟨.S,.R⟩ := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

def fluorinatedLightArm : RawMolecule :=
  let m := molecule 13 12
  {m with atoms := m.atoms.set 10 (.aliphatic .F)}

/-- An additional fluorine attached to the lighter ring carbon puts its
route first by Rule 1a. It is three bonds from the focus, one sphere farther
out than the isotopic difference. -/
theorem farther_constitution_decides :
    atomicOrder? fluorinatedLightArm [0] 2 = some [14,4,1,5] ∧
    IsotopePriority.order? fluorinatedLightArm [0] = some [14,4,1,5] := by
  constructor <;> decide +kernel

/-- Two identically labelled cyclopentyl groups attached to CHF. The
coordinates below make the groups enantiomorphic. Their ring CH centers
are atoms 3 and 17. Each methylene has two explicit hydrogen atoms. -/
def paired : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .F,.aliphatic .H] ++ atoms 13 12 ++ atoms 13 12
  bonds := ([(0,1),(0,2)] ++ [3,17].flatMap (fun k =>
    (0,k) :: edges.map fun (a,b) => (k+a,k+b))).map bond

def pairedGeometry : Geometry := fun i =>
  if i < 3 then ([⟨0,0,0⟩,⟨0,0,2⟩,⟨0,-2,-2⟩] : List CartesianPoint3)[i]?
  else if i < 17 then ringPositions[i-3]?
  else (ringPositions[i-17]?).map CartesianPoint3.reflectX

private def exchange (i : Nat) : Nat := if i < 3 then i else if i < 17 then i+14 else i-14

private def hints : List Nat → Option Recursive.Frame
  | [0] => some ⟨.five,1,3,17,2,exchange,false⟩
  | _ => none

/-- The two remote-isotope comparisons supply the R and S auxiliary hands
used by the central Rule 5 comparison. -/
theorem retained_pair :
    derived paired pairedGeometry [0,3] = some ⟨.R,.S⟩ ∧
    derived paired pairedGeometry [0,17] = some ⟨.S,.R⟩ := by
  constructor <;> decide +kernel

/-- The normal recursive evaluator uses the retained auxiliaries to assign
lowercase s at the common carbon, which keeps its raw S on reflection. -/
theorem parent_assignment :
    Promotion.Justified paired pairedGeometry [0] ⟨.S,.S⟩ ∧
    (Reading.mk .S .S).label = some (.pseudoasymmetric .s) := by
  have found : (Promotion.deriveAt paired pairedGeometry hints (fun _ => 1) 2 [0]).map Subtype.val =
      some ⟨.S,.S⟩ := by decide +kernel
  obtain ⟨cert,_,eq⟩ := Option.map_eq_some_iff.mp found
  exact ⟨eq ▸ cert.property,rfl⟩

end TetraStereo.Examples.RingRemoteIsotope

assert_kernel_only TetraStereo.Examples.RingRemoteIsotope.equal_isotope_symmetry
assert_kernel_only TetraStereo.Examples.RingRemoteIsotope.remote_orders
assert_kernel_only TetraStereo.Examples.RingRemoteIsotope.remote_readings
assert_kernel_only TetraStereo.Examples.RingRemoteIsotope.farther_constitution_decides
assert_kernel_only TetraStereo.Examples.RingRemoteIsotope.retained_pair
assert_kernel_only TetraStereo.Examples.RingRemoteIsotope.parent_assignment
