import TetraStereo.Engine.RingReferenceDerivation
import TetraStereo.Engine.LocalizedChemicalRingPublic
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000
set_option Elab.async false

namespace TetraStereo.Examples.RingRemoteIsotopeCoverage
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation
def deuterium : AtomSpec := {element := .H, isotope? := some 2}
def hydrogen : AtomSpec := .aliphatic .H

/-- A fluorocyclopropane with CH₂–CHD₂ and CH₂–CH₂D substituents on carbon 0. -/
def molecule : RawMolecule where
  atoms := List.replicate 5 (.aliphatic .C) ++ [.aliphatic .F,hydrogen,hydrogen,hydrogen,deuterium,deuterium,hydrogen,deuterium,hydrogen,hydrogen,.aliphatic .C,.aliphatic .C,hydrogen,hydrogen,hydrogen,hydrogen]
  bonds := ([(0,1),(0,2),(1,2),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8),
    (3,15),(3,17),(3,18),(4,16),(4,19),(4,20),(15,9),(15,10),(15,11),(16,12),(16,13),(16,14)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration := ⟨[⟨0,0,0⟩,⟨2,1,0⟩,⟨2,-1,0⟩,⟨-1,0,2⟩,⟨-1,0,-2⟩,
  ⟨3,2,1⟩,⟨3,2,-1⟩,⟨3,-2,1⟩,⟨3,-2,-1⟩,⟨-3,1,4⟩,⟨-4,-1,4⟩,⟨-4,0,2⟩,
  ⟨-3,1,-4⟩,⟨-4,-1,-4⟩,⟨-4,0,-2⟩,⟨-3,0,3⟩,⟨-3,0,-3⟩,
  ⟨-1,1,3⟩,⟨0,-1,2⟩,⟨-1,1,-3⟩,⟨0,-1,-2⟩]⟩
def geometry : Geometry := fun i => spatial.positions[i]?
theorem admitted : saturatedWithHalogens molecule = true ∧ (LocalizedChemicalRing.admitRawSpatial? molecule spatial).isSome = true ∧
  ∀ a ∈ [0,1,2,3,4,15,16], (readback? geometry (molecule.writtenNeighbors a)).isSome = true := by decide +kernel

/-- Positive barycentric weights verify that each carbon lies inside its ligand tetrahedron. -/
def interior (i : Nat) : Bool :=
  let ns := molecule.writtenNeighbors i
  let weight (j : Nat) : Rat :=
    if i = 0 then (if j = 3 ∨ j = 4 then 2 else 1)
    else if i = 1 ∨ i = 2 then (if j = 3-i then 1 else 2)
    else 1
  ([CartesianPoint3.x, CartesianPoint3.y, CartesianPoint3.z]).all fun axis =>
    ((ns.mapM fun j => (geometry j).map fun p => weight j * axis p).map List.sum) ==
      (geometry i).map fun p => (ns.map weight).sum * axis p

theorem carbons : (List.range molecule.atomCount).filter (fun i => (molecule.atoms[i]?.map (·.element)) == some .C) =
    [0,1,2,3,4,15,16] := by decide +kernel

theorem physically_interior : [0,1,2,3,4,15,16].all interior = true := by decide +kernel

private def pair (i j : Nat) :=
  (IsotopePriority.compareIncident? molecule [0] i j).map (fun c => (c.ordering,c.rule?))

/-- The actual comparison engine resolves the remote isotope order in
both directions at the same third sphere. -/
theorem certified_pair :
    pair 3 4 = some (.gt,some (.isotopeMass 3)) ∧
    pair 4 3 = some (.lt,some (.isotopeMass 3)) := by decide +kernel

private def decidingParents (i j : Nat) : Option (List Nat × List Nat × Nat) := do
  let c ← IsotopePriority.compareIncident? molecule [0] i j
  let read {a b} (d : IsotopePriority.RemoteTerminalOrder molecule a b) :=
    (d.left.parent.route.map (·.atom),d.right.parent.route.map (·.atom),d.difference.slot)
  match c.verdict with
  | .greater (.singleParent d ..) => return read d
  | .less (.singleParent d ..) => return read d
  | _ => none

/-- Both signs come from the single-parent evidence. In either request its
heavy and light methyl parents and its first unequal slot are the same. -/
theorem deciding_parents :
    decidingParents 3 4 = some ([3,15],[4,16],1) ∧
    decidingParents 4 3 = some ([3,15],[4,16],1) := by decide +kernel

theorem certified_center :
    (IsotopePriority.rank? molecule [0]).map (·.order) = some [1,2,3,4] ∧
    (ReferenceDerivation.derive? molecule geometry 3 molecule.atomCount [0]).map (·.verdict) =
      some (some ⟨.R,.S⟩) ∧
    (ReferenceDerivation.derive? molecule (mirror geometry) 3 molecule.atomCount [0]).map (·.verdict) =
      some (some ⟨.S,.R⟩) := by decide +kernel

/-- Additional recursion fuel preserves the independently certified
descriptor at the stated observation depth. -/
theorem stable_assignment (extra : Nat) :
    (ReferenceDerivation.derive? molecule geometry 3 (molecule.atomCount+extra) [0]).map (·.verdict) =
      some (some ⟨.R,.S⟩) := by
  rw [← ReferenceDerivation.derive_stable molecule geometry 3 molecule.atomCount extra [0]
    (by simp)]
  exact certified_center.2.1

open CertifiedLocalizedCIPInput

def constitutionalTie : Option Bool := do
  let f ← occurrence? molecule [0]
  let l ← occurrence? molecule [0,3]
  let r ← occurrence? molecule [0,4]
  return IsotopePriority.isomorphic molecule [0] (IsotopePriority.budget molecule+1) ⟨l,some f⟩ ⟨r,some f⟩

/-- The two complete trees agree under the observations for preceding rules. -/
theorem constitutional_tie : constitutionalTie = some true := by decide +kernel

def earlierMasses (i k : Nat) : Option (List Nat) := do
  let f ← occurrence? molecule [0]
  let l ← occurrence? molecule [0,i]
  let ss ← IsotopeSpheres.sitesAt molecule ⟨l,some f⟩ k
  ss.mapM (IsotopeSpheres.realMass? molecule)

/-- The nonempty isotope observations on spheres I and II coincide. -/
theorem prior_spheres : earlierMasses 3 0 = earlierMasses 4 0 ∧
    earlierMasses 3 1 = earlierMasses 4 1 ∧
    (earlierMasses 3 0).isSome ∧ (earlierMasses 3 1).isSome := by decide +kernel

def terminalSphere (arm methyl : Nat) : Option (List (List Nat) × List (List Nat)) := do
  let f ← occurrence? molecule [0]
  let a ← occurrence? molecule [0,arm]
  let c ← occurrence? molecule [0,arm,methyl]
  let sites ← IsotopeSpheres.sitesAt molecule ⟨a,some f⟩ 2
  let cs := (⟨c,some a⟩ : CanonicalRerootCursor).children molecule
  guard (sites.map IsotopeSpheres.Site.cursor == cs)
  let measured ← IsotopePriority.readTerminalMasses? molecule cs
  return (sites.map (fun (e : IsotopeSpheres.Site) => e.route.map (·.atom)),
    IsotopePriority.siblingWord (measured.map IsotopePriority.TerminalMass.key))

/-- Sphere III consists exactly of the three real terminal hydrogens on each methyl.
Their measured masses in legal sibling order give strict seniority to arm 3. -/
theorem sphere_three :
    (do let (l,ls) ← terminalSphere 3 15
        let (r,rs) ← terminalSphere 4 16
        return (l,r,compare ls rs)) = some
        ([[3,15,9],[3,15,10],[3,15,11]],
         [[4,16,12],[4,16,13],[4,16,14]],.gt) := by decide +kernel

/-- Every remaining unordered pair at carbon 0 already has a strict
source-bound comparison. Combining these five with sphere III above
gives [1,2,3,4], whose coordinate readbacks give opposite uppercase letters. -/
theorem other_pairs_and_geometry :
    ([(1,2),(1,3),(1,4),(2,3),(2,4)] : List (Nat × Nat)).mapM (fun (i,j) =>
      (IsotopePriority.compareIncident? molecule [0] i j).map (·.ordering)) =
        some [.gt,.gt,.gt,.gt,.gt] ∧
    Recursive.geometric geometry [1,2,3,4] [1,2,3,4] = some ⟨.R,.S⟩ := by decide +kernel

assert_kernel_only admitted
assert_kernel_only carbons
assert_kernel_only physically_interior
assert_kernel_only constitutional_tie
assert_kernel_only prior_spheres
assert_kernel_only sphere_three
assert_kernel_only other_pairs_and_geometry
assert_kernel_only certified_pair
assert_kernel_only deciding_parents
assert_kernel_only certified_center
assert_kernel_only stable_assignment

end TetraStereo.Examples.RingRemoteIsotopeCoverage
