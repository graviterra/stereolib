import TetraStereo.Engine.RingReferenceDerivation
import TetraStereo.Engine.LocalizedChemicalRingPublic
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000
set_option Elab.async false
namespace TetraStereo.Examples.RingGroupedIsotopeCoverage
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation
def deuterium : AtomSpec := {element := .H, isotope? := some 2}
def hydrogen : AtomSpec := .aliphatic .H
/-- A fluorocyclopropane with two CHD₂ methyls on arm 3 and two CH₂D methyls on arm 4. -/
def molecule : RawMolecule where
  atoms := List.replicate 5 (.aliphatic .C) ++ [.aliphatic .F,hydrogen,hydrogen,hydrogen,deuterium,deuterium,hydrogen,deuterium,hydrogen,hydrogen,.aliphatic .C,.aliphatic .C,hydrogen,.aliphatic .C,hydrogen,.aliphatic .C,deuterium,deuterium,hydrogen,deuterium,hydrogen,hydrogen]
  bonds := ([(0,1),(0,2),(1,2),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8),
    (3,15),(3,17),(3,18),(4,16),(4,19),(4,20),(15,9),(15,10),(15,11),(16,12),(16,13),(16,14),(18,21),(18,22),(18,23),(20,24),(20,25),(20,26)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩
def spatial : SpatialConfiguration := ⟨[⟨0,0,0⟩,⟨2,1,0⟩,⟨2,-1,0⟩,⟨-1,0,2⟩,⟨-1,0,-2⟩,
  ⟨3,2,1⟩,⟨3,2,-1⟩,⟨3,-2,1⟩,⟨3,-2,-1⟩,⟨-3,1,4⟩,⟨-4,-1,4⟩,⟨-4,0,2⟩,
  ⟨-3,1,-4⟩,⟨-4,-1,-4⟩,⟨-4,0,-2⟩,⟨-3,0,3⟩,⟨-3,0,-3⟩,
  ⟨-1,1,3⟩,⟨0,-1,2⟩,⟨-1,1,-3⟩,⟨0,-1,-2⟩,⟨2,-1,3⟩,⟨0,-3,3⟩,⟨-1,0,0⟩,
  ⟨1,-1,-4⟩,⟨1,-3,-3⟩,⟨-1,0,1⟩]⟩
def geometry : Geometry := fun i => spatial.positions[i]?
theorem admitted : saturatedWithHalogens molecule = true ∧ (LocalizedChemicalRing.admitRawSpatial? molecule spatial).isSome = true ∧
  ∀ a ∈ [0,1,2,3,4,15,16,18,20], (readback? geometry (molecule.writtenNeighbors a)).isSome = true := by decide +kernel
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
    [0,1,2,3,4,15,16,18,20] := by decide +kernel

theorem physically_interior : [0,1,2,3,4,15,16,18,20].all interior = true := by decide +kernel
open CertifiedLocalizedCIPInput

def constitutionalTie : Option Bool := do
  let f ← occurrence? molecule [0]
  let l ← occurrence? molecule [0,3]
  let r ← occurrence? molecule [0,4]
  return IsotopePriority.isomorphic molecule [0] (IsotopePriority.budget molecule+1) ⟨l,some f⟩ ⟨r,some f⟩

theorem constitutional_tie : constitutionalTie = some true := by decide +kernel

def earlierMasses (i k : Nat) : Option (List Nat) := do
  let f ← occurrence? molecule [0]
  let l ← occurrence? molecule [0,i]
  let ss ← IsotopeSpheres.sitesAt molecule ⟨l,some f⟩ k
  ss.mapM (IsotopeSpheres.realMass? molecule)

theorem prior_spheres : earlierMasses 3 0 = earlierMasses 4 0 ∧
    earlierMasses 3 1 = earlierMasses 4 1 ∧
    (earlierMasses 3 0).isSome ∧ (earlierMasses 3 1).isSome := by decide +kernel

def parentalMasses (arm : Nat) (parents : List Nat) : Option (List (List (List Nat))) := do
  let f ← occurrence? molecule [0]
  let a ← occurrence? molecule [0,arm]
  let sites ← IsotopeSpheres.sitesAt molecule ⟨a,some f⟩ 2
  let rows ← parents.mapM fun i => do
    let p ← occurrence? molecule [0,arm,i]
    let cs := (⟨p,some a⟩ : CanonicalRerootCursor).children molecule
    let ts ← IsotopePriority.readTerminalMasses? molecule cs
    return (cs,IsotopePriority.siblingWord (ts.map IsotopePriority.TerminalMass.key))
  guard ((rows.map Prod.fst).flatten == sites.map IsotopeSpheres.Site.cursor)
  return rows.map Prod.snd

theorem parent_orders :
    (do let [a,b] ← parentalMasses 3 [15,18] | none
        let [c,d] ← parentalMasses 4 [16,20] | none
        return (a == b, c == d, compare a c)) = some (true,true,.gt) := by decide +kernel

private def decidingGroups (i j : Nat) : Option (Ordering × List (List Nat) × List (List Nat) × Nat) := do
  let r ← IsotopePriority.compareIncident? molecule [0] i j
  let project {a b} (d : IsotopePriority.GroupedTerminalOrder molecule a b) := (
    d.left.order.map (fun (x : IsotopePriority.ParentGroup molecule) => x.parent.route.map (·.atom)),
    d.right.order.map (fun (x : IsotopePriority.ParentGroup molecule) => x.parent.route.map (·.atom)),
    d.difference.slot)
  guard (r.rule? == some (.isotopeMass 3))
  match r.verdict with
  | .greater (.groupedParents d ..) => return (r.ordering,project d)
  | .less (.groupedParents d ..) => return (r.ordering,project d)
  | _ => none

/-- Each of the two permitted methyl orders gives the same decisive
second sibling: D on the senior arm, H on the junior arm. -/
theorem deciding_groups :
    decidingGroups 3 4 = some (.gt,[[3,15],[3,18]],[[4,16],[4,20]],1) ∧
    decidingGroups 4 3 = some (.lt,[[3,15],[3,18]],[[4,16],[4,20]],1) := by
  constructor <;> decide +kernel

private def decisiveTerminal (arm : Nat) : Option (List Nat × Nat) := do
  let f ← occurrence? molecule [0]
  let a ← occurrence? molecule [0,arm]
  let sphere ← IsotopePriority.groupedSphere? molecule ⟨a,some f⟩ 1
  let (parent,terminal) ← sphere.addresses[1]?
  return ((parent.parent.route ++ [terminal.cursor.node]).map (·.atom),terminal.mass)

theorem deciding_sources :
    decisiveTerminal 3 = some ([3,15,10],2014101777844) ∧
    decisiveTerminal 4 = some ([4,16,13],1007825031898) := by decide +kernel

theorem central_assignment :
    (IsotopePriority.rank? molecule [0]).map (·.order) = some [1,3,4,2] ∧
    (ReferenceDerivation.derive? molecule geometry 3 molecule.atomCount [0]).map (·.verdict) = some (some ⟨.R,.S⟩) ∧
    (ReferenceDerivation.derive? molecule (mirror geometry) 3 molecule.atomCount [0]).map (·.verdict) = some (some ⟨.S,.R⟩) := by decide +kernel

/-- Both arms carry precisely one D. On arm 3 it is attached to O, on
arm 4 it is attached to C. Oxygen precedes carbon on both branches. -/
def exchanged : RawMolecule where
  atoms := List.replicate 5 (.aliphatic .C) ++ [.aliphatic .F,hydrogen,hydrogen,hydrogen,hydrogen,hydrogen,hydrogen,deuterium,hydrogen,hydrogen,
    .aliphatic .C,.aliphatic .C,hydrogen,.aliphatic .O,hydrogen,.aliphatic .O,deuterium,hydrogen]
  bonds := ([(0,1),(0,2),(1,2),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8),
    (3,15),(3,17),(3,18),(4,16),(4,19),(4,20),(15,9),(15,10),(15,11),
    (16,12),(16,13),(16,14),(18,21),(20,22)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

private def oxygenParentDecision : Option (List (List Nat) × List (List Nat) × Nat × Bool) := do
  let f ← occurrence? exchanged [0]
  let l ← occurrence? exchanged [0,3]
  let r ← occurrence? exchanged [0,4]
  let a ← IsotopePriority.groupedSphere? exchanged ⟨l,some f⟩ 1
  let b ← IsotopePriority.groupedSphere? exchanged ⟨r,some f⟩ 1
  let diff ← IsotopePriority.siblingMassDifference? a.word b.word
  return (a.order.map (fun (x : IsotopePriority.ParentGroup exchanged) => x.parent.route.map (·.atom)),
    b.order.map (fun (x : IsotopePriority.ParentGroup exchanged) => x.parent.route.map (·.atom)),diff.slot,
    IsotopePriority.siblingWord a.word == IsotopePriority.siblingWord b.word)

/-- Global sorting makes the terminal masses indistinguishable. Preserving
the constitutional O-before-C parent order identifies D versus H at slot zero. -/
theorem parent_precedence : saturatedWithHalogens exchanged = true ∧
    oxygenParentDecision = some ([[3,18],[3,15]],[[4,20],[4,16]],0,true) := by decide +kernel

assert_kernel_only admitted
assert_kernel_only carbons
assert_kernel_only physically_interior
assert_kernel_only constitutional_tie
assert_kernel_only prior_spheres
assert_kernel_only parent_orders

assert_kernel_only deciding_groups
assert_kernel_only deciding_sources
assert_kernel_only central_assignment
assert_kernel_only parent_precedence
end TetraStereo.Examples.RingGroupedIsotopeCoverage
