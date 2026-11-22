import TetraStereo.Engine.RingReferenceDerivation
import TetraStereo.Examples.Rule6CageAuxiliaries
import TetraStereo.Engine.LocalizedChemicalRingPublic
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace TetraStereo.Examples.RingHydrocarbonCage
open OneCenter Engine LocalizedGenericMarkedRecalculation RingChemicalPriority CertifiedLocalizedCIPInput

/-- Replace the three oxygen bridges of the cage by C(CH₃)₂ in the same positions. -/
def molecule : RawMolecule where
  atoms :=
    let c := AtomSpec.aliphatic .C
    let h := AtomSpec.aliphatic .H
    [c,c,c,c,c,c,c,c,c,c,
      h,h,h,h,h,h,h,h,h,h,
      c,c,c,c,c,c,h,h,h,h,
      h,h,h,h,h,h,h,h,h,h,
      h,h,h,h]
  bonds :=
    [⟨0,10,.single⟩,⟨0,1,.single⟩,⟨1,4,.single⟩,⟨4,7,.single⟩,
      ⟨7,2,.single⟩,⟨1,11,.single⟩,⟨7,14,.single⟩,⟨7,15,.single⟩,
      ⟨0,2,.single⟩,⟨2,5,.single⟩,⟨5,8,.single⟩,⟨8,3,.single⟩,
      ⟨2,12,.single⟩,⟨8,16,.single⟩,⟨8,17,.single⟩,⟨0,3,.single⟩,
      ⟨3,6,.single⟩,⟨6,9,.single⟩,⟨9,1,.single⟩,⟨3,13,.single⟩,
      ⟨9,18,.single⟩,⟨9,19,.single⟩,⟨4,20,.single⟩,⟨20,26,.single⟩,
      ⟨20,27,.single⟩,⟨20,28,.single⟩,⟨4,21,.single⟩,⟨21,29,.single⟩,
      ⟨21,30,.single⟩,⟨21,31,.single⟩,⟨5,22,.single⟩,⟨22,32,.single⟩,
      ⟨22,33,.single⟩,⟨22,34,.single⟩,⟨5,23,.single⟩,⟨23,35,.single⟩,
      ⟨23,36,.single⟩,⟨23,37,.single⟩,⟨6,24,.single⟩,⟨24,38,.single⟩,
      ⟨24,39,.single⟩,⟨24,40,.single⟩,⟨6,25,.single⟩,⟨25,41,.single⟩,
      ⟨25,42,.single⟩,⟨25,43,.single⟩]

private def rotate : Nat → CartesianPoint3 → CartesianPoint3
  | 0,p => p
  | n+1,p => rotate n ⟨p.z,p.x,p.y⟩

def spatial : SpatialConfiguration :=
  let methyl : List CartesianPoint3 := [⟨5,2,4⟩,⟨6,-1,-1⟩]
  let hydro : List CartesianPoint3 :=
    [⟨6,0,4⟩,⟨5,3,6⟩,⟨5,4,5⟩,⟨7,-3,-1⟩,⟨6,0,1⟩,⟨7,-2,-5⟩]
  ⟨Rule6CageAuxiliaries.xyz.positions ++ (List.range 3).flatMap (fun k => methyl.map (rotate k)) ++
    (List.range 3).flatMap (fun k => hydro.map (rotate k))⟩

private def geometry : Geometry := fun i => spatial.positions[i]?

private def interior (i : Nat) : Bool :=
  let ns := molecule.writtenNeighbors i
  let weight (j : Nat) : Rat := if i = 0 ∧ j = 10 then 3 else 1
  ([CartesianPoint3.x, CartesianPoint3.y, CartesianPoint3.z]).all fun axis =>
    ((ns.mapM fun j => (geometry j).map fun p => weight j * axis p).map List.sum) ==
      (geometry i).map fun p => (ns.map weight).sum * axis p

theorem atom_count : molecule.atomCount = 44 := by decide +kernel

private def ordersAtSplit (root high low : Nat) := do
  let p ← occurrence? molecule [0,root]
  let x ← occurrence? molecule [0,root,high]
  let y ← occurrence? molecule [0,root,low]
  let d ← ReferenceDistance.rootedPriority? molecule p x y
  return d.ordering

/-- At the two arms' branch points, the two carbon children tie by
nuclear charge. The substituted carbon ranks above the methylene in both. -/
theorem internal_priority :
    ordersAtSplit 2 5 7 = some .gt ∧ ordersAtSplit 3 6 8 = some .gt := by decide +kernel

private def earlyMark (i j : Nat) := do
  let f ← occurrence? molecule [0]
  let l ← occurrence? molecule [0,i]
  let r ← occurrence? molecule [0,j]
  let a : CanonicalRerootCursor := ⟨l,some f⟩
  let b : CanonicalRerootCursor := ⟨r,some f⟩
  let obs := IsotopePriority.fullObservation? molecule [0]
  if h : IsotopePriority.treesMatch molecule obs (IsotopePriority.budget molecule+1) a b = true then
    let strict ← ReferenceDistance.difference? (IsotopePriority.treesMatch_sound h) 1
    let v : ReferenceDistance.Verdict molecule obs a b 1 := .strict strict
    return (v.ordering,v.route?)
  none

/-- Both arms reach the marked atom at sphere IV. Branch priority breaks
the tie in favor of the route through the substituted carbon at atom 6. -/
theorem marked_directions :
    earlyMark 2 3 = some (.lt,some [3,6,9,1]) ∧
    earlyMark 3 2 = some (.gt,some [3,6,9,1]) := by decide +kernel

/-- Executable validation of the complete recursive certificate, its
published comparisons, and the orders actually used by the three trials. -/
def validate : IO Unit := do
  let require (valid : Bool) (message : String) : IO Unit :=
    unless valid do throw (IO.userError message)
  require ((LocalizedChemicalRing.admitRawSpatial? molecule spatial).isSome &&
    saturatedWithHalogens molecule) "hydrocarbon cage admission failed"
  require ((List.range molecule.atomCount).all fun i =>
    (molecule.atoms[i]?.map (·.element) != some .C) ||
      ((readback? geometry (molecule.writtenNeighbors i)).isSome && interior i))
    "a carbon is degenerate or outside its ligand tetrahedron"
  let some c := ReferenceDerivation.derive? molecule geometry 3 molecule.atomCount [0] |
    throw (IO.userError "missing cage center certificate")
  require (c.verdict == some ⟨.R,.S⟩) "incorrect actual or reflected descriptor"
  for (i,j,sign) in [(2,3,Ordering.lt),(3,2,Ordering.gt)] do
    let some pair := c.compare? i j 1 | throw (IO.userError "missing published comparison")
    require (pair.verdict.ordering == sign && pair.verdict.route? == some [3,6,9,1])
      "wrong sign or winning occurrence from published comparison"
  let some f := c.frame? 3 | throw (IO.userError "missing published frame")
  let some trials := f.promotion?.bind ReferenceFrame.Frame.population? |
    throw (IO.userError "missing reference trials")
  let observed := trials.trials.map fun t =>
    (t.mark, ReferenceFrame.orders f.ids t.table false, ReferenceFrame.orders f.ids t.table true)
  let expected := [(1,[1,3,2,10]), (2,[2,1,3,10]), (3,[3,2,1,10])]
  require (observed == expected.map fun (mark,order) => (mark,[order],[order]))
    "wrong marked order on the actual or reflected cage"

#eval validate

end TetraStereo.Examples.RingHydrocarbonCage

assert_kernel_only TetraStereo.Examples.RingHydrocarbonCage.atom_count
assert_kernel_only TetraStereo.Examples.RingHydrocarbonCage.internal_priority
assert_kernel_only TetraStereo.Examples.RingHydrocarbonCage.marked_directions
