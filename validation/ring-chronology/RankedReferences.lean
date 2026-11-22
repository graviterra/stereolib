import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.RankedRingReference

set_option autoImplicit false
namespace TetraStereo.Examples.RankedReferenceReplay
open OneCenter Engine Engine.RingChemicalPriority Recursive RankedRingReference
open LocalizedGenericMarkedRecalculation

def check (m : RawMolecule) (g : Geometry) (expected : RS) : IO Unit := do
  let radius := fun _ : List Nat => 1
  for rev in [false,true] do
    let some f := hints [0] | throw (IO.userError "missing frame")
    let some comparison := compareRingRule4b? m g [0] f 1 rev 3 hints radius |
      throw (IO.userError "frame or earlier-rule comparison unresolved")
    unless comparison.result == .lt do throw (IO.userError "wrong comparison")
    let a := comparison.left
    let b := comparison.right
    unless (compareRingRule4b? m g [0] {f with rename := id} 1 rev 3 hints radius).isNone do
      throw (IO.userError "accepted invalid path correspondence")
    for (refs,sz,rows) in [(a.population.references,a.population.members.length,a.population.sites.length),
                           (b.population.references,b.population.members.length,b.population.sites.length)] do
      unless refs == [.R,.S] && sz == 2 && rows == 3 do throw (IO.userError "wrong senior class")
    unless a.bounds.low == a.bounds.high && a.bounds.low.flatten == [1,0,1,0] &&
        b.bounds.low == b.bounds.high && b.bounds.low.flatten == [1,0,1,1] &&
        rankedDecision? a.population.references b.population.references a.bounds b.bounds == some .lt do
      throw (IO.userError "wrong ranked words")
  let some root := deriveRingOccurrence? m g [0] 3 hints radius | throw (IO.userError "root unresolved")
  unless root.val.actual == expected && root.val.reflected == expected.swap &&
      root.val.label == some (.chiral expected) do throw (IO.userError "wrong report casing")
  unless (rankRingArm? m g [0] false 3 hints radius).isNone &&
      (rankRingArm? m g [0,3] false 0 hints radius).isNone do throw (IO.userError "accepted incomplete input")

end TetraStereo.Examples.RankedReferenceReplay

open TetraStereo TetraStereo.OneCenter TetraStereo.Examples.RankedRingReference
open TetraStereo.Examples.RankedReferenceReplay in
def main : IO Unit := do
  for m in [molecule,{molecule with bonds := molecule.bonds.reverse}] do
    check m geometry .R
    check m (LocalizedGenericMarkedRecalculation.mirror geometry) .S
  let some f := hints [0] | throw (IO.userError "missing root frame")
  for rev in [false,true] do
    let some tie := Engine.compareRingRule4b? molecule enantiomorphicGeometry [0] f 1 rev 3 hints (fun _ => 1) |
      throw (IO.userError "failed to establish the enantiomorphic Rule 4b tie")
    unless tie.result == .eq do throw (IO.userError "wrong Rule 4b equality")
    unless (Engine.compareRingRule4b? brominated geometry [0] f 1 rev 3 hints (fun _ => 1)).isNone do
      throw (IO.userError "used Rule 4b before resolving the constitutional difference")
  IO.println "Both reference choices, complete ranked words and uppercase assignment verified on both geometries and both bond orders."

assert_kernel_only TetraStereo.Engine.RankedRingArm.comparison
assert_kernel_only TetraStereo.Examples.RankedRingReference.root_assignment
assert_kernel_only TetraStereo.Examples.RankedRingReference.competing_references
assert_kernel_only TetraStereo.Examples.RankedRingReference.carbon_frames_interior
assert_kernel_only TetraStereo.Engine.RingRule4bComparison.all_readings
assert_kernel_only TetraStereo.Engine.RingRule4bComparison.complete_words
