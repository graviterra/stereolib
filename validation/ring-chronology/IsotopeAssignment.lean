import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.RingIsotopeAssignment

set_option autoImplicit false

open TetraStereo TetraStereo.Engine TetraStereo.OneCenter
open TetraStereo.Examples.RingIsotopeAssignment LocalizedGenericMarkedRecalculation

private def verifyAssignment (m : RawMolecule) (g : Geometry) (path order : List Nat)
    (expected : RS) : IO Unit := do
  let some ranking := rankRingIsotopes? m path | throw (IO.userError "missing isotope ranking")
  unless ranking.order == order do throw (IO.userError "incorrect ligand order")
  let some r := deriveRingOccurrence? m g path 1 (fun _ => none) (fun _ => 0) |
    throw (IO.userError "failed to derive the occurrence from the molecule")
  unless r.val.label == some (.chiral expected) && r.val.reflected == expected.swap do
    throw (IO.userError "incorrect letter or reflection")

def main : IO Unit := do
  for (left,right,mid,hand) in [(13,12,[1,2],RS.R),(12,13,[2,1],RS.S)] do
    let m := molecule left right
    for mol in [m,{m with bonds := m.bonds.reverse}] do
      for path in [[0],[3,0]] do
        let order := [3] ++ mid ++ [4]
        verifyAssignment mol geometry path order hand
        verifyAssignment mol (mirror geometry) path order hand.swap
  unless (rankRingIsotopes? (molecule 12 12) [0]).isNone do
    throw (IO.userError "resolved equal masses")
  unless (rankRingIsotopes? (molecule 13 12) [0,7]).isNone do
    throw (IO.userError "accepted an unreachable occurrence")
  unless (rankRingIsotopes? (molecule 999 12) [0]).isNone do
    throw (IO.userError "accepted an unknown nuclide")
  IO.println "Verified isotope orders and uppercase readings at the root and retained occurrence."

assert_kernel_only TetraStereo.Engine.ringIsotopeAssignment
