import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.RingRemoteIsotope
import TetraStereo.Examples.BlueBookRingDuplicate

set_option autoImplicit false
namespace TetraStereo.Examples.RingConstitutionReplay
open OneCenter Engine RingChemicalPriority IsotopePriority Recursive LocalizedGenericMarkedRecalculation

private def requirePair (m : RawMolecule) (p : List Nat) (i j : Nat) (o : Ordering)
    (basis : Option Rule) : IO (IncidentComparison m p i j) := do
  let some c := compareRingConstitution? m p i j | throw (IO.userError "unresolved comparison")
  unless c.ordering == o && c.rule? == basis do throw (IO.userError "incorrect rule, sphere or direction")
  return c

def checkPublished : IO Unit := do
  for m in [BlueBookRingDuplicate.molecule, BlueBookRingDuplicate.isotopeControl] do
    for mol in [m,{m with bonds := m.bonds.reverse}] do
      let _ ← requirePair mol [1] 2 10 .gt (some (.duplicateOrigin 7))
      let _ ← requirePair mol [1] 10 2 .lt (some (.duplicateOrigin 7))
      let _ ← requirePair mol [1] 0 2 .gt (some .atomicNumber)
      let g := BlueBookRingDuplicate.geometry
      for (geom,hand) in [(g,RS.S),(mirror g,RS.R)] do
        let some r := deriveRingOccurrence? mol geom [1] 1 (fun _ => none) (fun _ => 0) |
          throw (IO.userError "missing source center")
        unless r.val.label == some (.chiral hand) do throw (IO.userError "source center letter")
  let m := BlueBookRingDuplicate.molecule
  let some arm := occurrence? m [0,1] | throw (IO.userError "missing alcohol arm")
  unless ReferenceBlocks.precedes m arm (fun _ => 0) (fun _ => none) false
      ([0,1,2,3],.S) ([0,1,10,11],.R) do
    throw (IO.userError "descendant order lost the rule at the fork")

def checkIsotopes : IO Unit := do
  let m := RingRemoteIsotope.molecule 13 12
  for mol in [m,{m with bonds := m.bonds.reverse}] do
    for path in [[0],[14,0]] do
      let c ← requirePair mol path 1 4 .gt (some (.isotopeMass 2))
      let _ ← requirePair mol path 4 1 .lt (some (.isotopeMass 2))
      match c.verdict with
      | .greater (.spheres d ..) =>
        unless d.first.left.site.cursor.node.history.reverse == path ++ [1,2] &&
            d.first.right.site.cursor.node.history.reverse == path ++ [4,3] do
          throw (IO.userError "incorrect first unequal occurrences")
      | _ => throw (IO.userError "missing molecular isotope traces")
  let _ ← requirePair (RingRemoteIsotope.molecule 12 12) [0] 1 4 .eq none
  let _ ← requirePair RingRemoteIsotope.fluorinatedLightArm [0] 1 4 .lt (some .atomicNumber)
  unless (compareRingConstitution? (RingRemoteIsotope.molecule 999 12) [0] 1 4).isNone do
    throw (IO.userError "assigned an unsupported mass")
  let exchange (i : Nat) := if i < 3 then i else if i < 17 then i+14 else i-14
  let hints : List Nat → Option Recursive.Frame := fun p =>
    if p == [0] then some ⟨.five,1,3,17,2,exchange,false⟩ else none
  for g in [RingRemoteIsotope.pairedGeometry,mirror RingRemoteIsotope.pairedGeometry] do
    let some r := deriveRingOccurrence? RingRemoteIsotope.paired g [0] 2 hints (fun _ => 1) |
      throw (IO.userError "missing recursive assignment")
    unless r.val.label == some (.pseudoasymmetric .s) do throw (IO.userError "incorrect parent casing")

end TetraStereo.Examples.RingConstitutionReplay

def main : IO Unit := do
  TetraStereo.Examples.RingConstitutionReplay.checkPublished
  TetraStereo.Examples.RingConstitutionReplay.checkIsotopes
  IO.println "Verified the published Rule 1b S, both isotope traces, constitutional equality and the recursive Rule 5 s."

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.OriginDecision.first_difference
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopeSpheres.Decision.first_difference
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.IncidentComparison.equal_observer
