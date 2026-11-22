import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.BlueBookRule4aSource
import TetraStereo.Examples.RingVerifiedAbsence

set_option autoImplicit false

namespace TetraStereo.Examples.UnitClassReplay
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

private abbrev Hints := List Nat → Option Recursive.Frame

private def volume? (g : Geometry) (order : List Nat) : Option ℚ := do
  let [a,b,c,d] ← order.mapM g | none
  return CartesianPoint3.orientedVolume a b c d

/-- Inspect the parent once and read the class comparison, omission, exact
ordered frame, determinant and both hands from that same public result. -/
private def checkParent (m : RawMolecule) (g : Geometry) (hint : Hints)
    (leftSenior : Bool) : IO Unit := do
  let some checked := inspectRingOccurrence? m g [4] 3 hint (fun _ => 1) |
    throw (IO.userError "unresolved C4")
  let .compared a := checked.val | throw (IO.userError "C4 has no molecular comparison certificate")
  let .fourA c := a.step.decision | throw (IO.userError "C4 was not decided by Rule 4a")
  let first := c.difference.first
  let left := first.left
  let right := first.right
  let (lv,rv) := if leftSenior then (1,0) else (0,1)
  let hand := if leftSenior then RS.S else RS.R
  let absentPath := if leftSenior then [4,5] else [4,3]
  let signedVolume : ℚ := if leftSenior then 96 else -96
  unless c.prior.ordering == .eq && c.sphere == 1 && first.index == 0 &&
      c.ordering == (if leftSenior then .gt else .lt) &&
      left.site.cursor.node.history.reverse == [4,3] && left.value == lv &&
      right.site.cursor.node.history.reverse == [4,5] && right.value == rv do
    throw (IO.userError "incorrect earlier-rule tie, decisive sphere, occurrence or class")
  unless a.missing.map Sigma.fst == [absentPath] &&
      a.step.orders == (leftSenior,leftSenior) do
    throw (IO.userError "incorrect auxiliary omission or reflected priorities")
  let order := a.frame.order a.step.orders.1
  unless order == (if leftSenior then [0,3,5,31] else [0,5,3,31]) &&
      volume? g order == some signedVolume && volume? (mirror g) order == some (-signedVolume) &&
      a.reading.actual == hand && a.reading.reflected == hand.swap &&
      a.reading.label == some (.chiral hand) do
    throw (IO.userError "incorrect signed volume or uppercase letter at C4")

private def checkAbsence (m : RawMolecule) (g : Geometry) (hint : Hints)
    (expected : Recursive.Facts) : IO Unit := do
  let some checked := inspectRingOccurrence? m g [4,5] 2 hint (fun _ => 1) |
    throw (IO.userError "missing C5 absence certificate")
  let .absent c := checked.val | throw (IO.userError "C5 received a descriptor")
  unless c.classes.length == 3 && decide (c.positiveFacts.Perm expected) do
    throw (IO.userError "incorrect C5 ligand classes or loss of certified descendant occurrences")

def checkSource : IO Unit := do
  let m := BlueBookRule4aSource.molecule
  let g := BlueBookRule4aSource.geometry
  let hints := BlueBookRule4aSource.hints
  checkParent m g hints true
  checkParent m BlueBookRule4aSource.opposed hints false
  checkAbsence m g hints [([4,5,6],⟨.R,.S⟩),([4,5,10],⟨.R,.S⟩)]
  let some r := deriveRingOccurrence? m g [4] 3 hints (fun _ => 1) |
    throw (IO.userError "positive public API lost the published source assignment")
  unless r.val.label == some (.chiral .S) do throw (IO.userError "positive API did not return S")

def checkRing : IO Unit := do
  let m := RingVerifiedAbsence.molecule
  let g := RingVerifiedAbsence.geometry
  let hints := RingVerifiedAbsence.hints
  let expected : Recursive.Facts := [
    ([4,5,6],⟨.R,.S⟩),([4,5,6,7,11,10],⟨.S,.R⟩),
    ([4,5,10],⟨.R,.S⟩),([4,5,10,11,7,6],⟨.S,.R⟩)]
  for mol in [m,{m with bonds := m.bonds.reverse}] do
    checkParent mol g hints true
    checkAbsence mol g hints expected
  let missingChlorine : Geometry := fun i => if i = 13 then none else g i
  unless (inspectRingOccurrence? m missingChlorine [4,5] 2 hints (fun _ => 1)).isNone &&
      (inspectRingOccurrence? m g [4,5] 1 hints (fun _ => 1)).isNone do
    throw (IO.userError "an unresolved C5 inspection was reported as a chemical result")

end TetraStereo.Examples.UnitClassReplay

def main : IO Unit := do
  TetraStereo.Examples.UnitClassReplay.checkSource
  TetraStereo.Examples.UnitClassReplay.checkRing
  IO.println "Verified Rule 4a at C4, the C5 absence, all retained chiral occurrences and the unresolved controls."

assert_kernel_only TetraStereo.Engine.inspectRingOccurrence?
assert_kernel_only TetraStereo.Engine.deriveRingOccurrence?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.UnitClasses.Decision.fullTie
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.UnitClasses.Earlier.tied
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.UnitClasses.kind_mirror
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RingAuxiliaryInventory.Assignment.justified
assert_kernel_only TetraStereo.Examples.BlueBookRule4aSource.source_assignment
assert_kernel_only TetraStereo.Examples.RingVerifiedAbsence.parent_uses_absence
