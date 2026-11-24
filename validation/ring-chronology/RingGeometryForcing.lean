import TetraStereo.Engine.RingGeometryCertificates
import TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime

open TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Examples
open CertifiedLocalizedCIPInput
open RingActivePairReport (Slot)
attribute [local instance] lexOrd

private def point (x y z : ℚ) : CartesianPoint3 := ⟨x,y,z⟩

-- The focus is bonded to two oxygens and two carbons. A C–C bond joins
-- the two three-membered rings even after deleting the focus.
private def bridged : SpatialConfiguration := ⟨[point 0 0 0, point 1 0 1, point 0 1 (-1),
  point 0 (-1) (-1), point (-1) 0 1, point 0 2 (-2), point 0 (-2) (-2)]⟩

private def input (smiles : String) (xyz : SpatialConfiguration) : IO LocalizedChemicalRing.Input := do
  let .ok (some i) := LocalizedChemicalRing.admitSmilesSpatial? smiles xyz | throw (IO.userError "structural admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "degenerate geometry")
  return i

private def swapAtom (a b n : Nat) := if n = a then b else if n = b then a else n
private def swapBridges (a b n : Nat) :=
  swapAtom (2*a+2) (2*b+2) (swapAtom (2*a+1) (2*b+1) (swapAtom a b n))

private def probe (i : LocalizedChemicalRing.Input) (id : Nat) (propellane : Bool) : IO Int := do
  let some root := (RingGroupedReport.centres i).find? (fun a => a.val == id) | throw (IO.userError "missing centre")
  let q := RingGroupedReport.origin i root
  let some ctx := RingGeometryCertificates.prepare? i q | throw (IO.userError "unresolved geometric context")
  let read := ctx.read
  let fr := ctx.fr
  let arms := ctx.arms
  let marks := RingGroupedOrders.marks arms
  let atom := RingGroupedTrials.atom fr
  let slots := List.finRange 4
  let result : Option RingNestedActivePair.Labels ← if propellane then do
    unless marks.map atom == [2,3,4] do throw (IO.userError "expected the three methylene marks")
    let propose (s : Slot) : RingBranchMatching.Proposal :=
      let other := ([2,3,4] : List Nat).filter (fun n => n != atom s)
      let a := other[0]!
      let b := other[1]!
      let slot (n : Nat) := (slots.find? (fun k => atom k == n)).getD 0
      ⟨slot a,slot b,swapBridges a b⟩
    let some _ := ctx.refusal? propose | throw (IO.userError "molecular exchange certificate failed")
    pure none
  else do
    unless fr.atoms slots == [1,2,3,4] do throw (IO.userError "unexpected ligand frame")
    let some ⟨letters,_⟩ := ctx.descriptor? 0 3 1 2 | throw (IO.userError "first-sphere descriptor certificate failed")
    pure (some letters)
  let mut votes : List Int := []
  for s in marks do
    let w := RingOrientation.markedWord fr read s
    let vote := RingOrientation.orientation (RingGroupedOrders.wins arms false w)
    votes := votes ++ [vote]
  let base := RingOrientation.baseline fr
  let balance := base * votes.sum
  IO.println s!"centre {id}, ligand atoms {slots.map atom}, marks {marks.map atom}, orientation signs {votes}, signed balance {balance}, letters {repr result}"
  (← IO.getStdout).flush
  let some signature := RingGeometryCriterion.signature? i q read | throw (IO.userError "missing geometric signature")
  unless signature.balance == balance && signature.letters == result do throw (IO.userError "geometric descriptor")
  if propellane then
    unless marks.length == 3 && votes.all (· == 0) && result.isNone do throw (IO.userError "expected three surviving ties")
  else
    let written : RS := if 0 < balance then .R else .S
    unless marks.length == 4 && votes.sum.natAbs == 4 && result == some (.chiral written,.chiral written.swap) do
      throw (IO.userError "expected four concordant strict orders and opposite uppercase letters")
  return balance

def main (args : List String) : IO Unit := do
  unless args == [] || args == ["--bridged"] || args == ["--propellane"] do
    throw (IO.userError "expected --bridged, --propellane, or no arguments")
  if args == [] || args == ["--bridged"] then
    let a ← input "C123OC1C2O3" bridged
    unless [(1,2),(2,3),(3,4)].all (fun (u,v) => a.molecule.bondOrder u v == 1) do
      throw (IO.userError "expected a connected path between the four ligands after deleting the focus")
    let reflected : SpatialConfiguration := ⟨bridged.positions.map (fun p => {p with x := -p.x})⟩
    let b ← input "C123OC1C2O3" reflected
    let v ← probe a 0 false
    let w ← probe b 0 false
    unless v == 4 && w == -4 do throw (IO.userError "expected R on the written configuration and S on reflection")
  if args == [] || args == ["--propellane"] then
    let i ← input LocalizedChemicalRingPropellaneLifetime.smiles LocalizedChemicalRingPropellaneLifetime.spatial
    for n in [0,1] do
      let _ ← probe i n true
