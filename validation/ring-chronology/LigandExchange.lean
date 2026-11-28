import TetraStereo.Engine.PublicAPI
open TetraStereo.OneCenter TetraStereo.Engine
open RingActivePairReport (Slot)

private def swaps {i : LocalizedChemicalRing.Input} {f : RingActivePairs.Site i}
    (fr : RingNestedActivePair.Frame i f) : Slot → RingBranchMatching.Proposal :=
  let atom := RingGroupedTrials.atom fr
  let slots := List.finRange 4
  let slot (n : Nat) := (slots.find? (fun s => atom s == n)).getD 0
  fun s =>
    let (l,u) := if atom s ≤ 2 then (3,4) else (1,2)
    ⟨slot l,slot u,fun n => if n = l then u else if n = u then l else n⟩

private def proposals (valid : Bool) (i : LocalizedChemicalRing.Input) : RingExchangeStore.Proposals i :=
  fun f fr _ => if f.val.root.val == 0 && f.val.address.isEmpty then
    some (if valid then swaps fr else fun _ => ⟨0,0,id⟩)
  else none

def main : IO Unit := do
  let m : RawMolecule := {
    atoms := ([.C,.O,.O,.S,.S] : List Element).map AtomSpec.aliphatic
    bonds := [(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)].map fun (a,b) => ⟨a,b,.single⟩ }
  let xyz : SpatialConfiguration := ⟨(List.range 5).map fun j =>
    let t : ℚ := j
    ⟨t,t*t,t*t*t⟩⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m xyz | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinates")
  let some a := (RingGroupedReport.centres i).find? (fun x => x.val == 0) | throw (IO.userError "root")
  let f := RingGroupedReport.origin i a
  let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "frame")
  let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
  let pick := swaps fr
  unless RingLigandExchange.check fr r pick do throw (IO.userError "tree matching")
  unless RingChemicalGraphProof.root i a == some none do throw (IO.userError "state")
  unless RingExchangeStore.checked (proposals true i) f r &&
      !RingExchangeStore.checked (proposals false i) f r do throw (IO.userError "proposal selection")
  let request := [0,0]
  let expected : Option RingGroupedReport.Report := some [(0,none),(0,none)]
  unless ringMolecularReportFromRaw? m xyz request == expected do throw (IO.userError "public raw report")
  for valid in [true,false] do
    unless ringExchangeReportFromRaw? (proposals valid) m xyz request == expected do
      throw (IO.userError s!"raw exchange report, valid proposal = {valid}")
  let distinct : RawMolecule := {
    atoms := ([.C,.O,.S,.F,.Cl] : List Element).map AtomSpec.aliphatic
    bonds := [(0,1),(1,2),(2,0),(0,3),(0,4)].map fun (a,b) => ⟨a,b,.single⟩ }
  -- Cl, S, F, O are atoms 4, 2, 3, 1. Their oriented determinant is +12.
  let chiral : Option RingGroupedReport.Report := some [(0,some (.chiral .S,.chiral .R))]
  unless ringMolecularReportFromRaw? distinct xyz [0] == chiral &&
      ringExchangeReportFromRaw? (proposals true) distinct xyz [0] == chiral do
    throw (IO.userError "a false exchange erased or changed the chiral center")
  IO.println "Four nonterminal exchanges verified; a false exchange preserves the control's S and reflected R."
