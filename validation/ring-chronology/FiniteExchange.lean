import TetraStereo.Engine.RingFiniteExchange

/-! The same pair of nonterminal sulfur arms admits or excludes a marked
exchange according to the nominated atom. Both decisions finish before the
exhaustive reference search. -/
open TetraStereo.OneCenter TetraStereo.Engine

def main : IO Unit := do
  let m : RawMolecule := {
    atoms := [.C,.O,.O,.S,.S].map AtomSpec.aliphatic
    bonds := [(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)].map fun (a,b) => ⟨a,b,.single⟩ }
  let xyz : SpatialConfiguration := ⟨(List.range 5).map fun n =>
    let t : ℚ := n
    ⟨t,t*t,t*t*t⟩⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m xyz | throw (IO.userError "admission")
  let some a := (RingGroupedReport.centres i).find? (fun x => x.val == 0) | throw (IO.userError "root")
  let f := RingGroupedReport.origin i a
  let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "frame")
  let read := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
  let slot (id : Nat) := (List.finRange 4).find? fun s => RingGroupedTrials.atom fr s == id
  let some o := slot 1 | throw (IO.userError "oxygen ligand")
  let some u := slot 3 | throw (IO.userError "first sulfur ligand")
  let some v := slot 4 | throw (IO.userError "second sulfur ligand")
  for (nominee,expected) in [(o,true),(u,false)] do
    unless RingFiniteExchange.quick? fr read nominee u v == some expected do
      throw (IO.userError "expected a decisive fast comparison")
    unless RingFiniteExchange.decidePair fr read nominee u v == expected do
      throw (IO.userError "incorrect exact decision")
  IO.println "The sulfur arms exchange under an oxygen mark and cannot exchange under a mark on the first sulfur."
