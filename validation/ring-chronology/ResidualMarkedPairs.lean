import TetraStereo.Engine.RingResidualPairDecision
open TetraStereo.OneCenter TetraStereo.Engine
open RingResidualPairDecision (Classification)

/-! The shared carbon joins an O–O ring and an S–S ring. Both pairs tie
before nomination. Marking sulfur selects that sulfur. Marking oxygen
preserves the exchange of the two sulfur branches. -/
def main : IO Unit := do
  let m : RawMolecule := {
    atoms := ([.C,.O,.O,.S,.S] : List Element).map AtomSpec.aliphatic
    bonds := [(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)].map fun (a,b) => ⟨a,b,.single⟩ }
  let xyz : SpatialConfiguration := ⟨(List.range 5).map fun j =>
    let t : ℚ := j
    ⟨t,t*t,t*t*t⟩⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m xyz | throw (IO.userError "raw admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinates")
  let some root := (RingGroupedReport.centres i).find? (fun x => x.val == 0) | throw (IO.userError "root")
  let f := RingGroupedReport.origin i root
  let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "frame")
  let batch := RingActiveDistanceSchedule.height i + 1
  let some trials := RingResidualPairDecision.atSite? i root batch f | throw (IO.userError "schedule")
  let slots := List.finRange 4
  unless (trials.map (·.nomination)).Perm (slots.map some) do throw (IO.userError "mark nominations")
  let findSlot (id : Nat) := slots.find? (fun s => RingGroupedTrials.atom fr s == id)
  let some a := findSlot 3 | throw (IO.userError "first sulfur")
  let some b := findSlot 4 | throw (IO.userError "second sulfur")
  for (trial,ordinal) in trials.zipIdx do
    let some s := trial.nomination | throw (IO.userError "missing mark")
    let answer : Classification :=
      if s == a then .noExchangeLeft .activeMark
      else if s == b then .noExchangeRight .activeMark
      else .exchangeTie
    for rev in [false,true] do
      let value := RingResidualPairDecision.classifyAt? i root batch f ordinal rev a b
      unless value == some (some s,answer) do throw (IO.userError s!"marked sulfur pair {repr value}")
  IO.println "Four nominations on both geometries matched the predicted sulfur orders and exchanges."
