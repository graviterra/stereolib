import TetraStereo.Engine.RingFullPathTrialReadings
import TetraStereo.Engine.RingSphereQueue

open TetraStereo.OneCenter TetraStereo.Engine

-- Two triangles share carbon 0. Only the shared atom is tetrahedral.
private def spiro (partner : Element) : RawMolecule :=
  { atoms := [Element.C,.S,partner,.S,partner].map AtomSpec.aliphatic
    bonds := ([(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)] : List (Nat × Nat)).map
      fun (a,b) => ⟨a,b,.single⟩ }

private def coords : SpatialConfiguration :=
  ⟨[⟨0,0,0⟩,⟨1,1,1⟩,⟨1,-1,-1⟩,⟨-1,1,-1⟩,⟨-1,-1,1⟩]⟩

private def check (partner : Element) (expected : Option RS) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? (spiro partner) coords
    | throw (IO.userError "molecular admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission")
  let some f := (RingActiveDistanceSchedule.sites i).find? (fun q =>
    q.val.root.val == 0 && q.val.node.history.map Fin.val == [0])
    | throw (IO.userError "missing spiro root")
  let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "missing root frame")
  let state : RingActiveDistanceSchedule.View i := fun q =>
    if i.certified.localizedOccurrenceDescriptorCenter? q = none then some none else RingGroupedPublication.state i q
  have exactState : state = RingGroupedPublication.state i := by
    funext q
    unfold state
    split
    next no => exact ((RingGroupedPublication.state_eq i q).trans (RingSphereQueue.grouped_skips i q _ no)).symm
    next => rfl
  let read := RingActiveDistanceSchedule.frozen state f
  have _exactReader : read = RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f := by
    unfold read
    rw [exactState]
  let copies := (RingActiveDistanceSchedule.sites i).countP (fun q =>
    q.val.root == f.val.root && q.val.node.provenance == .ringDuplicate 0)
  unless copies == 4 do throw (IO.userError "wrong number of root duplicates")
  for rev in [false,true] do
    let some out := RingFullPathTrialReadings.readings? fr read rev
      | throw (IO.userError "incomplete promotion trials")
    let wanted := if rev then expected.map RS.swap else expected
    let marks := out.map Prod.fst
    unless marks == (List.finRange 4).map some && out.all (fun pair => pair.2 == wanted) do
      throw (IO.userError s!"unexpected promotion readings: {repr out}")
    IO.println s!"partner={repr partner}, mirror={rev}, four marked readings: {repr (out.map Prod.snd)}"
    (← IO.getStdout).flush

def main : IO Unit := do
  -- Promoting S1 or O1 gives order 1,3,2,4. The other marks swap both
  -- pairs. The determinant is -16 in both orders.
  check .O (some .R)
  -- The two sulfur atoms in the unmarked triangle remain equivalent.
  check .S none
