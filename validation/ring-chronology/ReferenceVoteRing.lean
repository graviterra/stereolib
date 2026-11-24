import TetraStereo.Engine.RingRebuiltStereo

open TetraStereo.OneCenter TetraStereo.Engine
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader)

-- A cyclopropyl group is bonded to C3. Each of the three carbon branches
-- at C3 carries three CH(F)Cl groups; every atom and hydrogen is explicit.
private def mol : RawMolecule where
  atoms := ((List.replicate 16 Element.C) ++ (List.range 9).flatMap (fun _ => [Element.F,Element.Cl,Element.H]) ++
    List.replicate 5 Element.H).map AtomSpec.aliphatic
  bonds := (([(0,1),(1,2),(2,0),(0,3),(0,43),(1,44),(1,45),(2,46),(2,47)] : List (Nat × Nat)) ++
    (List.range 3).map (fun j => (3,4+j)) ++ (List.range 9).flatMap (fun j =>
      [(4+j/3,7+j),(7+j,16+3*j),(7+j,17+3*j),(7+j,18+3*j)])).map fun (a,b) => ⟨a,b,.single⟩

private def desired (j : Nat) : RS := if [3,4,6,7].contains j then .R else .S

private def geometry (swapAt : Nat → Bool) : SpatialConfiguration :=
  ⟨(List.range 48).map fun n =>
    let m := if 16 ≤ n && n < 43 && swapAt ((n-16)/3) then
      match (n-16)%3 with | 0 => n+1 | 1 => n-1 | _ => n
      else n
    let t : ℚ := m
    ⟨t,t*t,t*t*t⟩⟩

private def admit (swaps : Nat → Bool) : IO LocalizedChemicalRing.Input := do
  let some i := LocalizedChemicalRing.admitRawSpatial? mol (geometry swaps) | throw (IO.userError "structural admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission")
  return i

private def get (i : LocalizedChemicalRing.Input) (sites : List (Site i)) (path : List Nat) : IO (Site i) := do
  let some f := sites.find? (fun f => f.val.node.provenance == .realAtom && f.val.node.history.map Fin.val == path)
    | throw (IO.userError s!"missing path {path}")
  return f

private def path (j : Nat) := [7+j,4+j/3,3,0]

-- Pass --grouped to replay with the grouped evaluator and its constitutional early exit.
def main (args : List String) : IO Unit := do
  unless args.isEmpty || args == ["--grouped"] do throw (IO.userError "expected no arguments or --grouped")
  let grouped := !args.isEmpty
  let initial ← admit (fun _ => false)
  let rawSites := (RingActiveDistanceSchedule.sites initial).filter fun q => q.val.root.val == 0
  let first ← get initial rawSites (path 0)
  let some sig := RingSphereQueue.early? initial first | throw (IO.userError "first geometric hand missing")
  let some (.chiral base,_) := sig.letters | throw (IO.userError "first hand was not absolute")
  let i ← admit (fun j => desired j != base)
  let sites := (RingActiveDistanceSchedule.sites i).filter fun q => q.val.root.val == 0
  let f ← get i sites [0]
  let trunk ← get i sites [3,0]
  let root := f.val.root
  let inventory := sites.filter fun q => decide (RingSphereQueue.candidate root q)
  let queue := fun d => inventory.filter fun q => RingActiveDistanceSchedule.distance q == d
  IO.println s!"Admitted 48 atoms, materializing {inventory.length} auxiliary occurrences"
  (← IO.getStdout).flush
  let top := RingActiveDistanceSchedule.height i
  let rule : RingActiveDistanceSchedule.Rule i := if grouped then fun q rd =>
      match RingSphereQueue.early? i q with
      | some sig => some sig.letters
      | none => RingGroupedPublication.publish? i q rd
    else RingRebuiltStereo.publish i
  let rows := RingSphereQueue.stored rule root queue top (top+1)
  let read := RingSphereQueue.reader root (RingSphereQueue.viewOf rows)
  for j in List.range 9 do
    let q ← get i sites (path j)
    unless read q == some (some (.chiral (desired j),.chiral (desired j).swap)) do
      throw (IO.userError s!"incorrect geometry-derived hand at {path j}: {repr (read q)}")
  for j in List.range 3 do
    let q ← get i sites [4+j,3,0]
    unless read q == some none do throw (IO.userError s!"unexpected earlier reference {repr (read q)}")
  unless read trunk == some none do throw (IO.userError s!"trunk acquired a descriptor {repr (read trunk)}")
  let arm : Arm i := ⟨trunk,some f⟩
  let some hits := (if grouped then (RingGroupedStereo.arm? i read arm).map (·.hits)
    else (RingRebuiltStereo.arm? i read 0 arm).map (·.1.hits)) | throw (IO.userError "trunk rank missing")
  let actual := RingRetainedReferenceGroup.hands hits false
  unless actual.count .R == 4 && actual.count .S == 5 &&
      RingRetainedReferenceGroup.references hits false == [.S] &&
      RingRetainedReferenceGroup.references hits true == [.R] do
    throw (IO.userError s!"unexpected reference population {repr actual}")
  IO.println "Scheduled R/S counts by parent 0:3, 2:1, 2:1. Rule 4b pools 4:5 and selects S, reflected R. Voting by parent selects R."
