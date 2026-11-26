import TetraStereo.Engine.RingOriginTwinStore

/-! The two written hydrogen leaves on carbon 3 remain identical at every
eligible occurrence of that carbon in the bicyclic input. The graph-only and atomic-only
justifications both fail at these occurrences. -/
open TetraStereo.OneCenter TetraStereo.Engine

private def trialControl (missing sameParity : Bool) : RingPairwisePublication.Data :=
  let ordinary : RingPairwisePublication.Directions := fun a b => decide (a.val / 2 < b.val / 2)
  let ordered : RingPairwisePublication.Directions := fun a b => decide (a < b)
  let exchanged : RingPairwisePublication.Directions := fun a b =>
    decide (Equiv.swap (0 : Fin 4) 1 a < Equiv.swap (0 : Fin 4) 1 b)
  { ordinary := fun _ => ordinary
    marked := fun _ s => match s with
      | some 0 => some ordered
      | some 1 => if missing then none else some (if sameParity then ordered else exchanged)
      | _ => some ordinary }

def main : IO Unit := do
  unless RingOriginTwinBallots.check (trialControl false false) 0 1 &&
      !RingOriginTwinBallots.check (trialControl false true) 0 1 &&
      !RingOriginTwinBallots.check (trialControl true false) 0 1 do
    throw (IO.userError "strict opposite-parity, same-parity or unavailable marked-trial control")

  let m : RawMolecule := {
    atoms := [.C,.B,.B,.C,.S,.F,.C,.F,.Cl,.Br,.H,.H].map AtomSpec.aliphatic
    bonds := [(0,1),(0,2),(1,2),(1,3),(3,4),(4,2),(0,5),(0,6),(6,7),(6,8),(6,9),(3,10),(3,11)].map
      (fun (a,b) => ⟨a,b,.single⟩) }
  let coords : List CartesianPoint3 := [⟨0,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩,⟨2,1,0⟩,⟨1,2,1⟩,
    ⟨0,0,1⟩,⟨-1,-1,-1⟩,⟨-2,-1,-1⟩,⟨-1,-2,-1⟩,⟨-1,-1,-2⟩,⟨2,1,1⟩,⟨3,1,0⟩]
  let g : SpatialConfiguration := ⟨coords⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i && (RingHydrogenCompletion.plan m).isEmpty do
    throw (IO.userError "expected admitted hydrogen-complete input")
  let some root := (List.finRange i.certified.certified.input.molecule.atomCount)[0]? | throw (IO.userError "root")
  if RingAtomicMetricPublication.check i root then throw (IO.userError "prior certificate unexpectedly passed")
  let n := RingActiveDistanceSchedule.height i + 1
  let some audit := RingOriginTwinStore.audit i root n | throw (IO.userError "twin certificate failed")
  let native := RingSphereStore.rows i root n
  let active := RingOriginIndexedKeys.rows i root n
  unless audit == native && audit == active do throw (IO.userError "complete row mismatch")
  let rescued := audit.filter fun row => !RingOriginOrderCheck.focus row.1 &&
    (RingAtomicMetricPublication.early? i row.1).isNone
  unless !rescued.isEmpty && rescued.all (fun row => row.1.val.node.current?.any (fun a => a.val == 3) &&
    row.2 == some none) do throw (IO.userError s!"wrong rescued rows {rescued.length}")
  let x := RingHydrogenReport.fromRaw? m g [0]
  let y := RingOriginIndexedKeys.fromRaw? m g [0]
  unless x == y && (x.bind List.head?).any (fun row => row.2.isSome) do throw (IO.userError "raw output")
  IO.println s!"{rescued.length} twin refusals, {audit.length} equal rows; raw {repr x}"
