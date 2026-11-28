import TetraStereo.Engine.RingLayeredHandCounts
import TetraStereo.Engine.RingCountedPathVerdict

/-! In this 25-atom model each boron arm has one near phosphorus and two
farther phosphorus atoms. Test how the near hand sets the reference used to
pair the two farther hands. The triangle at atom zero supplies the ring. -/
open TetraStereo.OneCenter TetraStereo.Engine
open RingResidualPairDecision (Verdict)
open RingLayeredHandCounts (profile? outcome)

private def molecule (mixed : Bool) : RawMolecule :=
  let elements : List Element := [.C,.O,.S] ++ List.replicate 4 .B ++ List.replicate 6 .P ++
    (List.range 6).flatMap (fun k => [.F,if mixed && (k == 2 || k == 4) then .Br else .Cl])
  let core := [(0,1),(1,2),(2,0),(0,3),(0,4),(3,5),(4,6),(3,7),(4,8),
    (5,9),(5,10),(6,11),(6,12)]
  let ligands := (List.range 6).flatMap fun k => [(7+k,13+2*k),(7+k,14+2*k)]
  {atoms := elements.map AtomSpec.aliphatic, bonds := (core ++ ligands).map fun (a,b) => ⟨a,b,.single⟩}

private def point (n : Nat) : CartesianPoint3 :=
  let t : ℚ := n
  ⟨t,t*t/4,t*t*t/16⟩

private def geometry (inverted : List Nat) : SpatialConfiguration := ⟨(List.range 25).map fun n =>
  let p := point n
  let k := (n-14)/2
  if n ≥ 14 && n%2 == 0 && inverted.contains k then
    let c := point (7+k)
    ⟨2*c.x-p.x,2*c.y-p.y,2*c.z-p.z⟩
  else p⟩

private def run (inverted : List Nat) (original mirror : Verdict) (mixed := false) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? (molecule mixed) (geometry inverted) | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "geometry")
  let some root := (RingGroupedReport.centres i).find? (fun a => a.val == 0) | throw (IO.userError "root")
  let some fr := RingNestedActivePair.frame? i (RingGroupedReport.origin i root) | throw (IO.userError "frame")
  let slot (n : Nat) := (List.finRange 4).find? fun s => RingGroupedTrials.atom fr s == n
  let some l := slot 3 | throw (IO.userError "left boron")
  let some q := slot 4 | throw (IO.userError "right boron")
  let rows := RingSparseTwinReport.sparse i root 0
  let r := RingSphereQueue.reader root (RingSphereQueue.viewOf rows)
  for rev in [false,true] do
    let expected := if rev then mirror else original
    let counted := RingCountedPathVerdict.pair? fr r rev none l q
    unless counted == some expected do throw (IO.userError s!"unexpected interval verdict {repr counted}")
    if mixed then
      for slot in [l,q] do
        if (profile? i r rev (RingGroupedCentre.cursor fr slot)).isSome then
          throw (IO.userError "the one-group-per-sphere test admitted unequal path priorities")
      IO.println s!"mixed chlorine/bromine tips {inverted}, reflected {rev}, {repr expected}"
    else
      let some a := profile? i r rev (RingGroupedCentre.cursor fr l) | throw (IO.userError "left profile")
      let some b := profile? i r rev (RingGroupedCentre.cursor fr q) | throw (IO.userError "right profile")
      let counts (tips : List Nat) :=
        let nr := (tips.filter fun k => inverted.contains k != rev).length
        (nr,tips.length-nr)
      let active (xs : List (Nat × Nat)) := xs.filter (· != (0,0))
      for (side,near,far) in [(a,[0],[2,3]),(b,[1],[4,5])] do
        let want := [counts near,counts far]
        unless active side.fourB == want && active side.five == want do
          throw (IO.userError s!"tips {inverted}, reflected {rev}: got {active side.fourB}, expected {want}")
      unless outcome a b [] [] == expected do throw (IO.userError s!"unexpected layered result for {inverted}")
      IO.println s!"tips {inverted}, reflected {rev}, layers {active a.fourB} versus {active b.fourB}, {repr expected}"
    (← IO.getStdout).flush

def main : IO Unit := do
  run [0] (.right .rule4b) (.right .rule4b)
  run [0,4,5] (.left .rule5) (.right .rule5)
  run [2,4] .tie .tie
  -- On each arm the near phosphorus is R and the far phosphorus pair is R/S.
  -- Only the left arm puts R on the higher-ranked bromine-bearing path.
  run [0,1,2,5] (.left .rule4b) (.left .rule4b) true
