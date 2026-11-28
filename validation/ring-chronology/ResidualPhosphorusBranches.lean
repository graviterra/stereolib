import TetraStereo.Examples.ResidualPhosphorusCarrier
import TetraStereo.Engine.RingParentHandCounts
open TetraStereo.OneCenter TetraStereo.Engine
open RingResidualPairDecision (Classification)
open TetraStereo.Examples.ResidualPhosphorusCarrier (molecule unsignedCheck signedCheck matching?)

/-! Two boron arms each carry four phosphorus tips. Each pair of tips
shares a parent. The two balanced arms partition their hands differently. -/

private def point (n : Nat) : CartesianPoint3 :=
  let t : ℚ := n
  ⟨t,t*t/4,t*t*t/16⟩

private def geometry (flips : List Nat) : SpatialConfiguration := ⟨(List.range 33).map fun id =>
  let p := point id
  let k := (id-18)/2
  if 18 ≤ id && id%2 == 0 && flips.contains k then
    let c := point (9+k)
    ⟨2*c.x-p.x,2*c.y-p.y,2*c.z-p.z⟩
  else p⟩

/-- Counts on each pair of tips determine whether the two rooted binary
branches exchange. The total and its complement determine their ordinary CIP order. -/
private def predict (flips : List Nat) (rev : Bool) : Classification := Id.run do
  let counts (start : Nat) := [start,start+2].map fun k =>
    ([k,k+1].filter fun j => flips.contains j).length
  let l := counts 0
  let r := counts 4
  let nl := l.sum
  let nr := r.sum
  let strength (n : Nat) := max n (4-n)
  if strength nl ≠ strength nr then
    return if strength nl > strength nr then .noExchangeLeft .rule4b else .noExchangeRight .rule4b
  if nl ≠ nr then
    return if (if rev then nr > nl else nl > nr) then .noExchangeLeft .rule5 else .noExchangeRight .rule5
  return if l.mergeSort = r.mergeSort then .exchangeTie else .noExchangeTie

private def checkCase (flips : List Nat) (full := false) (exchangesOnly := false) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule (geometry flips)
    | throw (IO.userError "raw molecular admission failed")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinates")
  let some a := (RingGroupedReport.centres i).find? (fun a => a.val == 0) | throw (IO.userError "root")
  -- The compact store has the same lookup at every address (sparse_exact).
  let rows := RingSparseTwinReport.sparse i a 0
  let r := RingSphereQueue.reader a (RingSphereQueue.viewOf rows)
  for k in List.range 8 do
    let observed := rows.filterMap fun (q,cell) => do
      let atom ← q.val.node.current?
      guard (atom.val == 9+k)
      return cell
    let h : RS := if flips.contains k then .R else .S
    unless observed == [some (some (.chiral h,.chiral h.swap))] do
      throw (IO.userError s!"unexpected auxiliary row for phosphorus {9+k}")
  let code := flips.foldl (fun bits k => bits ||| (1 <<< k)) 0
  let mask : Fin 256 := ⟨code % 256,Nat.mod_lt _ (by decide)⟩
  unless signedCheck a r mask do throw (IO.userError s!"unexpected signed public reader for {flips}")
  unless (matching? mask).isSome == (predict flips false).exchanged do
    throw (IO.userError s!"unexpected exchange for {flips}")
  if exchangesOnly then return
  unless unsignedCheck a r do throw (IO.userError s!"unexpected unsigned public reader for {flips}")
  let f := RingGroupedReport.origin i a
  let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "root frame")
  let slot (id : Nat) := (List.finRange 4).find? (fun s => RingGroupedTrials.atom fr s == id)
  let some u := slot 3 | throw (IO.userError "left boron")
  let some v := slot 4 | throw (IO.userError "right boron")
  for (slot,first) in [(u,0),(v,4)] do
    let n := ((List.range 4).filter fun j => flips.contains (first+j)).length
    for rev in [false,true] do
      let nr := if rev then 4-n else n
      unless RingEqualPathHandCounts.armCheck i r rev (RingGroupedCentre.cursor fr slot) nr (4-nr) do
        throw (IO.userError s!"unequal priority paths at arm {first}, tips {flips}, reflected {rev}")

  if predict flips false == .noExchangeTie then
    let byParent (s : Fin 4) := RingParentHandCounts.counts r false .R 1 1 (RingGroupedCentre.cursor fr s)
    if (byParent u).mergeSort == (byParent v).mergeSort then
      throw (IO.userError s!"failed to exclude a hand-preserving exchange for {flips}")
  if !full then return
  let some [trial] := RingResidualPairDecision.diagnose? fr r | throw (IO.userError "trial count")
  unless trial.nomination == none do throw (IO.userError "expected the ordinary trial")
  for rev in [false,true] do
    let table := trial.table rev
    let result := RingResidualPairDecision.classify fr r none u v table[u.val][v.val]
    let expected := predict flips rev
    unless result == expected do
      throw (IO.userError s!"tips {flips}, reflected {rev}: got {repr result}, expected {repr expected}")
  let cell := RingFullPathPublication.publish? i f r
  let expectedCell : RingActiveDistanceSchedule.Cell := some (match predict flips false with
    | .noExchangeLeft .rule4b => some (.chiral .S,.chiral .R)
    | .noExchangeRight .rule4b => some (.chiral .R,.chiral .S)
    | .noExchangeLeft .rule5 => some (.pseudoasymmetric .s,.pseudoasymmetric .s)
    | .noExchangeRight .rule5 => some (.pseudoasymmetric .r,.pseudoasymmetric .r)
    | _ => none)
  unless cell == expectedCell do throw (IO.userError s!"unexpected root publication {repr cell}")
  IO.println s!"tips {flips}, original pair {repr (predict flips false)}, root {repr cell}"
  (← IO.getStdout).flush

private def sweep (start stop : Nat) (exchangesOnly := false) : IO Unit := do
  unless start < stop && stop ≤ 256 do throw (IO.userError "expected 0 ≤ start < stop ≤ 256")
  for mask in List.range' start (stop-start) do
    checkCase ((List.range 8).filter fun k => mask.testBit k) false exchangesOnly
    if (mask+1)%8 == 0 || mask+1 == stop then
      IO.println s!"verified masks {start} through {mask}"
      (← IO.getStdout).flush

private def checkTotals : IO Unit := do
  let classified := (List.range 256).flatMap fun mask =>
    let tips := (List.range 8).filter fun k => mask.testBit k
    [predict tips false,predict tips true]
  let total (stage : RingLigandFirstDifference.Stage) :=
    classified.count (.noExchangeLeft stage) + classified.count (.noExchangeRight stage)
  let totals := [total .rule4b,total .rule5,classified.count .exchangeTie,classified.count .noExchangeTie]
  unless totals == [304,68,108,32] do throw (IO.userError s!"unexpected classification totals {totals}")

def main (args : List String) : IO Unit := do
  checkTotals
  match args with
  | [] =>
    checkCase [2,3,5,7] true
    checkCase [2,3,5] true
    checkCase [0,1,2,4] true
  | ["--exchanges"] => sweep 0 256 true
  | ["--all"] => sweep 0 256
  | ["--all",lo,hi] =>
    let some start := lo.toNat? | throw (IO.userError "invalid first mask")
    let some stop := hi.toNat? | throw (IO.userError "invalid upper bound")
    sweep start stop
  | _ => throw (IO.userError "expected --all [start stop], --exchanges or no arguments")
