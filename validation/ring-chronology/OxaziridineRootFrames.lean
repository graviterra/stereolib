import TetraStereo.Engine.RingSparseTwinReport
import TetraStereo.Engine.RingMetricChoiceRobustness
import TetraStereo.Engine.RingRootIndexedEarly
open TetraStereo.OneCenter TetraStereo.Engine
open CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)

/-! Exact signed frames on the hydrogen-completed two-arm graph used by
CentresOxaziridineRoot. The second arm is a proper half-turn of the first
about the z axis. Coordinates are synthetic. -/

private def molecule : RawMolecule := {
  atoms := (([.C,.H,.F] : List Element) ++ List.flatten (List.replicate 2
    [Element.N,.O,.C,.C,.C,.C])).map AtomSpec.aliphatic
  bonds := ([(0,1),(0,2)] ++ [3,9].flatMap (fun base =>
    [(0,base+3)] ++ [(0,1),(1,2),(2,0),(0,3),(3,4),(4,5),(5,2)].map
      (fun (a,b) => (base+a,base+b)))).map fun (a,b) => ⟨a,b,.single⟩ }

private def geom : SpatialConfiguration :=
  let arm := (List.range 6).map (fun k =>
    let t : ℚ := k + 2
    (⟨t,t*t,t*t*t⟩ : CartesianPoint3))
  ⟨[⟨0,0,0⟩,⟨2,1,0⟩,⟨0,0,1⟩] ++ arm ++ arm.map (fun p => ⟨-p.x,-p.y,p.z⟩)⟩

private def checkFrames (m : RawMolecule) (g : SpatialConfiguration) : IO Unit := do
  let mut frameMask := 0
  let mut j := 0
  for center in [0,3,5,6,9,11,12] do
    let off := if center < 9 then 3 else 9
    let ids ← if center == 0 then pure [1,2,6,12] else if center == off then pure [off+1,off+2,off+3,off] else do
      let some h := (RingAtomicNeighborOrder.neighbors m center).find? (fun v => RingAtomicNeighborOrder.atomicNumber m v == 1)
        | throw (IO.userError "hydrogen missing at tertiary CH")
      pure (if center == off+2 then [off+1,off,off+5,h] else [off,off+4,0,h])
    let some hand := (ids.mapM (g.positions[·]?)).bind descriptorOfPriorityOrderedPoints? | throw (IO.userError s!"flat {center}")
    IO.println s!"frame {center} {ids} {repr hand}"
    if hand == .S then frameMask := frameMask + 2^j
    j := j+1
  unless frameMask == 91 && m.atomCount == 27 do
    throw (IO.userError s!"unexpected admitted frame inventory: {m.atomCount} atoms, mask {frameMask}")
  IO.println s!"admitted {m.atomCount} atoms, frame mask {frameMask}"

/-- These two physical carbons are the ring carbon and external alkyl carbon
in each arm. Both must have been visited without being the incoming parent. -/
private def switched (i : Input) (q : Site i) (mode : String) : Bool := Id.run do
  let some a := q.val.node.current? | return false
  if !(a.val == 3 && (mode == "left" || mode == "both") ||
       a.val == 9 && (mode == "right" || mode == "both")) then return false
  let history := q.val.node.history.map Fin.val
  let parent := q.val.node.parent?.map Fin.val
  return RingOxaziridineNitrogen.constrained i a &&
    [a.val+2,a.val+3].all (fun w => !RingPyramidalPathRank.realEndpoint history parent w)

/-- Test intervention only. A precondition checked on every retained row
ensures later auxiliary computations are independent of all earlier labels.
The ordinary root publisher receives the completed table. -/
private def intervention (i : Input) (a : i.certified.Atom) (mode : String) : IO Unit := do
  let base := RingSparseTwinReport.sparse i a 0
  let mut changes := 0
  let mut rows := []
  for (q,v) in base do
    unless RingSparseTwinReport.facts i q == some v do
      throw (IO.userError s!"auxiliary needs a prior table at {q.val.node.history.map Fin.val}")
    if switched i q mode then
      let some (some hands) := v | throw (IO.userError "target nitrogen unassigned")
      unless hands.1 != hands.2 do throw (IO.userError "target did not change")
      changes := changes + 1
      rows := (q,some (some hands.swap)) :: rows
    else
      rows := (q,v) :: rows
  unless changes == (if mode == "both" then 2 else 1) do throw (IO.userError "target count")
  let q := RingGroupedReport.origin i a
  let reader := RingSphereQueue.reader a (RingSphereQueue.viewOf rows.reverse)
  let result := RingSparseRefusalStore.guarded (RingSparseTwinReport.keep i)
    (RingSparseTwinReport.residual i) q reader
  IO.println s!"{mode}, switched {changes} nitrogen rows, public root evaluation {repr result}"
  let expected : RingActiveDistanceSchedule.Cell := match mode with
    | "left" => some (some (.chiral .S,.chiral .R))
    | "right" => some (some (.chiral .R,.chiral .S))
    | _ => some none
  unless result == expected do throw (IO.userError "unexpected intervention result")

open private indexedPublish indexedPublish_eq from TetraStereo.Engine.RingRootIndexedEarly

/-- Reuse the root-local constitutional index at every stock publication, even
on a store resulting from earlier switches. -/
private def indexedTrial (i : Input) (r : i.certified.Atom) (paths : List (List Nat)) :=
  let hybrid : RingActiveDistanceSchedule.Rule i := fun q =>
    if RingMetricChoiceRobustness.address q ∈ paths then RingOriginIndexedKeys.publish i q else indexedPublish i q
  indexedPublish i (RingGroupedReport.origin i r)
    (RingSphereQueue.reader r (RingSphereQueue.viewOf
      (RingRootLayerStore.rows i (RingPyramidalPublication.eligible i) hybrid r)))

private theorem indexedTrial_eq (i : Input) (r : i.certified.Atom) (paths : List (List Nat)) :
    indexedTrial i r paths = RingMetricChoiceRobustness.trialPaths i r paths := by
  simp only [indexedTrial,RingMetricChoiceRobustness.trialPaths,indexedPublish_eq]
assert_kernel_only indexedTrial_eq

/-- Switch Rule 1b itself at each chosen address and rerun the full schedule. -/
private def metricTrial (i : Input) (root : i.certified.Atom) (mode : String) : IO Unit := do
  let left := [0,6,7,8,5,4,3]
  let right := [0,12,13,14,11,10,9]
  let (paths,expected) : List (List Nat) × RingActiveDistanceSchedule.Cell := match mode with
    | "metric-left" => ([left],some (some (.chiral .S,.chiral .R)))
    | "metric-right" => ([right],some (some (.chiral .R,.chiral .S)))
    | "metric-both" => ([left,right],some none)
    | _ => ([],some none)
  let result := indexedTrial i root paths
  unless result == expected do throw (IO.userError s!"{mode}: {repr result}")
  IO.println s!"{mode} {paths} {repr result}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let some (m,g) := RingHydrogenCompletion.prepare? molecule geom | throw (IO.userError "prepare")
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "structural admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "geometry admission")
  checkFrames m g
  (← IO.getStdout).flush
  let some root := (List.finRange i.certified.certified.input.molecule.atomCount)[0]?
    | throw (IO.userError "missing root")
  for mode in args do
    if mode == "baseline" then
      let result := RingSparseTwinReport.fromRaw? molecule geom [0]
      IO.println s!"untouched public raw report {repr result}"
      unless result == some [(0,none)] do throw (IO.userError "unexpected raw report")
    else if mode == "left" || mode == "right" || mode == "both" then
      intervention i root mode
    else if ["metric-left","metric-right","metric-both","metric-neither"].contains mode then
      metricTrial i root mode
    else throw (IO.userError s!"unknown replay mode {mode}")
