import TetraStereo.Engine.RingOccurrenceStereo
import TetraStereo.Engine.RingRebuiltStereo
import TetraStereo.Examples.RankedRingReference
import TetraStereo.Examples.RingPairedAuxiliary

open TetraStereo TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Examples
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader Labels)
open RingRetainedStereoDecision (Result Rule)

/-- The same original-root sphere queue used for the recursive report. Limit
the inventory to real auxiliary centres before traversing distances. -/
private def inspectRoot (i : LocalizedChemicalRing.Input) (left right : Nat)
    (check : (f a b : Site i) → Reader i → IO Unit) (known : Option (Reader i) := none) : IO Unit := do
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission failed")
  let sites := (RingActiveDistanceSchedule.sites i).filter fun q => q.val.root.val == 0
  let get (path : List Nat) : IO (Site i) := do
    let some q := sites.find? (fun q => q.val.node.history.map Fin.val == path &&
        q.val.node.provenance == .realAtom) | throw (IO.userError s!"missing occurrence {path}")
    return q
  let f ← get [0]
  let a ← get [left,0]
  let b ← get [right,0]
  if let some read := known then return ← check f a b read
  let root := f.val.root
  let inventory := sites.filter fun q => decide (RingSphereQueue.candidate root q)
  let queue := fun d => inventory.filter fun q => RingActiveDistanceSchedule.distance q == d
  IO.println s!"Computing {inventory.length} auxiliary occurrences for {i.molecule.atomCount} atoms"
  (← IO.getStdout).flush
  let top := RingActiveDistanceSchedule.height i
  let rows := RingSphereQueue.stored (RingRebuiltStereo.publish i) root queue top (top+1)
  unless rows.length == inventory.length do throw (IO.userError "incomplete auxiliary table")
  IO.println s!"Materialized {rows.length} auxiliary cells"
  (← IO.getStdout).flush
  check f a b (RingSphereQueue.reader root (RingSphereQueue.viewOf rows))

private def expect (i : LocalizedChemicalRing.Input) (f a b : Site i) (r : Reader i)
    (rule : Option Rule) (x y : Int) : IO Unit := do
  for (u,v,p,q) in [(a,b,x,y),(b,a,-x,-y)] do
    let wanted : Result × Result := (⟨rule,p⟩,⟨rule,q⟩)
    let got := RingOccurrenceStereo.comparison? i f u v r
    unless got == some wanted do throw (IO.userError s!"expected {repr wanted}, got {repr got}")
    let rebuilt := RingRebuiltStereo.comparison? i f u v r
    unless rebuilt == some wanted do throw (IO.userError s!"expected rebuilt scores {repr wanted}, got {repr rebuilt}")
    unless RingOccurrenceStereo.incidentScore? i f u v r == some (p,q) do
      throw (IO.userError "zero-mass comparison and casing score differ")

private def small (control : Bool) : IO Unit := do
  let i := RingPairedAuxiliary.input control
  inspectRoot i 3 5 fun f a b r => do
    if control then expect i f a b r (some .likePair) (-1) (-1)
    else expect i f a b r (some .fixedPair) 2 (-2)
    IO.println "Coordinate-derived signs passed"
    (← IO.getStdout).flush
    let marked (left right : Option Labels) : Reader i := fun q =>
      some (if q == a then left else if q == b then right else none)
    expect i f a b (marked (some (.chiral .R,.chiral .S)) none) (some .unit) 1 1
    expect i f a b (marked (some (.pseudoasymmetric .r,.pseudoasymmetric .r))
      (some (.pseudoasymmetric .s,.pseudoasymmetric .s))) (some .lower) 1 1
    expect i f a b (marked none none) none 0 0
    IO.println s!"17 atoms, coordinate control {control}, both ligand directions passed"

/-- Independent address-by-address publications from the earlier geometry
certificate for this fixture, including both pseudoasymmetric arm roots. -/
private def certifiedStore (i : LocalizedChemicalRing.Input)
    (g : LocalizedGenericMarkedRecalculation.Geometry) : IO (Reader i) := do
  let m := RankedRingReference.molecule
  let mut cells : List (List Nat × Labels) := []
  for endpoint in [3,26] do
    let some start := RingChemicalPriority.occurrence? m [0,endpoint] | throw (IO.userError "missing arm")
    let some paths := RingChemicalPriority.carbonSites m (m.atomCount+1) start | throw (IO.userError "incomplete arm")
    for path in paths do
      let some v := RingChemicalPriority.Recursive.derive m g RankedRingReference.hints (fun _ => 1) 2 path
        | throw (IO.userError s!"independent auxiliary certificate failed at {path}")
      let some x := v.val.label | throw (IO.userError "original label missing")
      let some y := v.val.reverse.label | throw (IO.userError "reflected label missing")
      cells := (path.reverse,(x,y)) :: cells
  let table := cells
  return fun q => if q.val.root.val != 0 then none else
    some (if q.val.node.provenance == .realAtom then table.lookup (q.val.node.history.map Fin.val) else none)

private def dual (mirroredArm : Bool) : IO Unit := do
  let g := if mirroredArm then RankedRingReference.enantiomorphicGeometry else RankedRingReference.geometry
  let m := RankedRingReference.molecule
  let some positions := (List.range m.atomCount).mapM g | throw (IO.userError "geometry incomplete")
  let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨positions⟩ | throw (IO.userError "49-atom admission failed")
  let known ← certifiedStore i g
  inspectRoot i 3 26 (fun f a b r => do
    let profiles ← [a,b].mapM fun q => do
      let some e := RingRebuiltStereo.arm? i r 0 ⟨q,some f⟩ | throw (IO.userError "missing rebuilt reference arm")
      return e.1
    for rev in [false,true] do
      let arm (q : Site i) : Arm i := ⟨q,some f⟩
      for q in [a,b] do
        let seeds := RingOccurrenceStereo.seeds? i r rev (arm q)
        unless seeds == some [.R,.S] do throw (IO.userError s!"expected two references, got {repr seeds}")
      let words := [a,b].flatMap fun q => [RS.R,.S].map fun s =>
        (RingOccurrenceStereo.pairs? i r rev false s (arm q)).map (List.map Bool.toNat)
      let ar := [1,0,0,1]
      let as_ := [1,0,1,0]
      let br := if mirroredArm then as_ else [1,0,1,1]
      let bs := if mirroredArm then ar else [1,0,0,0]
      let expected := (if rev then [as_,ar,bs,br] else [ar,as_,br,bs]).map some
      IO.println s!"49 atoms, mirrored arm {mirroredArm}, reflected reading {rev}, R/S lists {repr words}"
      (← IO.getStdout).flush
      unless words == expected do throw (IO.userError s!"expected {repr expected}")
      let rebuiltWords := profiles.flatMap fun p =>
        let p := if rev then p.reflect else p
        [RS.R,.S].map fun s => some ((RingRetainedStereoDecision.accepted p.unit (p.localPair s)).map Bool.toNat)
      unless rebuiltWords == expected &&
          profiles.all (fun p => RingRetainedReferenceGroup.references p.hits rev == [.R,.S]) do
        throw (IO.userError s!"rebuilt references or words differ: {repr rebuiltWords}")
    let result := RingOccurrenceStereo.comparison? i f a b r
    IO.println s!"49 atoms, first deciding rules and scores {repr result}"
    (← IO.getStdout).flush
    let expected : Result × Result := if mirroredArm then (⟨some .fixedPair,-2⟩,⟨some .fixedPair,2⟩)
      else (⟨some .likePair,-1⟩,⟨some .likePair,-1⟩)
    unless result == some expected && RingRebuiltStereo.comparison? i f a b r == some expected do throw (IO.userError s!"expected {repr expected}")) (some known)

def main (args : List String) : IO Unit := do
  unless args == [] || args == ["--small"] || args == ["--dual"] do
    throw (IO.userError "expected --small, --dual, or no arguments")
  if args == [] || args == ["--small"] then for control in [false,true] do small control
  unless args == ["--small"] do for mirroredArm in [false,true] do dual mirroredArm
