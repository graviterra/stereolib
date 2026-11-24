import TetraStereo.Engine.PublicAPI
import TetraStereo.Engine.RingZeroDuplicateMass

open TetraStereo.OneCenter TetraStereo.Engine
open RingRetainedChemicalPreorder (directions keyFor)
open RingMassDifference (entry?)

/-- The public reader uses the full molecular carrier. -/
example {i : LocalizedChemicalRing.Input} {f a b : RingActivePairs.Site i} {order : Ordering}
    (strict : order ≠ .eq) (hit : ringRetainedChemicalComparison? i f a b =
      some [⟨.atomicNumber,.eq⟩,⟨.duplicateAtom,.eq⟩,⟨.isotopeMass,order⟩]) :=
  RingMassDifference.comparison_first_mass_real strict hit

example (i : LocalizedChemicalRing.Input) (f a b : RingActivePairs.Site i) :
    RingZeroDuplicateMass.compareAt? i f a b =
      (ringRetainedChemicalComparison? i f a b).map cipTraceOutcome :=
  RingZeroDuplicateMass.compareAt_agrees i f a b

/-- At carbon 0 the two ring arms begin with carbon. Replacing one hydrogen
on carbon 1 with deuterium distinguishes the arms below their roots. -/
private def molecule (label labelRoot : Bool) : RawMolecule :=
  let atoms := ([.C,.C,.C,.H,.H,.H,.H,.H,.H] : List Element).map AtomSpec.aliphatic
  let atoms := if labelRoot then atoms.set 0 { AtomSpec.aliphatic .C with isotope? := some 13 } else atoms
  { atoms := if label then atoms.set 5 { AtomSpec.aliphatic .H with isotope? := some 2 } else atoms
    bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)] :
      List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩ }

private def check (label labelRoot : Bool) : IO Unit := do
  let geometry : SpatialConfiguration := ⟨(List.range 9).map fun n =>
    let t : ℚ := n
    ⟨t,t*t,t*t*t⟩⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? (molecule label labelRoot) geometry
    | throw (IO.userError "cyclopropane admission failed")
  let some root := (RingGroupedReport.centres i).find? (fun a => a.val == 0)
    | throw (IO.userError "carbon 0 missing")
  let f := RingGroupedReport.origin i root
  let arm (n : Nat) := (directions i f).find? fun a => (a.val.val.node.current?.map Fin.val) == some n
  let some a := arm 1 | throw (IO.userError "carbon 1 missing")
  let some b := arm 2 | throw (IO.userError "carbon 2 missing")
  let trace (s : Ordering) : Option (List CIPRuleDecision) :=
    some [⟨.atomicNumber,.eq⟩,⟨.duplicateAtom,.eq⟩,⟨.isotopeMass,s⟩]
  unless ringRetainedChemicalComparison? i f a.val b.val == trace (if label then .gt else .eq) &&
      ringRetainedChemicalComparison? i f b.val a.val == trace (if label then .lt else .eq) do
    throw (IO.userError "unexpected public trace")
  for x in directions i f do
    for y in directions i f do
      let expected := (ringRetainedChemicalComparison? i f x.val y.val).map cipTraceOutcome
      unless RingZeroDuplicateMass.compareAt? i f x.val y.val == expected do
        throw (IO.userError "rebuilding the arm priorities changed a public comparison")
  let xs := [b,a,b] ++ directions i f
  for deep in [false,true] do
    for breakTies in [false,true] do
      let later (x y : RingRetainedChemicalPreorder.Direction i f) :=
        if breakTies then compare x.val.val.node.history y.val.val.node.history else .eq
      let sorted := RingZeroDuplicateMass.rankedDirections
      unless sorted RingZeroDuplicateMass.rebuiltFor deep later xs == sorted keyFor deep later xs do
        throw (IO.userError "rebuilding changed the order of actual occurrences")
  if labelRoot then
    let ordinary := CIPRule2MassData.rule2MassPico? 6 none
    let flag := RingRetainedChemicalTrace.duplicateValue i.molecule.atomCount (some 0)
    for direction in [a,b] do
      let armKey := keyFor direction
      let some rebuilt := RingZeroDuplicateMass.rebuiltKey? i ⟨direction.val,some f⟩
        | throw (IO.userError "missing rebuilt arm")
      unless rebuilt.atomic == armKey.atomic && rebuilt.duplicate == armKey.duplicate &&
          rebuilt.mass.word != armKey.mass.word do
        throw (IO.userError "expected a change confined to the mass word")
      let q : RingActivePairs.Arm i := ⟨direction.val,some f⟩
      let labels : RingNestedActivePair.Reader i := fun _ => some none
      let some fresh := RingRebuiltStereo.arm? i labels 1 q | throw (IO.userError "rebuilt stereo arm missing")
      let some old := RingGroupedMark.arm? i labels 1 q | throw (IO.userError "grouped stereo arm missing")
      for stage in ([.unit,.localPair .R,.localPair .S,.lower,.fixedPair .R,.fixedPair .S,.marked] :
          List RingRebuiltStereo.Stage) do
        let x := stage.branch fresh
        let y := stage.branch old
        unless x.priorDeep[2]? == some rebuilt.mass.word && y.priorDeep[2]? == some armKey.mass.word &&
            x.word == y.word do throw (IO.userError "a stereo stage inherited the wrong mass or produced a different word")
      unless fresh.2.word.flatten.contains 1 do throw (IO.userError "the marked word lost the promoted atom")
      let mut seen := false
      for (row,r) in armKey.duplicate.word.zipIdx do
        for (priority,c) in row.zipIdx do
          if priority == flag then
            seen := true
            unless entry? armKey.atomic.word r c == some 6 && entry? armKey.mass.word r c == ordinary &&
                entry? rebuilt.mass.word r c == some 0 do
              throw (IO.userError "closure of the carbon-13 root has the wrong element or mass")
      unless seen && ordinary.isSome && ordinary != CIPRule2MassData.rule2MassPico? 6 (some 13) do
        throw (IO.userError "missing isotope-sensitive closure control")
    IO.println "Both closures of the carbon-13 root changed from ordinary carbon mass to zero. All seven stereo priorities inherited the new mass word and retained their observations."
  if label then
    let x := keyFor a
    let y := keyFor b
    let first := (x.mass.word.zip y.mass.word).zipIdx.findSome? fun ((l,k),r) =>
      (l.zip k).zipIdx.findSome? fun ((u,v),c) => if u != v then some (r,c,u,v) else none
    let some (r,c,u,v) := first | throw (IO.userError "missing first mass difference")
    unless r > 0 && entry? x.atomic.word r c == some 1 && entry? y.atomic.word r c == some 1 &&
        entry? x.duplicate.word r c == some 0 && entry? y.duplicate.word r c == some 0 &&
        CIPRule2MassData.rule2MassPico? 1 (some 2) == some u &&
        CIPRule2MassData.rule2MassPico? 1 none == some v do
      throw (IO.userError s!"unexpected entries at row {r}, column {c}")
    IO.println s!"Deuterated cyclopropane: row {r}, column {c}, mass entries {u} and {v}; reversed arms reverse priority."
  else
    IO.println "With no deuterium in either arm, all three rules tie in both directions."

def main : IO Unit := do
  check false false
  check true false
  check false true
  check true true
