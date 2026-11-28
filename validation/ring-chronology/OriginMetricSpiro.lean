import TetraStereo.Engine.RingMetricChoiceTable

/-! Final-descriptor counterexample for the two ring-duplicate distance
conventions. Jmol's independent replay reads the identical V2000 fixture.
Only the integral-coordinate, neutral C/O/H single bonds of this fixture
are decoded here. -/
open TetraStereo.OneCenter TetraStereo.Engine

private def text := include_str "OriginMetricSpiro.mol"

private def fields (line : String) := (line.splitOn " ").filter (· != "")

private def component? (s : String) : Option ℚ := do
  let [integer,"0000"] := s.splitOn "." | none
  return (← integer.toInt? : Int)

private def atom? (line : String) : Option (AtomSpec × CartesianPoint3) := do
  let x::y::z::symbol::attrs := fields line | none
  guard (attrs.all (· == "0"))
  let element ← match symbol with
    | "H" => some Element.H | "C" => some .C | "O" => some .O | _ => none
  return (AtomSpec.aliphatic element, ⟨← component? x, ← component? y, ← component? z⟩)

private def bond? (line : String) : Option (Nat × Nat) := do
  let a::b::"1"::flags := fields line | none
  guard (flags.all (· == "0"))
  let x ← a.toNat?
  let y ← b.toNat?
  guard (1 ≤ x && x ≤ 13 && 1 ≤ y && y ≤ 13)
  return (x-1,y-1)

private def input? : Option (RawMolecule × SpatialConfiguration) := do
  let lines := text.splitOn "\n"
  let counts ← lines[3]?
  guard ((fields counts).take 2 == ["13","16"] && lines[33]? == some "M  END")
  let points ← ((lines.drop 4).take 13).mapM atom?
  let edges ← ((lines.drop 17).take 16).mapM bond?
  let m : RawMolecule := {atoms := points.map Prod.fst, bonds := edges.map fun (x,y) => ⟨x,y,.single⟩}
  return (m,⟨points.map Prod.snd⟩)

private def check (m : RawMolecule) (g : SpatialConfiguration) (reflected : Bool) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "raw admission failed")
  unless LocalizedChemicalRing.coordinatesAdmitted i && (RingHydrogenCompletion.plan m).isEmpty do
    throw (IO.userError "expected admitted, hydrogen-complete geometry")
  let h := if reflected then RS.S else RS.R
  let native := RingHydrogenReport.fromRaw? m g [0]
  let active := RingOriginIndexedKeys.fromRaw? m g [0]
  unless native == some [(0,some (.chiral h,.chiral h.swap))] &&
      active == some [(0,some (.chiral h.swap,.chiral h))] do
    throw (IO.userError s!"unexpected root rows {repr native} and {repr active}")
  IO.println s!"reflected={reflected} public={repr h} active={repr h.swap}; mirror columns exchanged"

private def trace (i : LocalizedChemicalRing.Input) (r : i.certified.Atom) : IO Unit := do
  let count := RingActiveDistanceSchedule.height i + 1
  let original := RingSphereStore.rows i r count
  let alternate := RingOriginIndexedKeys.rows i r count
  unless original.map Prod.fst == alternate.map Prod.fst do throw (IO.userError "address mismatch")
  let expected : List (List Nat × RS) :=
    [([0,1,3],.S),([0,5,7],.R),([0,2,3,4,1],.S),([0,6,7,8,5],.S)]
  let mut found := []
  for ((q,a),(_,b)) in original.zip alternate do
    if a != b then
      let path := q.val.node.history.reverse.map Fin.val
      let some h := expected.lookup path | throw (IO.userError s!"unexpected changed address {path}")
      unless a == some (some (.chiral h,.chiral h.swap)) &&
          b == some (some (.chiral h.swap,.chiral h)) do throw (IO.userError "unexpected auxiliary hands")
      found := path :: found
      IO.println s!"changed auxiliary {path} from {repr h} to {repr h.swap}"
  unless found.length == expected.length && expected.all (fun x => found.contains x.1) do
    throw (IO.userError "missing changed occurrence")
  let site := RingGroupedReport.origin i r
  let some fr := RingNestedActivePair.frame? i site | throw (IO.userError "missing root frame")
  for (tag,rows) in [("public",original),("active",alternate)] do
    let read := RingSphereQueue.reader r (RingSphereQueue.viewOf rows)
    let arms := (List.finRange 4).map (RingGroupedCentre.cursor fr)
    let mut keys := []
    for arm in arms do
      let some id := arm.occurrence.val.node.current? | throw (IO.userError "missing adjacent atom")
      let some key := RingFullPathEligibility.key? i read false arm | throw (IO.userError "missing full key")
      keys := (id.val,key)::keys
    for (a,b) in [(1,5),(2,6)] do
      let some x := keys.lookup a | throw (IO.userError "missing first arm")
      let some y := keys.lookup b | throw (IO.userError "missing second arm")
      unless x.throughFourA == y.throughFourA do throw (IO.userError "earlier rules split matching arms")
      let cmp := compare x.bestFourB y.bestFourB
      let expectedDirection := if tag == "public" && a == 1 then Ordering.gt else Ordering.lt
      unless cmp == expectedDirection do throw (IO.userError "unexpected Rule 4b direction")
      IO.println s!"{tag} root arms {a}/{b} Rule 4b {repr cmp}"

/-- Recompute the entire store with one specified auxiliary occurrence switched.
Either length-three path reverses the root; either length-five path preserves it. -/
private def intervention (i : LocalizedChemicalRing.Input) (r : i.certified.Atom)
    (path : List Nat) (expected : RS) : IO Unit := do
  let actual := RingMetricChoiceRobustness.trialPaths i r [path]
  unless actual == some (some (.chiral expected,.chiral expected.swap)) do
    throw (IO.userError s!"unexpected single intervention {path}: {repr actual}")
  IO.println s!"active only at {path}: {repr actual}"

private def proposedPaths : List (List Nat) :=
  [[0,1,3],[0,5,7],[0,2,3,4,1],[0,6,7,8,5]]

private def support (i : LocalizedChemicalRing.Input) (r : i.certified.Atom) : IO Unit := do
  let sites := RingMetricChoiceRobustness.supportFromPaths r proposedPaths
  unless sites.length == 4 && (RingOriginCausal.inventory i r).length == 12 do
    throw (IO.userError "expected four proposed sites among twelve eligible occurrences")
  let stdout ← IO.getStdout
  for (chosen,certified) in RingMetricChoiceTable.table r sites do
    let paths := chosen.map RingMetricChoiceRobustness.address
    let mask := (proposedPaths.zipIdx.filter fun item => paths.contains item.1).foldl
      (fun value item => value + 2^item.2) 0
    let some cell := certified |
      throw (IO.userError s!"off-support changes at mask {mask} for {paths}")
    let expected := if paths.contains [0,1,3] || paths.contains [0,5,7] then RS.S else RS.R
    unless cell == some (some (.chiral expected,.chiral expected.swap)) do
      throw (IO.userError s!"unexpected root at mask {mask}: {repr cell}")
    stdout.putStrLn s!"mask {mask}: {repr cell}"
    stdout.flush
  IO.println "verified all 16 support subsets against arbitrary off-support choices"

def main (args : List String) : IO Unit := do
  let some (m,g) := input? | throw (IO.userError "invalid spiro fixture")
  match args with
  | ["trace"] =>
    let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "trace admission")
    let some r := (List.finRange i.certified.certified.input.molecule.atomCount)[0]? | throw (IO.userError "root")
    trace i r
  | ["support"] =>
    let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "support admission")
    let some r := (List.finRange i.certified.certified.input.molecule.atomCount)[0]? | throw (IO.userError "root")
    support i r
  | ["intervention",side] =>
    let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "intervention admission")
    let some r := (List.finRange i.certified.certified.input.molecule.atomCount)[0]? | throw (IO.userError "root")
    match side with
    | "left" => intervention i r [0,1,3] .S
    | "right" => intervention i r [0,5,7] .S
    | "deep-left" => intervention i r [0,2,3,4,1] .R
    | "deep-right" => intervention i r [0,6,7,8,5] .R
    | _ => throw (IO.userError "expected left, right, deep-left, or deep-right")
  | ["mirror"] => check m ⟨g.positions.map CartesianPoint3.reflectX⟩ true
  | [] => check m g false
  | _ => throw (IO.userError "expected no arguments, mirror, trace, support, or intervention with a path name")
