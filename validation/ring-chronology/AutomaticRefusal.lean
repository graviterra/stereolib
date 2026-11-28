import TetraStereo.Engine.RingAutomaticRefusal
import TetraStereo.Examples.RingPhosphaneOxiraneReport

/-! Automatic exchange discovery on small, hydrogen-complete ring inputs. All
fixture atom IDs are zero-based. -/
open TetraStereo.OneCenter TetraStereo.Engine
open RingHydrogenSpelling.PhosphaneOxirane

private def raw (elements : List Element) (bonds : List (Nat × Nat)) : RawMolecule :=
  { atoms := elements.map AtomSpec.aliphatic, bonds := bonds.map fun (a,b) => ⟨a,b,.single⟩ }

private def points (n : Nat) : SpatialConfiguration := ⟨(List.range n).map fun j =>
  let x : ℚ := j
  ⟨x,x*x,x*x*x⟩⟩

private def inspect (m : RawMolecule) (g : SpatialConfiguration) (expected : Bool)
    (markedOnly : Option Bool := none) (compareUnmarked : Option (Nat × Nat × Bool) := none) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "raw admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "geometry")
  let some a := (RingGroupedReport.centres i).find? (fun v => v.val == 0) | throw (IO.userError "root")
  let f := RingGroupedReport.origin i a
  let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "frame")
  -- The root reads the completed public store. Materialize it once for all comparisons.
  let rows := RingSphereStore.rows i a (RingActiveDistanceSchedule.height i + 1)
  let read := RingSphereQueue.reader a (RingSphereQueue.viewOf rows)
  unless RingAutomaticRefusal.select f read == expected do
    throw (IO.userError s!"unexpected decision for {m.atoms.length}-atom fixture, expected {expected}")
  if let some value := markedOnly then
    unless RingObservedTreeMatch.check fr read == value do throw (IO.userError "marked comparison")
  if let some (left,right,value) := compareUnmarked then
    let slot (id : Nat) := (List.finRange 4).find? fun s => RingGroupedTrials.atom fr s == id
    let some u := slot left | throw (IO.userError "left ligand")
    let some v := slot right | throw (IO.userError "right ligand")
    unless (RingObservedTreeMatch.unmarked? fr read u v).isSome == value do
      throw (IO.userError "unmarked comparison")

private def cyclopropane : IO Unit := do
  let m := raw [.C,.C,.C,.F,.Br,.H,.H,.H,.H]
    [(0,1),(0,2),(1,2),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)]
  let g := points 9
  inspect m g true (some false) (some (1,2,true))
  unless RingAutomaticRefusal.fromRaw? m g [0,0] == some [(0,none),(0,none)] do
    throw (IO.userError "tied cyclopropane")
  let labelled := {m with atoms := m.atoms.set 1 {AtomSpec.aliphatic .C with isotope? := some 13}}
  inspect labelled g false none (some (1,2,false))
  -- Priority Br, F, carbon-13, carbon-12 has oriented determinant +12.
  unless RingAutomaticRefusal.fromRaw? labelled g [0] == some [(0,some (.chiral .S,.chiral .R))] do
    throw (IO.userError "isotope stereocenter")
  IO.println "Cyclopropane: sole-pair certificate; one carbon-13 substitution restores S and reflected R."

private def spiro : IO Unit := do
  let m := raw [.C,.O,.O,.S,.S] [(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]
  inspect m (points 5) true (some true)
  IO.println "Spiro: discovered all four marked matches without atom renamings."

private def grouped : IO Unit := do
  -- All four flat shells agree, including the duplicate in shell three.
  -- On the left one boron carries both fluorines; on the right each carries one.
  let m := raw [.C,.C,.C,.F,.Cl,.B,.B,.B,.B,.F,.F,.H,.H,.F,.H,.F,.H]
    [(0,1),(0,2),(1,2),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8),(5,9),(5,10),
     (6,11),(6,12),(7,13),(7,14),(8,15),(8,16)]
  let g := points 17
  inspect m g false none (some (1,2,false))
  let some [(0,some (.chiral a,.chiral b))] := RingAutomaticRefusal.fromRaw? m g [0] |
    throw (IO.userError "grouped branches require uppercase assignment")
  unless b == a.swap do throw (IO.userError "reflected hand")
  IO.println s!"Same flat shells, different parents: {repr a} and {repr b}."

theorem automatic_phosphane_report (x : SpatialConfiguration) (ids : List Nat) :
    RingAutomaticRefusal.fromRaw? molecule x ids = expectedReport x ids :=
  (congrFun (congrFun (congrFun RingAutomaticRefusal.raw_exact molecule) x) ids).trans (public_exact x ids)

assert_kernel_only automatic_phosphane_report

private def phosphane : IO Unit := do
  for (other,same) in [(RS.R,true),(RS.S,false)] do
    let g := Representatives.representative .S (some .R) (some other)
    inspect molecule g same none (some (1,2,same))
    let expected : Option RingGroupedReport.Report := some [(0,labels .S (some .R) (some other) 0)]
    unless RingAutomaticRefusal.fromRaw? molecule g [0] == expected do throw (IO.userError "phosphane hands")
  IO.println "Same phosphorus hands: certified refusal. Opposite hands: lowercase s, including on reflection."

def main (args : List String) : IO Unit := do
  for (name,run) in [("cyclopropane",cyclopropane),("spiro",spiro),("grouped",grouped),("phosphane",phosphane)] do
    if args.isEmpty || args.contains name then
      run
      (← IO.getStdout).flush
