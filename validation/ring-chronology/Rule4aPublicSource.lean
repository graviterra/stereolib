import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.RingVerifiedAbsence

set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

open TetraStereo.OneCenter TetraStereo.Engine
namespace Rule4aPublicSource

/-- Literal source expectations: BlueBookRule4aSource.retained_at_three,
retained_at_five and source_assignment; RingVerifiedAbsence.parent_uses_absence.
No expected row is obtained by running a production ranking function. -/
def expected : RingGroupedReport.Report :=
  [(4,some (.chiral .S,.chiral .R)),
   (3,some (.pseudoasymmetric .s,.pseudoasymmetric .s)),(5,none)]

def audit (name : String) (m : RawMolecule) (points : List CartesianPoint3)
    (rootOnly : Bool := false) (snapshotsOnly : Bool := false) : IO Unit := do
  IO.eprintln s!"{name}: starting constitutional tie computation"
  IO.eprintln s!"{name}: constitutional C3/C5 = {repr ((RingChemicalPriority.IsotopePriority.compareIncident? m [4] 3 5).map (·.ordering))}"
  unless (RingChemicalPriority.IsotopePriority.compareIncident? m [4] 3 5).map (·.ordering) == some .eq do
    throw (IO.userError "source constitutional tie changed")
  let mut conforms := true
  for reflected in (if snapshotsOnly then [] else if rootOnly then [false] else [false,true]) do
    let ps := if reflected then points.map (fun p => {p with x := -p.x}) else points
    let wanted := if reflected then expected.map (fun (n,l) => (n,l.map Prod.swap)) else expected
    IO.eprintln s!"{name}: public mirror={reflected}, starting"
    let wanted := if rootOnly then wanted.take 1 else wanted
    let actual := ringMolecularReportFromRaw? m ⟨ps⟩ (if rootOnly then [4] else [4,3,5])
    IO.eprintln s!"{name}: public mirror={reflected}, actual={repr actual}, expected={repr wanted}"
    conforms := conforms && actual == some wanted

  if rootOnly then
    unless conforms do throw (IO.userError s!"{name}: public root mismatch")
    return
  let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨points⟩
    | throw (IO.userError s!"{name}: admission failed")
  unless LocalizedChemicalRing.coordinatesAdmitted i do
    throw (IO.userError s!"{name}: coordinates rejected")
  if bound : 4 < i.certified.certified.input.molecule.atomCount then
    let root : i.certified.Atom := ⟨4,bound⟩
    let queue := RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root
    let height := RingActiveDistanceSchedule.height i
    IO.eprintln s!"{name}: queue height {height}; computing actual publications"
    let rows := RingSphereQueue.stored (RingPyramidalPublication.publish i) root queue height height
    let mut seen := (0 : Nat)
    for (q,cell) in rows do
      let atom := q.val.node.current?.map Fin.val
      if q.val.address.length == 1 && (atom == some 3 || atom == some 5) then
        seen := seen + 1
        let wanted : RingActiveDistanceSchedule.Cell := if atom == some 3 then
          some (some (.pseudoasymmetric .s,.pseudoasymmetric .s)) else some none
        unless cell == wanted do
          throw (IO.userError s!"{name}: actual auxiliary C{repr atom}: {repr cell}, expected {repr wanted}")
      if [2,3,5,6,8,10].any (fun n => atom == some n) then
        -- Cell none is unresolved; some none is a completed refusal.
        IO.eprintln s!"{name}: history {repr (q.val.node.history.map Fin.val)}, distance {q.val.address.length}, cell {repr cell}"
    unless seen == 2 do throw (IO.userError s!"{name}: missing C3/C5 auxiliary occurrences")
    let rootCell := RingPyramidalPublication.publish i (RingGroupedReport.origin i root)
      (RingSphereQueue.reader root (RingSphereQueue.viewOf rows))
    IO.eprintln s!"{name}: actual root cell {repr rootCell}"
  else throw (IO.userError "root C4 out of range")
  unless conforms do throw (IO.userError s!"{name}: public source mismatch")

/-- P-92.5.1 P92510b PIN: (2R,3s,4S,6R), 5-[(1R)-1-chloroethyl],
3-[(1S)-1-chloroethyl], so C2/C6/C8/C10 are R/R/S/R.
Physical source frames independently ordered from the printed chloroethyl
ligands (Cl, central carbon, terminal carbon, H); C4 uses the source Rule4a
order O,C3,C5,H. This checks geometry without generating auxiliary labels. -/
def physical : IO Unit := do
  let ps := TetraStereo.Examples.BlueBookRule4aSource.positions
  for (atom,ids,wanted) in [
      (2,[12,3,1,29],RS.R),(6,[13,5,7,33],RS.R),
      (8,[14,3,9,34],RS.S),(10,[15,5,11,35],RS.R),
      (4,[0,3,5,31],RS.S)] do
    let points := ids.filterMap fun n => ps[n]?
    let actual := CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? points
    IO.eprintln s!"source frame C{atom}, order {repr ids}: {repr actual}, expected {repr wanted}"
    unless actual == some wanted do throw (IO.userError "source physical-frame mismatch")
  unless (RingChemicalPriority.IsotopePriority.compareIncident?
      TetraStereo.Examples.BlueBookRule4aSource.molecule [4] 3 5).map (·.ordering) == some .eq do
    throw (IO.userError "source C4 constitutional tie failed")
  IO.eprintln "Source physical frames and earlier constitutional tie passed."

end Rule4aPublicSource

def main (args : List String) : IO Unit := do
  if args == ["--physical"] then
    Rule4aPublicSource.physical
  else if args == ["--cyclic"] || args == ["--cyclic-root-only"] || args == ["--cyclic-snapshots-only"] then
    Rule4aPublicSource.audit "cyclic" TetraStereo.Examples.RingVerifiedAbsence.molecule
      ((List.range 32).filterMap TetraStereo.Examples.RingVerifiedAbsence.geometry)
      (args == ["--cyclic-root-only"]) (args == ["--cyclic-snapshots-only"])
  else
    Rule4aPublicSource.audit "acyclic" TetraStereo.Examples.BlueBookRule4aSource.molecule
      TetraStereo.Examples.BlueBookRule4aSource.positions (args != ["--full"] && args != ["--snapshots-only"])
      (args == ["--snapshots-only"])
