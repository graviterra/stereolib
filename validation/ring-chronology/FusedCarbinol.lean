import TetraStereo.Engine.PublicAPI
import TetraStereo.Engine.RingRootIndexedEarly
import TetraStereo.Examples.FusedCarbinolArms

/-! Synthetic carbinol with two octahydroinden-4-yl ligands differing at C7a.
Both copies use the atom order C4,C5,C6,C7,C7a,C1,C2,C3,C3a.
The points start on the moment curve (t,t²,t³). When a specified local orientation
requires reversal, its terminal hydrogen is inverted about the midpoint of the
first two frame vertices. Seven independent oriented-volume checks pin the model
to the supplied stereoframes. Coordinates encode parity only. -/
open TetraStereo.OneCenter TetraStereo.Engine

open TetraStereo.Examples.FusedCarbinolArms (molecule)

private def points : List CartesianPoint3 := [
    ⟨0,0,0⟩, ⟨1,1,1⟩, ⟨2,4,8⟩, ⟨3,9,27⟩,
    ⟨4,16,64⟩, ⟨5,25,125⟩, ⟨6,36,216⟩, ⟨7,49,343⟩,
    ⟨8,64,512⟩, ⟨9,81,729⟩, ⟨10,100,1000⟩, ⟨11,121,1331⟩,
    ⟨12,144,1728⟩, ⟨13,169,2197⟩, ⟨14,196,2744⟩, ⟨15,225,3375⟩,
    ⟨16,256,4096⟩, ⟨17,289,4913⟩, ⟨18,324,5832⟩, ⟨19,361,6859⟩,
    ⟨-17,-395,-7991⟩, ⟨21,441,9261⟩, ⟨22,484,10648⟩, ⟨23,529,12167⟩,
    ⟨24,576,13824⟩, ⟨25,625,15625⟩, ⟨26,676,17576⟩, ⟨27,729,19683⟩,
    ⟨28,784,21952⟩, ⟨29,841,24389⟩, ⟨30,900,27000⟩, ⟨31,961,29791⟩,
    ⟨32,1024,32768⟩, ⟨33,1089,35937⟩, ⟨34,1156,39304⟩, ⟨35,1225,42875⟩,
    ⟨36,1296,46656⟩, ⟨37,1369,50653⟩, ⟨38,1444,54872⟩, ⟨39,1521,59319⟩,
    ⟨40,1600,64000⟩, ⟨41,1681,68921⟩, ⟨42,1764,74088⟩, ⟨43,1849,79507⟩,
    ⟨-11,-1379,-75581⟩, ⟨45,2025,91125⟩, ⟨46,2116,97336⟩, ⟨47,2209,103823⟩,
    ⟨48,2304,110592⟩, ⟨49,2401,117649⟩, ⟨50,2500,125000⟩, ⟨51,2601,132651⟩]

private def frames : List (RS × Nat × Nat × Nat × Nat) := [
    (.S,1,2,11,20), (.S,0,10,3,22), (.S,5,10,7,29),
    (.R,9,2,6,36), (.S,0,19,12,37), (.R,14,19,16,44),
    (.R,18,11,15,51)]

private theorem indexed_public : RingRootIndexedEarly.sparseFromRaw? = ringMolecularReportFromRaw? :=
  RingRootIndexedEarly.sparse_raw_exact
assert_kernel_only indexed_public

private theorem sparse_public : RingSparseTwinReport.fromRaw? = ringMolecularReportFromRaw? :=
  RingSparseTwinReport.raw_exact
assert_kernel_only sparse_public

def main (args : List String) : IO Unit := do
  let evaluate ← match args with
    | [] | ["--indexed"] | ["--aux-only"] => pure RingRootIndexedEarly.sparseFromRaw?
    | ["--sparse"] => pure RingSparseTwinReport.fromRaw?
    | ["--direct"] => pure ringMolecularReportFromRaw?
    | _ => throw (IO.userError "usage: --indexed | --sparse | --direct | --aux-only")
  for mirror in [false,true] do
    let ps := if mirror then points.map CartesianPoint3.reflectX else points
    let point (i : Nat) : IO CartesianPoint3 := do
      let some p := ps[i]? | throw (IO.userError "frame index outside molecule")
      return p
    for (h,a,b,c,d) in frames do
      let v := CartesianPoint3.orientedVolume (← point a) (← point b) (← point c) (← point d)
      let actual := if mirror then h.swap else h
      unless (if actual == .R then v < 0 else v > 0) do throw (IO.userError "incorrect frame hand")
    let some i := LocalizedChemicalRing.admitRawSpatial? molecule ⟨ps⟩ | throw (IO.userError "structural admission")
    unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "geometry admission")
    IO.println s!"reflected={mirror}, all seven input frames and coordinate admission checked"
    (← IO.getStdout).flush
    let some root := (List.finRange i.certified.certified.input.molecule.atomCount)[0]?
      | throw (IO.userError "missing carbinol")
    let sphere := (RingSparseTwinReport.layers i root).getD 3 []
    for (path,expected) in [([0,2,10,6], RS.R), ([0,11,19,15], RS.S)] do
      let some q := sphere.find? (fun q => q.val.node.history.reverse.map Fin.val == path)
        | throw (IO.userError s!"missing C7a occurrence {path}")
      let native := (RingRootIndexedEarly.early? i q).map RingGeometryCriterion.Signature.letters
      let alternative := (RingRootIndexedEarly.activeEarly? i q).map RingGeometryCriterion.Signature.letters
      let h := if mirror then expected.swap else expected
      IO.println s!"path={path}, construction {repr native}, focus {repr alternative}"
      (← IO.getStdout).flush
      unless native == some (some (.chiral h,.chiral h.swap)) &&
          alternative == some (some (.chiral h.swap,.chiral h)) do
        throw (IO.userError "C7a prediction differs from a constitutional result")
    if args == ["--aux-only"] then continue
    let rows := evaluate molecule ⟨ps⟩ [0]
    IO.println s!"reflected={mirror}, public carbinol {repr rows}"
    (← IO.getStdout).flush
    let h : RS := if mirror then .S else .R
    unless rows == some [(0,some (.chiral h,.chiral h.swap))] do
      throw (IO.userError "source-root prediction differs from public raw report")
