import TetraStereo.Engine.RingOriginOrderRawCheck

/-! Executable regression for two independently unwritten P/As hydrogen hands.
Connected ring P-O-As-S-P, with one omitted H on each P/As.
Every ordering of the four raw bonds is combined with independent reversals of
the two stored neighbor rows. No equality theorem supplies the computed results. -/
open TetraStereo.OneCenter TetraStereo.Engine
open RingHydrogenCompletion RingPyramidalChoices

private def bonds : List RawBond :=
  [(0,1),(1,2),(2,3),(3,0)].map fun (a,b) => ⟨a,b,.single⟩

private def molecule (bs : List RawBond) (reverseP reverseAs : Bool) : RawMolecule where
  atoms := ([.P,.O,.As,.S] : List Element).map AtomSpec.aliphatic
  bonds := bs
  neighborOrder := [if reverseP then [3,1] else [1,3], [0,2],
    if reverseAs then [3,1] else [1,3], [2,0]]

private def geometry (flat mirror : Bool) : SpatialConfiguration :=
  let ps : List CartesianPoint3 := [⟨0,0,0⟩,⟨1,0,0⟩,
    ⟨if flat then 2 else 1,if flat then 0 else 1,0⟩,
    ⟨if flat then 3 else 0,if flat then 0 else 1,0⟩]
  ⟨if mirror then ps.map CartesianPoint3.reflectX else ps⟩

private def placements (m : RawMolecule) (g : SpatialConfiguration) : IO (List (List Point)) := do
  let some (out,pos) := prepare? m g | throw (IO.userError "hydrogen preparation failed")
  let ss := sites m g out pos
  return choices ss pos.positions

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checkFamily (flat mirror : Bool) : IO Unit := do
  let g := geometry flat mirror
  let base := molecule bonds false false
  let reference ← placements base g
  check (reference.length == if flat then 1 else 4) "wrong number of independent variants"
  let some (out,pos) := prepare? base g | throw (IO.userError "base preparation failed")
  check (out.atomCount == 6 && addedParents base == [0,2]) "implicit hydrogen parent/index plan"
  let ss := sites base g out pos
  check (ss.length == if flat then 0 else 2) "P/As site inventory"
  check (RingOriginOrderRawCheck.check base g [0,2] == some true)
    "origin order changed on an implicit P/As placement"
  let referenceRows := reference.map fun ps => RingChemicalReport.fromRaw? out ⟨ps⟩ [0,2]
  if flat then
    check (referenceRows == [some [(0,none),(2,none)]]) "collinear frames must give completed refusals"
  else
    check (referenceRows.all Option.isSome) "a nondegenerate variant failed report admission"
    check (referenceRows.eraseDups.length == 4) "independent P/As hands did not produce four distinct reports"
  let mut checked := 0
  for bs in bonds.permutations do
    for reverseP in [false,true] do
      for reverseAs in [false,true] do
        let m := molecule bs reverseP reverseAs
        let family ← placements m g
        check (decide (family.Perm reference)) "bond/neighbor order changed actual variant family"
        checked := checked + 1
  check (checked == 96) "not all 24 bond orders and four neighbor-row reversals checked"
  for reverseP in [false,true] do
    for reverseAs in [false,true] do
      let m := molecule bonds.reverse reverseP reverseAs
      let response := RingHydrogenReport.fromRaw? m g [0,2]
      check (response == if flat then some [(0,none),(2,none)] else none)
        "public API changed completed-refusal/disagreement behavior"
      check (RingHydrogenReport.fromRaw? m g [1,3] == some [(1,none),(3,none)])
        "public API failed a request on which all variants agree"
      check (RingHydrogenReport.fromRaw? m g [6] == none) "out-of-range request accepted"
  IO.println s!"implicit P/As: flat={flat}, mirror={mirror}; 96 bond/neighbor presentations, {reference.length} variants, public agreement/refusal checks passed"

def main : IO Unit := do
  for flat in [false,true] do
    for mirror in [false,true] do
      checkFamily flat mirror
