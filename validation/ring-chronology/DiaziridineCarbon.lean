import TetraStereo.Engine.RingOrdinaryPairVerdict

/-! Cis and trans coordinate models of 1,2-dimethyl-3-tert-butyldiaziridine.
The cis nitrogen hands are opposite and Rule 5 ranks the R arm first. The
trans arms have the same hand and the ring carbon receives a refusal.
Experimental conformations: DOI 10.1070/MC1998v008n03ABEH000916. -/
open TetraStereo TetraStereo.OneCenter TetraStereo.Engine

namespace DiaziridineControl

private def methyls : List Nat := [3,4,6,7,8]

def molecule : RawMolecule := {
  atoms := ([.N,.N] ++ List.replicate 7 .C ++ List.replicate 16 .H : List Element).map AtomSpec.aliphatic
  bonds := ([(0,1),(0,2),(1,2),(0,3),(1,4),(2,5),(5,6),(5,7),(5,8),(2,9)] ++
    (methyls.zipIdx).flatMap (fun (entry : Nat × Nat) => (List.range 3).map fun j => (entry.1,10+3*entry.2+j))).map fun (a,b) => ⟨a,b,.single⟩ }

/-- The ring lies in the xy-plane. Change the side occupied by N1’s methyl
for the cis/trans pair and reflect every z coordinate for the mirror. -/
def geometry (cis mirror : Bool) : SpatialConfiguration := Id.run do
  let z : ℚ := if cis then 2 else -2
  let heavy : List CartesianPoint3 := [⟨0,0,0⟩,⟨2,0,0⟩,⟨1,2,0⟩,⟨-1,-1,2⟩,⟨3,-1,z⟩,
    ⟨1,3,2⟩,⟨0,4,3⟩,⟨2,4,3⟩,⟨1,2,3⟩,⟨1,3,-1⟩]
  let hydrogens : List CartesianPoint3 := methyls.flatMap fun n =>
    let p := heavy[n]?.getD ⟨0,0,0⟩
    [⟨p.x+1/4,p.y,p.z⟩,⟨p.x,p.y+1/4,p.z⟩,⟨p.x,p.y,p.z+1/4⟩]
  return ⟨(heavy ++ hydrogens).map fun p => if mirror then ⟨p.x,p.y,-p.z⟩ else p⟩

open RingFullPathEligibility (Key)
open RingLigandFirstDifference (stages directions)
open RingResidualPairDecision (Verdict words)
open private pick matrix from TetraStereo.Engine.RingResidualPairDecision
open private frame_eq from TetraStereo.Engine.RingGroupedReport

private def verdict (a b : Key) := pick (directions (words a []) (words b [])) stages

/-- Check the requested pair from its two keys without constructing the other
table entries or enumerating every root to find the height. -/
private theorem entry {i : LocalizedChemicalRing.Input} {c : i.certified.Atom}
    (fr : RingNestedActivePair.Frame i (RingGroupedReport.origin i c))
    (rev : Bool) {ks : RingActivePairReport.Slot → Key}
    (keys : RingFullPathPublication.keys? fr
      (RingSphereQueue.reader c (RingSphereQueue.viewOf (RingSparseTwinReport.sparse i c 0))) rev = some ks)
    (a b : RingActivePairReport.Slot) :
    (RingOrdinaryPairVerdict.table? i c (RingActiveDistanceSchedule.height i + 1)
      (RingGroupedReport.origin i c) rev).map (fun t => t[a.val][b.val]) =
      some (verdict (ks a) (ks b)) := by
  simp [RingOrdinaryPairVerdict.table?,RingOrdinaryPairVerdict.reader,frame_eq fr,
    RingOrdinaryPairVerdict.onReader?,keys,matrix,verdict]

/-- Resolve the ordinary nitrogen-arm comparison on the actual C3 reader. -/
def checkOrder (g : SpatialConfiguration) (cis mirror : Bool) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule g | throw (IO.userError "raw admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate gate")
  let some c := (List.finRange _ : List i.certified.Atom)[2]? | throw (IO.userError "missing C3")
  let f := RingGroupedReport.origin i c
  let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "missing C3 frame")
  let slot (id : Nat) := (List.finRange 4).find? fun k => fr.atoms [k] == [id]
  let some n0 := slot 0 | throw (IO.userError "first nitrogen")
  let some n1 := slot 1 | throw (IO.userError "second nitrogen")
  let rows := RingSparseTwinReport.sparse i c 0
  let r := RingSphereQueue.reader c (RingSphereQueue.viewOf rows)
  let some keys := RingFullPathPublication.keys? fr r false | throw (IO.userError "missing ordinary keys")
  let actual := verdict (keys n0) (keys n1)
  let expected : RingResidualPairDecision.Verdict :=
    if cis then (if mirror then .left .rule5 else .right .rule5) else .tie
  unless actual == expected do
    throw (IO.userError s!"expected {repr expected}, received {repr actual}")
  IO.println s!"cis={cis}, reflected={mirror}, ordinary nitrogen comparison {repr expected}"
  (← IO.getStdout).flush

end DiaziridineControl

open DiaziridineControl in
def main (args : List String) : IO Unit := do
  let orderOnly := args.contains "--order"
  let cases := args.filter (· != "--order")
  unless cases.all (["cis-written","cis-reflected","trans-written","trans-reflected"].contains ·) do
    throw (IO.userError "expected a cis/trans written/reflected case name")
  for cis in [true,false] do
    for mirror in [false,true] do
      let tag := (if cis then "cis" else "trans") ++ (if mirror then "-reflected" else "-written")
      if cases.isEmpty || cases.contains tag then
        let g := geometry cis mirror
        if orderOnly then
          checkOrder g cis mirror
          continue
        let n0 := if mirror then RS.R else RS.S
        let n1 := if cis then n0.swap else n0
        let nitrogen (h : RS) : Option RingNestedActivePair.Labels := some (.chiral h,.chiral h.swap)
        let carbon : Option RingNestedActivePair.Labels :=
          if cis then some (.pseudoasymmetric .r,.pseudoasymmetric .r) else none
        let expected : RingGroupedReport.Report := [(0,nitrogen n0),(1,nitrogen n1),(2,carbon)]
        let actual := RingSparseTwinReport.fromRaw? molecule g [0,1,2]
        unless actual == some expected do
          throw (IO.userError s!"{tag}: expected {repr expected}, received {repr actual}")
        IO.println s!"{tag}: {repr actual}"
        (← IO.getStdout).flush
