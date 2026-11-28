import TetraStereo.Engine.PublicAPI
import TetraStereo.Engine.RingRootIndexedEarly

/-! D₃ trans-perhydrotriphenylene, Cahn–Ingold–Prelog (1966), formula 35,
pp. 397–398, doi:10.1002/anie.196603851. At each central CH, the arm entering
a *different* lateral six-ring outranks the CH arm in its own lateral ring:
the latter's lateral circuit returns to the original atom; the former reaches
an equivalent atom. CH₂ and H rank third and fourth. The drawing is all R.

The fixture is the refined host in the deposited orthorhombic inclusion
crystal, doi:10.1021/ja971945s.s001. Tables S1, S2 and S4 supply carbon
positions, carbon bonds and hydrogen positions. Raw IDs 0–8 are C1–C9,
9–17 are C1A–C9A; H atoms follow their parent carbons in that order.
The fractional coordinates are given in units of 1/10000. Converting to
Cartesian coordinates uses a = 15.023, b = 23.198, c = 4.730 Å
from the refinement; the resulting integers are in units of 10⁻⁷ Å.
These operations preserve every oriented-volume sign. Hydrogen coordinates
are from the refinement model. The mirror is generated explicitly. This
racemic host model does not itself correlate handedness with optical rotation;
Stephens et al. determined S(+)/R(−), doi:10.1007/s00214-006-0245-7. -/
open TetraStereo.OneCenter TetraStereo.Engine

private def molecule : RawMolecule := {
  atoms := (List.replicate 18 (.C : Element) ++ List.replicate 30 Element.H).map AtomSpec.aliphatic
  bonds := [
    ⟨0,1,.single⟩, ⟨0,9,.single⟩, ⟨0,5,.single⟩, ⟨9,10,.single⟩, ⟨9,14,.single⟩,
    ⟨2,3,.single⟩, ⟨2,1,.single⟩, ⟨11,12,.single⟩, ⟨11,10,.single⟩, ⟨4,3,.single⟩,
    ⟨4,5,.single⟩, ⟨13,12,.single⟩, ⟨13,14,.single⟩, ⟨6,7,.single⟩, ⟨6,5,.single⟩,
    ⟨6,15,.single⟩, ⟨15,16,.single⟩, ⟨15,14,.single⟩, ⟨8,17,.single⟩, ⟨8,7,.single⟩,
    ⟨17,16,.single⟩, ⟨0,18,.single⟩, ⟨1,19,.single⟩, ⟨1,20,.single⟩, ⟨2,21,.single⟩,
    ⟨2,22,.single⟩, ⟨3,23,.single⟩, ⟨3,24,.single⟩, ⟨4,25,.single⟩, ⟨4,26,.single⟩,
    ⟨5,27,.single⟩, ⟨6,28,.single⟩, ⟨7,29,.single⟩, ⟨7,30,.single⟩, ⟨8,31,.single⟩,
    ⟨8,32,.single⟩, ⟨9,33,.single⟩, ⟨10,34,.single⟩, ⟨10,35,.single⟩, ⟨11,36,.single⟩,
    ⟨11,37,.single⟩, ⟨12,38,.single⟩, ⟨12,39,.single⟩, ⟨13,40,.single⟩, ⟨13,41,.single⟩,
    ⟨14,42,.single⟩, ⟨15,43,.single⟩, ⟨16,44,.single⟩, ⟨16,45,.single⟩, ⟨17,46,.single⟩,
    ⟨17,47,.single⟩] }

private def crystal : List CartesianPoint3 := [
    ⟨4513,3768,3011⟩, ⟨4007,4311,2094⟩, ⟨3044,4314,3073⟩, ⟨2558,3775,2144⟩,
    ⟨3048,3231,3031⟩, ⟨4022,3219,2031⟩, ⟨4512,2672,3011⟩, ⟨4038,2119,2101⟩,
    ⟨4522,1575,3034⟩, ⟨5487,3768,1989⟩, ⟨5993,4311,2906⟩, ⟨6956,4314,1927⟩,
    ⟨7442,3775,2856⟩, ⟨6952,3231,1969⟩, ⟨5978,3219,2969⟩, ⟨5488,2672,1989⟩,
    ⟨5962,2119,2899⟩, ⟨5478,1575,1966⟩, ⟨4524,3764,5125⟩, ⟨4316,4657,2875⟩,
    ⟨4022,4339,-15⟩, ⟨3026,4342,5182⟩, ⟨2736,4660,2279⟩, ⟨2492,3778,41⟩,
    ⟨1948,3773,2991⟩, ⟨2730,2889,2241⟩, ⟨3034,3200,5139⟩, ⟨4019,3219,-83⟩,
    ⟨4523,2677,5125⟩, ⟨3424,2117,2918⟩, ⟨3980,2117,-5⟩, ⟨4521,1551,5145⟩,
    ⟨4203,1229,2281⟩, ⟨5476,3764,-125⟩, ⟨5684,4657,2125⟩, ⟨5978,4339,5015⟩,
    ⟨6974,4342,-182⟩, ⟨7264,4660,2721⟩, ⟨7508,3778,4959⟩, ⟨8052,3773,2009⟩,
    ⟨7270,2889,2759⟩, ⟨6966,3200,-139⟩, ⟨5981,3219,5083⟩, ⟨5478,2677,-125⟩,
    ⟨6576,2117,2082⟩, ⟨6020,2117,5005⟩, ⟨5480,1551,-145⟩, ⟨5797,1229,2719⟩]

private def junctions : List Nat := [0,5,6,9,14,15]

/-- Four ligand IDs in the order independently obtained from formula 35. -/
private def sourceRows : List (Nat × Nat × Nat × Nat) := [
    (9,5,1,18), (6,0,4,27), (5,15,7,28),
    (0,14,10,33), (15,9,13,42), (14,6,16,43)]

private theorem indexed_public : RingRootIndexedEarly.fromRaw? = ringMolecularReportFromRaw? :=
  RingRootIndexedEarly.raw_exact
assert_kernel_only indexed_public

def main (args : List String) : IO Unit := do
  let evaluate ← match args with
    | [] | ["--indexed"] => pure RingRootIndexedEarly.fromRaw?
    | ["--direct"] => pure ringMolecularReportFromRaw?
    | _ => throw (IO.userError "usage: --indexed | --direct")
  let cartesian : List CartesianPoint3 := crystal.map fun p =>
    ⟨15023*p.x, 23198*p.y, 4730*p.z⟩
  for mirrored in [false, true] do
    let ps := if mirrored then cartesian.map (fun p => {p with x := -p.x}) else cartesian
    let first : RS := if mirrored then .R else .S
    let other : RS := if mirrored then .S else .R
    for (a,b,c,h) in sourceRows do
      let point (i : Nat) : IO CartesianPoint3 := do
        let some p := ps[i]? | throw (IO.userError "source atom index out of bounds")
        return p
      let v := CartesianPoint3.orientedVolume (← point a) (← point b) (← point c) (← point h)
      unless (if first == .R then v < 0 else 0 < v) do
        throw (IO.userError "published ligand order and coordinate handedness disagree")
    let rows := evaluate molecule ⟨ps⟩ junctions
    let expected : RingGroupedReport.Report :=
      junctions.map fun id => (id, some (.chiral first, .chiral other))
    unless rows == some expected do throw (IO.userError s!"unexpected public output: {repr rows}")
    IO.println s!"reflected={mirrored}, six public junctions {repr first}/{repr other}"
    (← IO.getStdout).flush
