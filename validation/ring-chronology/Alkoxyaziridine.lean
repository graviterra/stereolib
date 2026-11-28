import TetraStereo.Engine.PublicAPI

/-! Ioffe and Koroleva, *1-Alkoxyaziridines*, Chemistry of Heterocyclic
Compounds 8 (1972), 1367–1371, doi:10.1007/BF00471872. The authors
report preparative chromatographic separation of nitrogen invertomers on the
2,2,3-trimethylaziridine skeleton. Their O-alkyl substituents are methyl,
ethyl and isopropyl. These rational models specify relative configurations;
the experiment did not assign these coordinates or a peak to an absolute hand.

The ring is N0–C1–C2. At N0 the priorities are O3, gem-dimethyl C1,
monomethyl C2, phantom. At stereogenic C2 they are N0, C1, Me6, H7.
The gem-dimethyl C1 has two equivalent methyl groups. -/
open TetraStereo.OneCenter TetraStereo.Engine

/-- Atom 8 bears the O-alkyl methyl branches. The hydroxyl control makes 8 hydrogen. -/
private def fixture (extra : Nat) (z : Int) (hydroxyl := false) (ringMethyl := true) : RawMolecule × List CartesianPoint3 := Id.run do
  let extraMe := List.range extra |>.map (·+9)
  let elements : List Element := [.N,.C,.C,.O,.C,.C,if ringMethyl then .C else .H,.H,if hydroxyl then .H else .C] ++ List.replicate extra .C
  let base : List (Nat × Nat) := [(0,1),(0,2),(1,2),(0,3),(1,4),(1,5),(2,6),(2,7),(3,8)] ++
    extraMe.map fun c => (8,c)
  let mut edges := base
  let mut atoms := elements
  let mut ps : List CartesianPoint3 := [
    ⟨0,0,0⟩, ⟨2,0,0⟩, ⟨0,2,0⟩, ⟨0,0,z⟩,
    ⟨3,-1,1⟩, ⟨3,-1,-1⟩, ⟨0,3,1⟩, ⟨0,3,-1⟩, ⟨1,-1,2*z⟩] ++
    ([⟨2,-2,2*z+1⟩, ⟨2,0,2*z-1⟩, ⟨0,-2,2*z-1⟩] : List CartesianPoint3).take extra
  for c in (([4,5,6,8] : List Nat) ++ extraMe) do
    if elements[c]? != some .C then continue
    let degree := (base.filter fun edge => edge.1 == c || edge.2 == c).length
    for _ in List.range (4-degree) do
      let h := atoms.length
      let t : ℚ := h+10
      ps := ps ++ [⟨t,t*t,t*t*t⟩]
      atoms := atoms ++ [.H]
      edges := edges ++ [(c,h)]
  return (⟨atoms.map AtomSpec.aliphatic, edges.map (fun (a,b) => ⟨a,b,.single⟩),[],[]⟩,ps)

def main : IO Unit := do
  -- Each control changes just one substitution of the positive scaffold.
  for (name,control) in [("N–OH",fixture 0 2 true),("tert-butoxy",fixture 3 2),
      ("2,2-dimethyl ring",fixture 0 2 false false)] do
    let (m,ps) := control
    unless (RingHydrogenCompletion.plan m).isEmpty do throw (IO.userError s!"missing H in {name}")
    let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨ps⟩ | throw (IO.userError s!"admission {name}")
    unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError s!"geometry {name}")
    if RingPyramidalNitrogen.constrainedRaw m 0 then throw (IO.userError s!"unexpected selection {name}")
    IO.println s!"{name}: admitted, nitrogen outside the selector"
  for (name,extra) in [("methoxy",0),("ethoxy",1),("isopropoxy",2)] do
    for z in [(2 : Int),-2] do
      let (m,base) := fixture extra z
      unless (RingHydrogenCompletion.plan m).isEmpty do throw (IO.userError "expected explicit H")
      for mirror in [false,true] do
        let ps := if mirror then base.map CartesianPoint3.reflectX else base
        let some input := LocalizedChemicalRing.admitRawSpatial? m ⟨ps⟩ | throw (IO.userError "raw admission")
        unless LocalizedChemicalRing.coordinatesAdmitted input do throw (IO.userError s!"geometry {name}/{z}")
        let point (k : Nat) : IO CartesianPoint3 := do
          let some p := ps[k]? | throw (IO.userError "missing source atom")
          return p
        let nVol := CartesianPoint3.orientedVolume (← point 3) (← point 1) (← point 2) (← point 0)
        let cVol := CartesianPoint3.orientedVolume (← point 0) (← point 1) (← point 6) (← point 7)
        let parity : ℚ := if mirror then -1 else 1
        unless nVol == parity*4*z && cVol == parity*12 do throw (IO.userError "independent determinants")
        let n : RS := if nVol < 0 then .R else .S
        let c : RS := if cVol < 0 then .R else .S
        let expected : RingGroupedReport.Report :=
          [(0,some (.chiral n,.chiral n.swap)),(2,some (.chiral c,.chiral c.swap))]
        let report := ringMolecularReportFromRaw? m ⟨ps⟩ [0,2]
        IO.println s!"{name}, O height {z}, reflected {mirror}, N/C report {repr report}"
        (← IO.getStdout).flush
        unless report == some expected do throw (IO.userError "alkoxyaziridine public result")
