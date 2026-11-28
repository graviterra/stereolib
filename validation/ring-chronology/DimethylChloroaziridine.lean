import TetraStereo.Examples.Chloroaziridine

/-! The two enantiomers of 1-chloro-2,2-dimethylaziridine were resolved by
Reich, Trapp and Schurig (2000, PMID 11045506). Coordinates here are rational
models; they are not experimental coordinates or chromatographic peak assignments. -/
open TetraStereo.OneCenter TetraStereo.Engine

private abbrev molecule := Chloroaziridine.molecule true

private def geometry (z : Int) : SpatialConfiguration := ⟨[
  ⟨0,0,0⟩,⟨2,0,0⟩,⟨0,2,0⟩,⟨0,0,z⟩,⟨3,-1,1⟩,⟨3,-1,-1⟩,⟨0,3,1⟩,⟨0,3,-1⟩,
  ⟨4,-1,1⟩,⟨3,-2,1⟩,⟨3,-1,2⟩,⟨4,-1,-1⟩,⟨3,-2,-1⟩,⟨3,-1,-2⟩]⟩

def main : IO Unit := do
  for z in [(2 : Int),-2] do
    let xyz := geometry z
    let some i := LocalizedChemicalRing.admitRawSpatial? molecule xyz | throw (IO.userError "raw admission")
    unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinates")
    unless (RingHydrogenCompletion.plan molecule).isEmpty do throw (IO.userError "unexpected implicit H")
    -- Cl ranks first; the two carbon ligands present [C,C,C] and [C,H,H].
    -- The determinant of [Cl,C1,C2] relative to N is 4z. The phantom ranks last.
    let h : RS := if z > 0 then .S else .R
    let expected : Option RingGroupedReport.Report := some [(0,some (.chiral h,.chiral h.swap)),(1,none)]
    let report := RingHydrogenReport.fromRaw? molecule xyz [0,1]
    unless report == expected do throw (IO.userError "1-chloro-2,2-dimethylaziridine public report")
    let heavy : RawMolecule := {
      atoms := molecule.atoms.take 6
      bonds := molecule.bonds.filter fun b => b.source < 6 && b.target < 6 }
    let compact : SpatialConfiguration := ⟨xyz.positions.take 6⟩
    unless RingHydrogenReport.fromRaw? heavy compact [0,1] == expected do
      throw (IO.userError "implicit-H spelling changed the nitrogen or carbon result")
    IO.println s!"chlorine z={z}, explicit and implicit hydrogens agree: {repr report}"
