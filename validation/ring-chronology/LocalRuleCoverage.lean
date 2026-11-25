import TetraStereo.Engine.PublicAPI

open TetraStereo.OneCenter TetraStereo.Engine

namespace LocalRuleCoverage

private def molecule (elements : List Element) (edges : List (Nat × Nat)) : RawMolecule :=
  { atoms := elements.map AtomSpec.aliphatic
    bonds := edges.map fun (a,b) => ⟨a,b,.single⟩ }

/-- The reflection (x,y,z) ↦ (−y,−x,z) exchanges the two phosphorus arms and
fixes the oxirane ring. The ligand priority at each P is Cl, F, ring C, phantom. -/
private def positions : List CartesianPoint3 := [
  ⟨0,0,0⟩, ⟨2,2,2⟩, ⟨-2,-2,2⟩, ⟨2,-2,-2⟩, ⟨-2,2,-2⟩,
  ⟨4,1,2⟩, ⟨2,4,1⟩, ⟨-1,-4,2⟩, ⟨-4,-2,1⟩, ⟨-4,2,-3⟩, ⟨-2,4,-3⟩]

private def oxirane := molecule [.C,.P,.P,.O,.C,.Cl,.F,.Cl,.F,.H,.H]
  [(0,1),(0,2),(0,3),(0,4),(3,4),(1,5),(1,6),(2,7),(2,8),(4,9),(4,10)]

private def cyclopropane (count : Nat) : RawMolecule := molecule
  ([.C,.C,.C,.Br,.F] ++ List.replicate count .H)
  ([(0,1),(0,2),(0,3),(0,4),(1,2)] ++ [(1,5),(1,6),(2,7),(2,8)].take count)

private def checkReport (label : String) (m : RawMolecule) (points : List CartesianPoint3)
    (expected : RingGroupedReport.Report) : IO Bool := do
  let some rows := ringMolecularReportFromRaw? m ⟨points⟩ (expected.map Prod.fst)
    | throw (IO.userError s!"{label} failed admission")
  let conforms := rows == expected
  IO.println s!"{label} conforms to IUPAC = {conforms}, rows = {repr rows}"
  return conforms

def audit (args : List String) : IO Unit := do
  let mut conforms := true
  for (count,h1,h2) in [(0,2,2),(2,0,2),(4,0,0)] do
    let m := cyclopropane count
    unless m.implicitHydrogensAt? 1 == some h1 && m.implicitHydrogensAt? 2 == some h2 do
      throw (IO.userError "unexpected implied H count on the cyclopropane arms")
    let ok ← checkReport s!"Cyclopropane, {count} separate H atoms" m
      (positions.take (5 + count)) [(0,none)]
    conforms := conforms && ok
  let r := LocalizedTetrahedralRSPseudoDescriptor.chiral .R
  let s := LocalizedTetrahedralRSPseudoDescriptor.chiral .S
  let lower := LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric .s
  for (label,points,p1,p2) in [("original",positions,r,s),
      ("mirror",positions.map (fun p => {p with x := -p.x}),s,r)] do
    let ok ← checkReport s!"Oxirane, {label}" oxirane points
      [(0,some (lower,lower)),(1,some (p1,p2)),(2,some (p2,p1))]
    conforms := conforms && ok
  if args == ["--require-conformance"] && !conforms then
    throw (IO.userError "public report disagrees with the IUPAC controls")

end LocalRuleCoverage

def main := LocalRuleCoverage.audit
