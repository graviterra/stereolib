import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.AntipodalCyclohexaneReport
/-! P-93.5.1.1.2(a) of the IUPAC Blue Book gives (1s,4s) and (1r,4r)
for cis- and trans-cyclohexane-1,4-diol, respectively. The dimethyl cases
are entries 94 and 95 of the Centres validate.smi corpus used by
CentresEvaluation.lean. The geometries below encode the two faces directly.
https://iupac.qmul.ac.uk/BlueBook/P9.html -/

open TetraStereo.OneCenter TetraStereo.Engine

-- The planar ring hexagon fixes a common face convention. Each marked site
-- has one substituent above/below the ring and H on the opposite side.
private def fixture (sub : Element) (cis : Bool) (sites : List Nat := [0,3]) : RawMolecule × SpatialConfiguration := Id.run do
  let xy : List (Int × Int) := [(4,0),(2,3),(-2,3),(-4,0),(-2,-3),(2,-3)]
  let mut atoms := List.replicate 6 Element.C
  let mut ps : List CartesianPoint3 := xy.map fun (x,y) => ⟨x,y,0⟩
  let mut edges := (List.range 6).map fun i => (i,(i+1)%6)
  for ((x,y),i) in xy.zipIdx do
    let marked := sites.contains i
    let above : Int := if i == 3 && !cis then -1 else 1
    let j := atoms.length
    atoms := atoms ++ [if marked then sub else .H,.H]
    ps := ps ++ [⟨2*x,2*y,above⟩,⟨2*x,2*y,-above⟩]
    edges := edges ++ [(i,j),(i,j+1)]
    if marked then
      for _ in List.range (if sub == .C then 3 else 1) do
        let h := atoms.length
        let t : ℚ := 10+h
        atoms := atoms ++ [.H]
        ps := ps ++ [⟨t,t*t,t*t*t⟩]
        edges := edges ++ [(j,h)]
  return (⟨atoms.map AtomSpec.aliphatic,edges.map (fun (a,b) => ⟨a,b,.single⟩),[],[]⟩,⟨ps⟩)

-- Both source isomers have the precise labelled graph used by the all-geometry auxiliary proof.
example (cis : Bool) : (fixture .O cis).1 = TetraStereo.Examples.AntipodalCyclohexaneHands.molecule := by
  cases cis <;> decide +kernel

-- For both faces and their reflections, the independent determinant formula
-- reproduces the published labels and the completed refusal at a methylene.
example (cis reflected : Bool) :
    let points := (fixture .O cis).2.positions
    let x : SpatialConfiguration := ⟨if reflected then points.map CartesianPoint3.reflectX else points⟩
    let d : LocalizedTetrahedralRSPseudoDescriptor := if cis then .pseudoasymmetric .s else .pseudoasymmetric .r
    TetraStereo.Examples.AntipodalCyclohexaneReport.expected? x [3,1,0,3] =
      some [(3,some (d,d)),(1,none),(0,some (d,d)),(3,some (d,d))] := by
  cases cis <;> cases reflected <;> decide +kernel

example : RingSparseTwinReport.fromRaw? = ringMolecularReportFromRaw? := RingSparseTwinReport.raw_exact

-- Removing the opposite substituent restores equivalent ring paths at site 0.
-- Removing both leaves two identical H atoms at each queried carbon.
private def checkControls : IO Unit := do
  for sites in [([] : List Nat),[0]] do
    let (m,x) := fixture .O true sites
    let expected : RingGroupedReport.Report := [(0,none),(3,none)]
    let result := RingSparseTwinReport.fromRaw? m x [0,3]
    unless result == some expected do
      throw (IO.userError s!"substituted sites {sites}, expected two refusals, got {repr result}")
    IO.println s!"substituted sites {sites}: both sites unassigned"
    (← IO.getStdout).flush

-- Preserve the six ring IDs and both O coordinates. Retaining just H7 gives
-- one fully written reporting center and one whose H must be reconstructed.
private def checkHydrogenSpellings : IO Unit := do
  for cis in [true,false] do
    let (full,spatial) := fixture .O cis
    for retainFirst in [false,true] do
      let ids := [0,1,2,3,4,5,6,13] ++ (if retainFirst then [7] else [])
      let atoms := ids.filterMap fun n => full.atoms[n]?
      let bonds := full.bonds.filterMap fun bond =>
        if ids.contains bond.source && ids.contains bond.target then
          some ⟨ids.idxOf bond.source,ids.idxOf bond.target,bond.kind⟩ else none
      let raw : RawMolecule := ⟨atoms,bonds,[],[]⟩
      let x : SpatialConfiguration := ⟨ids.filterMap fun n => spatial.positions[n]?⟩
      let missing := ((RingHydrogenCompletion.plan raw).map Prod.snd).sum
      unless missing == (if retainFirst then 11 else 12) do throw (IO.userError "wrong H inventory")
      let d : LocalizedTetrahedralRSPseudoDescriptor :=
        if cis then .pseudoasymmetric .s else .pseudoasymmetric .r
      let expected : RingGroupedReport.Report := [(3,some (d,d)),(0,some (d,d))]
      let result := RingSparseTwinReport.fromRaw? raw x [3,0]
      unless result == some expected do
        throw (IO.userError s!"cis={cis} missing H={missing}, got {repr result}")
      IO.println s!"cis={cis}, inferred H={missing}, both root assignments passed"
      (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args == ["--hydrogen-spellings"] then return ← checkHydrogenSpellings
  checkControls
  for sub in [Element.C,.O] do
    for cis in [true,false] do
      let (m,x) := fixture sub cis
      unless (RingHydrogenCompletion.plan m).isEmpty do throw (IO.userError "incomplete hydrogens")
      for mirror in [false,true] do
        let g := if mirror then ⟨x.positions.map CartesianPoint3.reflectX⟩ else x
        let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "raw admission")
        unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission")
        let result := RingSparseTwinReport.fromRaw? m g [0,3]
        let d : LocalizedTetrahedralRSPseudoDescriptor := if cis then .pseudoasymmetric .s else .pseudoasymmetric .r
        let expected : RingGroupedReport.Report := [(0,some (d,d)),(3,some (d,d))]
        unless result == some expected do throw (IO.userError s!"{repr sub} cis={cis} mirror={mirror}, expected {repr expected}, got {repr result}")
        IO.println s!"{repr sub} cis={cis} mirror={mirror}: both sites passed"
        (← IO.getStdout).flush
