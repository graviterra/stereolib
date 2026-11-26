import TetraStereo.Engine.RingSparseTwinReport
import TetraStereo.Engine.RingLigandTreeStore

/-! A methyl-substituted cyclopropane has terminal twins in a ring CH₂ and in
the methyl group. Swapping one methyl H to the original root must leave two
other H available. Every cut is checked against the literal public store. -/
open TetraStereo.OneCenter TetraStereo.Engine
namespace SparseTwinControl

def molecule : RawMolecule where
  atoms := [.C,.C,.C,.F,.C,.Cl,.H,.H,.H,.H,.H,.H].map AtomSpec.aliphatic
  bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),
    (2,7),(2,8),(4,9),(4,10),(4,11)] : List (Nat × Nat)).map (fun (a,b) => ⟨a,b,.single⟩)

def geometry : SpatialConfiguration := ⟨[
  ⟨0,0,0⟩,⟨1,1,1⟩,⟨1,-1,-1⟩,⟨-1,1,-1⟩,⟨-1,-1,1⟩,⟨2,1,1⟩,
  ⟨1,2,1⟩,⟨2,-1,-1⟩,⟨1,-2,-1⟩,⟨-2,-1,1⟩,⟨-1,-2,1⟩,⟨-1,-1,2⟩]⟩

private def nextArm (i : LocalizedChemicalRing.Input) (q : RingActivePairs.Arm i)
    (id : Nat) : IO (RingActivePairs.Arm i) := do
  let some arm := (i.certified.executableLocalizedRerootChildren q).find?
    (fun t => t.occurrence.val.node.current?.map Fin.val == some id) |
    throw (IO.userError s!"Missing rerooted direction to {id}")
  return arm

private def second (i : LocalizedChemicalRing.Input) (arm : RingActivePairs.Arm i) : IO (List Nat) := do
  let some word := (RingRetainedChemicalTrace.key? i arm).bind (fun k => k.atomic.word[1]?) |
    throw (IO.userError "Missing actual second sphere")
  return word

def checkShell (i : LocalizedChemicalRing.Input) : IO Unit := do
  let some [root] := RingMolecularReport.resolve i [0] | throw (IO.userError "Ring root")
  let q := RingGroupedReport.origin i root
  let expected : RingNestedActivePair.Labels := (.chiral .S,.chiral .R)
  unless RingSecondShellDecision.direct? i q == some expected do throw (IO.userError "Two-shell ring hand")
  let start : RingActivePairs.Arm i := ⟨q,none⟩
  let c1 ← nextArm i start 1
  let c2 ← nextArm i start 2
  let methyl ← nextArm i start 4
  let words ← [c1,c2,methyl].mapM (second i)
  unless words == [[17,6,1],[6,1,1],[1,1,1]] do throw (IO.userError s!"Second spheres {words}")
  let inward ← nextArm i ⟨c1.occurrence,none⟩ 0
  let inwardWord ← second i inward
  unless inwardWord == [9,6,6] do throw (IO.userError s!"Inward sphere {inwardWord}")
  let atTwo ← nextArm i c1 2
  let duplicate ← nextArm i atTwo 0
  let duplicateWord ← second i duplicate
  let naive := RingSecondShellDecision.shell i.molecule 2 0
  unless duplicate.occurrence.val.node.provenance != .realAtom && duplicateWord == [] &&
      naive == [9,6,6] do throw (IO.userError s!"Closure actual={duplicateWord} graph={naive}")
  IO.println s!"C0 second-shell S; carbon rows {words}; inward {inwardWord}; closure {duplicateWord} versus physical {naive}"

def inspect (i : LocalizedChemicalRing.Input) (a : i.certified.Atom) : IO Unit := do
  let height := RingActiveDistanceSchedule.height i
  let mut omitted := 0
  for cut in List.range (height+3) do
    let full := RingSphereStore.rows i a (height+1-cut)
    let small := RingSparseTwinReport.sparse i a cut
    let audit := RingSparseTwinReport.audit i a cut
    let treeRows := RingLigandTreeStore.rows i a cut
    unless treeRows == full do throw (IO.userError s!"Tree-driven store differs at root {a.val}, cut {cut}")
    unless audit == full do throw (IO.userError s!"Audit differs at root {a.val}, cut {cut}")
    unless small == full.filter (fun row => RingSparseTwinReport.keep i row.1) do
      throw (IO.userError "Unexpected retained rows")
    if cut == 0 then
      omitted := full.length - small.length
      IO.println s!"Root {a.val}: {full.length} addressed rows, {small.length} stored, {omitted} certified refusals"
      unless full.any (fun row => row.1.val.node.current?.map Fin.val == some 4 &&
        row.2 == some none && !RingSparseTwinReport.keep i row.1) do
        throw (IO.userError "Expected a certified methyl refusal")
  unless omitted > 0 do throw (IO.userError "No cells omitted")

/-- Four distinct arms, a CH₂ pair and a CH₃ triple exercise each multiplicity. -/
def checkTrees (i : LocalizedChemicalRing.Input) : IO Unit := do
  for id in [0,2,4] do
    let some [c] := RingMolecularReport.resolve i [id] | throw (IO.userError "atom")
    let f := RingGroupedReport.origin i c
    let directions := RingRetainedChemicalPreorder.directions i f
    let n := RingLigandTreeComparison.depth i
    let mut samples := []
    for a in directions do
      let expected := RingRetainedChemicalPreorder.keyFor a
      unless RingLigandTreeComparison.reconstruct n (RingLigandTreeComparison.tree a) == some expected do
        throw (IO.userError s!"C{id} constitutional key")
      let t := RingLigandTreeComparison.zeroTree a
      let zero := RingZeroDuplicateMass.rebuiltFor a
      unless RingLigandTreeComparison.reconstruct n t == some zero do
        throw (IO.userError s!"C{id} zero-mass key")
      samples := (t,zero,expected) :: samples
    let mut tieCount := 0
    for (a,z,x) in samples do
      for (b,w,y) in samples do
        let ord := RingRetainedChemicalTrace.compareKeys x y
        unless RingRetainedChemicalTrace.compareKeys z w == ord &&
            RingLigandTreeComparison.sameTree n a b == (ord == .eq) do
          throw (IO.userError s!"C{id} structural comparison")
        if ord == .eq then tieCount := tieCount+1
    let expect := if id == 0 then 4 else if id == 2 then 6 else 10
    unless tieCount == expect do throw (IO.userError s!"C{id}: {tieCount} ties vs {expect}")
    IO.eprintln s!"C{id}: reconstructed {directions.length} keys under both mass conventions; {tieCount}/16 ordered pairs tied"

end SparseTwinControl

open SparseTwinControl

def main (args : List String) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule geometry | throw (IO.userError "Molecular admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "Coordinate admission")
  checkTrees i
  if args.contains "--trees-only" then return
  checkShell i
  for n in [0,9] do
    let some [a] := RingMolecularReport.resolve i [n] | throw (IO.userError "Atom request")
    inspect i a
  let native := RingHydrogenReport.fromRaw? SparseTwinControl.molecule SparseTwinControl.geometry [0,4,9,0]
  let sparse := RingSparseTwinReport.fromRaw? SparseTwinControl.molecule SparseTwinControl.geometry [0,4,9,0]
  let treeReport := RingLigandTreeStore.fromRaw? SparseTwinControl.molecule SparseTwinControl.geometry [0,4,9,0]
  unless sparse == native && treeReport == native && sparse.isSome do throw (IO.userError "Raw reports disagree")
  IO.println s!"Public, tree-driven and sparse reports agree {repr native}"
