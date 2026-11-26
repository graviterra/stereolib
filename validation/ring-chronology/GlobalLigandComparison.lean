import TetraStereo.Engine.RingConstitutionalResidual
import TetraStereo.Engine.RingRawLigandOrder
import TetraStereo.Engine.RingIndependentInventory
import TetraStereo.Examples.RingPyramidalInventoryBoundary
import TetraStereo.Examples.RingPhosphaneOxirane

/-! Runtime acceptance of the all-ligand comparison interface. Mutations below
are synthetic comparator experiments, not alternative chemical priority rules. -/
set_option autoImplicit false
namespace GlobalLigandComparison
open TetraStereo.OneCenter TetraStereo.Engine
open RingUniversalLigandOrder (Query)
open RingHydrogenSpelling

private def reversePyramidal : RingRawLigandOrder.Comparisons := fun i q r query =>
  match query with
  | .pyramidal rev trial a b => RingLigandNativeAnswers.nativeOracle i q r (.pyramidal rev trial b a)
  | other => RingLigandNativeAnswers.nativeOracle i q r other

private def tiePyramidal : RingRawLigandOrder.Comparisons := fun i q r query =>
  match query with
  | .pyramidal .. => false
  | other => RingLigandNativeAnswers.nativeOracle i q r other

private def paired (h : RS) : RingNestedActivePair.Labels := (.chiral h,.chiral h.swap)

private def progress (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

/-- Both ring neighbors are oxygen. Only the isotope separates them. -/
private def oxygenRing (pyramidal heavy : Bool) : RawMolecule :=
  let atoms := [AtomSpec.aliphatic (if pyramidal then .As else .C), AtomSpec.aliphatic .O,
    { AtomSpec.aliphatic .O with isotope? := if heavy then some 18 else none }, AtomSpec.aliphatic .F]
  let bonds : List RawBond := [⟨0,1,.single⟩,⟨1,2,.single⟩,⟨2,0,.single⟩,⟨0,3,.single⟩]
  if pyramidal then {atoms,bonds} else {atoms := atoms ++ [AtomSpec.aliphatic .Br],bonds := bonds ++ [⟨0,4,.single⟩]}

private def isotopeGate : IO Unit := do
  for pyramidal in [false,true] do
    for heavy in [false,true] do
      let m := oxygenRing pyramidal heavy
      let xyz := PyramidalInventoryBoundary.positions false
      let x := if pyramidal then xyz else ⟨xyz.positions ++ [⟨0,0,3⟩]⟩
      let some i := LocalizedChemicalRing.admitRawSpatial? m x | throw (IO.userError "oxygen ring admission")
      unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "oxygen ring coordinates")
      if bound : 0 < i.certified.certified.input.molecule.atomCount then
        let q := RingGroupedReport.origin i ⟨0,bound⟩
        unless (RingResidualPriority.graphCell? i q).isNone do throw (IO.userError "first-shell gate broke oxygen tie")
        let d := RingConstitutionalResidual.direct i q
        let order := if pyramidal then [3,2,1,0] else [4,3,2,1]
        let some h := LocalizedGenericMarkedRecalculation.readback? (RingWrittenPHReadings.geometry x) order
          | throw (IO.userError "isotope control orientation is flat")
        let label := if heavy then some (paired h) else none
        let expected : Option RingActiveDistanceSchedule.Cell := if heavy then some (some label) else none
        unless d == expected do throw (IO.userError s!"constitutional isotope gate mismatch {pyramidal}, {heavy}: {repr d}")
        unless RingHydrogenReport.fromRaw? m x [0] == some [(0,label)] do throw (IO.userError "oxygen ring raw report")
      else throw (IO.userError "empty oxygen ring")
  progress "Constitutional gate preserved both O/O ties and resolved both O-18/O priorities on C and As."

/-- A constitutional tie can still require a lowercase descriptor. -/
private def enantiomorphicGate : IO Unit := do
  let m := PhosphaneOxirane.molecule
  let x : SpatialConfiguration := ⟨PhosphaneOxirane.Representatives.base⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m x | throw (IO.userError "oxirane admission")
  if bound : 0 < i.certified.certified.input.molecule.atomCount then
    let q := RingGroupedReport.origin i ⟨0,bound⟩
    unless (RingConstitutionalResidual.direct i q).isNone do throw (IO.userError "constitution broke the enantiomorphic arm tie")
    let lower : LocalizedTetrahedralRSPseudoDescriptor := .pseudoasymmetric .s
    unless RingHydrogenReport.fromRaw? m x [0] == some [(0,some (lower,lower))] do
      throw (IO.userError "Rule 5 failed to resolve the mirror-related arms")
  else throw (IO.userError "empty oxirane")
  progress "Constitution deferred the enantiomorphic phosphane arms. The public rule gave s on both geometries."

/-- Small admitted graph for an exhaustive diagnostic, including the control
where the artificial policy and the native policy select the same centers. -/
private def inventoryDiagnosis : IO Unit := do
  let m : RawMolecule := {
    atoms := List.replicate 3 (.aliphatic .O)
    bonds := [⟨0,1,.single⟩,⟨1,2,.single⟩,⟨2,0,.single⟩] }
  let x : SpatialConfiguration := ⟨[⟨0,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩]⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m x | throw (IO.userError "three-oxygen ring admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "three-oxygen ring coordinates")
  unless RingIndependentInventory.check i (RingIndependentInventory.native i) do
    throw (IO.userError "native policy disagreed with itself")
  let synthetic : RingIndependentInventory.Policy i :=
    {eligible := fun a => a.val == 0, primitive := fun _ _ => some (some (paired .R))}
  let some q := RingIndependentInventory.diagnose? i synthetic
    | throw (IO.userError "missed synthetic selection discrepancy")
  unless q.val.node.current?.map Fin.val == some 0 do
    throw (IO.userError "inventory diagnosis returned a different atom")
  progress s!"Whole-graph inventory check passed. Synthetic selection at atom 0 diagnosed at depth {RingActiveDistanceSchedule.distance q}."

def audit : IO Unit := do
  inventoryDiagnosis
  isotopeGate
  enantiomorphicGate
  let m := PyramidalInventoryBoundary.molecule
  let ids := [0,0]
  for reflected in [false,true] do
    let x := PyramidalInventoryBoundary.positions reflected
    let h := if reflected then RS.S else RS.R
    let expected : RingGroupedReport.Report := ids.map fun n => (n,if n == 0 then some (paired h) else none)
    let reversed : RingGroupedReport.Report := ids.map fun n => (n,if n == 0 then some (paired h.swap) else none)
    let refused : RingGroupedReport.Report := ids.map fun n => (n,none)
    let actual := RingHydrogenReport.fromRaw? m x ids
    progress s!"As mirror={reflected}: raw evaluated"
    let reconstructed := RingRawLigandOrder.fromRaw? RingLigandNativeAnswers.nativeOracle m x ids
    progress s!"As mirror={reflected}: nativeOracle evaluated"
    let reverseResult := RingRawLigandOrder.fromRaw? reversePyramidal m x ids
    progress s!"As mirror={reflected}: reversed queries evaluated"
    let tieResult := RingRawLigandOrder.fromRaw? tiePyramidal m x ids
    progress s!"As mirror={reflected}: tie queries evaluated"
    unless actual == some expected do throw (IO.userError s!"As mirror {reflected}: native raw labels changed: {repr actual}")
    unless reconstructed == actual do throw (IO.userError s!"As mirror {reflected}: nativeOracle reconstruction disagreed")
    unless reverseResult == some reversed do throw (IO.userError s!"As mirror {reflected}: reversed directed queries yielded {repr reverseResult}")
    unless tieResult == some refused do throw (IO.userError s!"As mirror {reflected}: all-tied directed queries yielded {repr tieResult}")
    unless (RingRawLigandOrder.fromRaw? RingLigandNativeAnswers.nativeOracle m x [0,4,0]).isNone do
      throw (IO.userError "nativeOracle reconstruction accepted an invalid original ID")
    let some i := LocalizedChemicalRing.admitRawSpatial? m x
      | throw (IO.userError "As regression source admission failed")
    unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "As regression coordinate admission failed")
    if bound : 0 < i.certified.certified.input.molecule.atomCount then
      let a : i.certified.Atom := ⟨0,bound⟩
      let origin := RingGroupedReport.origin i a
      let native := RingIndependentInventory.native i
      let excluded : RingIndependentInventory.Policy i := {
        eligible := fun a => if a.val == 0 then false else native.eligible a
        primitive := native.primitive }
      let prior : RingActiveDistanceSchedule.View i := fun _ => some none
      unless native.eligible a && !excluded.eligible a do
        throw (IO.userError "As supplied occurrence was not selected/excluded respectively")
      unless native.rule origin prior == some (some (paired h)) && excluded.rule origin prior == some none do
        throw (IO.userError "As supplied occurrence did not expose the expected nonempty inventory difference")
    else throw (IO.userError "As regression atom range is empty")
    IO.println s!"As mirror={reflected}: raw/nativeOracle, reversed queries, ties, repeats, invalid ID and nonempty supplied inventory witness passed"
end GlobalLigandComparison

def main : IO Unit := GlobalLigandComparison.audit
