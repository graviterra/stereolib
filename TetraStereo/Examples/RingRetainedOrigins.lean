import TetraStereo.Engine.RingComparisonAgreement
import TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option Elab.async false

namespace TetraStereo.Examples.RingRetainedOrigins
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

private abbrev propellane := LocalizedChemicalRingPropellaneLifetime.parsedMol
private def geometry (i : Nat) := LocalizedChemicalRingPropellaneLifetime.spatial.positions[i]?

private def atClosure (i : Nat) : Option (List Nat × Nat × Nat) := do
  let p := [2,1,3,0]
  let focus ← occurrence? propellane p
  let c ← (occurrenceLigandCursors propellane focus).find? (fun node => node.node.atom == i)
  let a ← DuplicatePriority.ancestorOrigin? propellane p c
  return (a.origin.history.reverse,a.depth,IsotopePriority.pathDistance p a.origin.history.reverse)

/-- The actual two terminal copies point to different ancestors of this
bridgehead path. Measuring from the auxiliary site reverses their order. -/
theorem opposite_distances : atClosure 2 = some ([2],0,3) ∧ atClosure 1 = some ([2,1],1,2) := by
  constructor <;> decide +kernel

def comparison (m : RawMolecule) (p : List Nat) (i j : Nat) :=
  (IsotopePriority.compareIncident? m p i j).map fun c => (c.ordering,c.rule?)

theorem bridgehead_comparison : comparison propellane [2,1,3,0] 2 1 =
    some (.gt,some (.duplicateOrigin 1)) := by decide +kernel

private def reading (g : Geometry) (p : List Nat) :=
  (ReferenceDerivation.derive? propellane g 3 4 p).map
    (fun c => CentresRing.labelCode (c.verdict.bind Recursive.Reading.label))

/-- The constitutional closure decision yields an absolute auxiliary hand
at this occurrence on both geometries. -/
theorem bridgehead_auxiliary : reading geometry [2,1,3,0] = some "S" ∧
    reading (mirror geometry) [2,1,3,0] = some "R" := by
  constructor <;> decide +kernel

private def parsed (s : String) : RawMolecule :=
  match parseAndNormalizeOpenSMILESCertified s [] with
  | .ok v => v.result.parsed.withExplicitHydrogens
  | .error _ => {atoms := [], bonds := []}

/-- The two cyclobutyl ligands in the release's example 115 close at
equal distance from the auxiliary focus. On the original digraph their
real origins are in different spheres, first deciding in sphere V. -/
theorem remote_closures :
    comparison (parsed "O[C@@H]([C@H]1C[C@@H](C1)O)[C@@H]2C[C@@H](C2)O") [2,1] 2 7 =
      some (.gt,some (.duplicateOrigin 5)) := by decide +kernel

/-- Opposite SMILES parity flags survive intake. The two complete arms
in myo-inositol still tie through isotopic mass before stereochemistry. -/
theorem inositol_constitution :
    let m := parsed "O[C@H]1[C@H](O)[C@@H](O)[C@H](O)[C@H](O)[C@@H]1O"
    (m.atoms[2]?).bind AtomSpec.tetrahedral? ≠ (m.atoms[10]?).bind AtomSpec.tetrahedral? ∧
    comparison m [1] 2 10 = some (.eq,none) := by decide +kernel

end TetraStereo.Examples.RingRetainedOrigins

assert_kernel_only TetraStereo.Examples.RingRetainedOrigins.opposite_distances
assert_kernel_only TetraStereo.Examples.RingRetainedOrigins.bridgehead_comparison
assert_kernel_only TetraStereo.Examples.RingRetainedOrigins.bridgehead_auxiliary
assert_kernel_only TetraStereo.Examples.RingRetainedOrigins.remote_closures
assert_kernel_only TetraStereo.Examples.RingRetainedOrigins.inositol_constitution
