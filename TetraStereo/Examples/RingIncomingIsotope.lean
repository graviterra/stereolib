import TetraStereo.Engine.RingRecursiveSigned

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace TetraStereo.Examples.RingIncomingIsotope
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

/-- A 2-cyclopropoxy-2-fluoropropane with the methyl at index 0 labelled
carbon-13. At the auxiliary carbon 1, that methyl is the incoming ligand. -/
private def molecule : RawMolecule :=
  match parseAndNormalizeOpenSMILESCertified "[13CH3]C(C)(F)OC1CC1" [] with
  | .ok v => v.result.parsed.withExplicitHydrogens
  | .error _ => {atoms := [], bonds := []}

/-- A regular tetrahedron at the tested carbon, with the focus at its
barycenter. The constitutional assignment only reads these four neighbors. -/
private def geometry : Geometry
  | 0 => some ⟨-1,1,-1⟩
  | 1 => some ⟨0,0,0⟩
  | 2 => some ⟨-1,-1,1⟩
  | 3 => some ⟨1,1,1⟩
  | 4 => some ⟨1,-1,-1⟩
  | n => some ⟨n,n*n,n*n*n⟩

private def decidingMasses := (CursorMass.rank? molecule [0,1] 3).map fun r =>
  (r.split.heavy.node.history.reverse,r.split.light.node.history.reverse,r.split.heavyMass,r.split.lightMass)

theorem exact_sites : decidingMasses = some ([0],[0,1,2],13003354835340,12011000000000) := by
  decide +kernel

theorem strict_order : (CursorMass.rank? molecule [0,1] 3).map (·.order) = some [3,4,0,2] := by
  decide +kernel

private def recursiveHand (g : Geometry) := do
  let c ← RecursiveSigned.derive? molecule g 3 molecule.atomCount [0,1]
  match c.step with
  | .cursorMass _ r _ => r.label
  | _ => none

/-- The order is F, O, ¹³C, ordinary C. Each coordinate set receives
an uppercase constitutional descriptor from the recursive entry point. -/
theorem actual_and_reflected :
    recursiveHand geometry = some (.chiral .S) ∧
    recursiveHand (mirror geometry) = some (.chiral .R) := by
  constructor <;> decide +kernel

theorem previously_unresolved :
    (IsotopePriority.rank? molecule [0,1]).isNone = true ∧
    (ReferenceDerivation.derive? molecule geometry 3 molecule.atomCount [0,1]).isNone = true := by
  constructor <;> decide +kernel

end TetraStereo.Examples.RingIncomingIsotope

assert_kernel_only TetraStereo.Examples.RingIncomingIsotope.exact_sites
assert_kernel_only TetraStereo.Examples.RingIncomingIsotope.strict_order
assert_kernel_only TetraStereo.Examples.RingIncomingIsotope.actual_and_reflected
assert_kernel_only TetraStereo.Examples.RingIncomingIsotope.previously_unresolved
