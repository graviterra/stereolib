import TetraStereo.Engine.RingRecursiveSignedReport

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace TetraStereo.Examples.RingIncomingMethyl
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

/-- 2-cyclopropoxy-2-fluoropropane. The methyl at atom 0 roots the
digraph and its neighbor at atom 1 is the auxiliary focus. -/
private def molecule : RawMolecule :=
  match parseAndNormalizeOpenSMILESCertified "CC(C)(F)OC1CC1" [] with
  | .ok v => v.result.parsed.withExplicitHydrogens
  | .error _ => {atoms := [], bonds := []}

private def g : Geometry := fun i => some ⟨i,i*i,i*i*i⟩

theorem incoming_pair :
    (CursorTie.singlePair? molecule [0,1] 3 []).map
      (fun t => (t.left.node.history.reverse,t.right.node.history.reverse)) = some ([0],[0,1,2]) := by
  decide +kernel

/-- This is a completed structural refusal independent of coordinates.
The earlier recursive procedure cannot derive the same occurrence. -/
theorem recovered :
    (ReferenceDerivation.derive? molecule g 3 molecule.atomCount [0,1]).isNone = true ∧
    ((RecursiveSigned.derive? molecule g 3 molecule.atomCount [0,1]).map fun c =>
      match c.step with
      | .cursorTie es _ => some es.length
      | _ => none) = some (some 0) := by
  constructor <;> decide +kernel

end TetraStereo.Examples.RingIncomingMethyl

assert_kernel_only TetraStereo.Examples.RingIncomingMethyl.incoming_pair
assert_kernel_only TetraStereo.Examples.RingIncomingMethyl.recovered
