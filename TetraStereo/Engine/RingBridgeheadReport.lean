import TetraStereo.Engine.RingSparseTwinReport

/-! The public raw kernel definition remains the reference. A molecule with a
selected pyramidal nitrogen uses the sphere store with proved first-shell decisions;
other requests retain the existing raw evaluation procedure. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBridgeheadReport
open OneCenter

private def hasPyramidalNitrogen (m : RawMolecule) : Bool :=
  m.atoms.zipIdx.any fun (atom,n) =>
    atom.element == .N && atom.charge == 0 && !atom.aromatic && (m.writtenNeighbors n).length == 3 &&
      RingPyramidalNitrogen.constrainedRaw m n

def fromRaw? (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :=
  if hasPyramidalNitrogen m then RingSparseTwinReport.fromRaw? m g ids
  else RingRawComparisonLift.fromRaw RingChemicalReport.report? m g ids

/-- This compiler rewrite covers every raw input, including inadmissible
ones, implicit-H preparations, arbitrary requested indices and refusals. -/
@[csimp] theorem public_raw : @RingHydrogenReport.fromRaw? = @fromRaw? := by
  have ordinary := RingRawComparisonLift.eq_native_of_admitted RingChemicalReport.report? (fun _ _ _ => rfl)
  funext m g ids
  simp only [fromRaw?, RingSparseTwinReport.raw_exact, ordinary, ite_self]

end TetraStereo.Engine.RingBridgeheadReport
assert_kernel_only TetraStereo.Engine.RingBridgeheadReport.public_raw
