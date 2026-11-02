import TetraStereo.OneCenter.LocalizedShortCircuitDescriptor
import TetraStereo.Examples.LocalizedDieneReferenceProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedShortCircuitDescriptorProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedReference

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

/-- This test uses an empty dependency view; the whole-carrier fixed point is tested separately. -/
def main : IO Unit := do
  let some input := admitSource? LocalizedDieneReferenceProbe.dieneSource
    | throw (IO.userError "diene admission failed")
  let some center := input.certified.canonicalTetrahedralCenters.find?
    (fun c => c.val.val == 0) | throw (IO.userError "central candidate absent")
  let target := input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center
  let descriptor := input.certified.localizedOccurrenceShortCircuitRule3Through5Descriptor?
    target (fun _ _ => none)
  IO.println s!"diene short-circuit descriptor under empty view: {repr descriptor}"
  checkAssertion "full-budget short-circuit descriptor is R"
    (decide (descriptor = some (.chiral .R)))
  let some base := input.certified.localizedNoDoubleFourLigandFrameExec? target
    | throw (IO.userError "four-ligand frame absent")
  let frame := input.certified.buildLocalizedShortCircuitRule3FrameExec?
    target (fun _ _ => none) 32 base.cursors
  checkAssertion "complete four-ligand Rule3 frame succeeds at nested fuel 32" frame.isSome

#eval main
end TetraStereo.Examples.LocalizedShortCircuitDescriptorProbe
