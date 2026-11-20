import TetraStereo.OneCenter.LocalizedPhysicalMarkedCorrectnessProbe
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# Executable distant-reference check with the equivalent sparse backend

The fixture, coordinates, ordinary callback, reference policy and comparison meaning are
unchanged. The theorem below transfers any sparse result to the dense operations. The diagnostics
are executions, not kernel proofs of their outputs or a whole generated-state computation.
The empty state and zero depth are explicit; no desired auxiliary labels are inserted.
-/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedCorrectnessSparseProbe

open LocalizedPhysicalMarkedCorrectnessProbe LocalizedMarkedOperationEvaluator

def sparseOps : Operations :=
  LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations certified mol

theorem operations_agree : sparseOps = actualOperations :=
  LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations_eq certified mol

#eval do
  IO.println s!"direct distant reference: {repr (markedReading? mol sparseOps geom [] far 6)}"
  IO.println s!"raw inherited reference: {repr (rawStep? mol sparseOps geom [] (some 6) far (fun _ => []))}"
  IO.println s!"reflected raw inherited reference: {repr (rawStep? mol sparseOps (LocalizedGenericMarkedRecalculation.mirror geom) [] (some 6) far (fun _ => []))}"
  IO.println s!"depth-zero descriptor: {repr (descriptor? mol sparseOps 0 geom [] (some 6) far)}"

end TetraStereo.OneCenter.LocalizedPhysicalMarkedCorrectnessSparseProbe

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedCorrectnessSparseProbe.operations_agree
