import TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantPreservation
import TetraStereo.OneCenter.LocalizedPhysicalMarkedCorrectnessProbe
import TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantCache

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# Focused actual-backend distant-reference diagnostic

Compute the ordinary partition and one marked ranking exactly once, then read that ranking in
the original and reflected coordinates. No supplied auxiliary labels and no whole-state run.
The progress file retains completed stages if a later computation is interrupted. These are
execution diagnostics, not kernel proofs of their results or chemical sufficiency.
-/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantProbe

open LocalizedPhysicalMarkedCorrectnessProbe
open LocalizedGenericMarkedRecalculation (frameAtoms? rankedAtoms? readback? mirror)

def ops : LocalizedMarkedOperationEvaluator.Operations :=
  LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations certified mol

theorem operations_agree : ops = actualOperations :=
  LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations_eq certified mol

private def progressPath : System.FilePath :=
  "tmp/rings-physical-20261102/distant-probe-progress.txt"

private def appendProgress (text : String) : IO Unit :=
  IO.FS.withFile progressPath .append fun handle => handle.putStr text

#eval do
  IO.FS.writeFile progressPath "starting ordinary partition\n"
  let started ← IO.monoMsNow
  let ordinary := ops.ordinary [] far
  let ordinaryEnd ← IO.monoMsNow
  appendProgress s!"ordinary ({ordinaryEnd - started} ms): {repr ordinary}\nstarting distant marked ranking\n"
  let ranking := ops.marked [] far 6
  let markedEnd ← IO.monoMsNow
  appendProgress s!"marked ({markedEnd - ordinaryEnd} ms): {repr ranking}\n"
  let reading := do
    let atoms ← frameAtoms? mol far
    let r ← ranking
    let ordered ← rankedAtoms? atoms r
    readback? geom ordered
  let reflected := do
    let atoms ← frameAtoms? mol far
    let r ← ranking
    let ordered ← rankedAtoms? atoms r
    readback? (mirror geom) ordered
  let summary := s!"direct distant reference: {repr reading}\nreflected direct reference: {repr reflected}\n"
  appendProgress summary
  IO.println summary
  let cached := LocalizedPhysicalMarkedDistantCache.withPointCache ops [] far 6 ordinary ranking
  let raw := LocalizedPhysicalMarkedDistantReference.rawStep? mol cached geom [] (some 6) far
    (fun _ => [])
  let rawMirror := LocalizedPhysicalMarkedDistantReference.rawStep? mol cached (mirror geom) []
    (some 6) far (fun _ => [])
  let result := s!"successor raw step: {repr raw}\nreflected successor raw step: {repr rawMirror}\n"
  appendProgress result
  IO.println result

end TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantProbe

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantProbe.operations_agree
