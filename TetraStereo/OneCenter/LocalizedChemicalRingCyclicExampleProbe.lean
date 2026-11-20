import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput

set_option autoImplicit false
set_option maxRecDepth 8192

/-! Focused executable diagnostics of the actual retained comparator on the nine-atom ring.
These observations are not kernel proofs of descriptors. No auxiliary labels are supplied. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleProbe

open LocalizedChemicalRingCyclicExampleInput

private def progress : System.FilePath := "tmp/rings-chemical-fable-20261104/scratch/cyclic-probe.txt"

private def record (line : String) : IO Unit :=
  IO.FS.withFile progress .append fun stream => stream.putStrLn line

#eval do
  IO.FS.writeFile progress "starting actual ordinary root\n"
  let start ← IO.monoMsNow
  let ordinary := ops.ordinary [] root
  let elapsed ← IO.monoMsNow
  record s!"ordinary root {elapsed-start}ms: {repr ordinary}"
  record "starting actual ordinary arm2"
  let armOrdinary := ops.ordinary [] arm2
  record s!"ordinary arm2: {repr armOrdinary}"
  record "starting actual marked arm2 with reference4"
  let armMarked := ops.marked [] arm2 4
  record s!"marked arm2 reference4: {repr armMarked}"
  record "starting depth0 descriptor arm2 with reference4"
  let d := LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol ops 0 geom [] (some 4) arm2
  record s!"depth0 descriptor arm2: {repr d}"
  IO.println "Cyclic focused probe finished; see progress file."

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleProbe
