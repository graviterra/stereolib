import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput

set_option autoImplicit false
set_option maxRecDepth 8192

/-! Executable full-report diagnostic on the small nine-atom cyclic input, following the
successful focused single-occurrence probes. No descriptor is assumed or inserted. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleReportProbe

open LocalizedChemicalRingCyclicExampleInput

/-- Explicit opt-in diagnostic; importing this module does not execute the expensive report. -/
def run : IO Unit := do
  let path : System.FilePath := "tmp/rings-chemical-fable-20261104/scratch/cyclic-report-probe.txt"
  IO.FS.writeFile path "starting actual distant-reference report\n"
  for center in [0, 2, 4] do
    let started ← IO.monoMsNow
    let result := LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol ops geom center
    let finished ← IO.monoMsNow
    IO.FS.withFile path .append fun stream =>
      stream.putStrLn s!"center {center} ({finished-started}ms): {repr result}"
  IO.println "Cyclic report probe finished; see progress file."

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleReportProbe
