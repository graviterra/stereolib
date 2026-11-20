import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input
import TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations

set_option autoImplicit false
set_option maxRecDepth 32768

/-! Executable diagnostics on actual sparse operations and actual generated facts.
These observations are not kernel proofs. Each invocation writes a fresh progress file;
no initial auxiliary labels are supplied and no comparison callback is substituted. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Probe

open LocalizedChemicalRingDoubleC3Input
open LocalizedMarkedOperationEvaluator (underWith markedReading?)
open LocalizedPhysicalMarkedDistantEvaluator (facts descriptor? assignCenter?)
open LocalizedGenericMarkedRecalculation (structuralDepth readback?)
open LocalizedMarkedRetainedStateReader (factLabel)

private def record (path : System.FilePath) (line : String) : IO Unit :=
  IO.FS.withFile path .append fun stream => stream.putStrLn line

private def run {α : Type} [Repr α] (path : System.FilePath)
    (name : String) (f : Unit → α) : IO Unit := do
  record path s!"starting {name}"
  let started ← IO.monoMsNow
  record path s!"{name}: {reprStr (f ())}"
  let ended ← IO.monoMsNow
  record path s!"elapsed {name}: {ended - started} ms"

@[noinline] private def materialize (opposite : Bool) :=
  (certified opposite).localizedRerootCarrierCache
    (LocalizedMarkedRetainedMolecularSelection.retainedCarrierFuel (certified opposite))

private def probe : IO Unit := do
  let stamp ← IO.monoMsNow
  let path : System.FilePath := s!"tmp/rings-chemical-fable-20261104/scratch/double-c3-probe-{stamp}.txt"
  IO.println s!"Double-C3 actual probe: {path}"
  record path "Input: 25 atoms, detected centers 0, 3, 14; empty initial auxiliary state."
  for opposite in [true, false] do
    record path s!"=== opposite geometry = {opposite} ==="
    record path "materializing exact carrier cache"
    let cache := materialize opposite
    record path s!"carrier frames: {cache.frames.length}"
    let slice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache cache (0 : Fin 25)
    record path s!"root slice frames: {slice.frames.length}"
    let actual := LocalizedChemicalRingCachedOperations.operations (certified opposite) slice mol
    run path "ordinary root" (fun _ => actual.ordinary [] root)
    run path "ordinary left auxiliary" (fun _ => actual.ordinary [] leftCenter)
    run path "root frame geometry" (fun _ => readback? (geom opposite) [1, 2, 4, 15])
    run path "left frame geometry" (fun _ => readback? (geom opposite) [4, 5, 6, 7])
    run path "right frame geometry" (fun _ => readback? (geom opposite) [15, 16, 17, 18])
    run path "left local reference4 depth0" (fun _ =>
      descriptor? mol actual 0 (geom opposite) [] (some 4) leftCenter)
    run path "left distant reference15 depth0" (fun _ =>
      descriptor? mol actual 0 (geom opposite) [] (some 15) leftCenter)
    run path "right distant reference4 depth0" (fun _ =>
      descriptor? mol actual 0 (geom opposite) [] (some 4) rightCenter)
    for mark in [4, 15] do
      record path s!"starting actual root snapshot, reference {mark}"
      let generated : OccurrenceAuxState := underWith mol actual (geom opposite) [] root
        (facts mol actual (structuralDepth mol root)) mark
      record path s!"generated reference {mark}: {reprStr (generated.map fun f => (f.key.history, factLabel f))}"
      run path s!"root marked reading reference {mark}" (fun _ =>
        markedReading? mol actual (geom opposite) generated root mark)
    run path "actual root assignment" (fun _ => assignCenter? mol actual (geom opposite) 0)
  record path "COMPLETE"
  IO.println s!"Double-C3 probe complete: {path}"

#eval probe

end TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Probe
