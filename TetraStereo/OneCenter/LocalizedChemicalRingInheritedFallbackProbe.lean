import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input
import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput
import TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback

set_option autoImplicit false
set_option maxRecDepth 32768

/-! Executable comparison of the isolated inherited-refusal successor with the actual
double-C3 physical inputs. Initial states are empty; the candidate generates every
auxiliary fact itself. The exact child-reader substitution changes no comparison keys.
Printed outcomes and checks are executable evidence, not kernel theorems. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallbackProbe

open LocalizedChemicalRingDoubleC3Input

private def record (path : System.FilePath) (line : String) : IO Unit :=
  IO.FS.withFile path .append fun stream => stream.putStrLn line

@[noinline] private def materialize (input : CertifiedLocalizedCIPInput) :=
  input.localizedRerootCarrierCache
    (LocalizedMarkedRetainedMolecularSelection.retainedCarrierFuel input)

private def probe : IO Unit := do
  let stamp ← IO.monoMsNow
  let path : System.FilePath :=
    s!"tmp/rings-chemical-fable-20261104/scratch/inherited-fallback-probe-{stamp}.txt"
  IO.println s!"Experimental inherited-fallback probe: {path}"
  record path "Actual 25-atom inputs; empty initial states; isolated candidate, unchanged comparison operations."
  record path "starting accepted nine-atom report regression"
  let smallInput := LocalizedChemicalRingCyclicExampleInput.certified
  let smallCache := materialize smallInput
  let smallOps := LocalizedChemicalRingCachedOperations.operations smallInput smallCache
    LocalizedChemicalRingCyclicExampleInput.mol
  for center in [0, 2, 4] do
    let outcome := LocalizedChemicalRingInheritedFallback.assignCenter?
      LocalizedChemicalRingCyclicExampleInput.mol smallOps
      LocalizedChemicalRingCyclicExampleInput.geom center
    record path s!"nine-atom center {center}: {reprStr outcome}"
    let agrees := match outcome with
      | some (.pseudoasymmetric .s) => true
      | _ => false
    record path s!"matches accepted nine-atom result: {agrees}"
  for opposite in [true, false] do
    record path s!"=== opposite geometry = {opposite} ==="
    let cache := materialize (certified opposite)
    let slice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache cache (0 : Fin 25)
    record path s!"carrier/slice frames: {cache.frames.length}/{slice.frames.length}"
    let actual := LocalizedChemicalRingCachedOperations.operations (certified opposite) slice mol
    if opposite then
      record path "starting candidate local-reference auxiliary"
      let started ← IO.monoMsNow
      let auxiliary := LocalizedChemicalRingInheritedFallback.descriptor? mol actual 0
        (geom opposite) [] (some 4) leftCenter
      record path s!"candidate local-reference auxiliary: {reprStr auxiliary}"
      let ended ← IO.monoMsNow
      record path s!"elapsed auxiliary: {ended - started} ms"
    record path "starting candidate actual root assignment"
    let started ← IO.monoMsNow
    let outcome := LocalizedChemicalRingInheritedFallback.assignCenter? mol actual (geom opposite) 0
    record path s!"candidate actual root assignment: {reprStr outcome}"
    let ended ← IO.monoMsNow
    record path s!"elapsed root: {ended - started} ms"
    let agrees := if opposite then
      match outcome with
      | some (.pseudoasymmetric _) => true
      | _ => false
    else outcome.isNone
    record path s!"matches physical classification criterion: {agrees}"
  record path "COMPLETE"
  IO.println s!"Experimental inherited-fallback probe complete: {path}"

#eval probe

end TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallbackProbe
