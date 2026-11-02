import TetraStereo.Examples.LocalizedRule3ShortCircuitOddProbe
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitFuelStability

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedRule3ExtendedFrameProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

/-- Compare every stored field without adding production equality instances. -/
private def keySame {input : CertifiedLocalizedCIPInput}
    (a b : input.LocalizedRerootRecursiveRule3SpatialKey) : Bool :=
  decide (a.constitutional.rule1a = b.constitutional.rule1a) &&
  decide (a.constitutional.rule1b = b.constitutional.rule1b) &&
  decide (a.constitutional.rule2 = b.constitutional.rule2) &&
  decide (a.constitutional.sourceNodes = b.constitutional.sourceNodes) &&
  decide (a.constitutional.complete = b.constitutional.complete) &&
  decide (a.observations = b.observations) && decide (a.rule3 = b.rule3)

private def keysSame {input : CertifiedLocalizedCIPInput}
    (a b : List input.LocalizedRerootRecursiveRule3SpatialKey) : Bool :=
  a.length == b.length && (a.zip b).all fun pair => keySame pair.1 pair.2

private def frameSame {input : CertifiedLocalizedCIPInput}
    (a b : input.LocalizedRule3CanonicalKeyFrame) : Bool :=
  keysSame a.rawKeys b.rawKeys && keysSame a.keys b.keys &&
    decide (a.coupled = b.coupled) && decide (a.excluded = b.excluded)

def main : IO Unit := do
  let start ← IO.monoMsNow
  let some input := admitSource? LocalizedRule3ShortCircuitOddProbe.source
    | throw (IO.userError "linked odd axes admission failed")
  let some _ready := input.certified.localizedExtendedRule3NoCallbackCertificate? (carrierFuel input)
    | throw (IO.userError "whole-carrier callback-free certificate refused")
  checkTest "entire finite carrier has checked empty extended callback requests" true
  let scanned ← IO.monoMsNow
  IO.println s!"TIMING whole-carrier readiness: {scanned - start}ms"
  let roots := (Families.canonicalDoubleBonds input).filter fun bond =>
    (bond.val.1.val == 0 && bond.val.2.val == 1) ||
    (bond.val.1.val == 4 && bond.val.2.val == 5)
  checkTest "exactly two linked-axis roots selected for full frames" (roots.length == 2)
  let budget := 2 * (carrierFuel input + 1) + 2
  for bond in roots do
    let before ← IO.monoMsNow
    let name := s!"frame root ({bond.val.1.val},{bond.val.2.val})"
    let occurrence := input.certified.localizedCanonicalDoubleBondFirstChildOccurrenceExec
      (carrierFuel input) bond
    let cursor : input.certified.LocalizedRerootCursor (carrierFuel input) := { occurrence }
    let target := OrdinaryPlanar.target input.certified (carrierFuel input) bond
    let view : input.certified.LocalizedDependencyView target := fun _ _ => none
    let some frame := input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view budget [cursor] | throw (IO.userError (name ++ " at structural bound refused"))
    checkTest (name ++ " positive complete two-pass frame at structural bound")
      (frame.rawKeys.length == 1 && frame.keys.length == 1)
    let some larger := input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view (budget + 7) [cursor] | throw (IO.userError (name ++ " larger budget refused"))
    checkTest (name ++ " every raw/rebuilt frame field stable at bound+7")
      (frameSame frame larger)
    let geometries := frame.keys.flatMap fun key =>
      key.observations.flatMap fun layer => layer.map fun entry => entry.2.unit.geometry
    checkTest (name ++ " full frame retains both actual axis geometries")
      (decide (.seqcis ∈ geometries) && decide (.seqtrans ∈ geometries))
    let after ← IO.monoMsNow
    IO.println s!"TIMING {name}: budget={budget}, {after - before}ms"
  let finish ← IO.monoMsNow
  IO.println s!"TIMING full linked-axis frames: {finish - start}ms"

#eval main
end TetraStereo.Examples.LocalizedRule3ExtendedFrameProbe
