import TetraStereo.OneCenter.LocalizedFamilyCertificate
import TetraStereo.Examples.LocalizedFamilyReferenceProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedFamilyCertificateAxesProbe
open OneCenter OneCenter.LocalizedShortCircuit

private def assertTest (name : String) (condition : Bool) : IO Unit := do
  if condition then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

private def runSource (source : AuthoritativeChemicalInput) :
    IO ((input : Input) × Families.Result input) := do
  let some result := Families.evaluateSource? source | throw (IO.userError "family admission failed")
  pure result

def main : IO Unit := do
  let startEven ← IO.monoMsNow
  let allene ← runSource LocalizedOmissionReadinessProbe.alleneSource
  let evenPayload := FamilyCertificate.exportPayload allene.2
  assertTest "even report retains canonical [4,5,6] axis and positive Ra"
    (decide (evenPayload.report.even = [([4, 5, 6], some .Ra)]))
  assertTest "even report retains shared tetrahedral R"
    (decide (evenPayload.report.tetrahedral = [(0, some (.chiral .R))]))
  assertTest "positive even-axis export accepted"
    (FamilyCertificate.check? allene.1 evenPayload).isSome
  let wrongEven : FamilyCertificate.Payload allene.1 :=
    { evenPayload with report := { evenPayload.report with even := [([6, 5, 4], some .Ra)] } }
  assertTest "reversed even-axis identifier rejected"
    (FamilyCertificate.check? allene.1 wrongEven).isNone
  let endEven ← IO.monoMsNow
  IO.println s!"TIMING even export/replay/mutation {endEven - startEven}ms"

  for cis in [false, true] do
    let startOdd ← IO.monoMsNow
    let odd ← runSource (LocalizedFamilyReferenceProbe.oddSource cis)
    let oddPayload := FamilyCertificate.exportPayload odd.2
    let expected : DoubleBondStereo := if cis then .Z else .E
    assertTest s!"odd report canonical [0,1,2,3], cis={cis}, expected={repr expected}"
      (decide (oddPayload.report.odd = [([0, 1, 2, 3], some expected)]))
    assertTest s!"positive odd-axis export accepted cis={cis}"
      (FamilyCertificate.check? odd.1 oddPayload).isSome
    let wrongOdd : FamilyCertificate.Payload odd.1 :=
      { oddPayload with report := { oddPayload.report with odd := [([0, 1, 3], some expected)] } }
    assertTest s!"truncated odd-axis identifier rejected cis={cis}"
      (FamilyCertificate.check? odd.1 wrongOdd).isNone
    let endOdd ← IO.monoMsNow
    IO.println s!"TIMING odd cis={cis} export/replay/mutation {endOdd - startOdd}ms"

  let startRing ← IO.monoMsNow
  let ring ← runSource LocalizedOmissionReadinessProbe.ringSource
  let ringPayload := FamilyCertificate.exportPayload ring.2
  assertTest "small-ring physical candidate [4,5] retained with none"
    (decide (ringPayload.report.monocyclic = [((4, 5), none)]))
  assertTest "small-ring omission report accepted"
    (FamilyCertificate.check? ring.1 ringPayload).isSome
  let missingRing : FamilyCertificate.Payload ring.1 :=
    { ringPayload with report := { ringPayload.report with monocyclic := [] } }
  assertTest "deleted small-ring candidate rejected"
    (FamilyCertificate.check? ring.1 missingRing).isNone
  let endRing ← IO.monoMsNow
  IO.println s!"TIMING small-ring export/replay/deletion {endRing - startRing}ms"

#eval main
end TetraStereo.Examples.LocalizedFamilyCertificateAxesProbe
