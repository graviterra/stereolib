import TetraStereo.OneCenter.LocalizedExtendedFamilyCertificate
import TetraStereo.Examples.LocalizedOrdinaryFamilyProbe
import TetraStereo.Examples.LocalizedFamilyReferenceProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedExtendedFamilyCertificateProbe
open OneCenter OneCenter.LocalizedExtendedShortCircuit
open Certificate.Dependency

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

private def runSource (source : AuthoritativeChemicalInput) : IO ((input : Input) × Families.Result input) := do
  let some result := Families.evaluateSource? source | throw (IO.userError "source admission failed")
  pure result

def main : IO Unit := do
  let start ← IO.monoMsNow
  let ordinary ← runSource (LocalizedOrdinaryFamilyProbe.ordinarySource true)
  let payload := FamilyCertificate.exportPayload ordinary.2
  checkTest "ordinary Z and refused monocyclic candidate both retained"
    (decide (payload.report.ordinaryAcyclic = [((0, 1), some (.alkene .Z))]) &&
     decide (payload.report.monocyclic = [((0, 1), none)]))
  checkTest "ordinary complete export accepted" (FamilyCertificate.check? ordinary.1 payload).isSome
  let some head := payload.auxiliaryNodes.head? | throw (IO.userError "nonempty auxiliary data required")
  let changed := { head with outcome := if head.outcome == some (.chiral .R) then some (.chiral .S) else some (.chiral .R) }
  checkTest "tampered auxiliary outcome rejected"
    (FamilyCertificate.check? ordinary.1 { payload with auxiliaryNodes := changed :: payload.auxiliaryNodes.tail }).isNone
  checkTest "incomplete auxiliary certificate rejected"
    (FamilyCertificate.check? ordinary.1 { payload with auxiliaryNodes := payload.auxiliaryNodes.tail }).isNone
  checkTest "duplicate auxiliary node rejected"
    (FamilyCertificate.check? ordinary.1 { payload with auxiliaryNodes := payload.auxiliaryNodes ++ [head] }).isNone
  checkTest "omitted refused monocyclic row rejected"
    (FamilyCertificate.check? ordinary.1 { payload with report := { payload.report with monocyclic := [] } }).isNone
  checkTest "extra monocyclic row rejected"
    (FamilyCertificate.check? ordinary.1 { payload with report := { payload.report with monocyclic := payload.report.monocyclic ++ payload.report.monocyclic } }).isNone
  checkTest "mutated ordinary E label rejected"
    (FamilyCertificate.check? ordinary.1 { payload with report := { payload.report with ordinaryAcyclic := [((0, 1), some (.alkene .E))] } }).isNone
  checkTest "sequence-cis remains distinct from ordinary Z"
    (FamilyCertificate.check? ordinary.1 { payload with report := { payload.report with ordinaryAcyclic := [((0, 1), some (.enantiomorphicDoubleBond .seqCis))] } }).isNone

  let allene ← runSource LocalizedOmissionReadinessProbe.alleneSource
  let even := FamilyCertificate.exportPayload allene.2
  checkTest "even canonical axis Ra and shared tetrahedral R exact"
    (decide (even.report.even = [([4, 5, 6], some .Ra)]) &&
     decide (even.report.tetrahedral = [(0, some (.chiral .R))]))
  checkTest "even positive export accepted" (FamilyCertificate.check? allene.1 even).isSome
  checkTest "reversed even axis identifier rejected"
    (FamilyCertificate.check? allene.1 { even with report := { even.report with even := [([6, 5, 4], some .Ra)] } }).isNone

  let odd ← runSource (LocalizedFamilyReferenceProbe.oddSource false)
  let axis := FamilyCertificate.exportPayload odd.2
  checkTest "odd canonical axis E exact" (decide (axis.report.odd = [([0, 1, 2, 3], some .E)]))
  checkTest "odd positive export accepted" (FamilyCertificate.check? odd.1 axis).isSome
  checkTest "odd label mutation rejected"
    (FamilyCertificate.check? odd.1 { axis with report := { axis.report with odd := [([0, 1, 2, 3], some .Z)] } }).isNone
  checkTest "swapped physical candidate order rejected"
    (FamilyCertificate.check? odd.1 { axis with report := { axis.report with monocyclic := axis.report.monocyclic.reverse } }).isNone

  let cyclic ← runSource (LocalizedPerceptionExecutableProbe.source true false)
  let boundary := FamilyCertificate.exportPayload cyclic.2
  checkTest "fully cyclic boundary identifier exact and open axes absent"
    (decide (boundary.report.cyclicBoundaries = [0]) && boundary.report.even.isEmpty && boundary.report.odd.isEmpty)
  checkTest "cyclic boundary export accepted" (FamilyCertificate.check? cyclic.1 boundary).isSome
  checkTest "omitted cyclic boundary rejected"
    (FamilyCertificate.check? cyclic.1 { boundary with report := { boundary.report with cyclicBoundaries := [] } }).isNone
  checkTest "extra cyclic boundary rejected"
    (FamilyCertificate.check? cyclic.1 { boundary with report := { boundary.report with cyclicBoundaries := [0, 0] } }).isNone
  checkTest "mutated cyclic boundary identifier rejected"
    (FamilyCertificate.check? cyclic.1 { boundary with report := { boundary.report with cyclicBoundaries := [1] } }).isNone
  let familyDone ← IO.monoMsNow
  IO.println s!"TIMING family export/replay/tamper: {familyDone - start}ms"

  let some input := admitSource? (LocalizedOrdinaryFamilyProbe.interactingSource false)
    | throw (IO.userError "callback-bearing source rejected")
  let cache := Cached.buildRuntimeCache input
  checkTest "callback-bearing input selects not-ready production fallback" cache.ready?.isNone
  let evaluation := Cached.referenceUsingCache input cache
  let labels := (report input evaluation.facts).map Prod.snd
  checkTest "fallback produces opposite chiral R/S auxiliary branches"
    (labels.length == 2 && decide (some (.chiral .R) ∈ labels) && decide (some (.chiral .S) ∈ labels))
  let some replayed := Cached.checkUsingCache? input cache evaluation.nodes
    | throw (IO.userError "fallback certificate replay rejected")
  checkTest "fallback complete certificate replay equals generated facts" (decide (replayed = evaluation.facts))
  let families := Families.ofEvaluation input evaluation
  checkTest "fallback ordinary output retains sequence-cis and actual Rule5 flags"
    (decide (families.ordinaryAcyclic.map (fun a => a.outcome.map fun outcome =>
      (outcome.outcome, outcome.left.selection.enantiomorphic, outcome.right.selection.enantiomorphic)) =
        [some (.enantiomorphicDoubleBond .seqCis, true, false)]))
  let finish ← IO.monoMsNow
  IO.println s!"TIMING callback-bearing fallback/replay/family: {finish - familyDone}ms"
  IO.println s!"TIMING total extended family certificate probe: {finish - start}ms"

#eval main
end TetraStereo.Examples.LocalizedExtendedFamilyCertificateProbe
