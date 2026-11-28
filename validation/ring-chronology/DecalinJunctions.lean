import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.DecalinPublishedCoordinates

/-! Two complete raw evaluations at the published SDF coordinates. The fixed
coordinate theorem uses these two row equalities as its computational premises. -/
open TetraStereo.OneCenter TetraStereo.Engine
open TetraStereo.Examples.DecalinFrames (molecule)
open TetraStereo.Examples.DecalinPublishedCoordinates (vs211 vs212)

private theorem sparsePublic : RingSparseTwinReport.fromRaw? = ringMolecularReportFromRaw? :=
  RingSparseTwinReport.raw_exact

assert_kernel_only sparsePublic

def main (args : List String) : IO Unit := do
  let evaluate ← match args with
    | [] | ["--sparse"] => pure RingSparseTwinReport.fromRaw?
    | ["--direct"] => pure ringMolecularReportFromRaw?
    | _ => throw (IO.userError "usage: DecalinJunctions.lean [--sparse|--direct]")
  let mut allAgree := true
  for (name, xyz, label) in [("VS211",vs211,LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric .s),
      ("VS212",vs212,.pseudoasymmetric .r)] do
    let rows := evaluate molecule xyz [0,1]
    IO.println s!"{name} (raw atom ID, original/mirror) {repr rows}"
    (← IO.getStdout).flush
    let expected : RingGroupedReport.Report := [(0,some (label,label)),(1,some (label,label))]
    allAgree := allAgree && rows == some expected
  unless allAgree do
    throw (IO.userError "ring junction result differs from Blue Book P-93.5.4.1")
