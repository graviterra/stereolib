import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.RingPhosphaneOxiraneReport

/-! Exhaust the coordinate representatives in `universal_reports_iff` through the
raw public evaluator. A failed or mismatching row fails the replay. -/
open TetraStereo TetraStereo.OneCenter TetraStereo.Engine
open RingHydrogenSpelling.PhosphaneOxirane

theorem phosphaneOxiranePublicAPI (x : SpatialConfiguration) (ids : List Nat) :
    ringMolecularReportFromRaw? molecule x ids = expectedReport x ids := public_exact x ids

assert_kernel_only phosphaneOxiranePublicAPI

def main : IO Unit := do
  let ids := List.range 11
  for c in [RS.R, RS.S] do
    for l in [none, some RS.R, some RS.S] do
      for r in [none, some RS.R, some RS.S] do
        let x := Representatives.representative c l r
        let expected := some (ids.map fun n => (n, labels c l r n))
        let actual := ringMolecularReportFromRaw? molecule x ids
        unless actual == expected do
          throw (IO.userError s!"C0={repr c}, P1={repr l}, P2={repr r}: got {repr actual}, expected {repr expected}")
        IO.println s!"C0={repr c}, P1={repr l}, P2={repr r}: all eleven public rows match."
