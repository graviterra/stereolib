import TetraStereo.Engine.CentresSpiroSource
import TetraStereo.Examples.LocalizedChemicalRingSpiroProjection

namespace TetraStereo.Examples.CentresSpiroSource
open OneCenter Engine Engine.CentresRing
open Engine.CentresRing.SpiroSource
open OneCenter.LocalizedGenericMarkedRecalculation (mirror)

private def unmarked : Trial := ⟨none, [4,8,1,5],
  [⟨4,8,0⟩,⟨8,1,-1⟩,⟨4,1,-1⟩,⟨8,5,-1⟩,⟨4,5,-1⟩,⟨1,5,0⟩]⟩

private def promoted : Trial := ⟨some 5, [1,5,4,8], [⟨1,5,-1⟩,⟨1,4,1⟩,⟨4,8,-1⟩,⟨1,8,1⟩]⟩
private def classes : List Comparison := [⟨1,5,0⟩,⟨5,4,1⟩,⟨4,8,0⟩]

def recorded : CenterTrace :=
  ⟨[],[],0,[⟨none,[unmarked],[]⟩,⟨none,[unmarked,promoted],classes⟩],"R"⟩

theorem published_comparisons : checkComparisons recorded = some 5 ∧ recorded.comparisons.length = 19 := by
  decide +kernel

def geometry : LocalizedGenericMarkedRecalculation.Geometry :=
  fun i => LocalizedChemicalRingSpiroProjection.spatial.positions[i]?

theorem independent_letters :
    sourceLetter geometry 1 = some (.chiral .R) ∧ sourceLetter geometry 5 = some (.chiral .R) ∧
    sourceLetter (mirror geometry) 1 = some (.chiral .S) ∧
    sourceLetter (mirror geometry) 5 = some (.chiral .S) := by
  decide +kernel

/-- This changes a same-element tie to a strict comparison *only in grouping*.
Use a unit-to-double change within the promoted sort as a separate casing control. -/
private def fakeTie : CenterTrace :=
  { recorded with passes := [⟨none,[unmarked],[]⟩,
      ⟨none,[unmarked,promoted],[⟨1,5,1⟩,⟨5,4,1⟩,⟨4,8,0⟩]⟩] }

private def fakeMagnitude : CenterTrace :=
  let alt := { promoted with comparisons := [⟨1,5,-2⟩,⟨1,4,1⟩,⟨4,8,-1⟩,⟨1,8,1⟩] }
  {recorded with passes := [⟨none,[unmarked],[]⟩,⟨none,[unmarked,alt],classes⟩],label := "r"}

theorem counterfactuals : checkComparisons fakeTie = none ∧ checkComparisons fakeMagnitude = none ∧
    (do let rank ← finalRankingOn molecule geometry [0] fakeMagnitude
        readRanking geometry rank).toOption = some (some (.pseudoasymmetric .r)) := by
  decide +kernel

end TetraStereo.Examples.CentresSpiroSource
assert_kernel_only TetraStereo.Examples.CentresSpiroSource.published_comparisons
assert_kernel_only TetraStereo.Examples.CentresSpiroSource.independent_letters
assert_kernel_only TetraStereo.Examples.CentresSpiroSource.counterfactuals

open TetraStereo.Examples.CentresSpiroSource TetraStereo.Examples TetraStereo.Engine
def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "supply the exported annotated spiro receipt")
  let packet : CentresRing.Receipt ← IO.ofExcept ((Lean.Json.parse (← IO.FS.readFile file)).bind Lean.fromJson?)
  unless Lean.toJson packet.traces == Lean.toJson [recorded] do throw (IO.userError "receipt differs from kernel fixture")
  let .ok (some input) := LocalizedChemicalRing.admitSmilesSpatial? LocalizedChemicalRingSpiroProjection.smiles
    LocalizedChemicalRingSpiroProjection.spatial | throw (IO.userError "spiro intake")
  let checked ← IO.ofExcept (CentresRing.SpiroSource.check input packet)
  unless checked.choice == 5 && checked.replay.report == [(0,some (.chiral .R))] do throw (IO.userError "source result")
  IO.println "19 molecular comparison values checked against the archived receipt. Source descriptor R."
