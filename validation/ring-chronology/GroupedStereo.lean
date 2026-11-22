import TetraStereo.Examples.RingRetainedUnitControl

open TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Examples

/-- The four addressed labels in this check are derived from the molecular
schedule and coordinates. Exchanging two coordinates moves the deciding rule
from fixed Rule 5 to Rule 4b in the published reference matrix. -/
private def scheduled (i : LocalizedChemicalRing.Input) (control : Bool) : IO Unit := do
  let sites := (RingActiveDistanceSchedule.sites i).filter fun q =>
    q.val.root.val == 0 && q.val.node.provenance == .realAtom
  let findSite (path : List Nat) : IO (RingActivePairs.Site i) := do
    let some q := sites.find? (fun q => q.val.node.history.map Fin.val == path)
      | throw (IO.userError s!"missing scheduled occurrence {path}")
    return q
  let f ← findSite [0]
  let a ← findSite [3,0]
  let b ← findSite [5,0]
  let got := RingGroupedStereo.scheduledComparison? i f.val.root f a b
  let expected : RingRetainedStereoDecision.Result × RingRetainedStereoDecision.Result :=
    if control then (⟨some .likePair,-1⟩,⟨some .likePair,-1⟩)
    else (⟨some .fixedPair,2⟩,⟨some .fixedPair,-2⟩)
  unless got == some expected do throw (IO.userError s!"expected {repr expected}, obtained {repr got}")
  IO.println s!"17-atom coordinate control {control}: {repr expected}"

def main (args : List String) : IO Unit := do
  unless args == [] || args == ["--scheduled"] || args == ["--frozen"] do
    throw (IO.userError "expected --scheduled, --frozen, or no arguments to run both")
  unless args == ["--frozen"] do
    for control in [false,true] do scheduled (RingPairedAuxiliary.input control) control
  unless args == ["--scheduled"] do
    RingRetainedUnitControl.verify
    IO.println "Verified signed comparisons on the controlled 31-atom ring and its matched-sibling variant."
