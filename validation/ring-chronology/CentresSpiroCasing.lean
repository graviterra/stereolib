import TetraStereo.Engine.PublicAPI

open TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Engine.CentresRing
open TetraStereo.Examples.CentresRingSpiroCasing

assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.no_invariant_fidelity
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.no_mirror_fidelity
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.independent_scaffold_readings
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.actual_orders_follow_rings

assert_kernel_only TetraStereo.Engine.CentresRing.MirrorCasing.exists_source_mirror_violation

private def shape (l : Molecular.Layout) :=
  (l.root,l.discovered,l.passStarts,l.auxStarts)

private def validate (dir name : String) (live : Bool) (m : RawMolecule) (g : SpatialConfiguration)
    (layouts : List Molecular.Layout) (expected : List String) : IO Molecular.SourceReceipt := do
  let some input := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted input && inventory input == [0,1,2,3,4] do
    throw (IO.userError s!"{name}: coordinates or default inventory")
  let bytes ← IO.FS.readBinFile (dir ++ "/" ++ name ++ ".source.json")
  let some raw := String.fromUTF8? bytes | throw (IO.userError "invalid receipt encoding")
  let packet : Molecular.SourceReceipt ← IO.ofExcept ((Lean.Json.parse raw).bind Lean.fromJson?)
  if live then
    let observed ← IO.ofExcept (← Molecular.observe input)
    unless (Lean.toJson observed).compress.toUTF8 == bytes do
      throw (IO.userError s!"{name}: live source differs from receipt")
  let c ← IO.ofExcept (Molecular.checkSourceReceipt input packet)
  let some ls := c.molecular.replay.traces.mapM Molecular.layout | throw (IO.userError "layout")
  unless ls.map shape == layouts.map shape do throw (IO.userError s!"{name}: layout mismatch")
  unless c.molecular.replay.report.map (fun row => labelCode row.2) == expected do
    throw (IO.userError s!"{name}: source report mismatch")
  IO.println s!"{name}: {expected}, {c.observed.length} checked comparisons"
  return packet

private def testPair (dir name : String) (live : Bool) (m : RawMolecule) (g : SpatialConfiguration)
    (layouts : List Molecular.Layout) (source mirrorSource forward backward : List String) : IO Unit := do
  let a ← validate dir name live m g layouts source
  let b ← validate dir (name ++ "-mirror") live m (reflected g) layouts mirrorSource
  let some input := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "admission")
  let some other := LocalizedChemicalRing.admitRawSpatial? m (reflected g) | throw (IO.userError "mirror")
  let describe (r : LocalizedChemicalRing.Report) := r.map fun (i,d) => (i,labelCode d)
  let first ← IO.ofExcept (MirrorCasing.check input a b)
  let second ← IO.ofExcept (MirrorCasing.check other b a)
  unless describe first.report == (inventory input).zip forward &&
      describe second.report == (inventory other).zip backward do
    throw (IO.userError s!"{name}: reflected case mismatch")
  if (MirrorCasing.check input a a).isOk then throw (IO.userError "accepted original as mirror")
  if live then
    let actual ← IO.ofExcept (← MirrorCasing.analyze input)
    unless describe actual.report == describe first.report do throw (IO.userError "live mirror mismatch")
  IO.println s!"{name}: mirror convention {forward}, reflected {backward}"

def main (args : List String) : IO Unit := do
  let (dir,live) ← match args with
    | [d] => pure (d,false)
    | [d,"--live"] => pure (d,true)
    | _ => throw (IO.userError "usage: CentresSpiroCasing.lean RECEIPT_DIR [--live]")
  testPair dir "original" live molecule spatial originalLayouts
    ["S","R","S","R","S"] ["R","S","R","S","R"] ["S","R","S","R","S"] ["R","S","R","S","R"]
  testPair dir "renumbered" live renumbered moved renumberedLayouts
    ["R","R","S","s","S"] ["S","S","R","r","R"] ["R","R","S","S","S"] ["S","S","R","R","R"]
