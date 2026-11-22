import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.LocalizedChemicalRingSpiroProjection
import TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime

open TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Engine.CentresRing
open TetraStereo.Examples.CentresRingSpiroCasing

private structure Row where
  atom : Nat
  source : String
  chemical : String
  calls : Nat
  updates : Nat
  deriving BEq, Repr

private def reports {m g} {ts : List CenterTrace} :
    ComparisonAgreement.Each (ComparisonAgreement.Diagnosis m g) ts →
      List Row
  | .nil => []
  | .cons (x := t) d ds =>
    ⟨t.atom,t.label,d.chemicalCode,d.replay.derived.calls.length,t.updates.length⟩ :: reports ds

private def checkFile (dir name : String) (m : RawMolecule) (s : SpatialConfiguration)
    (source chemical : List String) (root rootCalls allCalls : Nat) (live : Bool) : IO Unit := do
  let some input := LocalizedChemicalRing.admitRawSpatial? m s | throw (IO.userError "admission")
  let bytes ← IO.FS.readBinFile (dir ++ "/" ++ name ++ ".source.json")
  let some raw := String.fromUTF8? bytes | throw (IO.userError "receipt encoding")
  let packet : Molecular.SourceReceipt ← IO.ofExcept ((Lean.Json.parse raw).bind Lean.fromJson?)
  if live then
    let actual ← IO.ofExcept (← Molecular.observe input)
    unless (Lean.toJson actual).compress.toUTF8 == bytes do throw (IO.userError "live receipt differs")
  let result ← IO.ofExcept (ComparisonAgreement.diagnoseSource input packet 2)
  unless (ComparisonAgreement.requireAgreement result.centers).isSome == (source == chemical) do
    throw (IO.userError s!"{name}: exact report agreement")
  let rows := reports result.centers
  unless rows.map Row.atom == inventory input && rows.map Row.source == source &&
      rows.map Row.chemical == chemical && (rows.map Row.calls).sum == allCalls &&
      (rows.map Row.updates).sum == 8 &&
      (rows.find? (fun r => r.atom == root)).map (fun r => (r.calls,r.updates)) == some (rootCalls,8) do
    throw (IO.userError s!"{name}: {repr rows}")
  IO.println s!"{name}: {repr rows}"

private def published (file : String) (live : Bool) : IO Unit := do
  let s := TetraStereo.Examples.LocalizedChemicalRingSpiroProjection.spatial
  let some input := LocalizedChemicalRing.admitRawSpatial? SpiroSource.molecule s | throw (IO.userError "admission")
  let packet : Molecular.SourceReceipt ← IO.ofExcept ((Lean.Json.parse (← IO.FS.readFile file)).bind Lean.fromJson?)
  if live then
    let observed ← IO.ofExcept (← Molecular.observe input [0])
    unless Lean.toJson observed == Lean.toJson packet do throw (IO.userError "published receipt differs")
  let result ← IO.ofExcept (ComparisonAgreement.diagnoseSource input packet 2 [0])
  let rows := reports result.centers
  unless rows == [⟨0,"R","R",19,0⟩] && (ComparisonAgreement.requireAgreement result.centers).isSome do
    throw (IO.userError s!"published annotated center: {repr rows}")
  IO.println s!"published dioxaspiro: {repr rows}"

open TetraStereo.Examples in
private def fullInventory (dir : String) : IO Unit := do
  for (name,smiles,spatial,expected,calls,updates) in [
      ("spiro",LocalizedChemicalRingSpiroProjection.smiles,LocalizedChemicalRingSpiroProjection.spatial,
        [(0,"R"),(2,"-"),(3,"-"),(4,"-"),(6,"-"),(7,"-"),(8,"-")],790,120),
      ("propellane",LocalizedChemicalRingPropellaneLifetime.smiles,LocalizedChemicalRingPropellaneLifetime.spatial,
        [(0,"-"),(1,"-"),(2,"-"),(3,"-"),(4,"-")],585,92)] do
    let .ok (some input) := LocalizedChemicalRing.admitSmilesSpatial? smiles spatial
      | throw (IO.userError s!"{name}: admission failed")
    let data ← IO.FS.readFile (dir ++ "/" ++ name ++ ".source.json")
    let packet : Molecular.SourceReceipt ← IO.ofExcept ((Lean.Json.parse data).bind Lean.fromJson?)
    let d ← IO.ofExcept (ComparisonAgreement.diagnoseSource input packet 3)
    let rows := reports d.centers
    unless (ComparisonAgreement.requireAgreement d.centers).isSome &&
        rows.map (fun r => (r.atom,r.chemical)) == expected &&
        (rows.map Row.calls).sum == calls && (rows.map Row.updates).sum == updates do
      throw (IO.userError s!"{name}: {repr rows}")
    IO.println s!"{name}: {repr rows}"

def main (args : List String) : IO Unit := do
  if let ["--full",d] := args then return ← fullInventory d
  let (dir,file,live) ← match args with
    | [d,f] => pure (d,f,false)
    | [d,f,"--live"] => pure (d,f,true)
    | _ => throw (IO.userError "expected a fluorospiro receipt directory, published spiro receipt and optional --live")
  checkFile dir "original" molecule spatial ["S","R","S","R","S"] ["S","R","S","R","S"] 0 39 55 live
  checkFile dir "renumbered" renumbered moved ["R","R","S","s","S"] ["R","R","S","S","S"] 3 39 55 live
  checkFile dir "original-mirror" molecule (reflected spatial) ["R","S","R","S","R"] ["R","S","R","S","R"] 0 38 54 live
  checkFile dir "renumbered-mirror" renumbered (reflected moved) ["S","S","R","r","R"] ["S","S","R","R","R"] 3 36 52 live
  published file live
