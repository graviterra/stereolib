import TetraStereo.Engine.CentresSpiroSource
import TetraStereo.Engine.CentresRingMirror

open TetraStereo.OneCenter TetraStereo.Engine Lean

private def coord (j : Json) : Except String ℚ := do
  let n ← j.getNum?
  return (n.mantissa : ℚ) / 10 ^ n.exponent

private def point (j : Json) : Except String CartesianPoint3 := do
  let #[x,y,z] ← j.getArr? | throw "each position needs three coordinates"
  return ⟨← coord x, ← coord y, ← coord z⟩

private def parseInput (s : String) : Except String (LocalizedChemicalRing.Input × List Nat) := do
  let j ← Json.parse s
  let smiles ← (← j.getObjVal? "smiles").getStr?
  let positions ← (← (← j.getObjVal? "positions").getArr?).toList.mapM point
  let some input ← LocalizedChemicalRing.admitSmilesSpatial? smiles ⟨positions⟩
    | throw "molecule failed baseline domain admission"
  let requested ← match j.getObjVal? "centers" with
    | .ok v => fromJson? v
    | .error _ => pure (CentresRing.inventory input)
  return (input,requested)

private def printReport (profile : String) (report : LocalizedChemicalRing.Report) : IO Unit := do
  let rows := report.map fun (atom,label) =>
    Json.mkObj [("atom",toJson atom),("descriptor",if label.isNone then Json.null else toJson (CentresRing.labelCode label))]
  IO.println (Json.mkObj [("profile",toJson profile),("entries",toJson rows)]).compress

private def sourceReceipt (path : String) : IO CentresRing.Molecular.SourceReceipt := do
  IO.ofExcept ((Json.parse (← IO.FS.readFile path)).bind fromJson?)

private def usage := "usage: analyze.lean input.json " ++
  "[--mirror | --verify-mirror original.json reflected.json | " ++
  "(--save | --save-molecular | --verify-rule-prefixes | --verify | --verify-molecular | " ++
  "--verify-spiro-source) receipt.json]"

def main (args : List String) : IO Unit := do
  let file :: mode := args | throw (IO.userError usage)
  let (input,centers) ← IO.ofExcept (parseInput (← IO.FS.readFile file))
  if mode == ["--mirror"] then
    let r ← IO.ofExcept (← CentresRing.MirrorCasing.analyze input centers)
    return ← printReport "centres-1.0-mirror-casing" r.report
  if let ["--verify-mirror",original,reflected] := mode then
    let r ← IO.ofExcept (CentresRing.MirrorCasing.check input (← sourceReceipt original)
      (← sourceReceipt reflected) centers)
    return ← printReport "centres-1.0-mirror-casing" r.report
  let result ← match mode with
    | [] => IO.ofExcept (← CentresRing.analyze input centers)
    | ["--save",path] => do
      let r ← IO.ofExcept (← CentresRing.analyze input centers)
      let packet ← IO.ofExcept r.receipt
      let out ← IO.FS.Handle.mk path .writeNew
      out.putStrLn (toJson packet).compress
      pure r
    | ["--verify-spiro-source",path] => do
      if h : centers = [0] then
        let content ← IO.FS.readFile path
        let packet ← IO.ofExcept ((Json.parse content).bind fromJson?)
        let checked ← IO.ofExcept (CentresRing.SpiroSource.check input packet)
        pure (h.symm ▸ checked.replay)
      else throw (IO.userError "source check requires the single annotated spiro configuration [0]")
    | ["--save-molecular",path] => do
      let packet ← IO.ofExcept (← CentresRing.Molecular.observe input centers)
      let evidence ← IO.ofExcept (CentresRing.Molecular.checkSourceReceipt input packet centers)
      let out ← IO.FS.Handle.mk path .writeNew
      out.putStrLn (toJson packet).compress
      pure evidence.molecular.replay
    | ["--verify-rule-prefixes",path] => do
      let content ← IO.FS.readFile path
      let packet ← IO.ofExcept ((Json.parse content).bind fromJson?)
      let evidence ← IO.ofExcept (CentresRing.Molecular.checkSourceReceipt input packet centers)
      pure evidence.molecular.replay
    | ["--verify-molecular",path] => do
      let content ← IO.FS.readFile path
      let packet ← IO.ofExcept ((Json.parse content).bind fromJson?)
      let evidence ← IO.ofExcept (CentresRing.Molecular.check input packet centers)
      pure evidence.replay
    | ["--verify",path] => do
      let content ← IO.FS.readFile path
      let packet ← IO.ofExcept ((Json.parse content).bind fromJson?)
      IO.ofExcept (CentresRing.checkReceipt input packet centers)
    | _ => throw (IO.userError usage)
  printReport "centres-1.0" result.report
