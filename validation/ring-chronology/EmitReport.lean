import TetraStereo.Engine.LocalizedChemicalRingExport

def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected one output folder")
  let entry := TetraStereo.Engine.LocalizedChemicalRing.reportExportEntry.toSourceEntry
  let path ← entry.writeSource folder
  let bytes ← IO.FS.readBinFile path
  unless bytes == entry.fileSource.toUTF8 do throw (IO.userError "export byte mismatch")
  IO.println s!"Verified all {bytes.size} rendered bytes of {path}"
