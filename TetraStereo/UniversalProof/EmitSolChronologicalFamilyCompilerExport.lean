import TetraStereo.UniversalProof.ChronologicalFamilyCompilerClosure

set_option autoImplicit false

/-! Parent-operated production IO. Execute only after protected dependency and source gates. -/
#eval (show IO Unit from do
  let directory := "output/universal-proof/chronological-string-family-actual-emission-2026-10-03"
  if ← (System.FilePath.mk directory).pathExists then
    throw (IO.userError "Actual chronological STRING family export destination already exists")
  let path ← TetraStereo.UniversalProof.ChronologicalFamilyCompilerClosure.writeFamilyExport directory
  IO.println s!"Actual chronological STRING family certificate emitted: {path}"
)
