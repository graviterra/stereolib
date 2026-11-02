import TetraStereo.UniversalProof.SecondSphereCompilerClosure

set_option autoImplicit false

/-! DRAFT: parent-operated production IO. Execute only after all protected dependency
and compiler gates, then independently check the exact emitted source. No IO has run. -/
#eval (show IO Unit from do
  let directory := "output/universal-proof/second-sphere-string-family-actual-emission-2026-10-04"
  if ← (System.FilePath.mk directory).pathExists then
    throw (IO.userError "Actual second-sphere STRING family export destination already exists")
  let path ← TetraStereo.UniversalProof.SecondSphereCompilerClosure.writeFamilyExport directory
  IO.println s!"Actual second-sphere STRING family certificate emitted: {path}"
)
