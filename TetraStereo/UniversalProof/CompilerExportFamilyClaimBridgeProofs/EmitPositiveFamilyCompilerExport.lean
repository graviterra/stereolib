import TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge

set_option autoImplicit false

/- Parent-operated actual IO emission into a fresh evidence directory. -/
#eval (show IO Unit from do
  let directory := "output/universal-proof/positive-family-actual-emission-2026-10-03"
  if ← (System.FilePath.mk directory).pathExists then
    throw (IO.userError "Actual family export destination already exists")
  let path ← TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.writeFamilyExport directory
  IO.println s!"Actual positive family certificate emitted: {path}"
)
