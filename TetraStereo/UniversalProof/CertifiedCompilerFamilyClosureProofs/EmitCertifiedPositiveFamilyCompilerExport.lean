import TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure

set_option autoImplicit false

/- Parent-operated actual certified-family production IO into a fresh evidence directory. -/
#eval (show IO Unit from do
  let directory := "output/universal-proof/certified-positive-family-actual-emission-2026-10-03"
  if ← (System.FilePath.mk directory).pathExists then
    throw (IO.userError "Actual certified family export destination already exists")
  let path ← TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.writeCertifiedFamilyExport directory
  IO.println s!"Actual certified positive family certificate emitted: {path}"
)
