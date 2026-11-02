import TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosureKernelCertificate

set_option autoImplicit false

/-! Running this focused module executes the production exporter. The emitted Lean file
requires a separate bounded kernel gate; execution does not certify the emitted bytes. -/

#eval (do
  let outputDirectory := "output/universal-proof/native-nitrile-family-production-export-01"
  if (← (System.FilePath.mk outputDirectory).pathExists) then
    throw (IO.userError "production export directory already exists; preserve it")
  let path ← TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosure.writeFamilyExport
    outputDirectory
  let written ← IO.FS.readFile path
  unless written == TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosure.sourceEntry.fileSource do
    throw (IO.userError "production-written bytes differ from the compiler renderer")
  IO.println path.toString : IO Unit)
