import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityCompilerClosureKernelCertificate

set_option autoImplicit false

/-! Root-only execution fixture. The closure and all-eight finish endpoint must
first pass their bounded gates. This module calls the actual production writer;
the output still requires a separate exact-file Lean check. -/

#eval (do
  let outputDirectory := "output/universal-proof/parsed-parity-production-export-02"
  if (← (System.FilePath.mk outputDirectory).pathExists) then
    throw (IO.userError "production export directory already exists; preserve it")
  let path ← TetraStereo.UniversalProof.FramedParsedParityCompilerClosure.writeFamilyExport
    outputDirectory
  let written ← IO.FS.readFile path
  unless written ==
      TetraStereo.UniversalProof.FramedParsedParityCompilerClosure.sourceEntry.fileSource do
    throw (IO.userError "production-written bytes differ from the compiler renderer")
  IO.println path.toString : IO Unit)
