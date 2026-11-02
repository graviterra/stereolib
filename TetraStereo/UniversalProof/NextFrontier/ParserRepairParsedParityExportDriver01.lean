import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityCompilerClosureKernelCertificate

set_option autoImplicit false





#eval (do
  let outputDirectory := "output/universal-proof/parser-repair-parsed-parity-production-export-01"
  if (← (System.FilePath.mk outputDirectory).pathExists) then
    throw (IO.userError "production export directory already exists; preserve it")
  let path ← TetraStereo.UniversalProof.FramedParsedParityCompilerClosure.writeFamilyExport
    outputDirectory
  let written ← IO.FS.readFile path
  unless written == TetraStereo.UniversalProof.FramedParsedParityCompilerClosure.sourceEntry.fileSource do
    throw (IO.userError "production-written bytes differ from the compiler renderer")
  IO.println path.toString : IO Unit)
