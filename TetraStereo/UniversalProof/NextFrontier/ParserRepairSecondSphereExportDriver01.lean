import TetraStereo.UniversalProof.SecondSphereCompilerClosureKernelCertificate

set_option autoImplicit false





#eval (do
  let outputDirectory := "output/universal-proof/parser-repair-second-sphere-production-export-01"
  if (← (System.FilePath.mk outputDirectory).pathExists) then
    throw (IO.userError "production export directory already exists; preserve it")
  let path ← TetraStereo.UniversalProof.SecondSphereCompilerClosure.writeFamilyExport
    outputDirectory
  let written ← IO.FS.readFile path
  unless written == TetraStereo.UniversalProof.SecondSphereCompilerClosure.sourceEntry.fileSource do
    throw (IO.userError "production-written bytes differ from the compiler renderer")
  IO.println path.toString : IO Unit)
