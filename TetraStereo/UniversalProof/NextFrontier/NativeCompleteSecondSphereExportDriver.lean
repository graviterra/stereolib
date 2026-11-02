import TetraStereo.UniversalProof.SecondSphereCompilerClosureKernelCertificate

set_option autoImplicit false

/-! Development execution fixture. Building this module executes the actual production exporter
for the strengthened family claim. Root must first verify the fresh output directory and run the
existing bounded helper inside its aggregate memory scope. The written file then needs its own
Lean check; this fixture alone does not certify the emitted bytes. -/

#eval (do
  let path ← TetraStereo.UniversalProof.SecondSphereCompilerClosure.writeFamilyExport
    "output/universal-proof/complete-second-sphere-production-export-01"
  IO.println path.toString : IO Unit)
