import TetraStereo.Engine.CertificateCompiler
import TetraStereo.Examples.OnePhenylethanol

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace EngineTransaction

open OneCenter

noncomputable section

/-!
  Minimal end-to-end public engine transaction.

  This is the first product-shaped demo: a proof-facing molecule and realization enter through
  `Engine.runDescriptorRS`, the public facade returns a safe optional descriptor, and the successful
  result is compiled into a `LeanCertificateArtifact`.

  Descriptor calibration follows the corrected negative-orientation rule: the right-hand Cartesian
  realization of 1-phenylethanol is `S` (and the left-hand realization is `R`).  Historical export
  identifiers are preserved; statements and generated proof terms are corrected.
-/


def onePhenylethanolEngineTheoremPlan : Engine.PublicRSTheoremPlan where
  imports :=
    [ "TetraStereo.Engine.CertificateCompiler"
    , "TetraStereo.Examples.OnePhenylethanol"
    ]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "one_phenylethanol_engine_right_rs"
  moleculeExpr := "TetraStereo.Examples.OnePhenylethanol.oneCenter"
  realizationExpr := "TetraStereo.Examples.OnePhenylethanol.rightRealization"
  proofTerm :=
    "  simpa [TetraStereo.OneCenter.RSAssignmentCertificateClaim, TetraStereo.Engine.descriptorRS] using TetraStereo.Examples.OnePhenylethanol.rsCIP?_right_eq_some_S"

/-- The proof-facing one-center engine input for the right-hand 1-phenylethanol realization. -/
def onePhenylethanolEngineInput : Engine.EngineInput OnePhenylethanol.Atom where
  molecule := OnePhenylethanol.oneCenter
  realization := OnePhenylethanol.rightRealization
  theoremPlan := onePhenylethanolEngineTheoremPlan

/-- Run the public engine transaction. -/
def onePhenylethanolEngineDemo : Engine.EngineOutput onePhenylethanolEngineInput :=
  Engine.runDescriptorRS onePhenylethanolEngineInput

/-- The transaction returns the public safe descriptor `S`. -/
theorem onePhenylethanolEngineDemo_descriptor_eq_some_S :
    onePhenylethanolEngineDemo.descriptor? = some RS.S := by
  simpa [onePhenylethanolEngineDemo, Engine.runDescriptorRS, Engine.EngineOutput.descriptor?,
    onePhenylethanolEngineInput, Engine.descriptorRS] using
    OnePhenylethanol.rsCIP?_right_eq_some_S

/-- Historical API key retained; corrected statement: the transaction descriptor is `S`. -/
theorem onePhenylethanolEngineDemo_descriptor_eq_some_R :
    onePhenylethanolEngineDemo.descriptor? = some RS.S :=
  onePhenylethanolEngineDemo_descriptor_eq_some_S

/-- A named certified output for the same transaction. -/
def onePhenylethanolEngineCertified :
    Engine.CertifiedDescriptorOutput onePhenylethanolEngineInput where
  assignment :=
    { descriptor := RS.S
      certificate := OnePhenylethanol.rsCIP?_right_eq_some_S }
  artifact :=
    Engine.compilePublicRSAssignment onePhenylethanolEngineTheoremPlan
      { descriptor := RS.S
        certificate := OnePhenylethanol.rsCIP?_right_eq_some_S }
  artifact_eq := rfl

/-- The compiled engine transaction artifact is Lean-checked. -/
theorem onePhenylethanolEngineDemo_checked :
    onePhenylethanolEngineCertified.artifact.claim :=
  onePhenylethanolEngineCertified.artifact_checked

/-- The certified transaction also proves that descriptor priorities were resolved. -/
theorem onePhenylethanolEngineDemo_resolved :
    OnePhenylethanol.oneCenter.ResolvedCIPDescriptor :=
  onePhenylethanolEngineCertified.resolved

end
end EngineTransaction
end Examples
end TetraStereo
