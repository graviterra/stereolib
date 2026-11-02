import TetraStereo.Engine.PublicAPI

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section

/-!
  Engine transaction and certificate compiler.

  `PublicAPI.lean` defines the safe public facade.  This module turns that facade into the first
  engine-shaped transaction: a public one-center `R/S` request runs through `descriptorRS`, extracts
  a certified assignment when the safe API succeeds, and compiles the result into a
  `LeanCertificateArtifact`.
-/

/-- Render an `R/S` descriptor as a fully qualified Lean expression. -/
def rsExpr : RS → String
  | RS.R => "TetraStereo.OneCenter.RS.R"
  | RS.S => "TetraStereo.OneCenter.RS.S"


structure PublicRSTheoremPlan where
  imports : List String := ["TetraStereo.Engine.CertificateCompiler"]
  namespacePath : List String := ["TetraStereo", "Generated"]
  theoremName : String
  moleculeExpr : String
  realizationExpr : String
  proofTerm : String

namespace PublicRSTheoremPlan


def computedExpr (plan : PublicRSTheoremPlan) : String :=
  "(TetraStereo.Engine.descriptorRS " ++ plan.moleculeExpr ++ " " ++
    plan.realizationExpr ++ ").descriptor?"

end PublicRSTheoremPlan

/-- Compile a public descriptor-`R/S` assignment into a Lean certificate artifact.

Unlike lower-level helpers, the artifact claim is about the public facade expression
`(Engine.descriptorRS m g).descriptor?`, not directly about the raw kernel function beneath it. -/
def compilePublicRSAssignment {V : Type*} [Fintype V] [DecidableEq V]
    {m : OneCenterMolecule V} {g : TetrahedralGeometry.Realization}
    (plan : PublicRSTheoremPlan)
    (assignment : CertifiedRSAssignment m g) : LeanCertificateArtifact :=
  let publicProof :
      RSAssignmentCertificateClaim (descriptorRS m g).descriptor? assignment.descriptor := by
    simpa [descriptorRS] using assignment.certificate
  let base :=
    compileRSAssignmentCertificate plan.theoremName plan.computedExpr (rsExpr assignment.descriptor)
      plan.proofTerm (descriptorRS m g).descriptor? assignment.descriptor publicProof
  { base with
    title := "Public engine safe R/S assignment"
    theoremExport :=
      { base.theoremExport with
        imports := plan.imports
        namespacePath := plan.namespacePath } }

/-- A host-facing one-center descriptor request.

The molecule and realization are already proof-facing Lean values.  Future import adapters should
construct this after parsing/normalization/perception. -/
structure EngineInput (V : Type*) [Fintype V] [DecidableEq V] where
  molecule : OneCenterMolecule V
  realization : TetrahedralGeometry.Realization
  theoremPlan : PublicRSTheoremPlan

/-- A successful public descriptor output plus the certificate artifact compiled from it. -/
structure CertifiedDescriptorOutput {V : Type*} [Fintype V] [DecidableEq V]
    (input : EngineInput V) where
  assignment : CertifiedRSAssignment input.molecule input.realization
  artifact : LeanCertificateArtifact
  artifact_eq : artifact = compilePublicRSAssignment input.theoremPlan assignment

namespace CertifiedDescriptorOutput

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {input : EngineInput V}

/-- The output artifact is checked by construction. -/
theorem artifact_checked (output : CertifiedDescriptorOutput input) :
    output.artifact.claim := by
  rw [output.artifact_eq]
  exact (compilePublicRSAssignment input.theoremPlan output.assignment).checked

/-- A certified engine output implies resolved descriptor priorities. -/
theorem resolved (output : CertifiedDescriptorOutput input) :
    input.molecule.ResolvedCIPDescriptor :=
  output.assignment.resolved

end CertifiedDescriptorOutput

/-- Public engine output for a one-center descriptor request.

If `certified? = none`, the public facade refused to classify the center.  If it is `some`, the
payload carries both the certified assignment and a checked theorem artifact. -/
structure EngineOutput {V : Type*} [Fintype V] [DecidableEq V]
    (input : EngineInput V) where
  result : RSResult input.molecule input.realization
  certified? : Option (CertifiedDescriptorOutput input)
  result_eq : result = descriptorRS input.molecule input.realization

namespace EngineOutput

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {input : EngineInput V}

/-- The public optional descriptor returned by this engine transaction. -/
def descriptor? (output : EngineOutput input) : Option RS :=
  output.result.descriptor?

/-- The engine transaction descriptor is exactly the public facade descriptor. -/
theorem descriptor?_eq_public (output : EngineOutput input) :
    output.descriptor? = (descriptorRS input.molecule input.realization).descriptor? := by
  simp [descriptor?, output.result_eq]

/-- Any certified output produced by an engine transaction has a checked artifact. -/
theorem artifact_checked_of_certified_some (output : EngineOutput input)
    {certified : CertifiedDescriptorOutput input}
    (_h : output.certified? = some certified) :
    certified.artifact.claim :=
  certified.artifact_checked

/-- Any successful certified output implies resolved descriptor priorities. -/
theorem resolved_of_certified_some (output : EngineOutput input)
    {certified : CertifiedDescriptorOutput input}
    (_h : output.certified? = some certified) :
    input.molecule.ResolvedCIPDescriptor :=
  certified.resolved

end EngineOutput

/-- Run the public one-center descriptor transaction. -/
def runDescriptorRS {V : Type*} [Fintype V] [DecidableEq V]
    (input : EngineInput V) : EngineOutput input :=
  let result := descriptorRS input.molecule input.realization
  { result := result
    certified? :=
      match result.certified? with
      | some assignment =>
          some
            { assignment := assignment
              artifact := compilePublicRSAssignment input.theoremPlan assignment
              artifact_eq := rfl }
      | none => none
    result_eq := rfl }

end
end Engine
end TetraStereo
