import TetraStereo.Engine.CertificateCompiler

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section

/-!
  Certified public engine decisions.

  The success path already carries a checked `R/S` theorem artifact.  This module adds the equally
  important refusal path: when the safe public API returns `none`, the engine can return a checked
  certificate that it refused to assign a descriptor because descriptor priorities were unresolved.
-/

/-- Public reasons why the engine can refuse to emit a descriptor certificate. -/
inductive RefusalReason where
  | unresolvedDescriptorPriorities
  | unresolvedOfficialPriorities
  | unsupportedInput
  | unsupportedStereoElement
  | implementationLimit
  deriving DecidableEq, Repr

namespace RefusalReason

/-- Host-facing label for a refusal reason. -/
def label : RefusalReason → String
  | unresolvedDescriptorPriorities => "unresolved descriptor priorities"
  | unresolvedOfficialPriorities => "unresolved official priorities"
  | unsupportedInput => "unsupported input"
  | unsupportedStereoElement => "unsupported stereo element"
  | implementationLimit => "implementation limit"

end RefusalReason

/-- The refusal reason a descriptor computation justifies, if it refuses at all.

The safe CIP priority API declining is the only cause of refusal at this boundary, so
`unresolvedDescriptorPriorities` is the only reason derivable from the computation itself. -/
def descriptorRefusalReasonFor? {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) : Option RefusalReason :=
  match (descriptorRS m g).descriptor? with
  | none => some RefusalReason.unresolvedDescriptorPriorities
  | some _ => none

/-- A descriptor computation justifies a refusal reason exactly when the safe API declined, and the
only reason it justifies is `unresolvedDescriptorPriorities`. -/
theorem descriptorRefusalReasonFor?_eq_some_iff {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) (reason : RefusalReason) :
    descriptorRefusalReasonFor? m g = some reason ↔
      (descriptorRS m g).descriptor? = none ∧
        reason = RefusalReason.unresolvedDescriptorPriorities := by
  unfold descriptorRefusalReasonFor?
  cases h : (descriptorRS m g).descriptor? with
  | none => simp [eq_comm]
  | some descriptor => simp

/-- Compile a public descriptor-`R/S` refusal into a Lean certificate artifact.

`reason` appears in the artifact title, which the exported proposition
(`RSRefusalCertificateClaim`) does not mention, so it is pinned here by `hreason` instead.  Without
that argument a checked artifact could be titled with a cause the computation does not exhibit. -/
def compilePublicRSRefusal {V : Type*} [Fintype V] [DecidableEq V]
    {m : OneCenterMolecule V} {g : TetrahedralGeometry.Realization}
    (plan : PublicRSTheoremPlan) (reason : RefusalReason)
    (h : RSRefusalCertificateClaim (descriptorRS m g).descriptor?)
    (_hreason : descriptorRefusalReasonFor? m g = some reason) :
    LeanCertificateArtifact :=
  let base :=
    compileRSRefusalCertificate plan.theoremName plan.computedExpr plan.proofTerm
      (descriptorRS m g).descriptor? h
  { base with
    title := "Public engine safe R/S refusal: " ++ reason.label
    theoremExport :=
      { base.theoremExport with
        imports := plan.imports
        namespacePath := plan.namespacePath } }

/-- The refusal reason a public descriptor request justifies, if it refuses at all.

A request that reaches this boundary has one possible cause of refusal: the safe CIP priority API
declined to assign, i.e. the descriptor priorities were unresolved.  Deriving the reason from the
request rather than accepting it from the caller is what stops a refusal certificate from
advertising a cause the request does not exhibit. -/
def descriptorRefusalReason? {V : Type*} [Fintype V] [DecidableEq V]
    (input : EngineInput V) : Option RefusalReason :=
  descriptorRefusalReasonFor? input.molecule input.realization

/-- A descriptor request justifies a refusal reason exactly when the safe API declined, and the only
reason it justifies is `unresolvedDescriptorPriorities`. -/
theorem descriptorRefusalReason?_eq_some_iff {V : Type*} [Fintype V] [DecidableEq V]
    (input : EngineInput V) (reason : RefusalReason) :
    descriptorRefusalReason? input = some reason ↔
      (descriptorRS input.molecule input.realization).descriptor? = none ∧
        reason = RefusalReason.unresolvedDescriptorPriorities := by
  unfold descriptorRefusalReason?
  exact descriptorRefusalReasonFor?_eq_some_iff input.molecule input.realization reason

/-- A public descriptor refusal plus a checked theorem artifact.

`reason_eq` ties the advertised `reason` to the one the request itself justifies; without it the
field was free and any `RefusalReason` could be attached to any refusal. -/
structure CertifiedRSRefusal {V : Type*} [Fintype V] [DecidableEq V]
    (input : EngineInput V) where
  reason : RefusalReason
  refusal : (descriptorRS input.molecule input.realization).descriptor? = none
  reason_eq : descriptorRefusalReason? input = some reason
  artifact : LeanCertificateArtifact
  artifact_eq : artifact = compilePublicRSRefusal input.theoremPlan reason refusal reason_eq

namespace CertifiedRSRefusal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {input : EngineInput V}

/-- The refusal artifact is checked by construction. -/
theorem artifact_checked (refusal : CertifiedRSRefusal input) :
    refusal.artifact.claim := by
  rw [refusal.artifact_eq]
  exact (compilePublicRSRefusal input.theoremPlan refusal.reason refusal.refusal
    refusal.reason_eq).checked

end CertifiedRSRefusal

/-- A public descriptor refusal rules out resolved descriptor priorities. -/
theorem not_resolved_of_descriptorRS_none {V : Type*} [Fintype V] [DecidableEq V]
    {m : OneCenterMolecule V} {g : TetrahedralGeometry.Realization}
    (h : (descriptorRS m g).descriptor? = none) :
    ¬ m.ResolvedCIPDescriptor := by
  intro hresolved
  have hsome := m.rsCIP?_eq_some_rsCIP_of_resolvedCIPDescriptor hresolved g
  have hnone : m.rsCIP? g = none := by
    simpa [descriptorRS] using h
  rw [hsome] at hnone
  cases hnone

namespace CertifiedRSRefusal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {input : EngineInput V}

/-- A certified public refusal implies the center was not safely descriptor-resolved. -/
theorem not_resolved (refusal : CertifiedRSRefusal input) :
    ¬ input.molecule.ResolvedCIPDescriptor :=
  not_resolved_of_descriptorRS_none refusal.refusal

end CertifiedRSRefusal

/-- The total certified public decision algebra for descriptor `R/S`. -/
inductive EngineDecision {V : Type*} [Fintype V] [DecidableEq V]
    (input : EngineInput V) where
  | assigned (assignment : CertifiedDescriptorOutput input)
  | refused (refusal : CertifiedRSRefusal input)

namespace EngineDecision

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {input : EngineInput V}

/-- Optional descriptor exposed by a total certified engine decision. -/
def descriptor? (decision : EngineDecision input) : Option RS :=
  match decision with
  | assigned assignment => some assignment.assignment.descriptor
  | refused _ => none

/-- The decision descriptor is exactly the safe public facade descriptor. -/
theorem descriptor?_eq_public (decision : EngineDecision input) :
    decision.descriptor? = (descriptorRS input.molecule input.realization).descriptor? := by
  cases decision with
  | assigned assignment =>
      simpa [descriptor?, descriptorRS] using assignment.assignment.certificate.symm
  | refused refusal =>
      simpa [descriptor?] using refusal.refusal.symm

/-- Every certified engine decision carries a checked theorem artifact. -/
theorem artifact_checked (decision : EngineDecision input) :
    match decision with
    | assigned assignment => assignment.artifact.claim
    | refused refusal => refusal.artifact.claim := by
  cases decision with
  | assigned assignment => exact assignment.artifact_checked
  | refused refusal => exact refusal.artifact_checked

/-- If a decision is a refusal, descriptor priorities were not resolved. -/
theorem not_resolved_of_refusal (refusal : CertifiedRSRefusal input) :
    ¬ input.molecule.ResolvedCIPDescriptor :=
  refusal.not_resolved

end EngineDecision

/-- Run the total public descriptor decision, yielding either a checked assignment or refusal. -/
def decideDescriptorRS {V : Type*} [Fintype V] [DecidableEq V]
    (input : EngineInput V) : EngineDecision input :=
  match h : (descriptorRS input.molecule input.realization).descriptor? with
  | some descriptor =>
      let assignment : CertifiedRSAssignment input.molecule input.realization :=
        { descriptor := descriptor
          certificate := by
            simpa [descriptorRS] using h }
      EngineDecision.assigned
        { assignment := assignment
          artifact := compilePublicRSAssignment input.theoremPlan assignment
          artifact_eq := rfl }
  | none =>
      EngineDecision.refused
        { reason := RefusalReason.unresolvedDescriptorPriorities
          refusal := h
          reason_eq :=
            (descriptorRefusalReason?_eq_some_iff input
              RefusalReason.unresolvedDescriptorPriorities).mpr ⟨h, rfl⟩
          artifact :=
            compilePublicRSRefusal input.theoremPlan RefusalReason.unresolvedDescriptorPriorities h
              ((descriptorRefusalReason?_eq_some_iff input
                RefusalReason.unresolvedDescriptorPriorities).mpr ⟨h, rfl⟩)
          artifact_eq := rfl }

end
end Engine
end TetraStereo
