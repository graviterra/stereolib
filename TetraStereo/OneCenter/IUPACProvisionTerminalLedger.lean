import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.KernelOnly

set_option autoImplicit false









namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- Independent claims consumed by the proof-bearing provision ledger. -/
structure ProvisionClosureSemantics where
  ChemicallyAdmitted : AuthoritativeChemicalInput → Prop
  Applies : IUPACNormativeProvision → AuthoritativeChemicalInput → Prop
  EndToEndConforms : IUPACNormativeProvision → Prop
  SourceSuppliesRule : IUPACNormativeProvision → Prop

namespace ProvisionClosureSemantics

/-- No chemically admitted input is governed by this provision. -/
def UniversallyNotApplicable (semantics : ProvisionClosureSemantics)
    (provision : IUPACNormativeProvision) : Prop :=
  ∀ input, semantics.ChemicallyAdmitted input → ¬semantics.Applies provision input


def SourceAbsent (semantics : ProvisionClosureSemantics)
    (provision : IUPACNormativeProvision) : Prop :=
  ¬semantics.SourceSuppliesRule provision

end ProvisionClosureSemantics

/-- One proof-bearing terminal result emitted by the global provision compiler. -/
inductive ProvisionTerminalStatus (semantics : ProvisionClosureSemantics)
    (provision : IUPACNormativeProvision) where
  | conformant
      (sourceAudited : IUPACNormativeSource.ProvisionAuditComplete provision.source)
      (evidence : semantics.EndToEndConforms provision)
  | notApplicable
      (sourceAudited : IUPACNormativeSource.ProvisionAuditComplete provision.source)
      (evidence : semantics.UniversallyNotApplicable provision)
  | sourceAbsent
      (sourceAudited : IUPACNormativeSource.ProvisionAuditComplete provision.source)
      (evidence : semantics.SourceAbsent provision)

namespace ProvisionTerminalStatus

def IsConformant {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision} :
    ProvisionTerminalStatus semantics provision → Prop
  | .conformant _ _ => True
  | _ => False

def IsNotApplicable {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision} :
    ProvisionTerminalStatus semantics provision → Prop
  | .notApplicable _ _ => True
  | _ => False

def IsSourceAbsent {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision} :
    ProvisionTerminalStatus semantics provision → Prop
  | .sourceAbsent _ _ => True
  | _ => False

theorem exactly_one {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision}
    (status : ProvisionTerminalStatus semantics provision) :
    (status.IsConformant ∧ ¬status.IsNotApplicable ∧ ¬status.IsSourceAbsent) ∨
      (¬status.IsConformant ∧ status.IsNotApplicable ∧ ¬status.IsSourceAbsent) ∨
      (¬status.IsConformant ∧ ¬status.IsNotApplicable ∧ status.IsSourceAbsent) := by
  cases status <;> simp [IsConformant, IsNotApplicable, IsSourceAbsent]

theorem conformanceEvidence {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision}
    {status : ProvisionTerminalStatus semantics provision}
    (conformant : status.IsConformant) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source ∧
      semantics.EndToEndConforms provision := by
  cases status with
  | conformant sourceAudited evidence => exact ⟨sourceAudited, evidence⟩
  | notApplicable _ _ => simp [IsConformant] at conformant
  | sourceAbsent _ _ => simp [IsConformant] at conformant

theorem notApplicableEvidence {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision}
    {status : ProvisionTerminalStatus semantics provision}
    (notApplicable : status.IsNotApplicable) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source ∧
      semantics.UniversallyNotApplicable provision := by
  cases status with
  | conformant _ _ => simp [IsNotApplicable] at notApplicable
  | notApplicable sourceAudited evidence => exact ⟨sourceAudited, evidence⟩
  | sourceAbsent _ _ => simp [IsNotApplicable] at notApplicable

theorem sourceAbsentEvidence {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision}
    {status : ProvisionTerminalStatus semantics provision}
    (sourceAbsent : status.IsSourceAbsent) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source ∧
      semantics.SourceAbsent provision := by
  cases status with
  | conformant _ _ => simp [IsSourceAbsent] at sourceAbsent
  | notApplicable _ _ => simp [IsSourceAbsent] at sourceAbsent
  | sourceAbsent sourceAudited evidence => exact ⟨sourceAudited, evidence⟩

end ProvisionTerminalStatus

/-- The generated release artifact: one terminal proof object for every manifest provision. -/
structure ProvisionTerminalLedger (semantics : ProvisionClosureSemantics) where
  status : (provision : IUPACNormativeProvision) →
    ProvisionTerminalStatus semantics provision

namespace ProvisionTerminalLedger

/-- Completeness is structural: there is one terminal value for every provision and no open case. -/
theorem complete {semantics : ProvisionClosureSemantics}
    (ledger : ProvisionTerminalLedger semantics)
    (provision : IUPACNormativeProvision) :
    (ledger.status provision).IsConformant ∨
      (ledger.status provision).IsNotApplicable ∨
      (ledger.status provision).IsSourceAbsent := by
  rcases (ledger.status provision).exactly_one with first | second | third
  · exact Or.inl first.1
  · exact Or.inr (Or.inl second.2.1)
  · exact Or.inr (Or.inr third.2.2)

end ProvisionTerminalLedger
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionTerminalStatus.exactly_one
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionTerminalStatus.conformanceEvidence
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionTerminalStatus.notApplicableEvidence
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionTerminalStatus.sourceAbsentEvidence
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionTerminalLedger.complete
