import TetraStereo.OneCenter.IUPACProvisionTerminalLedger
import TetraStereo.OneCenter.IUPACNormativeCoveragePartition

set_option autoImplicit false

/-!
# Legacy project-management ledger for IUPAC provisions

This compatibility module retains the original open/maturity ledger used by historical tests and
work queues.  Release-facing compiler code imports `IUPACProvisionTerminalLedger` directly and
therefore does not depend on these hand-maintained maturity tags.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- Historical work-queue disposition.  Unlike `ProvisionTerminalStatus`, this type permits an
open row and requires the hand-maintained semantics-maturity tag for conformance. -/
inductive ProvisionClosureStatus (semantics : ProvisionClosureSemantics)
    (provision : IUPACNormativeProvision) where
  | open
  | conformant
      (sourceAudited : IUPACNormativeSource.ProvisionAuditComplete provision.source)
      (semanticsComplete : currentSemanticsMaturity provision = .provisionComplete)
      (evidence : semantics.EndToEndConforms provision)
  | notApplicable
      (sourceAudited : IUPACNormativeSource.ProvisionAuditComplete provision.source)
      (evidence : semantics.UniversallyNotApplicable provision)
  | sourceAbsent
      (sourceAudited : IUPACNormativeSource.ProvisionAuditComplete provision.source)
      (evidence : semantics.SourceAbsent provision)

namespace ProvisionClosureStatus

def IsConformant {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision} :
    ProvisionClosureStatus semantics provision → Prop
  | .conformant _ _ _ => True
  | _ => False

def IsNotApplicable {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision} :
    ProvisionClosureStatus semantics provision → Prop
  | .notApplicable _ _ => True
  | _ => False

def IsSourceAbsent {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision} :
    ProvisionClosureStatus semantics provision → Prop
  | .sourceAbsent _ _ => True
  | _ => False

def IsTerminal {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision} :
    ProvisionClosureStatus semantics provision → Prop
  | .open => False
  | _ => True

theorem evidence_of_isConformant {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision}
    {status : ProvisionClosureStatus semantics provision}
    (conformant : status.IsConformant) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source ∧
      currentSemanticsMaturity provision = .provisionComplete ∧
      semantics.EndToEndConforms provision := by
  cases status with
  | «open» => simp [IsConformant] at conformant
  | conformant sourceAudited semanticsComplete evidence =>
      exact ⟨sourceAudited, semanticsComplete, evidence⟩
  | notApplicable _ _ => simp [IsConformant] at conformant
  | sourceAbsent _ _ => simp [IsConformant] at conformant

theorem evidence_of_isNotApplicable {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision}
    {status : ProvisionClosureStatus semantics provision}
    (notApplicable : status.IsNotApplicable) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source ∧
      semantics.UniversallyNotApplicable provision := by
  cases status with
  | «open» => simp [IsNotApplicable] at notApplicable
  | conformant _ _ _ => simp [IsNotApplicable] at notApplicable
  | notApplicable sourceAudited evidence => exact ⟨sourceAudited, evidence⟩
  | sourceAbsent _ _ => simp [IsNotApplicable] at notApplicable

theorem evidence_of_isSourceAbsent {semantics : ProvisionClosureSemantics}
    {provision : IUPACNormativeProvision}
    {status : ProvisionClosureStatus semantics provision}
    (sourceAbsent : status.IsSourceAbsent) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source ∧
      semantics.SourceAbsent provision := by
  cases status with
  | «open» => simp [IsSourceAbsent] at sourceAbsent
  | conformant _ _ _ => simp [IsSourceAbsent] at sourceAbsent
  | notApplicable _ _ => simp [IsSourceAbsent] at sourceAbsent
  | sourceAbsent sourceAudited evidence => exact ⟨sourceAudited, evidence⟩

end ProvisionClosureStatus

/-- Historical total work-queue view linked to the coarse implementation-maturity manifest. -/
structure ProvisionClosureLedger (semantics : ProvisionClosureSemantics) where
  status : (provision : IUPACNormativeProvision) →
    ProvisionClosureStatus semantics provision
  endToEnd_iff_conformant : ∀ provision,
    currentMaturity provision = .endToEndProved ↔
      (status provision).IsConformant

namespace ProvisionClosureLedger

def Complete {semantics : ProvisionClosureSemantics}
    (ledger : ProvisionClosureLedger semantics) : Prop :=
  ∀ provision, (ledger.status provision).IsTerminal

theorem sourceAuditComplete_of_endToEnd {semantics : ProvisionClosureSemantics}
    (ledger : ProvisionClosureLedger semantics) {provision : IUPACNormativeProvision}
    (endToEnd : currentMaturity provision = .endToEndProved) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source :=
  (ProvisionClosureStatus.evidence_of_isConformant
    ((ledger.endToEnd_iff_conformant provision).mp endToEnd)).1

theorem semanticsComplete_of_endToEnd {semantics : ProvisionClosureSemantics}
    (ledger : ProvisionClosureLedger semantics) {provision : IUPACNormativeProvision}
    (endToEnd : currentMaturity provision = .endToEndProved) :
    currentSemanticsMaturity provision = .provisionComplete :=
  (ProvisionClosureStatus.evidence_of_isConformant
    ((ledger.endToEnd_iff_conformant provision).mp endToEnd)).2.1

theorem conformanceEvidence_of_endToEnd {semantics : ProvisionClosureSemantics}
    (ledger : ProvisionClosureLedger semantics) {provision : IUPACNormativeProvision}
    (endToEnd : currentMaturity provision = .endToEndProved) :
    semantics.EndToEndConforms provision :=
  (ProvisionClosureStatus.evidence_of_isConformant
    ((ledger.endToEnd_iff_conformant provision).mp endToEnd)).2.2

end ProvisionClosureLedger

/-- Honest present-day work queue: no terminal evidence has been claimed. -/
def currentOpenClosureLedger (semantics : ProvisionClosureSemantics) :
    ProvisionClosureLedger semantics where
  status := fun _ => .open
  endToEnd_iff_conformant := by
    intro provision
    constructor
    · intro endToEnd
      exact (currentMaturity_ne_endToEndProved provision endToEnd).elim
    · intro conformant
      simp [ProvisionClosureStatus.IsConformant] at conformant

theorem currentOpenClosureLedger_not_complete (semantics : ProvisionClosureSemantics) :
    ¬(currentOpenClosureLedger semantics).Complete := by
  intro complete
  have openTerminal := complete IUPACNormativeProvision.p92Rule1aAtomicNumber
  simp [currentOpenClosureLedger, ProvisionClosureStatus.IsTerminal] at openTerminal

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionClosureStatus.evidence_of_isConformant
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionClosureStatus.evidence_of_isNotApplicable
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionClosureStatus.evidence_of_isSourceAbsent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionClosureLedger.sourceAuditComplete_of_endToEnd
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionClosureLedger.semanticsComplete_of_endToEnd
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionClosureLedger.conformanceEvidence_of_endToEnd
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentOpenClosureLedger_not_complete
