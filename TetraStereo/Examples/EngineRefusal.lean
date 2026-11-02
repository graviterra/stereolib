import TetraStereo.Engine.Result
import TetraStereo.Examples.Symmetry

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace EngineRefusal

open OneCenter

noncomputable section

/-!
  Checked refusal example for the public engine boundary.

  Methane has four identical ligands.  The public descriptor engine must therefore refuse an
  `R/S` assignment instead of exposing the kernel's deterministic tie-breaking order as a chemical
  descriptor.
-/

/-- Methane is not descriptor-resolved: the hydrogen swap forces two cycle-cut keys to coincide. -/
theorem methane_not_resolvedCIPDescriptor :
    ¬ Methane.oneCenter.ResolvedCIPDescriptor := by
  intro hresolved
  have hkey10 :=
    Methane.oneCenter.cipKeyCycleCut_eq_cipKeyCycleCut_ligandPermHom
      (e := Methane.swap01CenterAut) (i := (0 : Fin 4))
  have hperm0 :
      Methane.oneCenter.ligandPermHom Methane.swap01CenterAut (0 : Fin 4) = 1 := by
    rw [Methane.ligandPermHom_swap01]
    simp
  have hkey :
      Methane.oneCenter.cipKeyCycleCut (1 : Fin 4) =
        Methane.oneCenter.cipKeyCycleCut (0 : Fin 4) := by
    simpa [hperm0] using hkey10
  have h10 : (1 : Fin 4) = 0 :=
    hresolved hkey
  norm_num at h10

/-- The raw safe descriptor function refuses methane because descriptor priorities tie. -/
theorem methane_rsCIP?_right_eq_none :
    Methane.oneCenter.rsCIP? bromochlorofluoromethaneRightRealization = none := by
  exact
    Methane.oneCenter.rsCycleCut?_eq_none_of_not_resolvedCIPCycleCut
      methane_not_resolvedCIPDescriptor bromochlorofluoromethaneRightRealization

/-- The public facade refuses methane instead of returning an unsafe descriptor. -/
theorem methaneEngineRefusal_descriptor_eq_none :
    (Engine.descriptorRS Methane.oneCenter
      bromochlorofluoromethaneRightRealization).descriptor? = none := by
  simpa [Engine.descriptorRS] using methane_rsCIP?_right_eq_none


def methaneRefusalTheoremPlan : Engine.PublicRSTheoremPlan where
  imports := ["TetraStereo.Engine.Result", "TetraStereo.Examples.EngineRefusal"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "methane_engine_refuses_rs"
  moleculeExpr := "TetraStereo.Examples.Methane.oneCenter"
  realizationExpr := "TetraStereo.Examples.bromochlorofluoromethaneRightRealization"
  proofTerm := "  exact TetraStereo.Examples.EngineRefusal.methaneEngineRefusal_descriptor_eq_none"

/-- Public engine input for the methane refusal example. -/
def methaneEngineInput : Engine.EngineInput Methane.Atom where
  molecule := Methane.oneCenter
  realization := bromochlorofluoromethaneRightRealization
  theoremPlan := methaneRefusalTheoremPlan

/-- Total decision output for methane. -/
def methaneEngineDecision : Engine.EngineDecision methaneEngineInput :=
  Engine.decideDescriptorRS methaneEngineInput

/-- A direct checked refusal package for methane. -/
def methaneEngineCertifiedRefusal : Engine.CertifiedRSRefusal methaneEngineInput where
  reason := Engine.RefusalReason.unresolvedDescriptorPriorities
  refusal := methaneEngineRefusal_descriptor_eq_none
  reason_eq :=
    (Engine.descriptorRefusalReason?_eq_some_iff methaneEngineInput
      Engine.RefusalReason.unresolvedDescriptorPriorities).mpr
      ⟨methaneEngineRefusal_descriptor_eq_none, rfl⟩
  artifact :=
    Engine.compilePublicRSRefusal methaneRefusalTheoremPlan
      Engine.RefusalReason.unresolvedDescriptorPriorities methaneEngineRefusal_descriptor_eq_none
      ((Engine.descriptorRefusalReason?_eq_some_iff methaneEngineInput
        Engine.RefusalReason.unresolvedDescriptorPriorities).mpr
        ⟨methaneEngineRefusal_descriptor_eq_none, rfl⟩)
  artifact_eq := rfl

/-- The total engine decision agrees with the public facade and returns no descriptor. -/
theorem methaneEngineDecision_descriptor_eq_none :
    methaneEngineDecision.descriptor? = none := by
  rw [Engine.EngineDecision.descriptor?_eq_public]
  exact methaneEngineRefusal_descriptor_eq_none

/-- The methane refusal artifact is checked by Lean. -/
theorem methaneEngineRefusal_checked :
    methaneEngineCertifiedRefusal.artifact.claim :=
  methaneEngineCertifiedRefusal.artifact_checked

/-- The refusal proof implies methane was not descriptor-resolved. -/
theorem methaneEngineRefusal_not_resolved :
    ¬ Methane.oneCenter.ResolvedCIPDescriptor :=
  methaneEngineCertifiedRefusal.not_resolved

/-- *Every* checked refusal for this input is forced to advertise the reason the request actually
justifies — a certificate cannot attach an unrelated cause.

While `CertifiedRSRefusal.reason` was an unconstrained field, this was unprovable: any of the four
`RefusalReason` values could be paired with the same refusal proof. -/
theorem methaneEngineRefusal_reason_forced
    (refusal : Engine.CertifiedRSRefusal methaneEngineInput) :
    refusal.reason = Engine.RefusalReason.unresolvedDescriptorPriorities := by
  have h := refusal.reason_eq
  rw [Engine.descriptorRefusalReason?_eq_some_iff] at h
  exact h.2

end
end EngineRefusal
end Examples
end TetraStereo
