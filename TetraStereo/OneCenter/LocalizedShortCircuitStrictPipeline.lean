import TetraStereo.OneCenter.LocalizedShortCircuitStrictCompleteness
import TetraStereo.OneCenter.LocalizedShortCircuitCachedPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedShortCircuit
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- Independent strict-Rule3 readiness forces the automatically generated dependency state to
assign the geometrically required descriptor. No state values or dependency answers are premises. -/
theorem reference_assigns_strictRule3
    (input : Input) (target : Occurrence input) (raw : RS)
    (ready : input.certified.LocalizedStrictRule3TetrahedralReadiness target raw) :
    referenceState input target = some (.chiral raw) := by
  rw [← reference_equation input target]
  exact input.certified.strictRule3_descriptor_total_all_views target raw ready _

/-- Every accepted certificate evaluation, including the checked fast path and the cached
fallback, contains that same required assignment. -/
theorem evaluation_assigns_strictRule3
    (input : Input) (result : Evaluation input) (target : Occurrence input) (raw : RS)
    (ready : input.certified.LocalizedStrictRule3TetrahedralReadiness target raw) :
    lookup result.facts target = some (.chiral raw) := by
  rw [evaluation_eq_reference input result]
  exact reference_assigns_strictRule3 input target raw ready

/-- Production and independent positive rule evidence hold together for any accepted evaluation. -/
theorem evaluation_strictRule3_assignment_sound
    (input : Input) (result : Evaluation input) (target : Occurrence input) (raw : RS)
    (ready : input.certified.LocalizedStrictRule3TetrahedralReadiness target raw) :
    lookup result.facts target = some (.chiral raw) ∧
      input.certified.DeclarativeLocalizedOccurrenceShortCircuitRule3Through5Descriptor
        target (input.certified.localizedDependencyView (lookup result.facts) target) (.chiral raw) := by
  have assigned := evaluation_assigns_strictRule3 input result target raw ready
  exact ⟨assigned, evaluation_positive_sound input result target (.chiral raw) assigned⟩

end TetraStereo.OneCenter.LocalizedShortCircuit
