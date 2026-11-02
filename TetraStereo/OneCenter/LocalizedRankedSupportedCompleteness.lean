import TetraStereo.OneCenter.LocalizedRankedDescriptorCompleteness
import TetraStereo.OneCenter.LocalizedShortCircuitSupportedDescriptorCertificate

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Bounded

/-- Certificate packaging preserves the complete optional evaluator result. -/
theorem descriptorCertificate?_map_descriptor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    (descriptorCertificate? input readChildren callbackFree target view).map Sigma.fst =
      descriptor? input readChildren target view := by
  unfold descriptorCertificate?
  split
  next compiled => simp [descriptor?, compiled]
  next evidence compiled =>
    split
    next geometry => simp [descriptor?, compiled, geometry]
    next raw geometry => simp [descriptor?, compiled, geometry]

/-- General construction of a returned certificate from independent ranked readiness.
The reader may be cached, provided its child results are exact. -/
theorem descriptorCertificate?_total_of_ranked
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (ready : input.LocalizedRankedTetrahedralReadiness target view) :
    ∃ certificate, descriptorCertificate? input readChildren callbackFree target view =
      some certificate := by
  obtain ⟨descriptor, computed⟩ := input.ranked_descriptor_total target view ready
  have projected := descriptorCertificate?_map_descriptor input readChildren callbackFree target view
  rw [descriptor?_eq_production input readChildren readEq callbackFree, computed] at projected
  cases produced : descriptorCertificate? input readChildren callbackFree target view with
  | none => simp [produced] at projected
  | some certificate => exact ⟨certificate, rfl⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Bounded

namespace TetraStereo.OneCenter.LocalizedShortCircuit
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- Checked support carries precisely the reference auxiliary view, so independent readiness
at that view suffices for the actual cached certificate constructor. -/
theorem certifyWithSupport?_total_of_ranked
    (input : Input) (cache : Cached.RuntimeCache input)
    (callbackFree : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input))
    (target : Occurrence input) (support : DependencySupport input target)
    (ready : input.certified.LocalizedRankedTetrahedralReadiness target
      (input.certified.localizedDependencyView (referenceState input) target)) :
    ∃ certificate, certifyWithSupport? input cache callbackFree target support = some certificate := by
  have readyAtSupport : input.certified.LocalizedRankedTetrahedralReadiness target
      (input.certified.localizedDependencyView (lookup support.facts) target) := by
    rw [support.view_eq_reference]
    exact ready
  have readEq : ∀ cursor, input.certified.localizedRerootChildrenFromCarrier? cache.carrier cursor =
      input.certified.executableLocalizedRerootChildren? cursor := by
    intro cursor
    rw [cache.exact]
    exact input.certified.localizedRerootChildrenFromCarrier?_eq_executable cursor
  obtain ⟨localEvidence, produced⟩ := Bounded.descriptorCertificate?_total_of_ranked input.certified
    _ readEq callbackFree target _ readyAtSupport
  refine ⟨⟨localEvidence.1, { cache, support, localEvidence := localEvidence.2 }⟩, ?_⟩
  simp [certifyWithSupport?, produced]

/-- The public constructor generates its own cache and predecessor support. The explicit
checker hypothesis records applicability of its callback-free bounded route; the remaining
readiness fields are independent topology, ligand separation and nondegenerate geometry. -/
theorem certifySupported?_total_of_ranked
    (input : Input) (target : Occurrence input)
    (callbackFree : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input))
    (checked : input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input) =
      some callbackFree)
    (ready : input.certified.LocalizedRankedTetrahedralReadiness target
      (input.certified.localizedDependencyView (referenceState input) target)) :
    ∃ certificate, certifySupported? input target = some certificate := by
  obtain ⟨certificate, produced⟩ := certifyWithSupport?_total_of_ranked input
    (Cached.buildRuntimeCache input) callbackFree target
    (Linear.produceDependencySupport input (Cached.buildRuntimeCache input) callbackFree target) ready
  refine ⟨certificate, ?_⟩
  simpa only [certifySupported?, checked, Option.bind_some] using produced

/-- Construct a returned descriptor together with both its reference-state agreement and
acceptance of the exported data-only certificate by the existing dependency checker. -/
theorem ranked_supported_result
    (input : Input) (target : Occurrence input)
    (callbackFree : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input))
    (checked : input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input) =
      some callbackFree)
    (ready : input.certified.LocalizedRankedTetrahedralReadiness target
      (input.certified.localizedDependencyView (referenceState input) target)) :
    ∃ certificate : Sigma fun descriptor => SupportedDescriptorCertificate input target descriptor,
      certifySupported? input target = some certificate ∧
      referenceState input target = some certificate.1 ∧
      check (runtimeSystem input) (dependencies input) certificate.2.nodes =
        some (certificate.2.support.facts ++ [(target, some certificate.1)]) := by
  obtain ⟨certificate, produced⟩ := certifySupported?_total_of_ranked input target callbackFree checked ready
  exact ⟨certificate, produced, certificate.2.reference_assignment, certificate.2.nodes_accepted⟩

end TetraStereo.OneCenter.LocalizedShortCircuit
