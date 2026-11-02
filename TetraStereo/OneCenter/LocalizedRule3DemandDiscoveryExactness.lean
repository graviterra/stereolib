import TetraStereo.OneCenter.LocalizedRule3DemandDiscoveryAcyclic

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Every edge checked by a rank certificate stays in its vertices and strictly decreases rank.
Callback requests include their extra frame step in the stronger stored inequality. -/
theorem Rule3DemandRankCertificate.edge_decreases
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.Rule3DemandRankCertificate fuel)
    (parent child : input.LocalizedRerootCursor fuel)
    (present : parent ∈ certificate.vertices) (edge : input.Rule3DemandEdge parent child) :
    child ∈ certificate.vertices ∧ certificate.height child < certificate.height parent := by
  change child ∈ input.executableLocalizedRerootChildren parent ++
    (input.rule3NodeCallbackRequests parent.occurrence).flatten at edge
  rcases List.mem_append.mp edge with childEdge | callbackEdge
  · obtain ⟨covered, bounded⟩ := certificate.children parent present child childEdge
    exact ⟨covered, by omega⟩
  · obtain ⟨request, requested, reference⟩ := List.mem_flatten.mp callbackEdge
    obtain ⟨covered, bounded⟩ := certificate.callbacks parent present request requested
    have belowMax := rule3CursorListHeight_mem certificate.height request child reference
    exact ⟨covered child reference, by omega⟩

theorem Rule3DemandRankCertificate.path_closed
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.Rule3DemandRankCertificate fuel)
    {parent child : input.LocalizedRerootCursor fuel}
    (present : parent ∈ certificate.vertices)
    (path : Relation.ReflTransGen input.Rule3DemandEdge parent child) :
    child ∈ certificate.vertices := by
  induction path with
  | refl => exact present
  | tail _ edge ih => exact (certificate.edge_decreases _ _ ih edge).1

theorem Rule3DemandRankCertificate.path_decreases
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.Rule3DemandRankCertificate fuel)
    {parent child : input.LocalizedRerootCursor fuel}
    (present : parent ∈ certificate.vertices)
    (path : Relation.TransGen input.Rule3DemandEdge parent child) :
    child ∈ certificate.vertices ∧ certificate.height child < certificate.height parent := by
  induction path with
  | single edge => exact certificate.edge_decreases _ _ present edge
  | tail _ edge ih =>
    obtain ⟨covered, smaller⟩ := certificate.edge_decreases _ _ ih.1 edge
    exact ⟨covered, smaller.trans ih.2⟩

/-- The certificate is sufficient to rule out all cycles reachable from the requested roots. -/
theorem Rule3DemandPlan.acyclic
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)} (plan : input.Rule3DemandPlan roots) :
    input.Rule3DemandAcyclic roots := by
  intro cursor reachable cycle
  obtain ⟨root, rootMember, path⟩ := reachable
  have present := plan.ranks.path_closed (plan.covers root rootMember) path
  exact Nat.lt_irrefl _ (plan.ranks.path_decreases present cycle).2



theorem prepareRule3DemandPlan_success_iff_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) :
    (∃ plan, input.prepareRule3DemandPlan roots = .ok plan) ↔ input.Rule3DemandAcyclic roots := by
  exact ⟨fun ⟨plan, _⟩ => plan.acyclic, input.prepareRule3DemandPlan_total_of_acyclic roots⟩

/-- Graph rejection has a concrete mathematical cause: a reachable cycle in the conservative
potential-demand graph. It does not assert that the molecule has no chemical descriptor. -/
theorem prepareRule3DemandPlan_error_has_cycle
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (failure : input.Rule3DemandDiscoveryFailure fuel)
    (failed : input.prepareRule3DemandPlan roots = .error failure) :
    ∃ cursor, input.Rule3DemandReachable roots cursor ∧
      Relation.TransGen input.Rule3DemandEdge cursor cursor := by
  classical
  by_contra absent
  have acyclic : input.Rule3DemandAcyclic roots := by
    intro cursor reachable cycle
    exact absent ⟨cursor, reachable, cycle⟩
  obtain ⟨plan, succeeds⟩ := input.prepareRule3DemandPlan_total_of_acyclic roots acyclic
  rw [failed] at succeeds
  contradiction



theorem prepareRule3DemandPlan_constructs_stable_evaluator
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) (acyclic : input.Rule3DemandAcyclic roots) :
    ∃ plan, input.prepareRule3DemandPlan roots = .ok plan ∧
      ∀ (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
        (budget : Nat), plan.bound ≤ budget →
          plan.evaluate target view = input.buildLocalizedShortCircuitRule3FrameExec? target view budget roots := by
  obtain ⟨plan, succeeds⟩ := input.prepareRule3DemandPlan_total_of_acyclic roots acyclic
  exact ⟨plan, succeeds, plan.evaluate_eq_above⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
