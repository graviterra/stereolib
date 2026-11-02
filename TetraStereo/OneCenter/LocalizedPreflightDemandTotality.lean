import TetraStereo.OneCenter.LocalizedPreflightDemandDiscovery
import TetraStereo.Certificate.WeightedDemandTotality

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand



































/-! ## The concrete budget is the generic cardinal budget -/

/-- The concrete structural traversal budget `occurrenceCount * (occurrenceCount + 1) + 1` is
exactly `Fintype.card cursor + 1` for the canonical cursor enumeration, by the exact card identity
`localizedRerootCursor_card`.  The `Fintype` instance is proof-only and never enumerated at
runtime. -/
theorem preflightExtendedDemandTraversalBudget_eq_card_add_one
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    [Fintype (input.LocalizedRerootCursor fuel)] :
    input.preflightExtendedDemandTraversalBudget fuel =
      Fintype.card (input.LocalizedRerootCursor fuel) + 1 := by
  dsimp only [preflightExtendedDemandTraversalBudget]
  rw [input.localizedRerootCursor_card fuel]

/-! ## Totality from acyclicity of the pruned reachable graph -/





theorem preparePreflightExtendedDemandPlan_total_of_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan := by
  letI := input.localizedRerootCursorFintype fuel
  obtain ⟨plan, computed⟩ :=
    prepare_total_of_acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots acyclic
  refine ⟨plan, ?_⟩
  show prepare (input.preflightExtendedWeightedDemandGraph fuel)
    (input.preflightExtendedDemandTraversalBudget fuel) roots = .ok plan
  rw [input.preflightExtendedDemandTraversalBudget_eq_card_add_one fuel]
  exact computed




theorem preparePreflightExtendedDemandPlan_success_iff_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) :
    (∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan) ↔
      Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots := by
  letI := input.localizedRerootCursorFintype fuel
  have generic := prepare_success_iff_acyclic
    (input.preflightExtendedWeightedDemandGraph fuel) roots
  constructor
  · rintro ⟨plan, computed⟩
    apply generic.mp
    refine ⟨plan, ?_⟩
    change prepare (input.preflightExtendedWeightedDemandGraph fuel)
      (input.preflightExtendedDemandTraversalBudget fuel) roots = .ok plan at computed
    rw [input.preflightExtendedDemandTraversalBudget_eq_card_add_one fuel] at computed
    exact computed
  · intro acyclic
    obtain ⟨plan, computed⟩ := generic.mpr acyclic
    refine ⟨plan, ?_⟩
    show prepare (input.preflightExtendedWeightedDemandGraph fuel)
      (input.preflightExtendedDemandTraversalBudget fuel) roots = .ok plan
    rw [input.preflightExtendedDemandTraversalBudget_eq_card_add_one fuel]
    exact computed

/-- Every constructor failure at the fixed structural budget has a concrete mathematical cause:
some cursor reachable in the pruned graph lies on a directed cycle.  Failure is therefore never a
budget artefact for an acyclic input. -/
theorem preparePreflightExtendedDemandPlan_error_has_reachableCycle
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (failure : DiscoveryFailure (input.LocalizedRerootCursor fuel))
    (failed : input.preparePreflightExtendedDemandPlan roots = .error failure) :
    ∃ cursor, Reachable (input.preflightExtendedWeightedDemandGraph fuel) roots cursor ∧
      Relation.TransGen (Edge (input.preflightExtendedWeightedDemandGraph fuel)) cursor cursor := by
  letI := input.localizedRerootCursorFintype fuel
  refine prepare_error_has_cycle (input.preflightExtendedWeightedDemandGraph fuel) roots failure ?_
  rw [← input.preflightExtendedDemandTraversalBudget_eq_card_add_one fuel]
  exact failed









theorem preparePreflightExtendedDemandPlan_produced_evaluate_eq_above
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : Plan (input.preflightExtendedWeightedDemandGraph fuel) roots)
    (produced : input.preparePreflightExtendedDemandPlan roots = .ok plan)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    input.preparePreflightExtendedDemandPlan roots = .ok plan ∧
      preflightExtendedDemandEvaluate plan target view =
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots :=
  ⟨produced, preflightExtendedDemandEvaluate_eq_above plan target view budget enough⟩



theorem preparePreflightExtendedDemandPlan_total_evaluate_stable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan ∧
      ∀ budget, plan.bound ≤ budget →
        preflightExtendedDemandEvaluate plan target view =
          input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots := by
  obtain ⟨plan, computed⟩ :=
    input.preparePreflightExtendedDemandPlan_total_of_acyclic roots acyclic
  exact ⟨plan, computed, fun budget enough =>
    preflightExtendedDemandEvaluate_eq_above plan target view budget enough⟩

/-! ## Discharging pruned acyclicity from existing inputs -/

/-- Existing extended-graph acyclicity implies totality of the pruned constructor, since the
preflight graph only removes edges. -/
theorem preparePreflightExtendedDemandPlan_total_of_extendedAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : input.ExtendedRule3DemandAcyclic roots) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan :=
  input.preparePreflightExtendedDemandPlan_total_of_acyclic roots
    (input.preflightExtendedWeightedDemandAcyclic_of_extended roots acyclic)



theorem preparePreflightExtendedDemandPlan_total_of_certificate
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (checked : input.ExtendedRule3DemandPlan roots) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan :=
  input.preparePreflightExtendedDemandPlan_total_of_acyclic roots checked.preflightAcyclic




theorem preflightExtendedWeightedDemandAcyclic_of_noPreflightRequests
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root)
    (noRequests : ∀ cursor : input.LocalizedRerootCursor fuel,
      input.LocalizedRerootCursorValid cursor →
        input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence = []) :
    Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots := by
  intro cursor reachable cycle
  obtain ⟨root, member, path⟩ := reachable
  have decreases : ∀ parent, input.LocalizedRerootCursorValid parent →
      ∀ child, Edge (input.preflightExtendedWeightedDemandGraph fuel) parent child →
        input.LocalizedRerootCursorValid child ∧
          input.localizedRerootCursorBudget child < input.localizedRerootCursorBudget parent := by
    intro parent valid child edge
    have childMember : child ∈ input.executableLocalizedRerootChildren parent := by
      have edge' := edge
      change child ∈ successors (input.preflightExtendedWeightedDemandGraph fuel) parent at edge'
      rw [preflightExtendedWeightedDemandGraph_successors, noRequests parent valid,
        List.flatten_nil, List.append_nil] at edge'
      exact edge'
    have derived := input.executableLocalizedRerootChildren_declarative parent
    exact ⟨input.localizedRerootChild_valid parent child _ derived childMember,
      input.localizedRerootChild_budget_lt parent child _ valid derived childMember⟩
  have pathClosed : ∀ {parent child}, input.LocalizedRerootCursorValid parent →
      Relation.ReflTransGen (Edge (input.preflightExtendedWeightedDemandGraph fuel)) parent child →
        input.LocalizedRerootCursorValid child := by
    intro parent child present path
    induction path with
    | refl => exact present
    | tail _ edge ih => exact (decreases _ ih _ edge).1
  have pathDecreases : ∀ {parent child}, input.LocalizedRerootCursorValid parent →
      Relation.TransGen (Edge (input.preflightExtendedWeightedDemandGraph fuel)) parent child →
        input.LocalizedRerootCursorValid child ∧
          input.localizedRerootCursorBudget child < input.localizedRerootCursorBudget parent := by
    intro parent child present path
    induction path with
    | single edge => exact decreases _ present _ edge
    | tail _ edge ih =>
      obtain ⟨valid, smaller⟩ := decreases _ ih.1 _ edge
      exact ⟨valid, smaller.trans ih.2⟩
  exact Nat.lt_irrefl _
    (pathDecreases (pathClosed (rootValid root member) path) cycle).2



theorem preparePreflightExtendedDemandPlan_total_of_noPreflightRequests
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root)
    (noRequests : ∀ cursor : input.LocalizedRerootCursor fuel,
      input.LocalizedRerootCursorValid cursor →
        input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence = []) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan :=
  input.preparePreflightExtendedDemandPlan_total_of_acyclic roots
    (input.preflightExtendedWeightedDemandAcyclic_of_noPreflightRequests roots rootValid noRequests)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
