import TetraStereo.OneCenter.LocalizedPreflightDemandTotality
import TetraStereo.OneCenter.LocalizedExtendedMandatoryRecursion
import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5Descriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand







































































/-! ## All-fuel refusal -/

/-- The actual extended two-pass evaluator refuses the requested frame at every budget.  This is a
purely operational property of the executable recursion; it says nothing about chemical
applicability, descriptor existence or topological ambiguity. -/
def UniversalRule3AllFuelRefusal (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  ∀ evaluationBudget,
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view evaluationBudget roots = none

/-! ## Constructor error is all-fuel refusal, not chemical ambiguity -/

/-- Every constructor error yields an operational all-fuel refusal of the actual extended frame.
The only mathematical cause used is the reachable preflight cycle extracted by the green totality
module, fed to the registered mandatory-recursion refusal theorem.  This is deliberately weaker
than a claim about chemical applicability: it says the executable evaluator produces `none` at
every budget, not that no declarative descriptor exists. -/
theorem preparePreflightExtendedDemandPlan_error_allFuelRefusal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (failure : DiscoveryFailure (input.LocalizedRerootCursor carrierFuel))
    (failed : input.preparePreflightExtendedDemandPlan roots = .error failure)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    UniversalRule3AllFuelRefusal input roots target view := by
  intro evaluationBudget
  obtain ⟨cursor, reachable, cycle⟩ :=
    input.preparePreflightExtendedDemandPlan_error_has_reachableCycle roots failure failed
  exact input.extendedShortCircuitRule3Frame_none_all_budgets_of_reachable_cycle
    target view roots reachable cycle evaluationBudget

/-- Exact operational characterization of constructor error: it is equivalent to the existence of
a reachable cycle in the preflight-pruned demand graph.  The forward direction is the green
reachable-cycle extraction; the backward direction uses success-implies-acyclicity. -/
theorem preparePreflightExtendedDemandPlan_error_iff_reachableCycle
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel)) :
    (∃ failure : DiscoveryFailure (input.LocalizedRerootCursor carrierFuel),
        input.preparePreflightExtendedDemandPlan roots = .error failure) ↔
      ∃ cursor : input.LocalizedRerootCursor carrierFuel,
        Reachable (input.preflightExtendedWeightedDemandGraph carrierFuel) roots cursor ∧
          Relation.TransGen
            (Edge (input.preflightExtendedWeightedDemandGraph carrierFuel)) cursor cursor := by
  constructor
  · rintro ⟨failure, failed⟩
    exact input.preparePreflightExtendedDemandPlan_error_has_reachableCycle roots failure failed
  · rintro ⟨cursor, reachable, cycle⟩
    cases computed : input.preparePreflightExtendedDemandPlan roots with
    | ok plan =>
        have acyclic :=
          (input.preparePreflightExtendedDemandPlan_success_iff_acyclic roots).mp ⟨plan, computed⟩
        exact False.elim (acyclic cursor reachable cycle)
    | error failure => exact ⟨failure, rfl⟩

/-! ## Executable preparation outcome -/





def prepareUniversalRule3EvaluationOutcome (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat × Option input.LocalizedRule3CanonicalKeyFrame :=
  match input.preparePreflightExtendedDemandPlan roots with
  | .ok plan => (plan.bound, preflightExtendedDemandEvaluate plan target view)
  | .error _ => (0, none)




theorem prepareUniversalRule3EvaluationOutcome_bound_cases
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (∃ plan : Plan (input.preflightExtendedWeightedDemandGraph carrierFuel) roots,
        input.preparePreflightExtendedDemandPlan roots = .ok plan ∧
          (prepareUniversalRule3EvaluationOutcome input roots target view).1 = plan.bound) ∨
      ((∃ failure : DiscoveryFailure (input.LocalizedRerootCursor carrierFuel),
          input.preparePreflightExtendedDemandPlan roots = .error failure) ∧
        (prepareUniversalRule3EvaluationOutcome input roots target view).1 = 0 ∧
        (prepareUniversalRule3EvaluationOutcome input roots target view).2 = none) := by
  cases computed : input.preparePreflightExtendedDemandPlan roots with
  | ok plan =>
      left
      exact ⟨plan, rfl, by simp [prepareUniversalRule3EvaluationOutcome, computed]⟩
  | error failure =>
      right
      refine ⟨⟨failure, rfl⟩, ?_, ?_⟩
      · simp [prepareUniversalRule3EvaluationOutcome, computed]
      · simp [prepareUniversalRule3EvaluationOutcome, computed]







theorem prepareUniversalRule3EvaluationOutcome_stable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ evaluationBudget,
      (prepareUniversalRule3EvaluationOutcome input roots target view).1 ≤ evaluationBudget →
        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          target view evaluationBudget roots =
          (prepareUniversalRule3EvaluationOutcome input roots target view).2 := by
  intro evaluationBudget enough
  cases computed : input.preparePreflightExtendedDemandPlan roots with
  | ok plan =>
      have boundEq :
          (prepareUniversalRule3EvaluationOutcome input roots target view).1 = plan.bound := by
        simp [prepareUniversalRule3EvaluationOutcome, computed]
      have frameEq :
          (prepareUniversalRule3EvaluationOutcome input roots target view).2 =
            preflightExtendedDemandEvaluate plan target view := by
        simp [prepareUniversalRule3EvaluationOutcome, computed]
      rw [frameEq]
      have enough' : plan.bound ≤ evaluationBudget := boundEq ▸ enough
      exact (preflightExtendedDemandEvaluate_eq_above plan target view evaluationBudget
        enough').symm
  | error failure =>
      have frameEq :
          (prepareUniversalRule3EvaluationOutcome input roots target view).2 = none := by
        simp [prepareUniversalRule3EvaluationOutcome, computed]
      rw [frameEq]
      exact input.preparePreflightExtendedDemandPlan_error_allFuelRefusal roots failure
        computed target view evaluationBudget

/-- In the refusal branch the computed bound is zero, so the stability hypothesis of the main
theorem is automatic at every budget; in particular the frame is `none` at all budgets.  This is
the all-fuel-refusal form of the outcome. -/
theorem prepareUniversalRule3EvaluationOutcome_error_allFuelRefusal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (refused : ∃ failure : DiscoveryFailure (input.LocalizedRerootCursor carrierFuel),
      input.preparePreflightExtendedDemandPlan roots = .error failure) :
    (prepareUniversalRule3EvaluationOutcome input roots target view).2 = none ∧
      UniversalRule3AllFuelRefusal input roots target view := by
  obtain ⟨failure, failed⟩ := refused
  have frameEq :
      (prepareUniversalRule3EvaluationOutcome input roots target view).2 = none := by
    simp [prepareUniversalRule3EvaluationOutcome, failed]
  exact ⟨frameEq,
    input.preparePreflightExtendedDemandPlan_error_allFuelRefusal roots failure failed target view⟩

/-! ## Successful outcomes retain the existing declarative meaning -/

/-- Whenever the returned optional frame is `some frame`, that frame has the existing declarative
meaning at the returned computed bound.  The statement is conditional on the outcome being
successful; the refusal branch is not reinterpreted as a declarative claim. -/
theorem prepareUniversalRule3EvaluationOutcome_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed :
      (prepareUniversalRule3EvaluationOutcome input roots target view).2 = some frame) :
    input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view
      (prepareUniversalRule3EvaluationOutcome input roots target view).1 roots frame := by
  cases prepared : input.preparePreflightExtendedDemandPlan roots with
  | ok plan =>
      have boundEq :
          (prepareUniversalRule3EvaluationOutcome input roots target view).1 = plan.bound := by
        simp [prepareUniversalRule3EvaluationOutcome, prepared]
      have frameEq :
          (prepareUniversalRule3EvaluationOutcome input roots target view).2 =
            preflightExtendedDemandEvaluate plan target view := by
        simp [prepareUniversalRule3EvaluationOutcome, prepared]
      have evaluateSome : preflightExtendedDemandEvaluate plan target view = some frame := by
        rw [← frameEq]
        exact computed
      rw [boundEq]
      exact preflightExtendedDemandEvaluate_sound plan target view frame evaluateSome
  | error failure =>
      have frameEq :
          (prepareUniversalRule3EvaluationOutcome input roots target view).2 = none := by
        simp [prepareUniversalRule3EvaluationOutcome, prepared]
      rw [frameEq] at computed
      cases computed








/-- Under the explicit side condition that the computed bound fits in the fixed production fuel,
the prepared optional frame equals the actual production evaluation at that fuel. -/
theorem prepareUniversalRule3EvaluationOutcome_eq_production_of_bound_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (enough :
      (prepareUniversalRule3EvaluationOutcome input roots target view).1 ≤
        localizedDescriptorBearingRule3EvaluationFuel carrierFuel) :
    (prepareUniversalRule3EvaluationOutcome input roots target view).2 =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) roots :=
  (input.prepareUniversalRule3EvaluationOutcome_stable roots target view
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) enough).symm

/-- In the refusal branch the computed bound is zero, so the production-fuel side condition holds
automatically and the prepared frame (`none`) equals the production evaluation.  No claim is made
that the production fuel is sufficient in the success branch. -/
theorem prepareUniversalRule3EvaluationOutcome_error_eq_production
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (refused : ∃ failure : DiscoveryFailure (input.LocalizedRerootCursor carrierFuel),
      input.preparePreflightExtendedDemandPlan roots = .error failure) :
    (prepareUniversalRule3EvaluationOutcome input roots target view).2 =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) roots := by
  obtain ⟨failure, failed⟩ := refused
  have frameEq :
      (prepareUniversalRule3EvaluationOutcome input roots target view).2 = none := by
    simp [prepareUniversalRule3EvaluationOutcome, failed]
  have productionNone :
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) roots = none :=
    input.preparePreflightExtendedDemandPlan_error_allFuelRefusal roots failure failed target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
  rw [frameEq, productionNone]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
