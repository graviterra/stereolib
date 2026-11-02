import TetraStereo.OneCenter.LocalizedFullyTerminalGuardedRule3Key
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand















































theorem actualPreparedKey_stable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (_prepared : prepareTerminalGuardedDemandPlan input target view roots = .ok plan)
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ plan.ranks.vertices)
    (first second : Nat) (firstEnough : plan.ranks.height cursor ≤ first)
    (secondEnough : plan.ranks.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.buildLocalizedFullyTerminalGuardedRule3KeyExec? target view first excluded cursor =
      input.buildLocalizedFullyTerminalGuardedRule3KeyExec? target view second excluded cursor :=
  buildLocalizedFullyTerminalGuardedRule3Key_stable (input := input) (carrierFuel := fuel)
    (target := target) (view := view) plan.ranks cursor member first second firstEnough
    secondEnough excluded

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPreparedKey_stable






theorem actualPreparedFrame_stable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (_prepared : prepareTerminalGuardedDemandPlan input target view roots = .ok plan)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view plan.bound roots =
      input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view budget roots :=
  fullyTerminalGuardedFrame_stable (input := input) (fuel := fuel) (target := target)
    (view := view) (buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion input target view)
    plan.ranks roots plan.covers plan.bound budget (Nat.le_refl _) enough

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPreparedFrame_stable



theorem actualPreparedEvaluate_eq_above
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (_prepared : prepareTerminalGuardedDemandPlan input target view roots = .ok plan)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    FullyTerminalGuardedPlan.evaluate plan
        (buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion input target view) =
      input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view budget roots :=
  buildLocalizedFullyTerminalGuardedRule3Plan_evaluate_eq_above (input := input)
    (carrierFuel := fuel) (target := target) (view := view) (roots := roots) plan budget enough

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPreparedEvaluate_eq_above



theorem actualPreparedEvaluate_at_bound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (_prepared : prepareTerminalGuardedDemandPlan input target view roots = .ok plan) :
    FullyTerminalGuardedPlan.evaluate plan
        (buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion input target view) =
      input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view plan.bound roots :=
  rfl

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPreparedEvaluate_at_bound

/-! ## Existence combined with acyclicity -/










theorem actualPreparePlan_exists_stability
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (succeeds : ∃ plan,
      prepareTerminalGuardedDemandPlan input target view roots = .ok plan) :
    ∃ plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots,
      Acyclic (terminalGuardedWeightedDemandGraph input target view) roots ∧
        (∀ budget, plan.bound ≤ budget →
          input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view plan.bound roots =
            input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view budget roots) ∧
        (∀ (cursor : input.LocalizedRerootCursor fuel), cursor ∈ plan.ranks.vertices →
          ∀ (first second : Nat), plan.ranks.height cursor ≤ first →
            plan.ranks.height cursor ≤ second →
              ∀ excluded : List input.LocalizedRule3PhysicalUnitId,
                input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
                    target view first excluded cursor =
                  input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
                    target view second excluded cursor) := by
  obtain ⟨plan, prepared⟩ := succeeds
  exact ⟨plan,
    prepareTerminalGuardedDemandPlan_acyclic input target view roots ⟨plan, prepared⟩,
    fun budget enough => actualPreparedFrame_stable input target view roots plan prepared
      budget enough,
    fun cursor member first second firstEnough secondEnough excluded =>
      actualPreparedKey_stable input target view roots plan prepared cursor member first second
        firstEnough secondEnough excluded⟩

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPreparePlan_exists_stability

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
