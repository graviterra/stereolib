import TetraStereo.OneCenter.OfficialDescriptorEnvironment
import Mathlib.Order.FixedPoints

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-! ### Deterministic reachable-state closure -/

/-- States on the single forward orbit of a deterministic transition from a specified seed. -/
def DeterministicReachable {State : Type*} (step : State → State)
    (seed state : State) : Prop :=
  ∃ iterations, (step^[iterations]) seed = state

namespace DeterministicReachable

variable {State : Type*} {step : State → State} {seed left right : State}

/-- Every seed is reachable in zero transitions. -/
theorem refl (seed : State) : DeterministicReachable step seed seed :=
  ⟨0, rfl⟩

/-- Taking one transition preserves reachability. -/
theorem next {state : State} (reachable : DeterministicReachable step seed state) :
    DeterministicReachable step seed (step state) := by
  rcases reachable with ⟨iterations, rfl⟩
  refine ⟨iterations + 1, ?_⟩
  rw [Function.iterate_succ_apply']

/-- A state reachable after starting with the first transition is reachable from the original
seed. -/
theorem from_next {state : State}
    (reachable : DeterministicReachable step (step seed) state) :
    DeterministicReachable step seed state := by
  rcases reachable with ⟨iterations, reached⟩
  refine ⟨iterations + 1, ?_⟩
  rw [Function.iterate_succ_apply]
  exact reached

/-- The deterministic orbit has at most one reachable fixed point.  No monotonicity or
inflationarity is required: after the orbit reaches a fixed point, every subsequent iterate is the
same state. -/
theorem fixedPoint_unique
    (leftReachable : DeterministicReachable step seed left)
    (rightReachable : DeterministicReachable step seed right)
    (leftFixed : step left = left) (rightFixed : step right = right) :
    left = right := by
  rcases leftReachable with ⟨leftIterations, leftAt⟩
  rcases rightReachable with ⟨rightIterations, rightAt⟩
  rcases Nat.le_total leftIterations rightIterations with leftFirst | rightFirst
  · obtain ⟨extra, rightEq⟩ := Nat.exists_eq_add_of_le leftFirst
    subst rightIterations
    rw [Nat.add_comm, Function.iterate_add_apply, leftAt,
      Function.iterate_fixed leftFixed] at rightAt
    exact rightAt
  · obtain ⟨extra, leftEq⟩ := Nat.exists_eq_add_of_le rightFirst
    subst leftIterations
    rw [Nat.add_comm, Function.iterate_add_apply, rightAt,
      Function.iterate_fixed rightFixed] at leftAt
    exact leftAt.symm

end DeterministicReachable

/-!
  Descriptor fixed points.

  The executable schedulers previously exposed only the conditional statement that two equal
  consecutive iterations constitute a fixed point.  This module states and proves the stronger
  mathematical boundary needed by recursive CIP Rules 4b/4c/5: a rule operator that only adds
  justified facts and is monotone in its available evidence has a canonical least fixed point above
  every seed.

  The theorem is deliberately independent of a traversal or schedule.  A concrete descriptor
  engine reaches the same result once its one-pass update is proved to implement the same closure
  operator.  Failure of either inflationarity or monotonicity is therefore an explicit obstruction,
  rather than an implicit appeal to iteration order.
-/

/-- A descriptor-rule closure operator over typed facts.  `monotone` says that making more evidence
available cannot invalidate an inference; `inflationary` says that established facts are retained. -/
structure DescriptorClosureOperator (Fact : Type*) where
  step : Set Fact →o Set Fact
  inflationary : ∀ facts, facts ⊆ step facts

namespace DescriptorClosureOperator

variable {Fact : Type*}

/-- Add a required seed to every update.  This is again monotone. -/
def seededStep (operator : DescriptorClosureOperator Fact) (seed : Set Fact) :
    Set Fact →o Set Fact where
  toFun facts := seed ∪ operator.step facts
  monotone' := by
    intro left right included
    exact Set.union_subset_union Set.Subset.rfl (operator.step.monotone included)

/-- The canonical descriptor assignment generated from a seed: the least fixed point of the
seed-preserving update. -/
def closureFrom (operator : DescriptorClosureOperator Fact) (seed : Set Fact) : Set Fact :=
  (operator.seededStep seed).lfp

/-- A descriptor state is an admissible fixed point above a seed. -/
def IsFixedPointAbove (operator : DescriptorClosureOperator Fact)
    (seed state : Set Fact) : Prop :=
  seed ⊆ state ∧ operator.step state = state

/-- The seeded update is itself inflationary. -/
theorem subset_seededStep (operator : DescriptorClosureOperator Fact)
    (seed facts : Set Fact) :
    facts ⊆ operator.seededStep seed facts := by
  exact Set.Subset.trans (operator.inflationary facts) Set.subset_union_right

/-- The least fixed point contains every seed fact. -/
theorem seed_subset_closureFrom (operator : DescriptorClosureOperator Fact)
    (seed : Set Fact) :
    seed ⊆ operator.closureFrom seed := by
  have fixed := (operator.seededStep seed).map_lfp
  intro fact member
  unfold closureFrom
  rw [← fixed]
  exact Set.mem_union_left _ member

/-- The least seeded fixed point is closed under the original descriptor operator. -/
theorem step_subset_closureFrom (operator : DescriptorClosureOperator Fact)
    (seed : Set Fact) :
    operator.step (operator.closureFrom seed) ⊆ operator.closureFrom seed := by
  have fixed := (operator.seededStep seed).map_lfp
  intro fact member
  unfold closureFrom at member ⊢
  rw [← fixed]
  exact Set.mem_union_right _ member

/-- The canonical closure is an actual fixed point of the original rule operator, not merely of
the seed-adjoining wrapper. -/
theorem step_closureFrom (operator : DescriptorClosureOperator Fact) (seed : Set Fact) :
    operator.step (operator.closureFrom seed) = operator.closureFrom seed := by
  apply Set.Subset.antisymm
  · exact operator.step_subset_closureFrom seed
  · exact operator.inflationary (operator.closureFrom seed)

/-- Existence: every seed has a descriptor fixed point extending it. -/
theorem closureFrom_isFixedPointAbove (operator : DescriptorClosureOperator Fact)
    (seed : Set Fact) :
    operator.IsFixedPointAbove seed (operator.closureFrom seed) :=
  ⟨operator.seed_subset_closureFrom seed, operator.step_closureFrom seed⟩

/-- Any fixed point of the original operator that contains the seed is also a fixed point of the
seeded update. -/
theorem seededStep_eq_of_isFixedPointAbove (operator : DescriptorClosureOperator Fact)
    {seed state : Set Fact} (fixed : operator.IsFixedPointAbove seed state) :
    operator.seededStep seed state = state := by
  apply Set.Subset.antisymm
  · exact Set.union_subset fixed.1 (fixed.2.le)
  · exact operator.subset_seededStep seed state

/-- Minimality: the canonical closure is below every descriptor fixed point extending the seed. -/
theorem closureFrom_subset_of_isFixedPointAbove (operator : DescriptorClosureOperator Fact)
    {seed state : Set Fact} (fixed : operator.IsFixedPointAbove seed state) :
    operator.closureFrom seed ⊆ state := by
  exact (operator.seededStep seed).lfp_le_fixed
    (operator.seededStep_eq_of_isFixedPointAbove fixed)

/-- The canonical closure is the least admissible fixed point above the seed. -/
theorem closureFrom_isLeast (operator : DescriptorClosureOperator Fact) (seed : Set Fact) :
    IsLeast { state | operator.IsFixedPointAbove seed state } (operator.closureFrom seed) :=
  ⟨operator.closureFrom_isFixedPointAbove seed,
    fun _ fixed => operator.closureFrom_subset_of_isFixedPointAbove fixed⟩

/-- Uniqueness in the relevant sense: any state claimed to be the least fixed point above the seed
is equal to the canonical closure.  Thus traversal-independent implementations have only one
possible least result. -/
theorem eq_closureFrom_of_isLeast (operator : DescriptorClosureOperator Fact)
    {seed state : Set Fact}
    (least : IsLeast { candidate | operator.IsFixedPointAbove seed candidate } state) :
    state = operator.closureFrom seed := by
  apply Set.Subset.antisymm
  · exact least.2 (operator.closureFrom_isFixedPointAbove seed)
  · exact operator.closureFrom_isLeast seed |>.2 least.1

/-- Two independently obtained least fixed points above the same seed are identical. -/
theorem leastFixedPoint_unique (operator : DescriptorClosureOperator Fact)
    {seed left right : Set Fact}
    (leftLeast : IsLeast { state | operator.IsFixedPointAbove seed state } left)
    (rightLeast : IsLeast { state | operator.IsFixedPointAbove seed state } right) :
    left = right := by
  exact Set.Subset.antisymm (leftLeast.2 rightLeast.1) (rightLeast.2 leftLeast.1)

/-- A schedule or traversal is semantically correct when it returns the least fixed point of the
same closure operator.  Any two correct implementations are therefore observationally identical. -/
theorem implementation_independent (operator : DescriptorClosureOperator Fact)
    {seed first second : Set Fact}
    (firstCorrect : IsLeast { state | operator.IsFixedPointAbove seed state } first)
    (secondCorrect : IsLeast { state | operator.IsFixedPointAbove seed state } second) :
    first = second :=
  operator.leastFixedPoint_unique firstCorrect secondCorrect

end DescriptorClosureOperator

end OneCenter
end TetraStereo
