import TetraStereo.OneCenter.DeclarativeCIPOccurrenceScheduler

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP
namespace RankedIteration

universe u v w

/-!
# Rank-bounded raw iteration for occurrence equations

This module adds a computable iteration front-end to the generic occurrence-level CIP fixed
point.  The iterator is deliberately independent of `OccurrenceSystem`: it accepts a raw step

    rawStep : (Occurrence → Option Label) → Occurrence → Option Label

and an arbitrary seed state, and iterates it by ordinary `Nat` recursion.  In particular the
runtime object does not mention `OccurrenceSystem.buildOccurrenceState`, which is a noncomputable
well-founded fixpoint, and it never needs `Fintype Occurrence`.

The main theorem proves that if the raw step agrees with `system.executableStep`, the evaluator is
local for `dependency`, and `dependency` strictly decreases a rank function, then after `n`
iterations every occurrence of rank `< n` has already reached the well-founded solution.  Thus a
finite uniform bound on the rank gives function equality, seed independence, fixedness, and
agreement with the scheduler closure.
-/

/-- A raw executable step between complete occurrence states. -/
abbrev RawStep (Occurrence : Type v) (Label : Type w) : Type (max v w) :=
  OccurrenceState Occurrence Label → OccurrenceState Occurrence Label

/-- Iterate a raw occurrence step from a seed state by `Nat` recursion.

This is a computable definition: no occurrence system, classical choice, or well-founded fixpoint
appears in its body. -/
def iterate {Occurrence : Type v} {Label : Type w}
    (rawStep : RawStep Occurrence Label) (seed : OccurrenceState Occurrence Label) :
    Nat → OccurrenceState Occurrence Label
  | 0 => seed
  | n + 1 => rawStep (iterate rawStep seed n)

@[simp] theorem iterate_zero {Occurrence : Type v} {Label : Type w}
    (rawStep : RawStep Occurrence Label) (seed : OccurrenceState Occurrence Label) :
    iterate rawStep seed 0 = seed := rfl

@[simp] theorem iterate_succ {Occurrence : Type v} {Label : Type w}
    (rawStep : RawStep Occurrence Label) (seed : OccurrenceState Occurrence Label) (n : Nat) :
    iterate rawStep seed n.succ = rawStep (iterate rawStep seed n) := rfl

/-- A strict rank decrease makes `dependency` well-founded by pulling back `Nat`'s own
well-founded order. -/
theorem wellFounded_of_rank {Occurrence : Type v}
    (dependency : Occurrence → Occurrence → Prop)
    (rank : Occurrence → Nat)
    (rank_decrease : ∀ {inner target : Occurrence},
      dependency inner target → rank inner < rank target) :
    WellFounded dependency := by
  refine Subrelation.wf ?_ (InvImage.wf rank (Nat.lt_wfRel).2)
  intro inner target hdependency
  show rank inner < rank target
  exact rank_decrease hdependency

section Convergence

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}
variable (system : OccurrenceSystem FinalUnit Occurrence Label)
variable (dependency : Occurrence → Occurrence → Prop)
variable (locality : system.EvaluatorLocalFor dependency)
variable (rank : Occurrence → Nat)
variable (rank_decrease : ∀ {inner target : Occurrence},
  dependency inner target → rank inner < rank target)
variable (rawStep : RawStep Occurrence Label)
variable (step_eq : ∀ (state : OccurrenceState Occurrence Label) (occurrence : Occurrence),
  rawStep state occurrence = system.executableStep state occurrence)

/- Every theorem below mentions only part of the section telescope in its own statement, while
several proofs also need the evaluator, the locality hypothesis and the raw-step agreement.
Unused section variables are not in scope in a theorem body in Lean 4, so the whole telescope is
included explicitly.  Each generated declaration therefore takes the leading explicit arguments
`system`, `dependency`, `locality`, `rank`, `rank_decrease`, `rawStep`, `step_eq`; calls between
these theorems below pass them by name.  The one exception is
`rawStep_eq_executableStateStep`, whose statement and proof use only `system`, `rawStep` and
`step_eq`: the remaining four are omitted there so that no declaration carries an argument it
never mentions. -/
include system dependency locality rank rank_decrease rawStep step_eq

omit dependency locality rank rank_decrease in
/-- The raw step is the executable state step pointwise. -/
theorem rawStep_eq_executableStateStep (state : OccurrenceState Occurrence Label) :
    rawStep state = system.executableStateStep state := by
  funext occurrence
  exact step_eq state occurrence

/-- The central rank-bounded convergence theorem.

After `n` iterations, every occurrence whose rank is below `n` has the same optional label as the
well-founded executable solution.  The proof is ordinary induction on `n`: the rank decrease moves
all strict dependencies of a target below the previous induction hypothesis, and locality plus the
fixed-point equation for `buildOccurrenceState` finish the step. -/
theorem iterate_eq_buildOccurrenceState
    (wellFounded : WellFounded dependency)
    (seed : OccurrenceState Occurrence Label) (n : Nat) :
    ∀ occurrence, rank occurrence < n →
      iterate rawStep seed n occurrence =
        system.buildOccurrenceState dependency wellFounded occurrence := by
  induction n with
  | zero =>
      intro occurrence h
      exact False.elim (Nat.not_lt_zero (rank occurrence) h)
  | succ n ih =>
      intro occurrence hrank
      have hrank_le : rank occurrence ≤ n := Nat.le_of_lt_succ hrank
      calc
        iterate rawStep seed n.succ occurrence
            = rawStep (iterate rawStep seed n) occurrence := rfl
        _ = system.executableStep (iterate rawStep seed n) occurrence :=
            step_eq (iterate rawStep seed n) occurrence
        _ = system.executableStep
              (system.buildOccurrenceState dependency wellFounded) occurrence :=
            locality (iterate rawStep seed n)
              (system.buildOccurrenceState dependency wellFounded) occurrence
              (fun inner hdependency =>
                ih inner (Nat.lt_of_lt_of_le (rank_decrease hdependency) hrank_le))
        _ = system.buildOccurrenceState dependency wellFounded occurrence := by
            have hfixed :=
              system.buildOccurrenceState_fixed dependency wellFounded locality
            exact congrFun hfixed occurrence

/-- A variant that derives well-foundedness from the rank decrease instead of taking it as a
separate hypothesis. -/
theorem iterate_eq_buildOccurrenceState_of_rank
    (seed : OccurrenceState Occurrence Label) (n : Nat) :
    ∀ occurrence, rank occurrence < n →
      iterate rawStep seed n occurrence =
        system.buildOccurrenceState dependency
          (wellFounded_of_rank dependency rank rank_decrease) occurrence := by
  exact iterate_eq_buildOccurrenceState
    (system := system) (dependency := dependency) (locality := locality)
    (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
    (step_eq := step_eq)
    (wellFounded_of_rank dependency rank rank_decrease) seed n

/-- A finite uniform rank bound gives function equality after the bound number of iterations. -/
theorem iterate_eq_buildOccurrenceState_of_uniformBound
    (wellFounded : WellFounded dependency)
    (seed : OccurrenceState Occurrence Label) (bound : Nat)
    (rank_lt_bound : ∀ occurrence, rank occurrence < bound) :
    iterate rawStep seed bound =
      system.buildOccurrenceState dependency wellFounded := by
  funext occurrence
  exact iterate_eq_buildOccurrenceState
    (system := system) (dependency := dependency) (locality := locality)
    (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
    (step_eq := step_eq)
    wellFounded seed bound occurrence (rank_lt_bound occurrence)

/-- Once a uniform rank bound has passed, the raw iteration is independent of the seed. -/
theorem iterate_seed_independent
    (wellFounded : WellFounded dependency)
    (seed seed' : OccurrenceState Occurrence Label) (bound : Nat)
    (rank_lt_bound : ∀ occurrence, rank occurrence < bound) :
    iterate rawStep seed bound = iterate rawStep seed' bound := by
  calc
    iterate rawStep seed bound
        = system.buildOccurrenceState dependency wellFounded :=
            iterate_eq_buildOccurrenceState_of_uniformBound
              (system := system) (dependency := dependency) (locality := locality)
              (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
              (step_eq := step_eq) wellFounded seed bound rank_lt_bound
    _ = iterate rawStep seed' bound :=
            (iterate_eq_buildOccurrenceState_of_uniformBound
              (system := system) (dependency := dependency) (locality := locality)
              (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
              (step_eq := step_eq) wellFounded seed' bound rank_lt_bound).symm

/-- At a uniform rank bound the raw iteration is a fixed point of the raw step. -/
theorem iterate_fixed_of_uniformBound
    (wellFounded : WellFounded dependency)
    (seed : OccurrenceState Occurrence Label) (bound : Nat)
    (rank_lt_bound : ∀ occurrence, rank occurrence < bound) :
    rawStep (iterate rawStep seed bound) = iterate rawStep seed bound := by
  calc
    rawStep (iterate rawStep seed bound)
        = iterate rawStep seed bound.succ := (iterate_succ rawStep seed bound).symm
    _ = system.buildOccurrenceState dependency wellFounded :=
            iterate_eq_buildOccurrenceState_of_uniformBound
              (system := system) (dependency := dependency) (locality := locality)
              (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
              (step_eq := step_eq) wellFounded seed bound.succ
              (fun occurrence =>
                Nat.lt_trans (rank_lt_bound occurrence) (Nat.lt_succ_self bound))
    _ = iterate rawStep seed bound :=
            (iterate_eq_buildOccurrenceState_of_uniformBound
              (system := system) (dependency := dependency) (locality := locality)
              (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
              (step_eq := step_eq) wellFounded seed bound rank_lt_bound).symm

/-- Under derivation/step correspondence, a rank-bounded raw iteration is a declarative CIP
model. -/
theorem cipModel_iterate_of_uniformBound
    (correspondence : system.DerivationStepCorrespondence)
    (wellFounded : WellFounded dependency)
    (seed : OccurrenceState Occurrence Label) (bound : Nat)
    (rank_lt_bound : ∀ occurrence, rank occurrence < bound) :
    system.CIPModel (iterate rawStep seed bound) := by
  rw [iterate_eq_buildOccurrenceState_of_uniformBound
    (system := system) (dependency := dependency) (locality := locality)
    (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
    (step_eq := step_eq) wellFounded seed bound rank_lt_bound]
  rw [system.cipModel_iff_executableStateStep_fixed correspondence]
  exact system.buildOccurrenceState_fixed dependency wellFounded locality

/-- Under correspondence, the rank-bounded raw iteration is the unique declarative model. -/
theorem iterate_eq_model_of_uniformBound
    (correspondence : system.DerivationStepCorrespondence)
    (wellFounded : WellFounded dependency)
    (seed : OccurrenceState Occurrence Label) (bound : Nat)
    (rank_lt_bound : ∀ occurrence, rank occurrence < bound)
    {state : OccurrenceState Occurrence Label} (model : system.CIPModel state) :
    iterate rawStep seed bound = state := by
  rw [iterate_eq_buildOccurrenceState_of_uniformBound
    (system := system) (dependency := dependency) (locality := locality)
    (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
    (step_eq := step_eq) wellFounded seed bound rank_lt_bound]
  have buildModel :
      system.CIPModel (system.buildOccurrenceState dependency wellFounded) := by
    rw [system.cipModel_iff_executableStateStep_fixed correspondence]
    exact system.buildOccurrenceState_fixed dependency wellFounded locality
  exact system.cipModel_unique_of_wellFounded correspondence dependency wellFounded locality
    (system.buildOccurrenceState dependency wellFounded) state buildModel model

/-- Existence and uniqueness of the declarative model, with the rank-bounded iteration as the
witness. -/
theorem existsUnique_cipModel_of_uniformBound
    (correspondence : system.DerivationStepCorrespondence)
    (wellFounded : WellFounded dependency)
    (seed : OccurrenceState Occurrence Label) (bound : Nat)
    (rank_lt_bound : ∀ occurrence, rank occurrence < bound) :
    ∃! state, system.CIPModel state := by
  refine ⟨iterate rawStep seed bound,
    cipModel_iterate_of_uniformBound
      (system := system) (dependency := dependency) (locality := locality)
      (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
      (step_eq := step_eq) correspondence wellFounded seed bound rank_lt_bound, ?_⟩
  intro state model
  exact (iterate_eq_model_of_uniformBound
    (system := system) (dependency := dependency) (locality := locality)
    (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
    (step_eq := step_eq) correspondence wellFounded seed bound rank_lt_bound model).symm

/-- Agreement with the scheduler: the rank-bounded raw iteration equals the decoded scheduler
closure once the uniform rank bound has passed. -/
theorem iterate_eq_schedulerClosure_decode
    (wellFounded : WellFounded dependency)
    (seed : OccurrenceState Occurrence Label) (bound : Nat)
    (rank_lt_bound : ∀ occurrence, rank occurrence < bound) :
    iterate rawStep seed bound =
      OccurrenceScheduler.decode system dependency
        (OccurrenceScheduler.closure system dependency) := by
  rw [iterate_eq_buildOccurrenceState_of_uniformBound
    (system := system) (dependency := dependency) (locality := locality)
    (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
    (step_eq := step_eq) wellFounded seed bound rank_lt_bound]
  exact (OccurrenceScheduler.decode_closure_eq_buildOccurrenceState system dependency
    wellFounded).symm

/-- Pointwise scheduler agreement below a rank bound, before a uniform bound is known. -/
theorem iterate_eq_schedulerClosure_decode_of_rank
    (wellFounded : WellFounded dependency)
    (seed : OccurrenceState Occurrence Label) (n : Nat) :
    ∀ occurrence, rank occurrence < n →
      iterate rawStep seed n occurrence =
        OccurrenceScheduler.decode system dependency
          (OccurrenceScheduler.closure system dependency) occurrence := by
  intro occurrence hrank
  calc
    iterate rawStep seed n occurrence
        = system.buildOccurrenceState dependency wellFounded occurrence :=
            iterate_eq_buildOccurrenceState
              (system := system) (dependency := dependency) (locality := locality)
              (rank := rank) (rank_decrease := rank_decrease) (rawStep := rawStep)
              (step_eq := step_eq) wellFounded seed n occurrence hrank
    _ = OccurrenceScheduler.decode system dependency
          (OccurrenceScheduler.closure system dependency) occurrence := by
            exact congrFun
              (OccurrenceScheduler.decode_closure_eq_buildOccurrenceState system dependency
                wellFounded).symm
              occurrence

end Convergence

/-! ## A computable toy reduction -/

section Toy

/-- A tiny raw step on `Nat` occurrences and `Bool` labels, used only to demonstrate that
`iterate` reduces without any occurrence system, `Fintype`, or classical choice. -/
def toyRawStep : RawStep Nat Bool :=
  fun state occurrence =>
    match occurrence with
    | 0 => some true
    | n + 1 => state n

/-- The all-`none` seed for the toy. -/
def toySeed : OccurrenceState Nat Bool := fun _ => none

/-- After three toy iterations, occurrence `2` has received the propagated `some true` value. -/
theorem toy_iterate_three_two : iterate toyRawStep toySeed 3 2 = some true := by
  decide

-- The same computable toy evaluated by the interpreter.
#eval iterate toyRawStep toySeed 3 2

end Toy

end RankedIteration
end DeclarativeCIP
end OneCenter
end TetraStereo
