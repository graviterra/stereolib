import TetraStereo.OneCenter.LocalizedOccurrenceFixedPoint
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier
import TetraStereo.OneCenter.RankedOccurrenceIteration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Computable rank-bounded evaluation of the localized occurrence equations

`TetraStereo.OneCenter.RankedOccurrenceIteration` provides a computable `Nat`-recursive iterator for
raw occurrence equations.  `TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier` provides the
executable finite carrier `localizedOccurrenceCarrier`, the executable dependency list
`localizedDependencyList`, the uniform rank bound `occurrence.1.remaining ≤ fuel + 1`, and the
strict causal measure `source.1.remaining < target.1.remaining` for `LocalizedDepthDependency`.

This module wires the two together.  The computable evaluator
`evaluateLocalizedOccurrences input fuel evaluator` iterates the dependency-restricted raw evaluator
`fuel + 2` times from the all-`none` seed.  Its body contains no occurrence system, no well-founded
fixpoint, no `Fintype` instance, and no classical choice: the evaluator is an explicit runtime
parameter, so this module makes no claim that any particular chemical Rules-3--6 evaluator is
computable, and no solution state is ever supplied as a premise.

The main results are:

* `evaluateLocalizedOccurrences_apply_eq_buildOccurrenceState` and
  `evaluateLocalizedOccurrences_eq_buildOccurrenceState_fun` — for a concrete localized semantics
  the computable iteration equals the noncomputable well-founded state `buildOccurrenceState`.
  Well-foundedness and the rank bound are internal theorems
  (`localizedDepthDependency_wellFounded`, `localizedCIPOccurrence_remaining_le_fuel_add_one`), not
  hypotheses.
* `evaluateLocalizedOccurrences_eq_schedulerClosure_decode` — the same iteration equals the decoded
  dependency-ready causal scheduler closure.
* `cipModel_evaluateLocalizedOccurrences` and `evaluateLocalizedOccurrences_eq_model` — the iteration
  is the unique declarative CIP model.
* `localizedSolvedFactList_outcome_iff_declarative` and `localizedSolvedFactList_none_iff_declarative`
  — the finite fact list `carrier.map (fun o => (o, state o))` is exactly the derivable
  (occurrence, outcome) pairs over the carrier, `none` outcomes included.

The only definitional steps are `localizedRawStep_eq_executableStep` (the raw step is the occurrence
system's executable step, by projection of the system literal) and the `rfl` computation rules
`evaluateLocalizedOccurrences_def` / `localizedRawStep`.  Everything else is proved by the generic
iterator theorems.

Residual work is unchanged and explicitly outside this module: a concrete Rules-3--6 implementation
must still supply the declarative derivation relation together with the restricted executable
evaluator and their complete optional-outcome correspondence, i.e. an inhabitant of
`LocalizedAuxiliaryRuleSemantics`.  This module only turns such a supplied semantics into a
computable evaluation front-end.
-/

namespace CertifiedLocalizedCIPInput

/-! ## The computable raw step and its iteration -/

/-- The raw executable step induced by a dependency-restricted localized evaluator.

`localizedExecutableStep` exposes only the target's proof-carrying strict-depth view, so this raw
step is a plain function of a complete optional occurrence state and is exactly the `rawStep` slot
of `DeclarativeCIP.RankedIteration`. -/
abbrev localizedRawStep
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (evaluator : input.LocalizedRestrictedEvaluator fuel) :
    DeclarativeCIP.RankedIteration.RawStep (input.LocalizedCIPOccurrence fuel)
      LocalizedAuxiliaryLabel :=
  input.localizedExecutableStep evaluator

/-- Computable `fuel + 2`-fold raw iteration of the localized occurrence equations from the
all-`none` seed.

The definition is `RankedIteration.iterate (input.localizedExecutableStep evaluator) (fun _ => none)
(fuel + 2)`: the runtime object is the explicit raw evaluator, never the `noncomputable`
`localizedAuxiliaryOccurrenceSystem`.  The budget `fuel + 2` is forced by the carrier rank bound
`occurrence.1.remaining ≤ fuel + 1` (`localizedCIPOccurrence_remaining_le_fuel_add_one`), so the
iteration covers every carried occurrence. -/
def evaluateLocalizedOccurrences
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel) :
    input.LocalizedAuxiliaryState fuel :=
  DeclarativeCIP.RankedIteration.iterate (input.localizedExecutableStep evaluator)
    (fun _ => none) (fuel + 2)

/-- Definitional unfolding of the computed state into the literal raw iteration. -/
theorem evaluateLocalizedOccurrences_def
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel) :
    input.evaluateLocalizedOccurrences fuel evaluator =
      DeclarativeCIP.RankedIteration.iterate (input.localizedExecutableStep evaluator)
        (fun _ => none) (fuel + 2) :=
  rfl

/-- The carrier rank bound: every carried occurrence has remaining expansion depth below `fuel + 2`,
the budget of `evaluateLocalizedOccurrences`. -/
theorem localizedRemaining_lt_fuel_add_two
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.remaining < fuel + 2 := by
  have bound := input.localizedCIPOccurrence_remaining_le_fuel_add_one fuel occurrence
  omega

/-- The raw localized step is exactly the executable step of the associated occurrence system.

This is a definitional projection fact: the system literal stores
`input.localizedExecutableStep semantics.executableRule` in its `executableStep` field. -/
theorem localizedRawStep_eq_executableStep
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedRawStep semantics.executableRule state occurrence =
      (input.localizedAuxiliaryOccurrenceSystem semantics).executableStep state occurrence :=
  rfl

/-- The executable dependency list of `LocalizedOccurrenceFiniteCarrier` is the exact read set of one
localized step: agreement on the listed occurrences already forces equality of the step. -/
theorem localizedExecutableStep_eq_of_dependencyListAgree
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (left right : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (agree : ∀ source, source ∈ input.localizedDependencyList fuel target →
      left source = right source) :
    input.localizedExecutableStep evaluator left target =
      input.localizedExecutableStep evaluator right target := by
  apply input.localizedExecutableStep_eq_of_depthAgree evaluator left right target
  intro source dependency
  exact agree source
    ((input.mem_localizedDependencyList_iff fuel target source).mpr dependency)

/-! ## Agreement with the well-founded executable solution -/

/-- Rank-refined agreement: after `n` raw iterations every occurrence of rank below `n` already
carries the well-founded executable value.  Well-foundedness is supplied by the internal depth
measure `localizedDepthDependency_wellFounded`, and the rank decrease is the carrier theorem
`localizedDepthDependency_remaining_lt`. -/
theorem localizedRawIterate_apply_eq_buildOccurrenceState_of_rank
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (n : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (rankBound : occurrence.1.remaining < n) :
    DeclarativeCIP.RankedIteration.iterate (input.localizedRawStep semantics.executableRule)
        (fun _ => none) n occurrence =
      (input.localizedAuxiliaryOccurrenceSystem semantics).buildOccurrenceState
        (@input.LocalizedDepthDependency fuel)
        (input.localizedDepthDependency_wellFounded fuel) occurrence := by
  apply DeclarativeCIP.RankedIteration.iterate_eq_buildOccurrenceState
    (system := input.localizedAuxiliaryOccurrenceSystem semantics)
    (dependency := @input.LocalizedDepthDependency fuel)
    (locality := input.localizedAuxiliaryEvaluatorLocal semantics)
    (rank := fun candidate => candidate.1.remaining)
    (rank_decrease := fun {inner target} dependency =>
      input.localizedDepthDependency_remaining_lt dependency)
    (rawStep := input.localizedRawStep semantics.executableRule)
    (step_eq := fun state occurrence =>
      input.localizedRawStep_eq_executableStep fuel semantics state occurrence)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (seed := fun _ => none)
    (n := n)
  exact rankBound

/-- Pointwise agreement of the computable state with the well-founded executable solution. -/
theorem evaluateLocalizedOccurrences_apply_eq_buildOccurrenceState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.evaluateLocalizedOccurrences fuel semantics.executableRule occurrence =
      (input.localizedAuxiliaryOccurrenceSystem semantics).buildOccurrenceState
        (@input.LocalizedDepthDependency fuel)
        (input.localizedDepthDependency_wellFounded fuel) occurrence := by
  rw [evaluateLocalizedOccurrences]
  apply DeclarativeCIP.RankedIteration.iterate_eq_buildOccurrenceState
    (system := input.localizedAuxiliaryOccurrenceSystem semantics)
    (dependency := @input.LocalizedDepthDependency fuel)
    (locality := input.localizedAuxiliaryEvaluatorLocal semantics)
    (rank := fun candidate => candidate.1.remaining)
    (rank_decrease := fun {inner target} dependency =>
      input.localizedDepthDependency_remaining_lt dependency)
    (rawStep := input.localizedRawStep semantics.executableRule)
    (step_eq := fun state occurrence =>
      input.localizedRawStep_eq_executableStep fuel semantics state occurrence)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (seed := fun _ => none)
    (n := fuel + 2)
  exact input.localizedRemaining_lt_fuel_add_two fuel occurrence

/-- The computable state equals the well-founded executable solution as a complete state. -/
theorem evaluateLocalizedOccurrences_eq_buildOccurrenceState_fun
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    input.evaluateLocalizedOccurrences fuel semantics.executableRule =
      (input.localizedAuxiliaryOccurrenceSystem semantics).buildOccurrenceState
        (@input.LocalizedDepthDependency fuel)
        (input.localizedDepthDependency_wellFounded fuel) := by
  rw [evaluateLocalizedOccurrences]
  exact DeclarativeCIP.RankedIteration.iterate_eq_buildOccurrenceState_of_uniformBound
    (system := input.localizedAuxiliaryOccurrenceSystem semantics)
    (dependency := @input.LocalizedDepthDependency fuel)
    (locality := input.localizedAuxiliaryEvaluatorLocal semantics)
    (rank := fun candidate => candidate.1.remaining)
    (rank_decrease := fun {inner target} dependency =>
      input.localizedDepthDependency_remaining_lt dependency)
    (rawStep := input.localizedRawStep semantics.executableRule)
    (step_eq := fun state occurrence =>
      input.localizedRawStep_eq_executableStep fuel semantics state occurrence)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (seed := fun _ => none)
    (bound := fuel + 2)
    (rank_lt_bound := fun occurrence =>
      input.localizedRemaining_lt_fuel_add_two fuel occurrence)

/-- The computable state equals the decoded dependency-ready causal scheduler closure. -/
theorem evaluateLocalizedOccurrences_eq_schedulerClosure_decode
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    input.evaluateLocalizedOccurrences fuel semantics.executableRule =
      DeclarativeCIP.OccurrenceScheduler.decode
        (input.localizedAuxiliaryOccurrenceSystem semantics)
        (@input.LocalizedDepthDependency fuel)
        (DeclarativeCIP.OccurrenceScheduler.closure
          (input.localizedAuxiliaryOccurrenceSystem semantics)
          (@input.LocalizedDepthDependency fuel)) := by
  rw [evaluateLocalizedOccurrences]
  exact DeclarativeCIP.RankedIteration.iterate_eq_schedulerClosure_decode
    (system := input.localizedAuxiliaryOccurrenceSystem semantics)
    (dependency := @input.LocalizedDepthDependency fuel)
    (locality := input.localizedAuxiliaryEvaluatorLocal semantics)
    (rank := fun candidate => candidate.1.remaining)
    (rank_decrease := fun {inner target} dependency =>
      input.localizedDepthDependency_remaining_lt dependency)
    (rawStep := input.localizedRawStep semantics.executableRule)
    (step_eq := fun state occurrence =>
      input.localizedRawStep_eq_executableStep fuel semantics state occurrence)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (seed := fun _ => none)
    (bound := fuel + 2)
    (rank_lt_bound := fun occurrence =>
      input.localizedRemaining_lt_fuel_add_two fuel occurrence)

/-- At the carrier budget the computed state is a fixed point of the raw localized step. -/
theorem localizedRawStep_evaluateLocalizedOccurrences_fixed
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    input.localizedRawStep semantics.executableRule
        (input.evaluateLocalizedOccurrences fuel semantics.executableRule) =
      input.evaluateLocalizedOccurrences fuel semantics.executableRule := by
  rw [evaluateLocalizedOccurrences]
  apply DeclarativeCIP.RankedIteration.iterate_fixed_of_uniformBound
    (system := input.localizedAuxiliaryOccurrenceSystem semantics)
    (dependency := @input.LocalizedDepthDependency fuel)
    (locality := input.localizedAuxiliaryEvaluatorLocal semantics)
    (rank := fun candidate => candidate.1.remaining)
    (rank_decrease := fun {inner target} dependency =>
      input.localizedDepthDependency_remaining_lt dependency)
    (rawStep := input.localizedRawStep semantics.executableRule)
    (step_eq := fun state occurrence =>
      input.localizedRawStep_eq_executableStep fuel semantics state occurrence)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (seed := fun _ => none)
    (bound := fuel + 2)
    (rank_lt_bound := fun occurrence =>
      input.localizedRemaining_lt_fuel_add_two fuel occurrence)

/-- Seed independence within the carrier budget: starting the raw iteration from any state reaches
the same computed value as the all-`none` seed. -/
theorem evaluateLocalizedOccurrences_seed_independent
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (seed : input.LocalizedAuxiliaryState fuel) :
    DeclarativeCIP.RankedIteration.iterate
        (input.localizedRawStep semantics.executableRule) seed (fuel + 2) =
      DeclarativeCIP.RankedIteration.iterate
        (input.localizedRawStep semantics.executableRule) (fun _ => none) (fuel + 2) := by
  apply DeclarativeCIP.RankedIteration.iterate_seed_independent
    (system := input.localizedAuxiliaryOccurrenceSystem semantics)
    (dependency := @input.LocalizedDepthDependency fuel)
    (locality := input.localizedAuxiliaryEvaluatorLocal semantics)
    (rank := fun candidate => candidate.1.remaining)
    (rank_decrease := fun {inner target} dependency =>
      input.localizedDepthDependency_remaining_lt dependency)
    (rawStep := input.localizedRawStep semantics.executableRule)
    (step_eq := fun state occurrence =>
      input.localizedRawStep_eq_executableStep fuel semantics state occurrence)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (seed := seed)
    (seed' := fun _ => none)
    (bound := fuel + 2)
    (rank_lt_bound := fun occurrence =>
      input.localizedRemaining_lt_fuel_add_two fuel occurrence)

/-! ## The computable state is the unique declarative model -/

/-- The computable iteration is a declarative CIP model of the occurring localized semantics.

The derivation/executable correspondence and evaluator locality are the existing
`localizedAuxiliaryDerivationStepCorrespondence` and `localizedAuxiliaryEvaluatorLocal`; no model is
assumed. -/
theorem cipModel_evaluateLocalizedOccurrences
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel
      (input.evaluateLocalizedOccurrences fuel semantics.executableRule) := by
  rw [evaluateLocalizedOccurrences]
  apply DeclarativeCIP.RankedIteration.cipModel_iterate_of_uniformBound
    (system := input.localizedAuxiliaryOccurrenceSystem semantics)
    (dependency := @input.LocalizedDepthDependency fuel)
    (locality := input.localizedAuxiliaryEvaluatorLocal semantics)
    (rank := fun candidate => candidate.1.remaining)
    (rank_decrease := fun {inner target} dependency =>
      input.localizedDepthDependency_remaining_lt dependency)
    (rawStep := input.localizedRawStep semantics.executableRule)
    (step_eq := fun state occurrence =>
      input.localizedRawStep_eq_executableStep fuel semantics state occurrence)
    (correspondence := input.localizedAuxiliaryDerivationStepCorrespondence semantics)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (seed := fun _ => none)
    (bound := fuel + 2)
    (rank_lt_bound := fun occurrence =>
      input.localizedRemaining_lt_fuel_add_two fuel occurrence)

/-- The computable iteration is a fixed point of the system's simultaneous executable step. -/
theorem evaluateLocalizedOccurrences_fixed
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedAuxiliaryOccurrenceSystem semantics).executableStateStep
        (input.evaluateLocalizedOccurrences fuel semantics.executableRule) =
      input.evaluateLocalizedOccurrences fuel semantics.executableRule :=
  ((input.localizedAuxiliaryOccurrenceSystem semantics).cipModel_iff_executableStateStep_fixed
      (input.localizedAuxiliaryDerivationStepCorrespondence semantics)
      (input.evaluateLocalizedOccurrences fuel semantics.executableRule)).1
    (input.cipModel_evaluateLocalizedOccurrences fuel semantics)

/-- Uniqueness: the computable iteration equals every declarative model, so no independently supplied
solution can differ from the computed one. -/
theorem evaluateLocalizedOccurrences_eq_model
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state) :
    input.evaluateLocalizedOccurrences fuel semantics.executableRule = state := by
  rw [evaluateLocalizedOccurrences]
  apply DeclarativeCIP.RankedIteration.iterate_eq_model_of_uniformBound
    (system := input.localizedAuxiliaryOccurrenceSystem semantics)
    (dependency := @input.LocalizedDepthDependency fuel)
    (locality := input.localizedAuxiliaryEvaluatorLocal semantics)
    (rank := fun candidate => candidate.1.remaining)
    (rank_decrease := fun {inner target} dependency =>
      input.localizedDepthDependency_remaining_lt dependency)
    (rawStep := input.localizedRawStep semantics.executableRule)
    (step_eq := fun state occurrence =>
      input.localizedRawStep_eq_executableStep fuel semantics state occurrence)
    (correspondence := input.localizedAuxiliaryDerivationStepCorrespondence semantics)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (seed := fun _ => none)
    (bound := fuel + 2)
    (rank_lt_bound := fun occurrence =>
      input.localizedRemaining_lt_fuel_add_two fuel occurrence)
  exact model

/-- Existence and uniqueness of the localized declarative model, with the computable iteration as
the explicit witness. -/
theorem existsUnique_localizedAuxiliaryCIPModel_iterate
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    ∃! state, (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state := by
  refine ⟨input.evaluateLocalizedOccurrences fuel semantics.executableRule,
    input.cipModel_evaluateLocalizedOccurrences fuel semantics, ?_⟩
  intro state model
  exact (input.evaluateLocalizedOccurrences_eq_model fuel semantics model).symm

/-! ## The exact finite solved-fact list -/

/-- The finite solved-fact list of the computable state: every carried occurrence paired with its
computed optional outcome, `none` outcomes included. -/
def localizedSolvedFactList (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel) :
    List (input.LocalizedCIPOccurrence fuel × Option LocalizedAuxiliaryLabel) :=
  (input.localizedOccurrenceCarrier fuel).map fun occurrence =>
    (occurrence, input.evaluateLocalizedOccurrences fuel evaluator occurrence)

/-- Pairing a carried occurrence with its computed outcome is injective, so the fact list inherits
the carrier's duplicate-freeness. -/
theorem localizedSolvedFactPair_injective
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel) :
    Function.Injective (fun occurrence : input.LocalizedCIPOccurrence fuel =>
      (occurrence, input.evaluateLocalizedOccurrences fuel evaluator occurrence)) := by
  intro left right equal
  exact (Prod.mk.inj equal).1

/-- Exact membership characterization of the solved-fact list, for an arbitrary evaluator. -/
theorem localizedSolvedFactList_mem_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (occurrence, outcome) ∈ input.localizedSolvedFactList fuel evaluator ↔
      occurrence ∈ input.localizedOccurrenceCarrier fuel ∧
        input.evaluateLocalizedOccurrences fuel evaluator occurrence = outcome := by
  rw [localizedSolvedFactList, List.mem_map]
  constructor
  · rintro ⟨other, otherPresent, equal⟩
    have otherEq : other = occurrence := (Prod.mk.inj equal).1
    have outcomeEq : input.evaluateLocalizedOccurrences fuel evaluator other = outcome :=
      (Prod.mk.inj equal).2
    exact ⟨otherEq ▸ otherPresent, by rw [← otherEq, outcomeEq]⟩
  · rintro ⟨present, outcome_eq⟩
    exact ⟨occurrence, present, by rw [outcome_eq]⟩

/-- Completeness: every carried occurrence appears in the solved-fact list with its computed
outcome. -/
theorem localizedSolvedFactList_complete
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (present : occurrence ∈ input.localizedOccurrenceCarrier fuel) :
    (occurrence, input.evaluateLocalizedOccurrences fuel evaluator occurrence) ∈
      input.localizedSolvedFactList fuel evaluator := by
  rw [localizedSolvedFactList, List.mem_map]
  exact ⟨occurrence, present, rfl⟩

/-- Soundness: every listed fact is a carried occurrence. -/
theorem localizedSolvedFactList_mem_carrier
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel)
    (present : (occurrence, outcome) ∈ input.localizedSolvedFactList fuel evaluator) :
    occurrence ∈ input.localizedOccurrenceCarrier fuel :=
  ((input.localizedSolvedFactList_mem_iff fuel evaluator occurrence outcome).1 present).1

/-- Each carried occurrence carries exactly one listed outcome, so the fact list is a partial
function table on the carrier. -/
theorem localizedSolvedFactList_outcome_unique
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    {left right : Option LocalizedAuxiliaryLabel}
    (leftPresent : (occurrence, left) ∈ input.localizedSolvedFactList fuel evaluator)
    (rightPresent : (occurrence, right) ∈ input.localizedSolvedFactList fuel evaluator) :
    left = right :=
  (((input.localizedSolvedFactList_mem_iff fuel evaluator occurrence left).1
      leftPresent).2).symm.trans
    (((input.localizedSolvedFactList_mem_iff fuel evaluator occurrence right).1
      rightPresent).2)

/-- The solved-fact list is duplicate free. -/
theorem localizedSolvedFactList_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel) :
    (input.localizedSolvedFactList fuel evaluator).Nodup := by
  rw [localizedSolvedFactList]
  exact List.Nodup.map (input.localizedSolvedFactPair_injective fuel evaluator)
    (input.localizedOccurrenceCarrier_nodup fuel)

/-- The solved-fact list has exactly one entry per carried occurrence. -/
theorem localizedSolvedFactList_length
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel) :
    (input.localizedSolvedFactList fuel evaluator).length =
      (input.localizedOccurrenceCarrier fuel).length := by
  rw [localizedSolvedFactList, List.length_map]

/-- Exactness including `none` outcomes: a pair is listed exactly when the occurrence is carried and
the solved state *derives* that outcome.  In particular a listed `none` is a derived refusal, not a
missing entry. -/
theorem localizedSolvedFactList_outcome_iff_declarative
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (occurrence, outcome) ∈ input.localizedSolvedFactList fuel semantics.executableRule ↔
      occurrence ∈ input.localizedOccurrenceCarrier fuel ∧
        (input.localizedAuxiliaryOccurrenceSystem semantics).DeclarativeDerivation
          (input.evaluateLocalizedOccurrences fuel semantics.executableRule)
          occurrence outcome := by
  rw [input.localizedSolvedFactList_mem_iff fuel semantics.executableRule occurrence outcome]
  constructor
  · rintro ⟨present, outcome_eq⟩
    refine ⟨present, ?_⟩
    rw [← outcome_eq]
    exact input.cipModel_evaluateLocalizedOccurrences fuel semantics occurrence
  · rintro ⟨present, derived⟩
    refine ⟨present, ?_⟩
    have executable_eq :
        (input.localizedAuxiliaryOccurrenceSystem semantics).executableStep
            (input.evaluateLocalizedOccurrences fuel semantics.executableRule) occurrence =
          outcome :=
      ((input.localizedAuxiliaryDerivationStepCorrespondence semantics)
        (input.evaluateLocalizedOccurrences fuel semantics.executableRule)
        occurrence outcome).1 derived
    have fixed :=
      ((input.localizedAuxiliaryOccurrenceSystem semantics).cipModel_iff_executableStateStep_fixed
        (input.localizedAuxiliaryDerivationStepCorrespondence semantics)
        (input.evaluateLocalizedOccurrences fuel semantics.executableRule)).1
        (input.cipModel_evaluateLocalizedOccurrences fuel semantics)
    exact (congrFun fixed occurrence).symm.trans executable_eq

/-- The `none` entries of the finite fact list are exactly the occurrences whose refusal the solved
state derives. -/
theorem localizedSolvedFactList_none_iff_declarative
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    (occurrence, none) ∈ input.localizedSolvedFactList fuel semantics.executableRule ↔
      occurrence ∈ input.localizedOccurrenceCarrier fuel ∧
        (input.localizedAuxiliaryOccurrenceSystem semantics).DeclarativeDerivation
          (input.evaluateLocalizedOccurrences fuel semantics.executableRule)
          occurrence none :=
  input.localizedSolvedFactList_outcome_iff_declarative fuel semantics occurrence none

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
