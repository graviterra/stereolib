import TetraStereo.OneCenter.LocalizedRankedIteration
import TetraStereo.Certificate.DependencyCheckedModel

set_option autoImplicit false

/-!
# Dependency-closed regional transport for localized evaluators

This module proves that two localized evaluators whose ranked reference states are computed by
`CertifiedLocalizedCIPInput.evaluateLocalizedOccurrences` agree on an explicitly
dependency-closed region as soon as

* the region is closed downwards under the strict root-relative depth dependency
  `LocalizedDepthDependency`, and
* the two evaluators produce the same optional outcome at every region target whenever their
  lower-rank dependency views agree pointwise.

Neither hypothesis can be dropped.  Evaluator equality on a region is *not* implied by proving
that one evaluator refines the other locally: an evaluator may differ at a target of the region,
or the region may fail to contain a strict dependency, in which case the iterated states can
diverge inside the region.  The premises below make the precise obligation explicit; no
whole-state equality, no global evaluator equality and no supplied solution state is assumed.

The proof is a rank induction that follows the existing architecture:

* `RankedIteration.iterate_eq_on_region` is the generic raw-iteration statement, parameterized
  by an arbitrary dependency relation, an arbitrary strict `Nat` rank and an arbitrary seed.
* `OccurrenceSystem.eq_on_region_of_fixed` is the generic fixed-point statement, parameterized by
  two occurrence systems (the repository's generic certificate-system abstraction) and two
  fixed states.  It does not need evaluator locality: the regional view-agreement premise says
  directly what is required.
* The localized corollaries instantiate these at rank `occurrence.1.remaining` and at the
  well-founded dependency `LocalizedDepthDependency`; the depth grading
  `localizedDepthDependency_remaining_lt` and the uniform carrier bound
  `localizedRemaining_lt_fuel_add_two` are existing theorems, not assumptions.
* `DependencyCheckedModel.checked_lookup_eq_on_region` transports the result to dependency-checked
  certificates, reusing `checked_lookup_fixed`, so globally complete accepted certificates agree
  on the region without assuming that they describe the same whole state.

The `none` outcomes are transported exactly like positive outcomes: the agreement premise concerns
the complete `Option LocalizedAuxiliaryLabel` view, so an explicit refusal is not silently
identified with absence.
-/

namespace TetraStereo.OneCenter
namespace DeclarativeCIP
namespace RankedIteration

universe u v w

variable {Occurrence : Type v} {Label : Type w}

/-- **Regional equality of two rank-bounded raw iterations.**

Let `dependency` be a relation strictly decreasing a `Nat` rank, let `region` be closed downwards
under `dependency`, and suppose the two raw steps agree at every region target on any pair of
states whose `dependency`-coordinates agree.  Then after any number `n` of iterations the two
states agree at every region target of rank below `n`, for *arbitrary* seeds.

The seed generality is genuine: a target of rank `0` has no `dependency` predecessor, so the
agreement premise already forces the two raw steps to agree there regardless of seed values; at
higher ranks all predecessors are handled by the induction hypothesis.  No well-foundedness,
occurrence system, or model is used. -/
theorem iterate_eq_on_region
    (rawStep₁ rawStep₂ : RawStep Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (rank : Occurrence → Nat)
    (rank_decrease : ∀ {inner target : Occurrence},
      dependency inner target → rank inner < rank target)
    (region : Occurrence → Prop)
    (region_closed : ∀ {inner target : Occurrence},
      dependency inner target → region target → region inner)
    (agree : ∀ target, region target →
      ∀ left right : OccurrenceState Occurrence Label,
        (∀ source, dependency source target → left source = right source) →
        rawStep₁ left target = rawStep₂ right target)
    (seed₁ seed₂ : OccurrenceState Occurrence Label) (n : Nat) :
    ∀ target, region target → rank target < n →
      iterate rawStep₁ seed₁ n target = iterate rawStep₂ seed₂ n target := by
  induction n with
  | zero =>
      intro target _ hrank
      exact absurd hrank (Nat.not_lt_zero (rank target))
  | succ n inductionHypothesis =>
      intro target hregion hrank
      simp only [iterate_succ]
      apply agree target hregion
      intro source related
      exact inductionHypothesis source (region_closed related hregion)
        (Nat.lt_of_lt_of_le (rank_decrease related) (Nat.le_of_lt_succ hrank))

end RankedIteration

namespace OccurrenceSystem

universe u v w

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

/-- **Regional equality of two fixed points of occurrence systems.**

If two states are fixed points of their respective simultaneous executable steps, the dependency
relation is well founded, the region is closed downwards under the dependency, and the two
evaluators agree at every region target on any pair of states with equal dependency coordinates,
then the two fixed states agree on the region.

No evaluator-locality hypothesis is required: the view-agreement premise directly licenses the
single cross-system comparison needed at each target.  This is the form reused for
dependency-checked certificates. -/
theorem eq_on_region_of_fixed
    (firstSystem secondSystem : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (region : Occurrence → Prop)
    (region_closed : ∀ {inner target : Occurrence},
      dependency inner target → region target → region inner)
    (agree : ∀ target, region target →
      ∀ left right : OccurrenceState Occurrence Label,
        (∀ source, dependency source target → left source = right source) →
        firstSystem.executableStep left target = secondSystem.executableStep right target)
    {firstState secondState : OccurrenceState Occurrence Label}
    (firstFixed : firstSystem.executableStateStep firstState = firstState)
    (secondFixed : secondSystem.executableStateStep secondState = secondState) :
    ∀ target, region target → firstState target = secondState target := by
  intro target
  refine wellFounded.induction
    (C := fun candidate => region candidate → firstState candidate = secondState candidate)
    target ?_
  intro target inductionHypothesis hregion
  calc
    firstState target = firstSystem.executableStep firstState target :=
      (congrFun firstFixed target).symm
    _ = secondSystem.executableStep secondState target :=
      agree target hregion firstState secondState
        (fun source related =>
          inductionHypothesis source related (region_closed related hregion))
    _ = secondState target := congrFun secondFixed target

end OccurrenceSystem

end DeclarativeCIP
end TetraStereo.OneCenter

namespace TetraStereo.Certificate.DependencyCheckedModel

open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.Certificate.Dependency

universe u v w

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

/-- **Regional transport for dependency-checked certificates.**

Two accepted, duplicate-free and occurrence-complete dependency-checked certificates induce
fixed lookup states for their respective occurrence systems.  If the systems' executable steps
agree at every target of a dependency-closed region on states with equal dependency coordinates,
then the two checked lookup states agree on that region.  The certificates may enumerate
different dependency lists; only the common comparison relation carries the region argument.

This is a direct application of `OccurrenceSystem.eq_on_region_of_fixed` to the fixed points
supplied by `checked_lookup_fixed`; no whole-state equality and no common certificate are
assumed. -/
theorem checked_lookup_eq_on_region
    [DecidableEq Occurrence] [DecidableEq Label]
    (firstSystem secondSystem : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (firstDependencies secondDependencies : Occurrence → List Occurrence)
    (firstLocality : firstSystem.EvaluatorLocalFor (relation firstDependencies))
    (secondLocality : secondSystem.EvaluatorLocalFor (relation secondDependencies))
    (firstNodes : List (Node Occurrence Label))
    (firstResult : List (Fact Occurrence Label))
    (secondNodes : List (Node Occurrence Label))
    (secondResult : List (Fact Occurrence Label))
    (firstAccepted : check firstSystem firstDependencies firstNodes = some firstResult)
    (secondAccepted : check secondSystem secondDependencies secondNodes = some secondResult)
    (firstNodup : (firstResult.map Prod.fst).Nodup)
    (secondNodup : (secondResult.map Prod.fst).Nodup)
    (firstComplete : ∀ occurrence, occurrence ∈ firstResult.map Prod.fst)
    (secondComplete : ∀ occurrence, occurrence ∈ secondResult.map Prod.fst)
    (region : Occurrence → Prop)
    (region_closed : ∀ {source target : Occurrence},
      dependency source target → region target → region source)
    (agree : ∀ target, region target →
      ∀ left right : OccurrenceState Occurrence Label,
        (∀ source, dependency source target → left source = right source) →
        firstSystem.executableStep left target = secondSystem.executableStep right target) :
    ∀ target, region target → lookup firstResult target = lookup secondResult target := by
  have firstFixed := checked_lookup_fixed firstSystem firstDependencies firstNodes firstResult
    firstAccepted firstNodup firstComplete firstLocality
  have secondFixed := checked_lookup_fixed secondSystem secondDependencies secondNodes secondResult
    secondAccepted secondNodup secondComplete secondLocality
  intro target hregion
  exact OccurrenceSystem.eq_on_region_of_fixed firstSystem secondSystem dependency wellFounded
    region region_closed agree firstFixed secondFixed target hregion

end TetraStereo.Certificate.DependencyCheckedModel

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.Dependency

/-! ## Localized evaluator reference states -/

/-- **Regional equality of the ranked reference states of two localized evaluators.**

`evaluateLocalizedOccurrences input fuel evaluator` is the reference state obtained by the
computable `fuel + 2`-fold iteration of the dependency-restricted evaluator from the all-`none`
seed.  Suppose `region` is closed downwards under `LocalizedDepthDependency`, and the two
evaluators agree at every region target whenever their strict lower-rank views agree pointwise.
Then the two reference states agree at every occurrence of the region.

The rank bound `fuel + 2` is the carrier theorem `localizedRemaining_lt_fuel_add_two`, and the
strict rank decrease is `localizedDepthDependency_remaining_lt`; neither is assumed.  Only the
view-agreement premise is caller-supplied, and it is exactly what a refinement proof of the two
evaluators has to establish on the closed region. -/
theorem evaluateLocalizedOccurrences_eq_on_region
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (first second : input.LocalizedRestrictedEvaluator fuel)
    (region : input.LocalizedCIPOccurrence fuel → Prop)
    (region_closed : ∀ {source target : input.LocalizedCIPOccurrence fuel},
      input.LocalizedDepthDependency source target → region target → region source)
    (agree : ∀ target, region target →
      ∀ (firstView secondView : input.LocalizedDependencyView target),
        (∀ source, ∀ dependency : input.LocalizedDepthDependency source target,
          firstView source dependency = secondView source dependency) →
        first target firstView = second target secondView) :
    ∀ target, region target →
      input.evaluateLocalizedOccurrences fuel first target =
        input.evaluateLocalizedOccurrences fuel second target := by
  intro target hregion
  rw [input.evaluateLocalizedOccurrences_def,
    input.evaluateLocalizedOccurrences_def]
  refine DeclarativeCIP.RankedIteration.iterate_eq_on_region
    (rawStep₁ := input.localizedExecutableStep first)
    (rawStep₂ := input.localizedExecutableStep second)
    (dependency := @input.LocalizedDepthDependency fuel)
    (rank := fun occurrence => occurrence.1.remaining)
    (region := region)
    (region_closed := region_closed)
    (seed₁ := fun _ => none) (seed₂ := fun _ => none)
    (n := fuel + 2)
    (rank_decrease := ?_) (agree := ?_)
    target hregion (input.localizedRemaining_lt_fuel_add_two fuel target)
  · intro inner outer related
    exact input.localizedDepthDependency_remaining_lt related
  · intro candidate hcandidate left right hleft
    exact agree candidate hcandidate
      (input.localizedDependencyView left candidate)
      (input.localizedDependencyView right candidate)
      (fun source related => hleft source related)

/-- Global corollary: if the two evaluators agree at every occurrence on every pair of
pointwise-equal strict lower-rank views, their reference states are equal as complete functions.
This is the strongest conclusion available once the closed region is taken to be the whole
carrier. -/
theorem evaluateLocalizedOccurrences_eq_of_agree
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (first second : input.LocalizedRestrictedEvaluator fuel)
    (agree : ∀ target,
      ∀ (firstView secondView : input.LocalizedDependencyView target),
        (∀ source, ∀ dependency : input.LocalizedDepthDependency source target,
          firstView source dependency = secondView source dependency) →
        first target firstView = second target secondView) :
    input.evaluateLocalizedOccurrences fuel first =
      input.evaluateLocalizedOccurrences fuel second := by
  funext target
  exact input.evaluateLocalizedOccurrences_eq_on_region fuel first second
    (fun _ => True) (fun _ _ => trivial)
    (fun candidate _ firstView secondView viewsAgree =>
      agree candidate firstView secondView viewsAgree)
    target trivial

/-! ## Well-founded and unique reference states -/

/-- **Regional equality of the well-founded executable reference states.**

For two localized rule semantics, the noncomputable well-founded states
`buildOccurrenceState LocalizedDepthDependency` agree on the closed region whenever the two
executable rules agree there on pointwise-equal lower-rank views.  The proof routes through the
computable iteration using the existing theorem
`evaluateLocalizedOccurrences_apply_eq_buildOccurrenceState`, so no separate well-founded
induction is needed. -/
theorem buildOccurrenceState_eq_on_region
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (first second : input.LocalizedAuxiliaryRuleSemantics fuel)
    (region : input.LocalizedCIPOccurrence fuel → Prop)
    (region_closed : ∀ {source target : input.LocalizedCIPOccurrence fuel},
      input.LocalizedDepthDependency source target → region target → region source)
    (agree : ∀ target, region target →
      ∀ (firstView secondView : input.LocalizedDependencyView target),
        (∀ source, ∀ dependency : input.LocalizedDepthDependency source target,
          firstView source dependency = secondView source dependency) →
        first.executableRule target firstView = second.executableRule target secondView) :
    ∀ target, region target →
      (input.localizedAuxiliaryOccurrenceSystem first).buildOccurrenceState
          (@input.LocalizedDepthDependency fuel)
          (input.localizedDepthDependency_wellFounded fuel) target =
        (input.localizedAuxiliaryOccurrenceSystem second).buildOccurrenceState
          (@input.LocalizedDepthDependency fuel)
          (input.localizedDepthDependency_wellFounded fuel) target := by
  intro target hregion
  rw [← input.evaluateLocalizedOccurrences_apply_eq_buildOccurrenceState fuel first target,
    ← input.evaluateLocalizedOccurrences_apply_eq_buildOccurrenceState fuel second target]
  exact input.evaluateLocalizedOccurrences_eq_on_region fuel first.executableRule
    second.executableRule region region_closed agree target hregion

/-- **Regional equality of the unique declarative models.**

Every declarative model of the occurrence system induced by a localized rule semantics is the
unique ranked reference state of that semantics.  Consequently, two models of two semantics with
regionally agreeing evaluators agree on the dependency-closed region.  This transports
uniqueness without ever assuming that the two models coincide outside the region. -/
theorem cipModel_eq_on_region
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (first second : input.LocalizedAuxiliaryRuleSemantics fuel)
    {firstState secondState : input.LocalizedAuxiliaryState fuel}
    (firstModel : (input.localizedAuxiliaryOccurrenceSystem first).CIPModel firstState)
    (secondModel : (input.localizedAuxiliaryOccurrenceSystem second).CIPModel secondState)
    (region : input.LocalizedCIPOccurrence fuel → Prop)
    (region_closed : ∀ {source target : input.LocalizedCIPOccurrence fuel},
      input.LocalizedDepthDependency source target → region target → region source)
    (agree : ∀ target, region target →
      ∀ (firstView secondView : input.LocalizedDependencyView target),
        (∀ source, ∀ dependency : input.LocalizedDepthDependency source target,
          firstView source dependency = secondView source dependency) →
        first.executableRule target firstView = second.executableRule target secondView) :
    ∀ target, region target → firstState target = secondState target := by
  intro target hregion
  calc
    firstState target =
        input.evaluateLocalizedOccurrences fuel first.executableRule target :=
      (congrFun (input.evaluateLocalizedOccurrences_eq_model fuel first firstModel) target).symm
    _ = input.evaluateLocalizedOccurrences fuel second.executableRule target :=
      input.evaluateLocalizedOccurrences_eq_on_region fuel first.executableRule
        second.executableRule region region_closed agree target hregion
    _ = secondState target :=
      congrFun (input.evaluateLocalizedOccurrences_eq_model fuel second secondModel) target

/-! ## Dependency-checked certificate bridge -/

/-- The localized occurrence system is local for the executable dependency list of the finite
carrier.  The list membership is converted to `LocalizedDepthDependency` by the existing
characterization `mem_localizedDependencyList_iff`. -/
theorem localizedEvaluatorLocalForDependencyList
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedAuxiliaryOccurrenceSystem semantics).EvaluatorLocalFor
      (relation (fun target => input.localizedDependencyList fuel target)) := by
  intro left right target agree
  exact input.localizedAuxiliaryEvaluatorLocal semantics left right target
    (fun source related =>
      agree source ((input.mem_localizedDependencyList_iff fuel target source).mpr related))

/-- **Regional equality of accepted localized dependency-checked certificates.**

Two accepted, duplicate-free and occurrence-complete certificates for two localized rule
semantics, both checked against the executable carrier dependency list, induce lookup states that
agree on every occurrence of a dependency-closed region whenever the two executable rules agree
there on pointwise-equal lower-rank views.  This instantiates
`DependencyCheckedModel.checked_lookup_eq_on_region`; the certificate itself supplies the
occurrence order, so neither well-foundedness-free replay nor a supplied global state is needed. -/
theorem checkedLookup_eq_on_region
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (first second : input.LocalizedAuxiliaryRuleSemantics fuel)
    (firstNodes : List (Node (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel))
    (firstResult : List (Fact (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel))
    (secondNodes : List (Node (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel))
    (secondResult : List (Fact (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel))
    (firstAccepted : check (input.localizedAuxiliaryOccurrenceSystem first)
      (fun target => input.localizedDependencyList fuel target) firstNodes = some firstResult)
    (secondAccepted : check (input.localizedAuxiliaryOccurrenceSystem second)
      (fun target => input.localizedDependencyList fuel target) secondNodes = some secondResult)
    (firstNodup : (firstResult.map Prod.fst).Nodup)
    (secondNodup : (secondResult.map Prod.fst).Nodup)
    (firstComplete : ∀ occurrence, occurrence ∈ firstResult.map Prod.fst)
    (secondComplete : ∀ occurrence, occurrence ∈ secondResult.map Prod.fst)
    (region : input.LocalizedCIPOccurrence fuel → Prop)
    (region_closed : ∀ {source target : input.LocalizedCIPOccurrence fuel},
      input.LocalizedDepthDependency source target → region target → region source)
    (agree : ∀ target, region target →
      ∀ (firstView secondView : input.LocalizedDependencyView target),
        (∀ source, ∀ dependency : input.LocalizedDepthDependency source target,
          firstView source dependency = secondView source dependency) →
        first.executableRule target firstView = second.executableRule target secondView) :
    ∀ target, region target → lookup firstResult target = lookup secondResult target := by
  refine TetraStereo.Certificate.DependencyCheckedModel.checked_lookup_eq_on_region
    (firstSystem := input.localizedAuxiliaryOccurrenceSystem first)
    (secondSystem := input.localizedAuxiliaryOccurrenceSystem second)
    (dependency := @input.LocalizedDepthDependency fuel)
    (wellFounded := input.localizedDepthDependency_wellFounded fuel)
    (firstDependencies := fun target => input.localizedDependencyList fuel target)
    (secondDependencies := fun target => input.localizedDependencyList fuel target)
    (firstLocality := input.localizedEvaluatorLocalForDependencyList fuel first)
    (secondLocality := input.localizedEvaluatorLocalForDependencyList fuel second)
    (firstAccepted := firstAccepted) (secondAccepted := secondAccepted)
    (firstNodup := firstNodup) (secondNodup := secondNodup)
    (firstComplete := firstComplete) (secondComplete := secondComplete)
    (region := region) (region_closed := region_closed)
    (agree := ?_)
    firstNodes firstResult secondNodes secondResult
  intro target hregion left right hleft
  exact agree target hregion
    (input.localizedDependencyView left target)
    (input.localizedDependencyView right target)
    (fun source related => hleft source related)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
