import TetraStereo.OneCenter.LocalizedNoDoubleReferenceInput
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.LocalizedRankedIteration
import TetraStereo.OneCenter.FiniteStateIteration
import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5FixedPoint

set_option autoImplicit false

/-!
# Runnable localized no-double-bond reference pipeline

This module assembles the full reference evaluation over the checked runtime intake of
`TetraStereo.OneCenter.LocalizedNoDoubleReferenceInput`.  Every object on the runnable path is an
ordinary `def`:

* `carrierFuel` is the constitutional expansion depth `atomCount + 1`;
* `iterationRounds` is the strict-dependency budget `carrierFuel + 2`;
* `evaluator` is the executable no-double-bond descriptor twin of
  `LocalizedNoDoubleDescriptorExecutable` (whose `localizedNoDoubleDescriptorExec?` is proved equal
  to the original descriptor-bearing occurrence descriptor under the admitted source hypothesis);
* `evaluatedFacts` materializes one tabulation round per carrier occurrence with
  `FiniteStateIteration.tabulatedFacts`, reading each previous round exactly once;
* `evaluatedState` is the dependency-certificate lookup of that fact list;
* `analyze` reports every detected tetrahedral center together with its optional computed label;
  no center is filtered out and no `none` entry is dropped.

The admitted `Input` already carries the structural certificate, the localized CIP graph readiness,
and the kernel proof of the source-record no-double-bond restriction, so a caller supplies no
per-molecule proof obligation.

## Exactness results

* `evaluatedState_eq_evaluateLocalizedOccurrences` — the tabulated state is exactly
  `CertifiedLocalizedCIPInput.evaluateLocalizedOccurrences` at the executable descriptor twin
  (via the generic `FiniteStateIteration.lookupState_tabulatedFacts`).
* `evaluatedState_eq_descriptorBearingBuildOccurrenceState` and
  `evaluatedState_eq_descriptorBearingModel` — the computed state equals the well-founded
  descriptor-bearing solution and every declarative descriptor-bearing model, via
  `LocalizedRankedIteration`'s generic theorems and the proved equality of the executable twin.
* `cipModel_evaluatedState` / `cipModel_evaluatedState_descriptorBearing` — the computed state is a
  complete model of the runtime semantics and of the descriptor-bearing semantics.
* `evaluatedState_apply_iff_declarative` and `evaluatedState_eq_executableStep_apply` — pointwise,
  the computed state agrees exactly with the repository's declarative descriptor-bearing outcome
  relation, and it is a fixed point of the restricted executable step.
* `analyze_mem_iff`, `analyze_length`, `analyze_center_reported` — the reported enumeration is
  exactly the center list, entry for entry, with no silent filtering.
* `analyze_positive_sound` and `occurrence_descriptor_refusal_iff_no_canonical` — every positively
  reported label is a canonical descriptor-bearing descriptor of the occurrence, and every `none`
  is reported precisely when the descriptor-bearing computation has no canonical result there: the
  refusal is a computed refusal, not a dropped entry.

## Scope of the claims (explicit)

`CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor` is the repository's exact
accepted-evidence relation: it requires `localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?`
to return `some evidence`, so it is an operational/evidence relation and not an independently
specified notion of chemical completeness.  A reported `none` therefore says only that this
descriptor-bearing computation produced no canonical evidence at the occurrence; it is not a claim
that the molecule has no stereogenic unit, and it is not chemical nonexistence.  In particular,
admission does not require spatial data: an admitted input without an exact configuration has a
well-defined report whose entries are refusals from missing evidence.

## Residual work (explicit, outside this module)

No certificate object is produced here (a separate producer supplies it), and no claim is made that
the reported optional state is complete over all descriptor families: `none` is a computed refusal
for the descriptor-bearing relation only, and the source gate admits molecules with no detected
center or with no stereogenic unit.  Nothing here asserts that successful admission implies any
particular descriptor outcome.
-/

namespace TetraStereo.OneCenter.LocalizedNoDoubleReference
open CertifiedLocalizedCIPInput

/-- Complete constitutional expansion depth for the admitted finite graph. -/
def carrierFuel (input : Input) : Nat := input.molecule.atomCount + 1

/-- Strict-dependency rounds sufficient for every carried occurrence. -/
def iterationRounds (input : Input) : Nat := carrierFuel input + 2

/-- The runtime rule observes the admitted input's no-double-bond domain. -/
def evaluator (input : Input) (fuel : Nat) : input.certified.LocalizedRestrictedEvaluator fuel :=
  input.certified.localizedNoDoubleDescriptorExec?

/-- Materialize each round once over the complete finite carrier. -/
def evaluatedFacts (input : Input) :
    List (Certificate.Dependency.Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel) :=
  FiniteStateIteration.tabulatedFacts
    (input.certified.localizedOccurrenceCarrier (carrierFuel input))
    (input.certified.localizedExecutableStep (evaluator input (carrierFuel input)))
    (fun _ => none) (iterationRounds input)

/-- The computed dependency-certificate state: the lookup of the tabulated fact list. -/
def evaluatedState (input : Input) : input.certified.LocalizedAuxiliaryState (carrierFuel input) :=
  Certificate.Dependency.lookup (evaluatedFacts input)

/-- Every detected center is reported, including unassigned optional outcomes. -/
def analyze (input : Input) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  let facts := evaluatedFacts input
  input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, Certificate.Dependency.lookup facts
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))

/-! ## The runtime semantics and the exact equality of the executable twin -/

/-- The executable descriptor twin, as a whole evaluator, equals the original descriptor-bearing
occurrence descriptor.  This is the pointwise-vs-view form of
`localizedNoDoubleDescriptorExec?_eq_localizedOccurrenceDescriptorBearingRule3Through5Descriptor?`,
using the admitted source-record no-double-bond proof and no further hypothesis. -/
theorem evaluator_eq_descriptorBearing (input : Input) (fuel : Nat) :
    evaluator input fuel =
      input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? := by
  funext target view
  simp only [evaluator]
  exact
    input.certified.localizedNoDoubleDescriptorExec?_eq_localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
      input.noDouble target view

/-- Pointwise/oriented form of `evaluator_eq_descriptorBearing`, for a single target and view. -/
theorem evaluator_apply_eq_descriptorBearing (input : Input) (fuel : Nat)
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target) :
    evaluator input fuel target view =
      input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? target view :=
  congrFun (congrFun (evaluator_eq_descriptorBearing input fuel) target) view

/-- The runtime localized rule semantics: the repository's declarative descriptor-bearing outcome
relation as the derivation, with the *executable* no-double-bond descriptor twin as the restricted
executable rule.  The correspondence field is exactly the proved equality of the twin under the
admitted no-double-bond hypothesis, so the derivation is not defined as executable equality; it is
the pre-existing evidence-bearing relation, restricted to the admitted domain.

This is an ordinary `def`: it stores only the computable executable rule plus a property-valued
function and a proof, so an instantiated semantics is directly available to downstream executable
consumers. -/
def runtimeSemantics (input : Input) (fuel : Nat) :
    input.certified.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation :=
    input.certified.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
  executableRule := evaluator input fuel
  derivation_executable_iff := by
    intro state target outcome
    rw [evaluator_apply_eq_descriptorBearing input fuel target
      (input.certified.localizedDependencyView state target)]
    exact
      input.certified.declarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome_iff
        state target outcome

/-- The descriptor-bearing semantics of `LocalizedOccurrenceDescriptorBearingRule3Through5FixedPoint`
as an explicit abbreviation, for the equality statements below. -/
noncomputable abbrev descriptorBearingSemantics (input : Input) (fuel : Nat) :
    input.certified.LocalizedAuxiliaryRuleSemantics fuel :=
  input.certified.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel

/-- The runtime semantics is an ordinary `def` whose restricted executable rule is exactly the
runtime evaluator, so a downstream executable consumer can read the rule off an instantiated
semantics without any noncomputability annotation. -/
@[simp] theorem runtimeSemantics_executableRule (input : Input) (fuel : Nat) :
    (runtimeSemantics input fuel).executableRule = evaluator input fuel := rfl

/-! ## The computed state is the computable iteration -/

/-- **Exact equality with the computable iteration.**  The tabulated state read off the runtime fact
list is exactly `evaluateLocalizedOccurrences` at the executable descriptor twin.  The only input is
carrier completeness, which is a theorem of the finite carrier. -/
theorem evaluatedState_eq_evaluateLocalizedOccurrences (input : Input) :
    evaluatedState input =
      input.certified.evaluateLocalizedOccurrences (carrierFuel input)
        (evaluator input (carrierFuel input)) := by
  unfold evaluatedState evaluatedFacts iterationRounds evaluateLocalizedOccurrences
  exact FiniteStateIteration.lookupState_tabulatedFacts
    (input.certified.localizedOccurrenceCarrier (carrierFuel input))
    (input.certified.localizedOccurrenceCarrier_complete (carrierFuel input))
    (input.certified.localizedExecutableStep (evaluator input (carrierFuel input)))
    (fun _ => none) (carrierFuel input + 2)

/-- **Exact equality with the old semantics' computable iteration.**  Evaluating the admitted input
through the new executable twin gives the same state as evaluating it through the original
descriptor-bearing occurrence descriptor. -/
theorem evaluatedState_eq_evaluateLocalizedOccurrences_descriptorBearing (input : Input) :
    evaluatedState input =
      input.certified.evaluateLocalizedOccurrences (carrierFuel input)
        (descriptorBearingSemantics input (carrierFuel input)).executableRule := by
  rw [evaluatedState_eq_evaluateLocalizedOccurrences]
  exact congrArg (input.certified.evaluateLocalizedOccurrences (carrierFuel input))
    (evaluator_eq_descriptorBearing input (carrierFuel input))

/-! ## The computed state is the descriptor-bearing model -/

/-- **Equality with the well-founded descriptor-bearing solution.**  The computed state equals the
noncomputable well-founded state built from the original descriptor-bearing semantics. -/
theorem evaluatedState_eq_descriptorBearingBuildOccurrenceState (input : Input) :
    evaluatedState input =
      (input.certified.localizedAuxiliaryOccurrenceSystem
        (descriptorBearingSemantics input (carrierFuel input))).buildOccurrenceState
        (@input.certified.LocalizedDepthDependency (carrierFuel input))
        (input.certified.localizedDepthDependency_wellFounded (carrierFuel input)) := by
  rw [evaluatedState_eq_evaluateLocalizedOccurrences_descriptorBearing]
  exact
    input.certified.evaluateLocalizedOccurrences_eq_buildOccurrenceState_fun (carrierFuel input)
      (descriptorBearingSemantics input (carrierFuel input))

/-- **Uniqueness against every descriptor-bearing model.**  Any declarative descriptor-bearing model
is the computed state, so no independently supplied solution can differ from the runtime result. -/
theorem evaluatedState_eq_descriptorBearingModel (input : Input)
    {state : input.certified.LocalizedAuxiliaryState (carrierFuel input)}
    (model : (input.certified.localizedAuxiliaryOccurrenceSystem
      (descriptorBearingSemantics input (carrierFuel input))).CIPModel state) :
    evaluatedState input = state := by
  rw [evaluatedState_eq_evaluateLocalizedOccurrences_descriptorBearing]
  exact
    input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
      (descriptorBearingSemantics input (carrierFuel input)) model

/-- The computed state is a complete model of the runtime semantics (executable twin as the rule). -/
theorem cipModel_evaluatedState (input : Input) :
    (input.certified.localizedAuxiliaryOccurrenceSystem
      (runtimeSemantics input (carrierFuel input))).CIPModel (evaluatedState input) := by
  rw [evaluatedState_eq_evaluateLocalizedOccurrences]
  exact
    input.certified.cipModel_evaluateLocalizedOccurrences (carrierFuel input)
      (runtimeSemantics input (carrierFuel input))

/-- The computed state is the decoded dependency-ready causal scheduler closure of the
descriptor-bearing occurrence system. -/
theorem evaluatedState_eq_descriptorBearingSchedulerClosure_decode (input : Input) :
    evaluatedState input =
      DeclarativeCIP.OccurrenceScheduler.decode
        (input.certified.localizedAuxiliaryOccurrenceSystem
          (descriptorBearingSemantics input (carrierFuel input)))
        (@input.certified.LocalizedDepthDependency (carrierFuel input))
        (DeclarativeCIP.OccurrenceScheduler.closure
          (input.certified.localizedAuxiliaryOccurrenceSystem
            (descriptorBearingSemantics input (carrierFuel input)))
          (@input.certified.LocalizedDepthDependency (carrierFuel input))) := by
  rw [evaluatedState_eq_evaluateLocalizedOccurrences_descriptorBearing]
  exact
    input.certified.evaluateLocalizedOccurrences_eq_schedulerClosure_decode (carrierFuel input)
      (descriptorBearingSemantics input (carrierFuel input))

/-- The computed state is a complete model of the descriptor-bearing semantics. -/
theorem cipModel_evaluatedState_descriptorBearing (input : Input) :
    (input.certified.localizedAuxiliaryOccurrenceSystem
      (descriptorBearingSemantics input (carrierFuel input))).CIPModel (evaluatedState input) := by
  rw [evaluatedState_eq_evaluateLocalizedOccurrences_descriptorBearing]
  exact
    input.certified.cipModel_evaluateLocalizedOccurrences (carrierFuel input)
      (descriptorBearingSemantics input (carrierFuel input))

/-- The computed state is a fixed point of the restricted executable step. -/
theorem evaluatedState_eq_executableStep_apply (input : Input)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input)) :
    evaluatedState input target =
      evaluator input (carrierFuel input) target
        (input.certified.localizedDependencyView (evaluatedState input) target) := by
  have ruleEq : (runtimeSemantics input (carrierFuel input)).executableRule =
      evaluator input (carrierFuel input) := rfl
  have fixed :=
    input.certified.localizedRawStep_evaluateLocalizedOccurrences_fixed (carrierFuel input)
      (runtimeSemantics input (carrierFuel input))
  rw [ruleEq, ← evaluatedState_eq_evaluateLocalizedOccurrences input] at fixed
  simpa only [localizedRawStep, localizedExecutableStep] using (congrFun fixed target).symm

/-- **The semantic-model theorem.**  Pointwise, the computed state satisfies the repository's
descriptor-bearing outcome relation *exactly*: an outcome is computed if and only if that relation
derives it.  Both the emitted label and the refusal are covered, so no optional outcome of the
descriptor-bearing computation is lost or invented. -/
theorem evaluatedState_apply_iff_declarative (input : Input)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (outcome : Option LocalizedAuxiliaryLabel) :
    evaluatedState input target = outcome ↔
      input.certified.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
        (evaluatedState input) target outcome := by
  constructor
  · intro computed
    have executable :
        evaluator input (carrierFuel input) target
            (input.certified.localizedDependencyView (evaluatedState input) target) = outcome :=
      (evaluatedState_eq_executableStep_apply input target).symm.trans computed
    exact
      ((runtimeSemantics input (carrierFuel input)).derivation_executable_iff
        (evaluatedState input) target outcome).mpr executable
  · intro derived
    have executable :
        evaluator input (carrierFuel input) target
            (input.certified.localizedDependencyView (evaluatedState input) target) = outcome :=
      ((runtimeSemantics input (carrierFuel input)).derivation_executable_iff
        (evaluatedState input) target outcome).mp derived
    exact (evaluatedState_eq_executableStep_apply input target).trans executable

/-- The `lookup` of a tabulated fact list is the computed state, definitionally. -/
theorem lookup_evaluatedFacts_eq_evaluatedState (input : Input)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input)) :
    Certificate.Dependency.lookup (evaluatedFacts input) target = evaluatedState input target :=
  rfl

/-! ## The reported center enumeration -/

/-- **Exact membership of the report.**  A pair is reported if and only if it comes from a detected
center of the canonical enumeration, with that center's atom index and that center's final
occurrence outcome.  No entry is invented, reordered away, or silently dropped. -/
theorem analyze_mem_iff (input : Input) (entry : Nat × Option LocalizedAuxiliaryLabel) :
    entry ∈ analyze input ↔
      ∃ center : input.certified.TetrahedralCenter,
        center ∈ input.certified.canonicalTetrahedralCenters ∧
          center.val.val = entry.1 ∧
            Certificate.Dependency.lookup (evaluatedFacts input)
              (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
                entry.2 := by
  unfold analyze
  rw [List.mem_map]
  constructor
  · rintro ⟨center, present, equal⟩
    exact ⟨center, present, (Prod.mk.inj equal).1, (Prod.mk.inj equal).2⟩
  · rintro ⟨center, present, indexEq, outcomeEq⟩
    exact ⟨center, present, Prod.ext indexEq outcomeEq⟩

/-- The report has exactly one entry per detected center: the enumeration never filters. -/
theorem analyze_length (input : Input) :
    (analyze input).length = input.certified.canonicalTetrahedralCenters.length := by
  unfold analyze
  rw [List.length_map]

/-- Every detected center is reported, with its atom index, whatever its optional outcome. -/
theorem analyze_center_reported (input : Input) (center : input.certified.TetrahedralCenter)
    (present : center ∈ input.certified.canonicalTetrahedralCenters) :
    ∃ label : Option LocalizedAuxiliaryLabel, (center.val.val, label) ∈ analyze input :=
  ⟨_, List.mem_map.mpr ⟨center, present, rfl⟩⟩

/-- Every reported entry is a detected center's entry: the report is a sublist-free image of the
canonical center enumeration. -/
theorem analyze_mem_canonicalCenter (input : Input) (entry : Nat × Option LocalizedAuxiliaryLabel)
    (reported : entry ∈ analyze input) :
    ∃ center ∈ input.certified.canonicalTetrahedralCenters, center.val.val = entry.1 :=
  let ⟨center, present, indexEq, _⟩ := (analyze_mem_iff input entry).mp reported
  ⟨center, present, indexEq⟩

/-! ## Positive soundness and derived refusal -/

/-- A positively computed executable outcome at a target and view is a canonical descriptor-bearing
descriptor: the executable twin is unfolded to the original descriptor-bearing occurrence
descriptor, whose `some`-outcomes are exactly the relation that records the accepted
descriptor-bearing evidence at that occurrence. -/
theorem canonical_of_executable_some (input : Input) (fuel : Nat)
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target)
    {label : LocalizedAuxiliaryLabel}
    (computed : evaluator input fuel target view = some label) :
    input.certified.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
      target view label := by
  rw [evaluator_apply_eq_descriptorBearing input fuel target view] at computed
  exact
    (input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_some_iff_canonical
      target view label).mp computed

/-- **Positive descriptor soundness at a detected center.**  Whenever the runtime report yields a
label at a center's final occurrence, that label is a canonical descriptor-bearing descriptor of the
occurrence, evaluated against the computed state's dependency view: the report cannot invent a
label. -/
theorem occurrence_descriptor_sound (input : Input)
    (center : input.certified.TetrahedralCenter) {label : LocalizedAuxiliaryLabel}
    (reported : Certificate.Dependency.lookup (evaluatedFacts input)
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
        some label) :
    input.certified.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
      (input.certified.localizedDependencyView (evaluatedState input)
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))
      label := by
  refine canonical_of_executable_some input (carrierFuel input)
    (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
    (input.certified.localizedDependencyView (evaluatedState input)
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)) ?_
  rw [← evaluatedState_eq_executableStep_apply input
    (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)]
  exact reported

/-- The declarative reading of a positively reported label: a canonical success is not merely an
optional outcome but satisfies the repository's declarative descriptor-bearing relation, whose
evidence is carried by the occurrence itself. -/
theorem occurrence_descriptor_sound_declarative (input : Input)
    (center : input.certified.TetrahedralCenter) {label : LocalizedAuxiliaryLabel}
    (reported : Certificate.Dependency.lookup (evaluatedFacts input)
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
        some label) :
    input.certified.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
      (input.certified.localizedDependencyView (evaluatedState input)
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))
      label :=
  CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor.implies_declarative
    input.certified
    (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
    (input.certified.localizedDependencyView (evaluatedState input)
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))
    label (occurrence_descriptor_sound input center reported)

/-- **Computed refusal, exactly.**  A `none` at a center's final occurrence is not missing data: it
is reported precisely when the descriptor-bearing computation has no canonical accepted evidence
there.  This is a statement about that computation, not about chemical nonexistence; in particular a
missing exact spatial configuration also yields `none`. -/
theorem occurrence_descriptor_refusal_iff_no_canonical (input : Input)
    (center : input.certified.TetrahedralCenter) :
    Certificate.Dependency.lookup (evaluatedFacts input)
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) = none ↔
      ¬ ∃ descriptor : LocalizedAuxiliaryLabel,
        input.certified.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
          (input.certified.localizedDependencyView (evaluatedState input)
            (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))
          descriptor := by
  have step :=
    evaluatedState_eq_executableStep_apply input
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
  constructor
  · intro refused
    have executableRefused :
        evaluator input (carrierFuel input)
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
          (input.certified.localizedDependencyView (evaluatedState input)
            (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)) =
          none := by
      rw [← step]
      exact refused
    rw [evaluator_apply_eq_descriptorBearing input (carrierFuel input)
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
      (input.certified.localizedDependencyView (evaluatedState input)
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))] at executableRefused
    exact
      (input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_none_iff_no_canonical
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
        (input.certified.localizedDependencyView (evaluatedState input)
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))).mp
        executableRefused
  · intro absent
    have executableRefused :
        evaluator input (carrierFuel input)
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
          (input.certified.localizedDependencyView (evaluatedState input)
            (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)) =
          none := by
      rw [evaluator_apply_eq_descriptorBearing input (carrierFuel input)
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
        (input.certified.localizedDependencyView (evaluatedState input)
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))]
      exact
        (input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_none_iff_no_canonical
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
          (input.certified.localizedDependencyView (evaluatedState input)
            (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))).mpr
          absent
    have stateRefused :
        evaluatedState input
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) = none := by
      rw [step]
      exact executableRefused
    exact stateRefused

/-- The report of a positively labelled entry: a detected center whose final occurrence carries a
canonical descriptor-bearing descriptor for the reported label. -/
def ReportedDescriptor (input : Input) (entry : Nat × Option LocalizedAuxiliaryLabel)
    (label : LocalizedAuxiliaryLabel) : Prop :=
  ∃ center ∈ input.certified.canonicalTetrahedralCenters,
    center.val.val = entry.1 ∧
      input.certified.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
        (input.certified.localizedDependencyView (evaluatedState input)
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))
        label

/-- **Center positive soundness of the report.**  Every entry the runtime report emits with a label
comes from a detected canonical center and is a canonical descriptor-bearing descriptor at that
center's root occurrence. -/
theorem analyze_positive_sound (input : Input) (entry : Nat × Option LocalizedAuxiliaryLabel)
    (label : LocalizedAuxiliaryLabel) (reported : (entry.1, some label) ∈ analyze input) :
    ReportedDescriptor input entry label := by
  obtain ⟨center, present, indexEq, lookupEq⟩ :=
    (analyze_mem_iff input (entry.1, some label)).mp reported
  exact ⟨center, present, indexEq, occurrence_descriptor_sound input center lookupEq⟩

/-- **Reported refusal soundness.**  Every `none` the report emits is a computed refusal: the
descriptor-bearing computation has no canonical accepted evidence at that center.  No entry is
dropped or silently replaced. -/
theorem analyze_refusal_sound (input : Input) (entry : Nat × Option LocalizedAuxiliaryLabel)
    (reported : (entry.1, none) ∈ analyze input) :
    ∃ center ∈ input.certified.canonicalTetrahedralCenters,
      center.val.val = entry.1 ∧
        ¬ ∃ descriptor : LocalizedAuxiliaryLabel,
          input.certified.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
            (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
            (input.certified.localizedDependencyView (evaluatedState input)
              (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))
            descriptor := by
  obtain ⟨center, present, indexEq, lookupEq⟩ :=
    (analyze_mem_iff input (entry.1, none)).mp reported
  exact ⟨center, present, indexEq,
    (occurrence_descriptor_refusal_iff_no_canonical input center).mp lookupEq⟩

/-! ## Checked-admission wrappers

Each wrapper keeps the exactness facts of the corresponding checked constructor and adds the
descriptor soundness of the report.  The source gate is a source-record restriction only: these
statements do not claim that successful admission yields any center, any label, or completeness over
descriptor families. -/

/-- Positive soundness for a source admitted by `admitSource?`, which is exactly the supplied
source. -/
theorem admitSource?_analyze_positive_sound (source : AuthoritativeChemicalInput) (input : Input)
    (admitted : admitSource? source = some input) (entry : Nat × Option LocalizedAuxiliaryLabel)
    (label : LocalizedAuxiliaryLabel) (reported : (entry.1, some label) ∈ analyze input) :
    input.certified.certified.input = source ∧ ReportedDescriptor input entry label :=
  ⟨(admitSource?_exact source input admitted).1, analyze_positive_sound input entry label reported⟩

/-- Positive soundness for a raw molecule with an independently supplied exact spatial
configuration, preserving the structure agreement and the coordinate assignment. -/
theorem admitRawSpatial?_analyze_positive_sound (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (input : Input)
    (admitted : admitRawSpatial? molecule spatial = some input)
    (entry : Nat × Option LocalizedAuxiliaryLabel) (label : LocalizedAuxiliaryLabel)
    (reported : (entry.1, some label) ∈ analyze input) :
    molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
      input.certified.certified.input.spatial? = some spatial ∧
        ReportedDescriptor input entry label := by
  obtain ⟨agreement, spatialEq, _⟩ := admitRawSpatial?_exact molecule spatial input admitted
  exact ⟨agreement, spatialEq, analyze_positive_sound input entry label reported⟩

/-- Positive soundness for an OpenSMILES-facing admission, exposing the certified normalization
result and the source-record restriction of the admitted molecule. -/
theorem admitSmilesSpatial?_analyze_positive_sound (text : String)
    (spatial : SpatialConfiguration) (cycles : List AromaticCycle) (input : Input)
    (admitted : admitSmilesSpatial? text spatial cycles = Except.ok (some input))
    (entry : Nat × Option LocalizedAuxiliaryLabel) (label : LocalizedAuxiliaryLabel)
    (reported : (entry.1, some label) ∈ analyze input) :
    ∃ certified : CertifiedChemistryNormalizationResult,
      parseAndNormalizeOpenSMILESCertified text cycles = Except.ok certified ∧
        input.NoDoubleRecords ∧ ReportedDescriptor input entry label := by
  obtain ⟨certified, parsed, _admissible, _agreement, _spatialEq, noDouble⟩ :=
    admitSmilesSpatial?_ok_exact text spatial cycles input admitted
  exact ⟨certified, parsed, noDouble, analyze_positive_sound input entry label reported⟩

end TetraStereo.OneCenter.LocalizedNoDoubleReference
