import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep
import TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus
import TetraStereo.OneCenter.Rule6Proposed2018PromotionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Independent axes of a ring reference policy

This module separates reference lifetime, auxiliary regeneration and aggregation, and pins the
actual source fallback to its operational policy. It is a policy investigation interface, not
a chemical source-model certificate.
In particular, neither reference discipline is attributed to the journal's optional extension.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy

open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedChemicalRingStabilizerConsensus

/-- Ordered retention and replacement by the current reference are different policies. -/
inductive ReferenceLifetime where
  | accumulated
  | current
  deriving DecidableEq

/-- Regeneration is independent of which references survive. -/
inductive AuxiliaryChronology where
  | frozen
  | regenerated
  deriving DecidableEq

inductive Aggregation where
  | consensus
  | cancellation
  deriving DecidableEq

structure Policy where
  lifetime : ReferenceLifetime
  chronology : AuxiliaryChronology
  aggregation : Aggregation

/-- No attribution to a source follows from choosing one of these constructors. -/
def extend {Atom : Type} (lifetime : ReferenceLifetime)
    (references : List Atom) (reference : Atom) : List Atom :=
  match lifetime with
  | .accumulated => references ++ [reference]
  | .current => [reference]

/-- Their difference is observable already at a second promotion, independently of labels. -/
theorem second_promotion_accumulated {Atom : Type} (first second : Atom) :
    extend .accumulated (extend .accumulated [] first) second = [first, second] := rfl

theorem second_promotion_current {Atom : Type} (first second : Atom) :
    extend .current (extend .current [] first) second = [second] := rfl

theorem second_promotion_contexts_ne {Atom : Type} (first second : Atom) :
    extend .accumulated (extend .accumulated [] first) second ≠
      extend .current (extend .current [] first) second := by
  intro h
  have lengths := congrArg List.length h
  simp [extend] at lengths

/-- Collapse the operational distinction only for the consensus comparison. Cancellation keeps
operational failure distinct from a completed unresolved promotion. -/
def promotionReading : PromotionOutcome → Option RS
  | .operationalFailure => none
  | .unresolved => none
  | .descriptor descriptor => some descriptor

/-- Both operators have the same result type; `some none` is completed refusal. -/
def aggregate (aggregation : Aggregation) (outcomes : List PromotionOutcome) :
    Option (Option RS) :=
  match aggregation with
  | .consensus => some (consensus (outcomes.map promotionReading))
  | .cancellation => promotionAggregate outcomes

/-- A majority is sufficient for cancellation and insufficient for consensus. This is an
operator counterexample, not a claim that this population is chemically realized. -/
theorem aggregation_axes_distinct :
    aggregate .cancellation [.descriptor .R, .descriptor .S, .descriptor .R] =
      some (some .R) ∧
    aggregate .consensus [.descriptor .R, .descriptor .S, .descriptor .R] =
      some none := by
  decide

/-- A completed nonunique promotion is ignored in cancellation, not in consensus. -/
theorem unresolved_axes_distinct :
    aggregate .cancellation [.descriptor .R, .unresolved] = some (some .R) ∧
    aggregate .consensus [.descriptor .R, .unresolved] = some none := by
  decide

/-- Failure must not silently become a completed refusal. -/
theorem failure_axes_distinct :
    aggregate .cancellation [.operationalFailure] = none ∧
    aggregate .consensus [.operationalFailure] = some none := by
  decide

/-! The bridge below pins the implemented one-promotion operation to these axes. It says
nothing about equivalence of independently regenerated profiles. -/

noncomputable section
open scoped Classical
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedGenericMarkedRecalculation (Geometry)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)

variable (input : CertifiedLocalizedCIPInput)

/-- Independently choose the comparison reference vector and the context of the auxiliary map.
Frozen means the map is read before this promotion, not that its whole recursive profile has
already been independently regenerated under a frozen policy. -/
def policyFallback (single : input.moleculeGraph.SimpleBonded)
    (lifetime : ReferenceLifetime) (chronology : AuxiliaryChronology)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) (slot : Fin 4) : Option RS :=
  (frameAtom? input frame slot).bind fun reference =>
    let extended := extend lifetime references reference
    let mapContext := match chronology with
      | .frozen => references
      | .regenerated => extended
    let selectedFamily : DescriptorFamily input := fun geometry _ => family geometry mapContext
    if Function.Injective
        (sourceKeysAt input single selectedFamily target frame geom extended) then
      sourceReading input geom frame
        (sourceKeysAt input single selectedFamily target frame geom extended)
    else none

/-- Exact operational mapping to CURRENT, without a claim about the journal's underspecified
reference lifetime or about a second recursive evaluator. -/
theorem actual_fallback_policy (single : input.moleculeGraph.SimpleBonded)
    (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) (slot : Fin 4) :
    policyFallback input single .accumulated .regenerated family target frame geom references slot =
      sourceFallback input single family target frame geom references slot := rfl

end

end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.ReferenceLifetime
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.AuxiliaryChronology
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.Aggregation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.Policy
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.extend
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.second_promotion_accumulated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.second_promotion_current
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.second_promotion_contexts_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.promotionReading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.aggregate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.aggregation_axes_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.unresolved_axes_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.failure_axes_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.policyFallback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy.actual_fallback_policy
