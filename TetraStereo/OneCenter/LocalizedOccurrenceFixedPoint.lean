import TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame
import TetraStereo.OneCenter.LocalizedPseudoasymmetricClassification
import TetraStereo.OneCenter.DeclarativeCIPOccurrenceScheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Typed localized auxiliary-descriptor fixed-point boundary

This module connects the finite, occurrence-local molecular carrier to the generic fixed-point
and causal scheduler theorems.  A concrete chemical evaluator is not permitted to receive a
total descriptor state.  It receives only a dependent `LocalizedDependencyView` containing
strictly deeper occurrences below the same final-center root.  Consequently evaluator locality
is a theorem of the interface, not an assertion supplied by a caller.

The remaining production obligation is explicit: a concrete Rules-3--6 implementation must
supply an independently defined derivation relation, the restricted executable evaluator, and a
proof that they agree for every complete optional outcome.  This file does not discharge that
chemical correspondence by defining the relation to be executable equality.
-/

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

/-- Occurrence-level tetrahedral labels retain uppercase/lowercase case. -/
abbrev LocalizedAuxiliaryLabel := LocalizedTetrahedralRSPseudoDescriptor

/-- Projection from an occurrence label to the independent specification's final descriptor
alphabet. -/
def localizedAuxiliaryDescriptor : LocalizedAuxiliaryLabel → DeclarativeCIP.Descriptor
  | .chiral .R => .R
  | .chiral .S => .S
  | .pseudoasymmetric .r => .r
  | .pseudoasymmetric .s => .s

/-- Complete optional auxiliary-label state over exact molecular occurrences. -/
abbrev LocalizedAuxiliaryState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :=
  input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel

/-- The only state view exposed to one local evaluator call.  A coordinate can be read only with
a proof that it is a strict deeper dependency of the current target. -/
abbrev LocalizedDependencyView
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :=
  ∀ source : input.LocalizedCIPOccurrence fuel,
    input.LocalizedDepthDependency source target → Option LocalizedAuxiliaryLabel

/-- Restrict a total occurrence state to the target's proof-carrying dependency view. -/
def localizedDependencyView
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedDependencyView target :=
  fun source _dependency => state source

/-- Executable evaluator signature whose action space contains no nondependency reads. -/
abbrev LocalizedRestrictedEvaluator
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :=
  ∀ target : input.LocalizedCIPOccurrence fuel,
    input.LocalizedDependencyView target → Option LocalizedAuxiliaryLabel

/-- Lift a dependency-restricted evaluator to the total-state signature used by the generic
occurrence fixed-point core. -/
def localizedExecutableStep
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel) : Option LocalizedAuxiliaryLabel :=
  evaluator target (input.localizedDependencyView state target)

/-- Agreement on strict dependencies is sufficient for equality of a restricted evaluator call.
No theorem hypothesis about locality is required. -/
theorem localizedExecutableStep_eq_of_depthAgree
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (left right : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (agree : ∀ source, input.LocalizedDepthDependency source target →
      left source = right source) :
    input.localizedExecutableStep evaluator left target =
      input.localizedExecutableStep evaluator right target := by
  unfold localizedExecutableStep
  apply congrArg (evaluator target)
  funext source dependency
  exact agree source dependency

/-- A concrete occurrence semantics must keep its declarative rules independent from execution
and prove their complete optional-outcome correspondence.  The executable member is restricted
by type to the exact strict-depth view. -/
structure LocalizedAuxiliaryRuleSemantics
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  DeclarativeDerivation :
    input.LocalizedAuxiliaryState fuel →
      input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel → Prop
  executableRule : input.LocalizedRestrictedEvaluator fuel
  derivation_executable_iff : ∀ state target outcome,
    DeclarativeDerivation state target outcome ↔
      executableRule target (input.localizedDependencyView state target) = outcome

/-- Concrete localized semantics as an instance of the generic occurrence system. -/
noncomputable def localizedAuxiliaryOccurrenceSystem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    OccurrenceSystem input.TetrahedralCenter
      (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel where
  finalOccurrence := input.localizedFinalOccurrence fuel
  descriptorOf := localizedAuxiliaryDescriptor
  DeclarativeDerivation := semantics.DeclarativeDerivation
  executableStep := input.localizedExecutableStep semantics.executableRule

/-- The concrete semantics' independent correspondence field supplies the generic bridge. -/
theorem localizedAuxiliaryDerivationStepCorrespondence
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedAuxiliaryOccurrenceSystem semantics).DerivationStepCorrespondence := by
  intro state target outcome
  exact semantics.derivation_executable_iff state target outcome

/-- Every dependency-restricted localized semantics is local for exact root-relative depth. -/
theorem localizedAuxiliaryEvaluatorLocal
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedAuxiliaryOccurrenceSystem semantics).EvaluatorLocalFor
      (@input.LocalizedDepthDependency fuel) := by
  intro left right target agree
  exact input.localizedExecutableStep_eq_of_depthAgree
    semantics.executableRule left right target agree

/-- Any concrete localized chemical semantics satisfying the independent correspondence
obligation has exactly one complete occurrence model. -/
theorem existsUnique_localizedAuxiliaryCIPModel
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    ∃! state,
      (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state :=
  (input.localizedAuxiliaryOccurrenceSystem semantics).existsUnique_cipModel_of_wellFounded
    (input.localizedAuxiliaryDerivationStepCorrespondence semantics)
    (@input.LocalizedDepthDependency fuel)
    (input.localizedDepthDependency_wellFounded fuel)
    (input.localizedAuxiliaryEvaluatorLocal semantics)

/-- The dependency-ready causal scheduler decodes to a model of any completed concrete localized
semantics.  The certificates are recursively built along the proved molecular depth grading. -/
theorem localizedAuxiliarySchedulerClosure_cipModel
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel
      (DeclarativeCIP.OccurrenceScheduler.decode
        (input.localizedAuxiliaryOccurrenceSystem semantics)
        (@input.LocalizedDepthDependency fuel)
        (DeclarativeCIP.OccurrenceScheduler.closure
          (input.localizedAuxiliaryOccurrenceSystem semantics)
          (@input.LocalizedDepthDependency fuel))) := by
  exact DeclarativeCIP.OccurrenceScheduler.decode_closure_cipModel
    (input.localizedAuxiliaryOccurrenceSystem semantics)
    (input.localizedAuxiliaryDerivationStepCorrespondence semantics)
    (@input.LocalizedDepthDependency fuel)
    (input.localizedDepthDependency_wellFounded fuel)
    (input.localizedAuxiliaryEvaluatorLocal semantics)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
