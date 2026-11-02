import TetraStereo.OneCenter.LocalizedFamilyReferencePipeline
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitCachedPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedExtendedShortCircuit.Families
open CertifiedLocalizedCIPInput Certificate.Dependency

/-! Existing state-parametric family assignments are reused unchanged. Only the checked
auxiliary evaluation and its reference-state semantics are replaced by the extended pipeline. -/
export LocalizedShortCircuit.Families
  (Attempt State EvenAttempt OddAttempt RingAttempt OrdinaryAttempt
   canonicalDoubleBondPairs canonicalDoubleBondPairs_eq canonicalDoubleBonds
   evenAttempts oddAttempts ringAttempts ordinaryAttempts
   ordinaryAttempts_candidates evenAttempts_candidates oddAttempts_candidates ringAttempts_candidates
   cyclicBoundaries cyclicBoundaries_eq cyclicBoundaries_exact)

/-- Families share one checked auxiliary certificate. The family evaluator meanings are relative
to its state; no identification with the old family scheduler is needed or claimed. -/
structure Result (input : Input) where
  auxiliary : Evaluation input
  even : List (EvenAttempt input (lookup auxiliary.facts))
  odd : List (OddAttempt input (lookup auxiliary.facts))
  monocyclic : List (RingAttempt input (lookup auxiliary.facts))
  ordinaryAcyclic : List (OrdinaryAttempt input (lookup auxiliary.facts))
  evenExact : even = evenAttempts input (lookup auxiliary.facts)
  oddExact : odd = oddAttempts input (lookup auxiliary.facts)
  monocyclicExact : monocyclic = ringAttempts input (lookup auxiliary.facts)
  ordinaryAcyclicExact : ordinaryAcyclic = ordinaryAttempts input (lookup auxiliary.facts)
  boundaries : List input.certified.LocalizedFullyCyclicCumuleneAuthorityBoundary
  boundariesExact : boundaries = cyclicBoundaries input

def ofEvaluation (input : Input) (auxiliary : Evaluation input) : Result input :=
  { auxiliary
    even := evenAttempts input (lookup auxiliary.facts)
    odd := oddAttempts input (lookup auxiliary.facts)
    monocyclic := ringAttempts input (lookup auxiliary.facts)
    ordinaryAcyclic := ordinaryAttempts input (lookup auxiliary.facts)
    evenExact := rfl, oddExact := rfl, monocyclicExact := rfl
    ordinaryAcyclicExact := rfl
    boundaries := cyclicBoundaries input, boundariesExact := rfl }

def evaluate (input : Input) (proposals : Nodes input := []) : Result input :=
  ofEvaluation input (Cached.evaluate input proposals)

/-- Transport every part of an ordinary assignment certificate to the generated reference state. -/
def ordinaryAtReference (input : Input) (result : Result input)
    (bond : input.certified.LocalizedCanonicalDoubleBond)
    (assignment : OrdinaryPlanar.Assignment input.certified (carrierFuel input)
      (lookup result.auxiliary.facts) bond) :
    OrdinaryPlanar.Assignment input.certified (carrierFuel input) (referenceState input) bond := by
  rw [← evaluation_eq_reference input result.auxiliary]
  exact assignment

/-- Each positive family result also has its independent meaning at the generated global state. -/
theorem even_global_sound (input : Input) (result : Result input)
    (attempt : EvenAttempt input (lookup result.auxiliary.facts))
    (assignment : input.certified.LocalizedEvenAxialSpatialAssignment (carrierFuel input))
    (computed : attempt.outcome = some assignment) :
    input.certified.DeclarativeLocalizedEvenAxialSpatialAssignmentWithState
      (carrierFuel input) (referenceState input) assignment := by
  have sound := attempt.sound assignment computed
  rwa [evaluation_eq_reference input result.auxiliary] at sound

theorem odd_global_sound (input : Input) (result : Result input)
    (attempt : OddAttempt input (lookup result.auxiliary.facts))
    (assignment : input.certified.LocalizedOddCumuleneEZSpatialAssignment (carrierFuel input))
    (computed : attempt.outcome = some assignment) :
    input.certified.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState
      (carrierFuel input) (referenceState input) assignment := by
  have sound := attempt.sound assignment computed
  rwa [evaluation_eq_reference input result.auxiliary] at sound

theorem ring_global_sound (input : Input) (result : Result input)
    (attempt : RingAttempt input (lookup result.auxiliary.facts))
    (assignment : input.certified.LocalizedOrdinaryMonocyclicEZSpatialAssignment (carrierFuel input))
    (computed : attempt.outcome = some assignment) :
    input.certified.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState
      (carrierFuel input) (referenceState input) assignment := by
  have sound := attempt.sound assignment computed
  rwa [evaluation_eq_reference input result.auxiliary] at sound

def evaluateSource? (source : AuthoritativeChemicalInput) (propose : Proposer := fun _ => []) :
    Option ((input : Input) × Result input) := do
  let input ← admitSource? source
  pure ⟨input, evaluate input (propose input)⟩

def evaluateSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) (propose : Proposer := fun _ => []) :
    Except ParserError (Option ((input : Input) × Result input)) :=
  (admitSmilesSpatial? text spatial cycles).map fun admitted =>
    admitted.map fun input => ⟨input, evaluate input (propose input)⟩

end TetraStereo.OneCenter.LocalizedExtendedShortCircuit.Families
