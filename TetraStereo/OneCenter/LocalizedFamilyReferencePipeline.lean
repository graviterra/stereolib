import TetraStereo.OneCenter.LocalizedFamilyAssignmentsExecutable
import TetraStereo.OneCenter.LocalizedOrdinaryAcyclicAssignment
import TetraStereo.OneCenter.LocalizedShortCircuitBoundedPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedShortCircuit.Families
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- Preserve every candidate, including refused attempts. Each positive result carries its
independent state-relative topology, priority and geometry meaning. -/
structure Attempt (Candidate Result : Type) (Meaning : Result → Prop) where
  candidate : Candidate
  outcome : Option Result
  sound : ∀ result, outcome = some result → Meaning result

abbrev State (input : Input) := input.certified.LocalizedAuxiliaryState (carrierFuel input)

abbrev EvenAttempt (input : Input) (state : State input) :=
  Attempt input.certified.LocalizedEvenAxialChain
    (input.certified.LocalizedEvenAxialSpatialAssignment (carrierFuel input))
    (input.certified.DeclarativeLocalizedEvenAxialSpatialAssignmentWithState (carrierFuel input) state)

abbrev OddAttempt (input : Input) (state : State input) :=
  Attempt input.certified.LocalizedOddCumuleneChain
    (input.certified.LocalizedOddCumuleneEZSpatialAssignment (carrierFuel input))
    (input.certified.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState (carrierFuel input) state)

abbrev RingAttempt (input : Input) (state : State input) :=
  Attempt input.certified.LocalizedCanonicalDoubleBond
    (input.certified.LocalizedOrdinaryMonocyclicEZSpatialAssignment (carrierFuel input))
    (input.certified.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState (carrierFuel input) state)

/-- The ordinary payload contains its input-derived topology, exact endpoint compilations,
Rule5 selections, rational geometry and final outcome evidence. -/
structure OrdinaryAttempt (input : Input) (state : State input) where
  candidate : input.certified.LocalizedCanonicalDoubleBond
  outcome : Option (OrdinaryPlanar.Assignment input.certified (carrierFuel input) state candidate)

def canonicalDoubleBondPairs (input : Input) : List (input.certified.Atom × input.certified.Atom) :=
  (List.finRange input.molecule.atomCount).flatMap fun left =>
    (List.finRange input.molecule.atomCount).filterMap fun right =>
      if left < right ∧ input.certified.moleculeGraph.bond left right = 2
        then some (left, right) else none

theorem canonicalDoubleBondPairs_eq (input : Input) :
    canonicalDoubleBondPairs input = input.certified.localizedCanonicalDoubleBondPairs := by
  unfold canonicalDoubleBondPairs localizedCanonicalDoubleBondPairs
  rfl

def canonicalDoubleBonds (input : Input) : List input.certified.LocalizedCanonicalDoubleBond :=
  (canonicalDoubleBondPairs input).attach.map fun bond =>
    ⟨bond.1, by rw [← canonicalDoubleBondPairs_eq input]; exact bond.2⟩

def evenAttempts (input : Input) (state : State input) : List (EvenAttempt input state) :=
  input.certified.localizedEvenAxialChains.attach.map fun axis =>
    { candidate := axis
      outcome := input.certified.localizedEvenAxialSpatialAssignmentAtWithStateExec? (carrierFuel input) state axis
      sound := input.certified.localizedEvenAxialSpatialAssignmentAtWithStateExec?_sound (carrierFuel input) state axis }

def oddAttempts (input : Input) (state : State input) : List (OddAttempt input state) :=
  input.certified.localizedOddCumuleneChains.attach.map fun axis =>
    { candidate := axis
      outcome := input.certified.localizedOddCumuleneEZSpatialAssignmentAtWithStateExec? (carrierFuel input) state axis
      sound := input.certified.localizedOddCumuleneEZSpatialAssignmentAtWithStateExec?_sound (carrierFuel input) state axis }

def ringAttempts (input : Input) (state : State input) : List (RingAttempt input state) :=
  (canonicalDoubleBonds input).map fun bond =>
    { candidate := bond
      outcome := input.certified.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec? (carrierFuel input) state bond
      sound := input.certified.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec?_sound (carrierFuel input) state bond }

def ordinaryAttempts (input : Input) (state : State input) : List (OrdinaryAttempt input state) :=
  (canonicalDoubleBonds input).map fun bond =>
    { candidate := bond
      outcome := OrdinaryPlanar.assignment? input.certified (carrierFuel input) state bond }

theorem ordinaryAttempts_candidates (input : Input) (state : State input) :
    (ordinaryAttempts input state).map (fun attempt => attempt.candidate) = canonicalDoubleBonds input := by
  simp [ordinaryAttempts, Function.comp_def]

/-- Candidate coverage is exact; neither successful assignments nor refusals drop a candidate. -/
theorem evenAttempts_candidates (input : Input) (state : State input) :
    (evenAttempts input state).map (fun attempt => attempt.candidate) =
      input.certified.localizedEvenAxialChains.attach := by
  simp [evenAttempts, Function.comp_def]

theorem oddAttempts_candidates (input : Input) (state : State input) :
    (oddAttempts input state).map (fun attempt => attempt.candidate) =
      input.certified.localizedOddCumuleneChains.attach := by
  simp [oddAttempts, Function.comp_def]

theorem ringAttempts_candidates (input : Input) (state : State input) :
    (ringAttempts input state).map (fun attempt => attempt.candidate) = canonicalDoubleBonds input := by
  simp [ringAttempts, Function.comp_def]

def cyclicBoundaries (input : Input) :
    List input.certified.LocalizedFullyCyclicCumuleneAuthorityBoundary :=
  input.certified.localizedCyclicCumuleneComponentsExec.map fun component => { component }

theorem cyclicBoundaries_eq (input : Input) :
    cyclicBoundaries input = input.certified.analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries := by
  simp only [cyclicBoundaries, analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries,
    localizedCyclicCumuleneComponentsExec_eq_original]

theorem cyclicBoundaries_exact (input : Input)
    (boundary : input.certified.LocalizedFullyCyclicCumuleneAuthorityBoundary) :
    boundary ∈ cyclicBoundaries input ↔
      input.certified.DeclarativeLocalizedFullyCyclicCumuleneAuthorityBoundary boundary := by
  rw [cyclicBoundaries_eq]
  exact input.certified.mem_analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_iff boundary

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

/-- Optional carrier-wide readiness chooses the proved smaller Rule3 budget. The default entry
uses the exact cached evaluator directly, avoiding this global prepass. -/
def evaluateLinear (input : Input) (proposals : Nodes input := []) : Result input :=
  ofEvaluation input (Linear.evaluate input proposals)

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

end TetraStereo.OneCenter.LocalizedShortCircuit.Families
