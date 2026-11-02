import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorRuntime
import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorAdoptionFixture

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
























namespace TetraStereo.UniversalProof.FramedDescriptorCarrierRegression

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.FrameRuntime
open TetraStereo.UniversalProof.FramedDescriptorAdoptionFixtureProofs.FramedDescriptorAdoptionFixture

/-! ## Synthetic test transform (explicit constructor: projections reduce by `rfl`) -/

/-- Synthetic per-fact transform: preserve key/history/provenance, atom, descriptor and priority
positions exactly; force `uppercase := false`. This is an algorithm-regression input, not chemistry. -/
def lowercaseFact (fact : OccurrenceAuxFact) : OccurrenceAuxFact where
  key := fact.key
  atom := fact.atom
  descriptor := fact.descriptor
  uppercase := false
  priorityPositions := fact.priorityPositions

/-- Synthetic state transform: lowercase every auxiliary fact, preserving order. -/
def lowercaseState (state : OccurrenceAuxState) : OccurrenceAuxState :=
  state.map lowercaseFact

/-- Explicitly tagged synthetic regression state. `syntheticTag` documents that this state is a
synthetic algorithm-regression input, not produced by the actual auxiliary builder. -/
structure SyntheticRegressionState where
  /-- The actual fixture auxiliary state after the synthetic lowercase transform. -/
  state : OccurrenceAuxState
  /-- Always `true` for the synthetic regression input. -/
  syntheticTag : Bool := true

/-- Build the tagged synthetic regression state from the actual fast auxiliary builder. -/
def syntheticRegressionStateVal (state : OccurrenceAuxState) : SyntheticRegressionState where
  state := lowercaseState state
  syntheticTag := true

/-! ## Closed structural laws of the synthetic transform (actual theorems) -/

theorem lowercaseState_length (state : OccurrenceAuxState) :
    (lowercaseState state).length = state.length := by
  simp [lowercaseState]

theorem lowercaseState_keys (state : OccurrenceAuxState) :
    (lowercaseState state).map (fun f => f.key) = state.map (fun f => f.key) := by
  unfold lowercaseState
  rw [List.map_map]
  rfl

theorem lowercaseState_atoms (state : OccurrenceAuxState) :
    (lowercaseState state).map (fun f => f.atom) = state.map (fun f => f.atom) := by
  unfold lowercaseState
  rw [List.map_map]
  rfl

theorem lowercaseState_descriptors (state : OccurrenceAuxState) :
    (lowercaseState state).map (fun f => f.descriptor) = state.map (fun f => f.descriptor) := by
  unfold lowercaseState
  rw [List.map_map]
  rfl

theorem lowercaseState_priorities (state : OccurrenceAuxState) :
    (lowercaseState state).map (fun f => f.priorityPositions) =
      state.map (fun f => f.priorityPositions) := by
  unfold lowercaseState
  rw [List.map_map]
  rfl

theorem lowercaseState_uppercase_all_false (state : OccurrenceAuxState) :
    (lowercaseState state).map (fun f => f.uppercase) = state.map (fun _ => false) := by
  unfold lowercaseState
  rw [List.map_map]
  rfl

theorem lowercaseState_mem_false (state : OccurrenceAuxState) (fact : OccurrenceAuxFact)
    (hf : fact ∈ lowercaseState state) : fact.uppercase = false := by
  simp only [lowercaseState, List.mem_map] at hf
  obtain ⟨g, _, rfl⟩ := hf
  rfl

theorem lowercaseState_idempotent (state : OccurrenceAuxState) :
    lowercaseState (lowercaseState state) = lowercaseState state := by
  unfold lowercaseState
  rw [List.map_map]
  rfl

/-- The synthetic state always satisfies the Rule-4c lowercase guard exactly when the original
state is nonempty. -/
theorem lowercaseState_any_lowercase (state : OccurrenceAuxState) :
    (lowercaseState state).any (fun fact => !fact.uppercase) = !state.isEmpty := by
  cases state with
  | nil => rfl
  | cons fact rest => rfl

/-- Nonempty synthetic state satisfies the lowercase guard. Earlier stages may still decide;
this theorem alone does not prove that the Rule-4c branch executes. -/
theorem synthetic_lowercase_enters_rule4c (state : OccurrenceAuxState) (h : state ≠ []) :
    (lowercaseState state).any (fun fact => !fact.uppercase) = true := by
  rw [lowercaseState_any_lowercase]
  cases state with
  | nil => exact absurd rfl h
  | cons fact rest => rfl

theorem syntheticRegressionStateVal_tag (state : OccurrenceAuxState) :
    (syntheticRegressionStateVal state).syntheticTag = true := rfl

/-! ## Computed observation helpers (actual fixture inputs; no invented molecule/state literal) -/

/-- Build the tagged synthetic state from the actual fast auxiliary builder at center 1. -/
def syntheticFastState? (mol : RawMolecule) : Option SyntheticRegressionState :=
  (buildOccurrenceAuxState? mol (analysisFuel mol) 1).map syntheticRegressionStateVal

/-- Build the tagged synthetic state from the actual fully-authoritative auxiliary builder. -/
def syntheticAuthoritativeState? (mol : RawMolecule) : Option SyntheticRegressionState :=
  (buildOccurrenceAuxStateFullyAuthoritative? mol (analysisFuel mol) 1).map
    syntheticRegressionStateVal

/-- Summary of one complete comparison: ordering code (`0=lt 1=eq 2=gt 3=none`), `pseudo`, and the
Rule-4c carrier projected to `(cursor atom, descriptor)` or `none`. This is a coarse diagnostic
projection; exact full-record checks are defined separately below. -/
def comparisonSummary (comparison : Option OccurrenceComparison) : Nat × Bool × Option (Nat × RS) :=
  match comparison with
  | none => (3, false, none)
  | some c =>
      (orderingCode c.ordering, c.pseudo,
        c.rule4cCarrier?.map (fun pair => (pair.1.node.atom, pair.2.descriptor)))

/-- The actual left/right arm cursors (atoms 2 and 7) under the actual profile at center 1. -/
def actualArmCursors? (mol : RawMolecule) :
    Option (Profile × CanonicalRerootCursor × CanonicalRerootCursor) := do
  let profile ← FrameRuntime.profile? mol (canonicalCenterRoot 1)
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let right ← roots.find? (fun cursor => cursor.node.atom == 7)
  pure (profile, left, right)

/-- Coarse `decisionComplete?` diagnostic in both modes; this projection alone does not
verify full cursor history, previous node, fact key or priority positions. -/
def syntheticDecisionObservation (mol : RawMolecule) (state : OccurrenceAuxState) :
    Option ((Nat × Bool × Option (Nat × RS)) × (Nat × Bool × Option (Nat × RS))) := do
  let (profile, left, right) ← actualArmCursors? mol
  let fuel := analysisFuel mol
  pure (comparisonSummary (decisionComplete? mol profile false state fuel left right),
        comparisonSummary (decisionComplete? mol profile true state fuel left right))

/-- Swap-orientation observation (authoritative mode): the carrier must remain the actual senior
occurrence, not the wrong side and not a pseudo flip. -/
def syntheticSwapObservation (mol : RawMolecule) (state : OccurrenceAuxState) :
    Option (Nat × Bool × Option (Nat × RS)) := do
  let (profile, left, right) ← actualArmCursors? mol
  let fuel := analysisFuel mol
  pure (comparisonSummary (decisionComplete? mol profile true state fuel right left))

/-- Explicit uppercase substate containing only the actual arm-2 fact (its `uppercase` flag is the
actual builder's value, not forced). Used to probe the HELPER Rule-4b stage. -/
def arm2UppercaseSubstate? (mol : RawMolecule) : Option OccurrenceAuxState := do
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let state ← buildOccurrenceAuxState? mol (analysisFuel mol) 1
  let fact ← state.factAt? left.node
  pure [fact]

/-- Empty auxiliary state (both reference lists empty; ties). -/
def emptyAuxState : OccurrenceAuxState := []

/-- Helper-stage Rule-4b probe on a supplied state: actual left/right reference lists, the fast and
authoritative `compareRule4b?` codes, and the outer Rule-4a code (which may decide earlier — these
are NOT claimed to be the actual final Rule-4b-stage decisions of `decisionComplete?`). -/
def rule4bHelperStageProbe (mol : RawMolecule) (state : OccurrenceAuxState) :
    Option (List RS × List RS × Nat × Nat × Nat) := do
  let (profile, left, right) ← actualArmCursors? mol
  let fuel := analysisFuel mol
  let leftReferences ← rule4bReferences? mol profile state fuel [.actual left]
  let rightReferences ← rule4bReferences? mol profile state fuel [.actual right]
  pure (leftReferences, rightReferences,
    optionOrderingCode (compareRule4b? mol profile false state fuel (.actual left) (.actual right)),
    optionOrderingCode (compareRule4b? mol profile true state fuel (.actual left) (.actual right)),
    optionOrderingCode (compareDescriptorAtTiedRoot? mol profile true state fuel .rule4a
      (.actual left) (.actual right)))

/-! Full-record regression: expectations independently use the original arm-2 cursor and its
actual fact in the synthetically transformed state. No coarse projection is used for equality. -/

def syntheticCarrierDecision? (authoritative swapped : Bool) : Option OccurrenceComparison := do
  let mol ← nativeFixtureMol?
  let (profile, left, right) ← actualArmCursors? mol
  let synthetic ← if authoritative then syntheticAuthoritativeState? mol else syntheticFastState? mol
  if swapped then
    decisionComplete? mol profile authoritative synthetic.state (analysisFuel mol) right left
  else
    decisionComplete? mol profile authoritative synthetic.state (analysisFuel mol) left right

/-- Both orientations must retain the original senior arm-2 cursor and the full transformed fact.
The expected fact is obtained with actual factAt?, not copied from the observed comparison. -/
def expectedSyntheticCarrier? (authoritative swapped : Bool) : Option OccurrenceComparison := do
  let mol ← nativeFixtureMol?
  let (_, left, _) ← actualArmCursors? mol
  let synthetic ← if authoritative then syntheticAuthoritativeState? mol else syntheticFastState? mol
  let fact ← synthetic.state.factAt? left.node
  pure { ordering := if swapped then .lt else .gt
         pseudo := false
         rule4cCarrier? := some (left, fact) }

-- Presence claims prevent equalities from succeeding merely because both computations fail.
theorem expected_fast_carrier_present :
    (expectedSyntheticCarrier? false false).isSome = true := by decide +kernel

theorem expected_authoritative_carrier_present :
    (expectedSyntheticCarrier? true false).isSome = true := by decide +kernel

theorem synthetic_fast_exact_carrier :
    syntheticCarrierDecision? false false = expectedSyntheticCarrier? false false := by decide +kernel

theorem synthetic_fast_swapped_exact_carrier :
    syntheticCarrierDecision? false true = expectedSyntheticCarrier? false true := by decide +kernel

theorem synthetic_authoritative_exact_carrier :
    syntheticCarrierDecision? true false = expectedSyntheticCarrier? true false := by decide +kernel

theorem synthetic_authoritative_swapped_exact_carrier :
    syntheticCarrierDecision? true true = expectedSyntheticCarrier? true true := by decide +kernel

/-- Helper-stage probes only. Selecting the actual arm-2 uppercase fact is a synthetic substate;
outer Rule4a may decide earlier, so these are not final decisionComplete? Rule4b path claims. -/
def rule4bShapeObservation? (onlyArm2 swapped : Bool) :
    Option (List RS × List RS × Option Ordering × Option Ordering) := do
  let mol ← nativeFixtureMol?
  let (profile, arm2, arm7) ← actualArmCursors? mol
  let state ← if onlyArm2 then arm2UppercaseSubstate? mol else some []
  let left := if swapped then arm7 else arm2
  let right := if swapped then arm2 else arm7
  let fuel := analysisFuel mol
  let leftReferences ← rule4bReferences? mol profile state fuel [.actual left]
  let rightReferences ← rule4bReferences? mol profile state fuel [.actual right]
  pure (leftReferences, rightReferences,
    compareRule4b? mol profile false state fuel (.actual left) (.actual right),
    compareRule4b? mol profile true state fuel (.actual left) (.actual right))

theorem mixed_reference_policy :
    rule4bShapeObservation? true false = some ([.R], [], none, some .gt) := by decide +kernel

theorem mixed_reference_swapped_policy :
    rule4bShapeObservation? true true = some ([], [.R], none, some .lt) := by decide +kernel

theorem empty_reference_policy :
    rule4bShapeObservation? false false = some ([], [], some .eq, some .eq) := by decide +kernel

theorem empty_reference_swapped_policy :
    rule4bShapeObservation? false true = some ([], [], some .eq, some .eq) := by decide +kernel

#eval syntheticCarrierDecision? false false
#eval syntheticCarrierDecision? false true
#eval syntheticCarrierDecision? true false
#eval syntheticCarrierDecision? true true
#eval rule4bShapeObservation? true false
#eval rule4bShapeObservation? true true
#eval rule4bShapeObservation? false false
#eval rule4bShapeObservation? false true

/-! ## Coarse computed observations (unexecuted here; diagnostic displays only).

Each line names the actual fixture and the synthetic transform explicitly. -/

#eval nativeFixtureMol?.map (fun mol => mol.atomCount)
#eval nativeFixtureMol?.map (fun mol => (syntheticFastState? mol).map (fun s => (s.syntheticTag,
  s.state.length)))
#eval nativeFixtureMol?.map (fun mol =>
  (syntheticFastState? mol).map (fun s => syntheticDecisionObservation mol s.state))
#eval nativeFixtureMol?.map (fun mol =>
  (syntheticAuthoritativeState? mol).map (fun s => syntheticDecisionObservation mol s.state))
#eval nativeFixtureMol?.map (fun mol =>
  (syntheticFastState? mol).map (fun s => syntheticSwapObservation mol s.state))
#eval nativeFixtureMol?.map (fun mol =>
  (arm2UppercaseSubstate? mol).map (fun state => rule4bHelperStageProbe mol state))
#eval nativeFixtureMol?.map (fun mol => rule4bHelperStageProbe mol emptyAuxState)

#check lowercaseState
#check synthetic_lowercase_enters_rule4c
#check syntheticDecisionObservation
#check rule4bHelperStageProbe

end TetraStereo.UniversalProof.FramedDescriptorCarrierRegression
