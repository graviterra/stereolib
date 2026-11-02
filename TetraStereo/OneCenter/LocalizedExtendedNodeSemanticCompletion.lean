import TetraStereo.OneCenter.LocalizedOriginalNodeObservableCompletion
import TetraStereo.OneCenter.LocalizedEndpointFrameCompletenessBridge
import TetraStereo.OneCenter.LocalizedEndpointObservableCompletion
import TetraStereo.OneCenter.LocalizedNodeTopologyCompletion
import TetraStereo.OneCenter.LocalizedSpatialSemanticCompletion
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness
import TetraStereo.OneCenter.LocalizedExtendedShortSuccessPreservation
import TetraStereo.OneCenter.LocalizedRecursiveRule3Preservation
import TetraStereo.OneCenter.LocalizedRule3DeclarativePriorityAgreement

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Semantic completion of the extended short-circuit Rule-3 node reader

This module closes the one-step node-completion interface
`LocalizedRule3ExtendedShortCircuitNodeComplete` of `LocalizedMutualObservableCompletion` from
component interfaces that are owned elsewhere:

* the original-node observation convertor of `LocalizedOriginalNodeObservableCompletion`, stated
  per occurrence at the **actual** extended frame callback and its declarative meaning.  Its six
  purely topological obligations are discharged by
  `LocalizedNodeTopologyCompletion`; only the three observation-collection interfaces are retained,
  and those are indexed by the frame fuel *and* the predecessor frame-completeness proof so that a
  spatial producer may consume it;
* the endpoint convertor of `LocalizedEndpointObservableCompletion`, instantiated at the actual
  extended frame callback, which retains only predecessor frame completeness and the weaker
  Rules-4a--5 **comparison-record** agreement (never exact key-payload identity);
* the ordinary and odd spatial convertors of `LocalizedSpatialSemanticCompletion`;
* the route recognition of `LocalizedRule3RouteCompleteness`;
* a new odd-cumulene topology recognition adapter, which is the only missing geometric converse.

The key technical point is that the preservation interfaces of
`LocalizedRule3ShortNodePreservation` / `LocalizedRule3ExtendedNodePreservation` are *not* used at
the original frame callback.  Both shortcut node readers are instead analysed at the actual
predecessor callback `buildLocalizedExtendedShortCircuitRule3FrameExec?`:

1. the extended frame builder is itself root-exact and constitutionally exact (Section 1);
2. therefore the ordinary and odd spatial observations are preserved verbatim (Section 3);
3. therefore both the ordinary shortcut and the extended shortcut preserve every successful
   original-node observation at that callback (Sections 3-4).

The declarative extended node relation deliberately retains `.previous` even when the executable
extends the odd route, so the overlap case is handled explicitly: after the odd detector fires, the
ordinary shortcut executable is rewritten to the old odd-cumulene branch and its observation is
transported through the new odd preservation result.

No desired node output, frame equality, callback equality, or routing precondition is assumed.
-/

/-! ## 1. Coherence of the actual extended frame builder

The extended frame meaning is an independent relation.  Its rebuilt-key component is a pointwise
`List.Forall₂` of extended key derivations.  The constitutional projection of each such derivation
is itself independently derived, so the Rule-1a head and the complete constitutional observation of
every rebuilt key are determined by the cursor alone. -/

/-- Successful extended frames are root-exact: every rebuilt key retains the addressed cursor's
atomic number as the singleton first sphere of Rule 1a.  The invariant is derived from frame
soundness and the constitutional projection of the extended key, not from any assumption about the
compiled observation payload. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_rootsExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view fuel cursors = some frame) : input.LocalizedRule3FrameRootsExact cursors frame := by
  have meaning := input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound
    target view fuel cursors frame computed
  cases fuel with
  | zero => exact False.elim meaning
  | succ fuel =>
      obtain ⟨_, _, _, _, rebuilt⟩ := meaning
      unfold LocalizedRule3FrameRootsExact
      apply List.Forall₂.imp ?_ rebuilt
      intro cursor key derivedKey
      exact input.declarative_constitutional_rule1a_head cursor fuel key.constitutional
        (input.extendedShortCircuitRule3Key_constitutional_derived
          target view fuel frame.excluded cursor key derivedKey)

/-- Successful extended frames are constitutionally exact: every rebuilt key's constitutional
observation agrees with the pure constitutional compilation at the cursor on every successful
budget.  Again this follows from frame soundness and independent constitutional uniqueness. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_constitutionalExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view fuel cursors = some frame) : input.LocalizedRule3FrameConstitutionalExact cursors frame := by
  have meaning := input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound
    target view fuel cursors frame computed
  cases fuel with
  | zero => exact False.elim meaning
  | succ fuel =>
      obtain ⟨_, _, _, _, rebuilt⟩ := meaning
      unfold LocalizedRule3FrameConstitutionalExact
      apply List.Forall₂.imp ?_ rebuilt
      intro cursor full head plainFuel plain plainComputed
      exact input.declarative_constitutional_observable_unique plainFuel fuel _ _ _
        (input.buildLocalizedRerootRuleMajorKeyExec?_sound _ _ _ plainComputed)
        (input.extendedShortCircuitRule3Key_constitutional_derived
          target view fuel frame.excluded cursor full head)

/-! ## 2. The original builder refines into the actual extended callback

The ordinary shortcut and the extended shortcut are both proved by the same mutual success
refinement, so their composition is a pointwise callback refinement. -/

/-- Every successful original frame is a successful extended frame with the identical value. -/
theorem descriptorBearingFrame?_refines_extendedFrameExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) : input.LocalizedRule3CallbackRefines
      (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel) := by
  intro cursors observation computed
  exact input.extendedShortCircuitRule3Frame_preserves_shortCircuit
    target view fuel cursors observation
    (input.shortCircuitRule3Frame_preserves_original
      target view fuel cursors observation computed)

/-! ## 3. Geometry preservation at the actual extended callback

The spatial observation equality theorems of `LocalizedRule3ShortCircuitSpatial` /
`LocalizedRule3ShortCircuitOddSpatial` consume exactly two coherence facts per endpoint: first
sphere root exactness and constitutional exactness.  Section 1 supplies both for the actual extended
frame builder, so the old successful eager observation is reproduced with the identical optional
identity-bearing payload. -/

/-- Successful original ordinary geometry is reproduced by the short-circuit geometry at the actual
extended frame callback with the entire identity-bearing observation unchanged. -/
theorem shortCircuitSpatial_preserves_extendedFrame_success
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (oldResult : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
      target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) =
        some oldResult) :
    ∃ result, input.localizedRule3ShortCircuitSpatialUnitWith?
      target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) =
        some result ∧ input.localizedRule3ShortCircuitSpatialObservation result =
          input.localizedRule3DescriptorBearingObservation oldResult := by
  let callback := input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget
  have derived := input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_sound
    target occurrence view callback (fun cursors frame => callback cursors = some frame)
    (fun _ _ h => h) oldResult computed
  have left := derived.2.1
  have right := derived.2.2.1
  apply input.localizedRule3ShortCircuitSpatialObservation_eq_of_parameterizedWith
    target occurrence view callback oldResult computed
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.leftCompilation
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_rootsExact target view budget _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.rightCompilation
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_rootsExact target view budget _ _
        right.2.2.2.1) right.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.leftCompilation
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_constitutionalExact target view budget _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.rightCompilation
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_constitutionalExact target view budget _ _
        right.2.2.2.1) right.2.2.2.2.1

/-- Successful original odd-cumulene geometry is reproduced by the odd short-circuit geometry at the
actual extended frame callback with the entire identity-bearing observation unchanged. -/
theorem shortCircuitOddSpatial_preserves_extendedFrame_success
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (oldResult : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult fuel)
    (computed : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
      target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) =
        some oldResult) :
    ∃ result, input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) =
        some result ∧ input.localizedRule3ShortCircuitOddSpatialObservation result =
          input.localizedRule3OddCumuleneDescriptorBearingObservation oldResult := by
  let callback := input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget
  have derived := input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_sound
    target occurrence view callback (fun cursors frame => callback cursors = some frame)
    (fun _ _ h => h) oldResult computed
  have left := derived.2.1
  have right := derived.2.2.1
  apply input.localizedRule3ShortCircuitOddSpatialObservation_eq_of_parameterizedWith
    target occurrence view callback oldResult computed
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.leftCompilation
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_rootsExact target view budget _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.rightCompilation
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_rootsExact target view budget _ _
        right.2.2.2.1) right.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.leftCompilation
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_constitutionalExact target view budget _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.rightCompilation
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_constitutionalExact target view budget _ _
        right.2.2.2.1) right.2.2.2.2.1

/-- Successful original nodes retain their exact optional identity-bearing observation when the
ordinary shortcut runs at the actual extended predecessor callback. -/
theorem shortNode_preserves_extendedFrame_callback
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedDescriptorBearingRule3NodeWith? target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) excluded)
      (input.localizedRule3ShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) excluded) := by
  let callback := input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget
  intro observation computed
  change input.localizedRule3ShortCircuitNodeWithExec? target occurrence view callback excluded =
    some observation
  have oldComputed : input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view callback excluded = some observation := by
    rw [localizedDescriptorBearingRule3NodeWithExec?_eq_original]
    exact computed
  cases routed : input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none => simpa [localizedRule3ShortCircuitNodeWithExec?, routed] using oldComputed
  | some certificate =>
      rw [input.originalNode_eq_ordinary_of_routeCertificate
        target occurrence view callback excluded certificate routed] at oldComputed
      cases spatial : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
          target occurrence view callback with
      | none => simp [spatial] at oldComputed
      | some oldResult =>
          have oldSpatial : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
              target occurrence view callback = some oldResult := by
            rwa [localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_eq_original] at spatial
          obtain ⟨newResult, newComputed, sameObservation⟩ :=
            input.shortCircuitSpatial_preserves_extendedFrame_success
              target occurrence view budget oldResult oldSpatial
          have newSpatial : input.localizedRule3ShortCircuitSpatialUnitWithExec?
              target occurrence view callback = some newResult := by
            rw [localizedRule3ShortCircuitSpatialUnitWithExec?_eq_localizedRule3ShortCircuitSpatialUnitWith?]
            exact newComputed
          simp only [spatial] at oldComputed
          by_cases omitted :
              (input.localizedRule3DescriptorBearingObservation oldResult).physicalUnitId ∈ excluded
          · simpa [localizedRule3ShortCircuitNodeWithExec?, routed, newSpatial,
              sameObservation, omitted] using oldComputed
          · simpa [localizedRule3ShortCircuitNodeWithExec?, routed, newSpatial,
              sameObservation, omitted] using oldComputed

/-- Successful ordinary-shortcut nodes retain their exact optional observation when the odd route
gains the extended shortcut, at the actual extended predecessor callback.  The overlap case is
handled: once the odd detector fires, the ordinary-shortcut evaluator is rewritten to the old
odd-cumulene branch and the observation is transported through the odd preservation result. -/
theorem extendedShortNode_preserves_shortCircuit_callback_at
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedRule3ShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) excluded)
      (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) excluded) := by
  let callback := input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget
  intro observation computed
  change input.localizedRule3ExtendedShortCircuitNodeWithExec?
    target occurrence view callback excluded = some observation
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      simpa only [localizedRule3ExtendedShortCircuitNodeWithExec?, routed, callback] using computed
  | some certificate =>
      have oldComputed : input.localizedRule3ShortCircuitNodeWithExec?
          target occurrence view callback excluded = some observation := by
        exact computed
      rw [input.shortNode_eq_odd_of_routeCertificate
        target occurrence view callback excluded certificate routed] at oldComputed
      cases spatial : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
          target occurrence view callback with
      | none => simp [spatial] at oldComputed
      | some oldResult =>
          have oldSpatial : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
              target occurrence view callback = some oldResult := by
            rwa [localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_eq_original] at spatial
          obtain ⟨result, next, same⟩ :=
            input.shortCircuitOddSpatial_preserves_extendedFrame_success
              target occurrence view budget oldResult oldSpatial
          simp only [spatial] at oldComputed
          by_cases omitted :
              (input.localizedRule3OddCumuleneDescriptorBearingObservation oldResult).physicalUnitId ∈ excluded
          · simpa [localizedRule3ExtendedShortCircuitNodeWithExec?, routed, next, same,
              callback, omitted] using oldComputed
          · simpa [localizedRule3ExtendedShortCircuitNodeWithExec?, routed, next, same,
              callback, omitted] using oldComputed

/-- The full composed preservation: original-node success reaches the extended node reader at the
actual extended predecessor callback with the same exact optional observation. -/
theorem extendedShortNode_preserves_extendedFrame_callback
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedDescriptorBearingRule3NodeWith? target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) excluded)
      (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget) excluded) :=
  (input.shortNode_preserves_extendedFrame_callback target occurrence view budget excluded).trans
    (input.extendedShortNode_preserves_shortCircuit_callback_at
      target occurrence view budget excluded)

/-! ## 4. Odd-cumulene topology recognition

`LocalizedRule3RouteCompleteness` recognises physical endpoint frames, terminal topologies, axis
walks, and terminal-to-terminal endpoint frames.  The odd-cumulene frame meaning adds the strict
oddity guard and the two terminal atom reads.  The adapter below proves that the executable
odd-cumulene frame recovery returns every independently derived odd frame, with the same walk
budget argument as the ordinary endpoint converse. -/

/-- The rightward cursor of a declaratively derived odd-cumulene frame is path-valid: the physical
endpoint frame certifies the carrier-parent half of the cut neighbourhood. -/
theorem declarativeOddEndpointFrame_rightCursor_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    input.LocalizedRerootCursorValid frame.initial.rightCursor := by
  rcases derived with ⟨physical, _terminal, _walk, _reverse, _rightPartner, _right,
    _count, _odd⟩
  rcases physical with ⟨_real, _current, _parent, _bond, parentDecl, _leftCurrent,
    _leftPrevious, rightOccurrence, rightPrevious⟩
  have parentInNeighbors : frame.initial.leftCursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) occurrence.1 := by
    rw [localizedRerootNeighborFrames, List.mem_append]
    exact Or.inl parentDecl
  unfold LocalizedRerootCursorValid
  rw [rightPrevious, rightOccurrence]
  exact input.mem_localizedRerootNeighborFrames_symm occurrence
    frame.initial.leftCursor.occurrence.1 parentInNeighbors

/-- The odd-cumulene walk is covered by the production traversal fuel.  This is the same
zipper-diameter bound as for the ordinary endpoint frame, not a chemical assumption. -/
theorem oddEndpointWalk_length_le_traversalFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    frame.rightward.length ≤ input.localizedRule3CumulatedTraversalFuel carrierFuel + 1 := by
  have rightValid := input.declarativeOddEndpointFrame_rightCursor_valid occurrence frame derived
  rcases derived with ⟨_physical, _terminal, walkDecl, _reverse, _rightPartner, _right,
    _count, _odd⟩
  have steps := declarativeWalk_steps_le_budget input frame.initial.rightCursor
    frame.rightward walkDecl rightValid
  have pos := input.declarativeWalk_length_pos walkDecl
  have budgetBound := input.localizedRerootCursorBudget_le_twice frame.initial.rightCursor
  simp only [localizedRule3CumulatedTraversalFuel, localizedOccurrenceRerootEvaluationFuel]
  omega

/-- Every declarative odd-cumulene frame is returned by the executable odd-cumulene recovery,
provided the traversal fuel covers the walk. -/
theorem localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (walkBound : frame.rightward.length ≤ traversalFuel + 1)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    input.localizedRule3OddCumuleneEndpointCursorFrame? traversalFuel occurrence = some frame := by
  rcases derived with ⟨physicalDecl, terminalDecl, walkDecl, reverseIdentity,
    rightPartnerEq, rightEq, countGt, oddCount⟩
  have physicalComputed :=
    input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
      occurrence frame.initial physicalDecl
  have terminalComputed :=
    input.localizedRule3AxisTopology?_eq_terminal_of_declarative terminalDecl
  have walkComputed :=
    input.walkLocalizedRule3CumulatedAxis?_eq_some_of_declarative
      traversalFuel frame.initial.rightCursor frame.rightward walkDecl walkBound
  obtain ⟨rest, restEq⟩ := reverseIdentity
  unfold localizedRule3OddCumuleneEndpointCursorFrame?
  rw [physicalComputed]
  simp only [bind, Option.bind_some]
  rw [terminalComputed]
  simp only [bind, Option.bind_some]
  rw [walkComputed]
  simp only [bind, Option.bind_some]
  rw [restEq]
  simp only
  rw [dif_pos (show 1 < frame.rightward.length ∧ Odd frame.rightward.length from
    ⟨countGt, oddCount⟩)]
  rw [rightPartnerEq]
  simp only [bind, Option.bind_some]
  rw [rightEq]
  simp only [bind, Option.bind_some]

/-- Production-fuel form of odd-cumulene topology recognition. -/
theorem localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_at_traversalFuel_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some frame :=
  input.localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_of_declarative
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence frame
    (input.oddEndpointWalk_length_le_traversalFuel occurrence frame derived) derived

/-! ## 5. One-step node completion

All pieces are now available at the actual extended callback and its declarative meaning.  The
ordinary shortcut is complemented first; the extended shortcut then adds the odd constructor and
handles the retained `.previous` derivations through the overlap lemma of Section 3. -/

/-- Ordinary-shortcut node completeness at the actual extended predecessor callback. -/
theorem localizedRule3ShortCircuitNodeWithExec?_complete_of_declarative_at
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frameFuel : Nat)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (spatialObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeSpatialObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (cyclicObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeCyclicObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (oddCumuleneObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeOddCumuleneObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedRule3ShortCircuitNodeWith target view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
      excluded occurrence observation) :
    input.localizedRule3ShortCircuitNodeWithExec? target occurrence view
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
      excluded = some observation := by
  cases derived with
  | original originalDerived =>
      have oldComputed :=
        input.localizedDescriptorBearingRule3NodeWithExec?_observable_complete
          target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
          excluded
          (input.localizedOriginalNodeObservableCompletionObligations_of_observations
            target occurrence view
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
            (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
            (spatialObservationComplete occurrence)
            (cyclicObservationComplete occurrence)
            (oddCumuleneObservationComplete occurrence))
          originalDerived
      exact input.shortNode_preserves_extendedFrame_callback
        target occurrence view frameFuel excluded observation
        (by
          simpa only [localizedDescriptorBearingRule3NodeWithExec?_eq_original] using oldComputed)
  | ordinary route result spatialDerived =>
      obtain ⟨certificate, routed⟩ := Option.isSome_iff_exists.mp
        (input.localizedRule3OrdinaryRouteCertificate?_isSome_of_route occurrence route)
      have topologyRecognized :=
        input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
          occurrence result.topology spatialDerived.1
      have leftRecognized :=
        input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_observable_extended
          target view frameFuel frameComplete rule45Agreement
          result.topology.left result.topology.right result.topology.leftCursor
          result.leftEndpoint spatialDerived.2.2.2.1
      have rightRecognized :=
        input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_observable_extended
          target view frameFuel frameComplete rule45Agreement
          result.topology.right result.topology.left result.topology.rightCursor
          result.rightEndpoint spatialDerived.2.2.2.2.1
      have spatialComputed :=
        input.localizedRule3ShortCircuitSpatialUnitWithExec?_eq_some_of_declarative
          target occurrence view _ _ result spatialDerived
          topologyRecognized leftRecognized rightRecognized
      simp [localizedRule3ShortCircuitNodeWithExec?, routed, spatialComputed]

/-- Extended-shortcut node completeness at the actual extended predecessor callback: an independent
extended-node derivation produces the same `Option` observation from the executable extended node
reader at the same exclusion list. -/
theorem localizedRule3ExtendedShortCircuitNodeWithExec?_complete_of_declarative_at
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frameFuel : Nat)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (spatialObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeSpatialObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (cyclicObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeCyclicObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (oddCumuleneObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeOddCumuleneObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith target view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
      excluded occurrence observation) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
      excluded = some observation := by
  cases derived with
  | previous shortDerived =>
      exact input.extendedShortNode_preserves_shortCircuit_callback_at
        target occurrence view frameFuel excluded observation
        (input.localizedRule3ShortCircuitNodeWithExec?_complete_of_declarative_at
          frameFuel target view frameComplete rule45Agreement
          spatialObservationComplete cyclicObservationComplete oddCumuleneObservationComplete
          occurrence excluded shortDerived)
  | odd route result spatialDerived =>
      obtain ⟨certificate, routed⟩ := Option.isSome_iff_exists.mp
        (input.localizedRule3OddRouteCertificate?_isSome_of_route occurrence route)
      have topologyRecognized :=
        input.localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_at_traversalFuel_of_declarative
          occurrence result.topology spatialDerived.1
      have leftRecognized :=
        input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_observable_extended
          target view frameFuel frameComplete rule45Agreement
          result.topology.initial.left result.topology.initial.right
          result.topology.initial.leftCursor result.leftEndpoint spatialDerived.2.1
      have rightRecognized :=
        input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_observable_extended
          target view frameFuel frameComplete rule45Agreement
          result.topology.right result.topology.rightPartner
          result.topology.rightCursor result.rightEndpoint spatialDerived.2.2.1
      have spatialComputed :=
        input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_some_of_declarative
          target occurrence view _ _ result spatialDerived
          topologyRecognized leftRecognized rightRecognized
      simp [localizedRule3ExtendedShortCircuitNodeWithExec?, routed, spatialComputed]

/-- Exact `LocalizedRule3ExtendedShortCircuitNodeCompleteAt` from the precise component
interfaces.  The exclusion-list difference between the independent and compiled derivations is
handled by the constructor-level transport of `LocalizedRule3ExclusionExtensionality`; no equality
of the lists themselves is assumed. -/
theorem localizedRule3ExtendedShortCircuitNodeCompleteAt_of_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frameFuel : Nat)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (spatialObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeSpatialObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (cyclicObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeCyclicObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (oddCumuleneObservationComplete : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedRule3NodeOddCumuleneObservationComplete target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)) :
    LocalizedRule3ExtendedShortCircuitNodeCompleteAt input frameFuel target view := by
  intro occurrence excluded compiledExcluded equivalent observation derived
  exact input.localizedRule3ExtendedShortCircuitNodeWithExec?_complete_of_declarative_at
    frameFuel target view frameComplete rule45Agreement
    spatialObservationComplete cyclicObservationComplete oddCumuleneObservationComplete
    occurrence compiledExcluded
    (declarativeLocalizedRule3ExtendedShortCircuitNodeWith_exclusion_transport
      input target view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
      equivalent occurrence derived)

/-- The one-step node-completion interface
`LocalizedRule3ExtendedShortCircuitNodeComplete`, from component interfaces whose frame-fuel
dependence is explicit.  This is a genuine lower-level premise of the mutual induction, not a
restatement of key or frame completeness. -/
theorem localizedRule3ExtendedShortCircuitNodeComplete_of_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (spatialObservationComplete : ∀ frameFuel,
      LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
        input.LocalizedRule3NodeSpatialObservationComplete target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (cyclicObservationComplete : ∀ frameFuel,
      LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
        input.LocalizedRule3NodeCyclicObservationComplete target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (oddCumuleneObservationComplete : ∀ frameFuel,
      LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
        input.LocalizedRule3NodeOddCumuleneObservationComplete target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)) :
    LocalizedRule3ExtendedShortCircuitNodeComplete input target view := by
  intro frameFuel frameComplete
  exact input.localizedRule3ExtendedShortCircuitNodeCompleteAt_of_components
    frameFuel target view frameComplete rule45Agreement
    (spatialObservationComplete frameFuel frameComplete)
    (cyclicObservationComplete frameFuel frameComplete)
    (oddCumuleneObservationComplete frameFuel frameComplete)

/-- Adapter taking the full nine-field original-node obligations *inside* the predecessor
frame-completeness induction, which is the seam a spatial producer can actually supply (it may use
`frameComplete`).  The six topological fields are irrelevant to the shortcut analysis, so only the
three observation-projections are forwarded to `..._of_components`. -/
theorem localizedRule3ExtendedShortCircuitNodeCompleteAt_of_obligations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frameFuel : Nat)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (originalObligations : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      input.LocalizedOriginalNodeObservableCompletionObligations target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)) :
    LocalizedRule3ExtendedShortCircuitNodeCompleteAt input frameFuel target view :=
  input.localizedRule3ExtendedShortCircuitNodeCompleteAt_of_components
    frameFuel target view frameComplete rule45Agreement
    (fun occurrence => (originalObligations occurrence).spatialObservationComplete)
    (fun occurrence => (originalObligations occurrence).cyclicObservationComplete)
    (fun occurrence => (originalObligations occurrence).oddCumuleneObservationComplete)

/-- One-step `NodeComplete` adapter whose obligations are indexed by the frame fuel and the
predecessor frame-completeness proof. -/
theorem localizedRule3ExtendedShortCircuitNodeComplete_of_obligations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (originalObligations : ∀ frameFuel,
      LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
        input.LocalizedOriginalNodeObservableCompletionObligations target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)) :
    LocalizedRule3ExtendedShortCircuitNodeComplete input target view := by
  intro frameFuel frameComplete
  exact input.localizedRule3ExtendedShortCircuitNodeCompleteAt_of_obligations
    frameFuel target view frameComplete rule45Agreement
    (originalObligations frameFuel frameComplete)

/-- Composed capstone: with the precise component interfaces, the existing mutual induction of
`LocalizedMutualObservableCompletion` yields key completeness and frame completeness for the
extended short-circuit compiler at every fuel.  The `NodeComplete` premise of the mutual induction
is discharged here, not assumed. -/
theorem localizedExtendedShortCircuitRule3_mutual_complete_of_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (spatialObservationComplete : ∀ frameFuel,
      LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
        input.LocalizedRule3NodeSpatialObservationComplete target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (cyclicObservationComplete : ∀ frameFuel,
      LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
        input.LocalizedRule3NodeCyclicObservationComplete target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel))
    (oddCumuleneObservationComplete : ∀ frameFuel,
      LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
        input.LocalizedRule3NodeOddCumuleneObservationComplete target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)) :
    ∀ fuel,
      LocalizedRerootExtendedShortCircuitRule3KeyCompleteAt input target view fuel ∧
        LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view fuel :=
  input.localizedExtendedShortCircuitRule3_mutual_complete target view
    (input.localizedRule3ExtendedShortCircuitNodeComplete_of_components
      target view rule45Agreement
      spatialObservationComplete cyclicObservationComplete oddCumuleneObservationComplete)

/-- Obligations-indexed capstone: identical conclusion, but the original-node component is the
full nine-field obligation relation supplied *inside* the frame-completeness induction.  This is
the seam intended for the separate assembly module that joins the original-spatial producer with
this shortcut analysis; no circular import is introduced here. -/
theorem localizedExtendedShortCircuitRule3_mutual_complete_of_obligations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (originalObligations : ∀ frameFuel,
      LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
        input.LocalizedOriginalNodeObservableCompletionObligations target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
          (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)) :
    ∀ fuel,
      LocalizedRerootExtendedShortCircuitRule3KeyCompleteAt input target view fuel ∧
        LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view fuel :=
  input.localizedExtendedShortCircuitRule3_mutual_complete target view
    (input.localizedRule3ExtendedShortCircuitNodeComplete_of_obligations
      target view rule45Agreement originalObligations)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
