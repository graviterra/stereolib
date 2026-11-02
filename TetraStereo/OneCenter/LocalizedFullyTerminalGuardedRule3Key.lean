import TetraStereo.OneCenter.LocalizedTerminalGuardedRecursiveRule3Key
import TetraStereo.OneCenter.LocalizedTerminalGuardedObservationAdapter
import TetraStereo.OneCenter.LocalizedEndpointObservableTransport
import TetraStereo.OneCenter.LocalizedRule3ExtendedNodePreservation
import TetraStereo.OneCenter.LocalizedFullyTerminalGuardedDemandStability
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TerminalGuardedRule3Node
open TerminalGuardedObservationAdapter

/-!
# The actual fully guarded mutual Rule-3 key/frame successor

The reviewed hybrid baseline `LocalizedTerminalGuardedRecursiveRule3Key` (F104740b) deliberately
hands the *old* predecessor frame callback to the guarded node evaluator, adapts accepted guard
identities to synthetic spatial observations, and never consumes the frame induction hypothesis.
This module replaces that successor by the actual one, without modifying the baseline.

The two builders below are twins of the original extended key/frame compiler of
`LocalizedRerootExtendedShortCircuitRule3Key`:

* `buildLocalizedFullyTerminalGuardedRule3KeyExec?` recurses on the same cursor children with the
  *new* key builder, performs the same structural descending sort, and assembles the same parent;
* `buildLocalizedFullyTerminalGuardedRule3FrameExec?` performs the same mandatory raw-key pass, the
  same actual coupled-topology resolution, the same excluded physical-unit computation on the
  actual raw keys, and the same rebuilt pass.  Both passes use the *new* key builder.

The predecessor callback handed to the adapter is exactly
`input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view predecessorFuel`, and the node
is the actual adapter `localizedRule3TerminalGuardedSpatialNodeWithExec?`.  The adapter converts an
accepted terminal guard into an actual spatial observation built from the canonical explicit
substituents of the two topology endpoints; when the opposite endpoint has no explicit substituent
it refuses with an outer `none`.  There is no fabricated endpoint and no legacy callback fallback.

## Refinement status

The final mutual old-to-new refinement theorems (`_refines_old`) are **not** proved in this module.
They live in the successor module `LocalizedFullyGuardedSuccessPreservation`, which consumes both the
key predecessor induction hypothesis and this module's public callback transport.

What this module does contribute is the layer that the sibling refinement cannot supply on its own:
the actual executable node evaluators are invariant under the pointwise observable callback relation
`LocalizedRule3FrameCallbackObservableRel`.  That invariance is exposed as the public theorem
`extendedShortNodeWith_observable_eq_of_callback_observableRel`, together with the private transport
of the three callback-reading spatial units it is built from.  The guard branch of the adapter is
callback-independent; the fallback branch is the extended short-circuit node, which is exactly what
the public theorem transports.

The expected shape of the successor proof is a mutual induction on fuel: the *key* hypothesis
refines the child keys, and the *frame* hypothesis replaces the old callback by the new one.  The
replacement proceeds in two steps — first an intermediate callback that agrees with the old callback
on old successes (using one-way exact success refinement), then the pointwise observable relation to
the new callback, transported here.  None of those refinement hypotheses are assumed, declared, or
discharged in this module.

## Matching guarded demand graph

The final section instantiates the accepted generic stability engine
`LocalizedFullyTerminalGuardedDemandStability` at these exact two functions.  The successor
equations are definitional (`rfl`), so no semantic hypothesis is added; the resulting stability
theorems concern the actual matching pruned demand graph with no old-rank premise.
-/

/-! ## The true mutually recursive core -/

mutual

  /-- The actual fully guarded recursive Rule-3 spatial key.  The zero branch is the original
  structural nonunit branch.  The successor branch runs the *actual* adapter
  `localizedRule3TerminalGuardedSpatialNodeWithExec?` on the fully guarded predecessor frame
  callback, then performs the original child recursion, structural sort and parent assembly with
  the fully guarded child builder. -/
  def buildLocalizedFullyTerminalGuardedRule3KeyExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        input.LocalizedRerootCursor carrierFuel →
          Option input.LocalizedRerootRecursiveRule3SpatialKey
    | 0, _excluded, cursor => do
        let children ← input.executableLocalizedRerootChildren? cursor
        let observation ← input.localizedRule3StructuralNodeExec
          cursor.occurrence
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else none
    | fuel + 1, excluded, cursor => do
        let children ← input.executableLocalizedRerootChildren? cursor
        let observation ← localizedRule3TerminalGuardedSpatialNodeWithExec?
          input target cursor.occurrence view
          (input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel)
          excluded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM
            (input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
              target view fuel excluded)
          let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
          some
            { constitutional := OfficialRuleMajorKey.assemble
                (input.moleculeGraph.officialRuleMajorRootKey
                  cursor.occurrence.1.node false)
                (sorted.map fun child => child.constitutional)
              observations := input.localizedRule3SpatialRootObservations observation ++
                input.mergeLocalizedRerootRule3ObservationChildren sorted
              rule3 := input.localizedRule3SpatialRootPriorities observation ++
                input.mergeLocalizedRerootRule3PriorityChildren sorted }

  /-- The actual fully guarded two-pass physical-unit frame.  The raw pass, the actual
  coupled-topology resolution, the excluded-unit computation and the rebuilt pass are all retained;
  both passes use the fully guarded key builder. -/
  def buildLocalizedFullyTerminalGuardedRule3FrameExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame
    | 0, _cursors => none
    | fuel + 1, cursors => do
        let rawKeys ← cursors.mapM
          (input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
            target view fuel [])
        let topology ← input.localizedRule3CoupledTopologyResolutionExec? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM
          (input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
            target view fuel excluded)
        some { rawKeys, coupled, excluded, keys }

end

/-! ## Smoke results at fuel zero -/

/-- At fuel zero the fully guarded key builder is literally the original structural key
builder. -/
theorem buildLocalizedFullyTerminalGuardedRule3KeyExec?_zero_eq_old
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
        target view 0 guardedExcluded cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view 0 excluded cursor := by
  simp [buildLocalizedFullyTerminalGuardedRule3KeyExec?,
    buildLocalizedRerootExtendedShortCircuitRule3KeyExec?]

/-- Every successful original zero-fuel key is reproduced by the fully guarded builder with a
topology-equivalent key. -/
theorem buildLocalizedFullyTerminalGuardedRule3KeyExec?_zero_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed :
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view 0 excluded cursor = some key) :
    ∃ guardedKey : input.LocalizedRerootRecursiveRule3SpatialKey,
      input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
          target view 0 guardedExcluded cursor = some guardedKey ∧
        LocalizedRule3SpatialKeyTopologyEquivalent input key guardedKey := by
  refine ⟨key, ?_, LocalizedRule3SpatialKeyTopologyEquivalent.refl input key⟩
  rw [input.buildLocalizedFullyTerminalGuardedRule3KeyExec?_zero_eq_old]
  exact computed

/-- At fuel zero the fully guarded frame builder refuses exactly as the original frame builder
does. -/
theorem buildLocalizedFullyTerminalGuardedRule3FrameExec?_zero
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
        target view 0 cursors = none := by
  simp [buildLocalizedFullyTerminalGuardedRule3FrameExec?]

/-! ## Congruence of the descriptor-bearing spatial unit at equal priorities -/

/-- The original descriptor-bearing spatial unit reads only its two extracted endpoint
priorities.  Endpoint key frames with equal priorities therefore give the identical unit,
including its geometry. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_eq_of_priorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame leftFrame' rightFrame' : input.LocalizedRule3EndpointKeyFrame)
    (leftPriority :
      input.localizedRule3EndpointPriority leftFrame =
        input.localizedRule3EndpointPriority leftFrame')
    (rightPriority :
      input.localizedRule3EndpointPriority rightFrame =
        input.localizedRule3EndpointPriority rightFrame') :
    input.localizedRule3DescriptorBearingSpatialUnit?
        left right leftFrame rightFrame =
      input.localizedRule3DescriptorBearingSpatialUnit?
        left right leftFrame' rightFrame' := by
  unfold localizedRule3DescriptorBearingSpatialUnit?
  simp only [leftPriority, rightPriority]

/-- The extended (bond-test-free) descriptor-bearing spatial unit reads only its two extracted
endpoint priorities. -/
theorem localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_of_priorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame leftFrame' rightFrame' : input.LocalizedRule3EndpointKeyFrame)
    (leftPriority :
      input.localizedRule3EndpointPriority leftFrame =
        input.localizedRule3EndpointPriority leftFrame')
    (rightPriority :
      input.localizedRule3EndpointPriority rightFrame =
        input.localizedRule3EndpointPriority rightFrame') :
    input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
        left right leftFrame rightFrame =
      input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
        left right leftFrame' rightFrame' := by
  unfold localizedRule3ExtendedDescriptorBearingSpatialUnit?
  simp only [leftPriority, rightPriority]

/-! ## Observable transport of the three callback-reading spatial units -/

/-- The occurrence descriptor-bearing spatial unit has the same observation projection under a
pointwise observably related callback.  Only the embedded frames may differ. -/
private theorem localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : LocalizedRule3FrameCallbackObservableRel input before after) :
    Option.map (fun result => input.localizedRule3DescriptorBearingObservation result)
        (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
          target occurrence view before) =
      Option.map (fun result => input.localizedRule3DescriptorBearingObservation result)
        (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
          target occurrence view after) := by
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
  cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => simp [topologyComputed]
  | some topology =>
      have relatedLeft := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
        target view before after rel topology.left topology.right topology.leftCursor
      have relatedRight := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
        target view before after rel topology.right topology.left topology.rightCursor
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view before topology.left topology.right topology.leftCursor with
      | none =>
          rw [leftComputed] at relatedLeft
          cases leftAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view after topology.left topology.right topology.leftCursor with
          | none => simp [topologyComputed, leftComputed, leftAfter]
          | some frameAfter => simp [leftAfter] at relatedLeft
      | some leftFrame =>
          rw [leftComputed] at relatedLeft
          cases leftAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view after topology.left topology.right topology.leftCursor with
          | none => simp [leftAfter] at relatedLeft
          | some leftFrameAfter =>
              have leftRelated : input.LocalizedRule3EndpointObservableRel
                  leftFrame.endpointFrame leftFrameAfter.endpointFrame := by
                simpa [leftAfter] using relatedLeft
              cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                  target view before topology.right topology.left topology.rightCursor with
              | none =>
                  rw [rightComputed] at relatedRight
                  cases rightAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                      target view after topology.right topology.left topology.rightCursor with
                  | none => simp [topologyComputed, leftComputed, leftAfter, rightComputed,
                      rightAfter]
                  | some frameAfter => simp [rightAfter] at relatedRight
              | some rightFrame =>
                  rw [rightComputed] at relatedRight
                  cases rightAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                      target view after topology.right topology.left topology.rightCursor with
                  | none => simp [rightAfter] at relatedRight
                  | some rightFrameAfter =>
                      have rightRelated : input.LocalizedRule3EndpointObservableRel
                          rightFrame.endpointFrame rightFrameAfter.endpointFrame := by
                        simpa [rightAfter] using relatedRight
                      have unitEq :
                          input.localizedRule3DescriptorBearingSpatialUnit?
                              topology.left topology.right
                              leftFrame.endpointFrame rightFrame.endpointFrame =
                            input.localizedRule3DescriptorBearingSpatialUnit?
                              topology.left topology.right
                              leftFrameAfter.endpointFrame rightFrameAfter.endpointFrame :=
                        input.localizedRule3DescriptorBearingSpatialUnit?_eq_of_priorities
                          topology.left topology.right _ _ _ _
                          (input.localizedRule3EndpointPriority_eq_of_observableRel
                            _ _ leftRelated)
                          (input.localizedRule3EndpointPriority_eq_of_observableRel
                            _ _ rightRelated)
                      cases unitComputed : input.localizedRule3DescriptorBearingSpatialUnit?
                          topology.left topology.right leftFrameAfter.endpointFrame
                          rightFrameAfter.endpointFrame with
                      | none =>
                          simp [topologyComputed, leftComputed, leftAfter, rightComputed,
                            rightAfter, unitEq, unitComputed]
                      | some unitValue =>
                          simp [topologyComputed, leftComputed, leftAfter, rightComputed,
                            rightAfter, unitEq, unitComputed,
                            localizedRule3DescriptorBearingObservation, leftRelated.1,
                            rightRelated.1]

/-- The odd-cumulene descriptor-bearing spatial unit has the same observation projection under a
pointwise observably related callback. -/
private theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_observation_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : LocalizedRule3FrameCallbackObservableRel input before after) :
    Option.map (fun result =>
        input.localizedRule3OddCumuleneDescriptorBearingObservation result)
        (input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
          target occurrence view before) =
      Option.map (fun result =>
        input.localizedRule3OddCumuleneDescriptorBearingObservation result)
        (input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
          target occurrence view after) := by
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
  cases topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [topologyComputed]
  | some topology =>
      have relatedLeft := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
        target view before after rel topology.initial.left topology.initial.right
        topology.initial.leftCursor
      have relatedRight := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
        target view before after rel topology.right topology.rightPartner
        topology.rightCursor
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view before topology.initial.left topology.initial.right
          topology.initial.leftCursor with
      | none =>
          rw [leftComputed] at relatedLeft
          cases leftAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view after topology.initial.left topology.initial.right
              topology.initial.leftCursor with
          | none => simp [topologyComputed, leftComputed, leftAfter]
          | some frameAfter => simp [leftAfter] at relatedLeft
      | some leftFrame =>
          rw [leftComputed] at relatedLeft
          cases leftAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view after topology.initial.left topology.initial.right
              topology.initial.leftCursor with
          | none => simp [leftAfter] at relatedLeft
          | some leftFrameAfter =>
              have leftRelated : input.LocalizedRule3EndpointObservableRel
                  leftFrame.endpointFrame leftFrameAfter.endpointFrame := by
                simpa [leftAfter] using relatedLeft
              cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                  target view before topology.right topology.rightPartner
                  topology.rightCursor with
              | none =>
                  rw [rightComputed] at relatedRight
                  cases rightAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                      target view after topology.right topology.rightPartner
                      topology.rightCursor with
                  | none => simp [topologyComputed, leftComputed, leftAfter, rightComputed,
                      rightAfter]
                  | some frameAfter => simp [rightAfter] at relatedRight
              | some rightFrame =>
                  rw [rightComputed] at relatedRight
                  cases rightAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                      target view after topology.right topology.rightPartner
                      topology.rightCursor with
                  | none => simp [rightAfter] at relatedRight
                  | some rightFrameAfter =>
                      have rightRelated : input.LocalizedRule3EndpointObservableRel
                          rightFrame.endpointFrame rightFrameAfter.endpointFrame := by
                        simpa [rightAfter] using relatedRight
                      have unitEq :
                          input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
                              topology.initial.left topology.right
                              leftFrame.endpointFrame rightFrame.endpointFrame =
                            input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
                              topology.initial.left topology.right
                              leftFrameAfter.endpointFrame rightFrameAfter.endpointFrame :=
                        input.localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_of_priorities
                          topology.initial.left topology.right _ _ _ _
                          (input.localizedRule3EndpointPriority_eq_of_observableRel
                            _ _ leftRelated)
                          (input.localizedRule3EndpointPriority_eq_of_observableRel
                            _ _ rightRelated)
                      cases unitComputed : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
                          topology.initial.left topology.right leftFrameAfter.endpointFrame
                          rightFrameAfter.endpointFrame with
                      | none =>
                          simp [topologyComputed, leftComputed, leftAfter, rightComputed,
                            rightAfter, unitEq, unitComputed]
                      | some unitValue =>
                          simp [topologyComputed, leftComputed, leftAfter, rightComputed,
                            rightAfter, unitEq, unitComputed,
                            localizedRule3OddCumuleneDescriptorBearingObservation,
                            leftRelated.1, rightRelated.1]

/-- The required monocyclic E/Z spatial unit has the same observation projection under a
pointwise observably related callback.  The cyclic authority route itself is
callback-independent. -/
private theorem localizedRule3RequiredMonocyclicEZWith?_observation_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : LocalizedRule3FrameCallbackObservableRel input before after) :
    Option.map (fun result => input.localizedRule3RequiredMonocyclicEZObservation result)
        (input.localizedRule3RequiredMonocyclicEZWith? target occurrence view before) =
      Option.map (fun result => input.localizedRule3RequiredMonocyclicEZObservation result)
        (input.localizedRule3RequiredMonocyclicEZWith? target occurrence view after) := by
  unfold localizedRule3RequiredMonocyclicEZWith?
  cases routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence with
  | none => simp [routeComputed]
  | some routeValue =>
      cases routeValue with
      | fullyCyclicCumulene => simp [routeComputed]
      | ordinaryMonocyclicPolicyGap => simp [routeComputed]
      | ordinaryNonmonocyclic => simp [routeComputed]
      | ordinaryMonocyclicPolicy initial closure policyResult =>
          cases policyComputed : policyResult.policy with
          | permanentlyOmit => simp [routeComputed, policyComputed]
          | requireEZ =>
              have relatedLeft :=
                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
                  target view before after rel initial.left initial.right initial.leftCursor
              have relatedRight :=
                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
                  target view before after rel initial.right initial.left initial.rightCursor
              cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                  target view before initial.left initial.right initial.leftCursor with
              | none =>
                  rw [leftComputed] at relatedLeft
                  cases leftAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                      target view after initial.left initial.right initial.leftCursor with
                  | none => simp [routeComputed, policyComputed, leftComputed, leftAfter]
                  | some frameAfter => simp [leftAfter] at relatedLeft
              | some leftFrame =>
                  rw [leftComputed] at relatedLeft
                  cases leftAfter : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                      target view after initial.left initial.right initial.leftCursor with
                  | none => simp [leftAfter] at relatedLeft
                  | some leftFrameAfter =>
                      have leftRelated : input.LocalizedRule3EndpointObservableRel
                          leftFrame.endpointFrame leftFrameAfter.endpointFrame := by
                        simpa [leftAfter] using relatedLeft
                      cases rightComputed :
                          input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                            target view before initial.right initial.left
                            initial.rightCursor with
                      | none =>
                          rw [rightComputed] at relatedRight
                          cases rightAfter :
                              input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                                target view after initial.right initial.left
                                initial.rightCursor with
                          | none => simp [routeComputed, policyComputed, leftComputed, leftAfter,
                              rightComputed, rightAfter]
                          | some frameAfter => simp [rightAfter] at relatedRight
                      | some rightFrame =>
                          rw [rightComputed] at relatedRight
                          cases rightAfter :
                              input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                                target view after initial.right initial.left
                                initial.rightCursor with
                          | none => simp [rightAfter] at relatedRight
                          | some rightFrameAfter =>
                              have rightRelated : input.LocalizedRule3EndpointObservableRel
                                  rightFrame.endpointFrame rightFrameAfter.endpointFrame := by
                                simpa [rightAfter] using relatedRight
                              have unitEq :
                                  input.localizedRule3DescriptorBearingSpatialUnit?
                                      initial.left initial.right
                                      leftFrame.endpointFrame rightFrame.endpointFrame =
                                    input.localizedRule3DescriptorBearingSpatialUnit?
                                      initial.left initial.right
                                      leftFrameAfter.endpointFrame
                                      rightFrameAfter.endpointFrame :=
                                input.localizedRule3DescriptorBearingSpatialUnit?_eq_of_priorities
                                  initial.left initial.right _ _ _ _
                                  (input.localizedRule3EndpointPriority_eq_of_observableRel
                                    _ _ leftRelated)
                                  (input.localizedRule3EndpointPriority_eq_of_observableRel
                                    _ _ rightRelated)
                              cases unitComputed :
                                  input.localizedRule3DescriptorBearingSpatialUnit?
                                    initial.left initial.right leftFrameAfter.endpointFrame
                                    rightFrameAfter.endpointFrame with
                              | none =>
                                  simp [routeComputed, policyComputed, leftComputed, leftAfter,
                                    rightComputed, rightAfter, unitEq, unitComputed]
                              | some unitValue =>
                                  cases geometryComputed :
                                      monocyclicSeniorLigandGeometryOfRule3?
                                        unitValue.geometry with
                                  | none =>
                                      simp [routeComputed, policyComputed, leftComputed,
                                        leftAfter, rightComputed, rightAfter, unitEq,
                                        unitComputed, geometryComputed]
                                  | some cyclicGeometry =>
                                      cases descriptorComputed :
                                          BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
                                            policyResult.carrier.ring.card
                                            policyResult.doubleBondCount cyclicGeometry with
                                      | none =>
                                          simp [routeComputed, policyComputed, leftComputed,
                                            leftAfter, rightComputed, rightAfter, unitEq,
                                            unitComputed, geometryComputed, descriptorComputed]
                                      | some descriptor =>
                                          simp [routeComputed, policyComputed, leftComputed,
                                            leftAfter, rightComputed, rightAfter, unitEq,
                                            unitComputed, geometryComputed, descriptorComputed,
                                            localizedRule3RequiredMonocyclicEZObservation,
                                            leftRelated.1, rightRelated.1]

/-! ## Observable invariance of the actual node evaluators

The intermediate step of the callback replacement compares two callbacks that are pointwise
observably related (`LocalizedRule3FrameCallbackObservableRel`).  The three node evaluators of the
original chain must reproduce the same comparison-visible observation under that relation.  The
short-circuit and odd-cumulene routes are already transported verbatim by
`LocalizedEndpointObservableTransport`; the missing layer is the original descriptor-bearing node,
whose three callback-reading spatial units are transported above. -/

/-- **Observable invariance of the original descriptor-bearing node.**  Under pointwise observably
related callbacks, a successful original node result is reproduced with the same
comparison-visible observation.  The three callback-reading spatial units contribute only their
packed observations, which the transport lemmas above preserve; the cyclic route dispatch in the
`ringClosure` refusal branch is callback-independent. -/
private theorem originalNodeWith_observable_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : LocalizedRule3FrameCallbackObservableRel input before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed :
      input.localizedDescriptorBearingRule3NodeWith?
        target occurrence view before excluded = some observation) :
    ∃ fresh,
      input.localizedDescriptorBearingRule3NodeWith?
          target occurrence view after excluded = some fresh ∧
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
          Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation := by
  classical
  unfold localizedDescriptorBearingRule3NodeWith? at computed ⊢
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · simp only [dif_pos edge] at computed ⊢
    cases entry : input.localizedRule3CumulatedAxisEntry? occurrence with
    | none => simp [entry] at computed
    | some entryValue =>
        cases entryValue with
        | internal =>
            simp only [entry] at computed
            simp only [] at computed ⊢
            have observationEq : observation = none := (Option.some.inj computed).symm
            rw [observationEq]
            exact ⟨none, rfl, rfl⟩
        | branched initial first second rest =>
            simp only [entry] at computed
            simp only [] at computed ⊢
            cases huB : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                target occurrence view before with
            | none => simp [huB] at computed
            | some result =>
                simp only [huB] at computed
                cases huA : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                    target occurrence view after with
                | none =>
                    have mapEq :=
                      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_eq_of_callback_observableRel
                        target occurrence view before after rel
                    simp [huB, huA] at mapEq
                | some result' =>
                    have obsEq : input.localizedRule3DescriptorBearingObservation result' =
                        input.localizedRule3DescriptorBearingObservation result := by
                      have mapEq :=
                        input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_eq_of_callback_observableRel
                          target occurrence view before after rel
                      simpa [huB, huA] using mapEq.symm
                    show ∃ fresh,
                      (if excluded.contains
                          (input.localizedRule3DescriptorBearingObservation result').physicalUnitId = true then
                          some none
                        else some (some (input.localizedRule3DescriptorBearingObservation result'))) =
                          some fresh ∧
                        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
                          Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation
                    rw [obsEq]
                    by_cases hc : excluded.contains
                        (input.localizedRule3DescriptorBearingObservation result).physicalUnitId = true
                    · rw [if_pos hc] at computed ⊢
                      have observationEq : observation = none := (Option.some.inj computed).symm
                      rw [observationEq]
                      exact ⟨none, rfl, rfl⟩
                    · rw [if_neg hc] at computed ⊢
                      have observationEq : observation =
                          some (input.localizedRule3DescriptorBearingObservation result) :=
                        (Option.some.inj computed).symm
                      rw [observationEq]
                      exact ⟨some (input.localizedRule3DescriptorBearingObservation result), rfl, rfl⟩
        | terminalStart initial =>
            simp only [entry] at computed
            simp only [] at computed ⊢
            cases axis : input.localizedRule3CumulatedEndpointCursorFrame?
                (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
            | none => simp [axis] at computed
            | some axisValue =>
                simp only [axis] at computed
                simp only [] at computed ⊢
                by_cases ordinary : axisValue.doubleBondCount = 1
                · simp only [dif_pos ordinary, if_pos ordinary] at computed ⊢
                  cases huB : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                      target occurrence view before with
                  | none => simp [huB] at computed
                  | some result =>
                      simp only [huB] at computed
                      cases huA : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                          target occurrence view after with
                      | none =>
                          have mapEq :=
                            input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_eq_of_callback_observableRel
                              target occurrence view before after rel
                          simp [huB, huA] at mapEq
                      | some result' =>
                          have obsEq : input.localizedRule3DescriptorBearingObservation result' =
                              input.localizedRule3DescriptorBearingObservation result := by
                            have mapEq :=
                              input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_eq_of_callback_observableRel
                                target occurrence view before after rel
                            simpa [huB, huA] using mapEq.symm
                          show ∃ fresh,
                            (if excluded.contains
                                (input.localizedRule3DescriptorBearingObservation result').physicalUnitId = true then
                                some none
                              else some (some (input.localizedRule3DescriptorBearingObservation result'))) =
                                some fresh ∧
                              Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
                                Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation
                          rw [obsEq]
                          by_cases hc : excluded.contains
                              (input.localizedRule3DescriptorBearingObservation result).physicalUnitId = true
                          · rw [if_pos hc] at computed ⊢
                            have observationEq : observation = none := (Option.some.inj computed).symm
                            rw [observationEq]
                            exact ⟨none, rfl, rfl⟩
                          · rw [if_neg hc] at computed ⊢
                            have observationEq : observation =
                                some (input.localizedRule3DescriptorBearingObservation result) :=
                              (Option.some.inj computed).symm
                            rw [observationEq]
                            exact ⟨some (input.localizedRule3DescriptorBearingObservation result), rfl, rfl⟩
                · simp only [dif_neg ordinary, if_neg ordinary] at computed ⊢
                  by_cases planar : Odd axisValue.doubleBondCount
                  · simp only [dif_pos planar, if_pos planar] at computed ⊢
                    cases huB : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
                        target occurrence view before with
                    | none => simp [huB] at computed
                    | some result =>
                        simp only [huB] at computed
                        cases huA : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
                            target occurrence view after with
                        | none =>
                            have mapEq :=
                              input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_observation_eq_of_callback_observableRel
                                target occurrence view before after rel
                            simp [huB, huA] at mapEq
                        | some result' =>
                            have obsEq :
                                input.localizedRule3OddCumuleneDescriptorBearingObservation result' =
                                  input.localizedRule3OddCumuleneDescriptorBearingObservation result := by
                              have mapEq :=
                                input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_observation_eq_of_callback_observableRel
                                  target occurrence view before after rel
                              simpa [huB, huA] using mapEq.symm
                            show ∃ fresh,
                              (if excluded.contains
                                  (input.localizedRule3OddCumuleneDescriptorBearingObservation result').physicalUnitId = true then
                                  some none
                                else some (some (input.localizedRule3OddCumuleneDescriptorBearingObservation result'))) =
                                  some fresh ∧
                                Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
                                  Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation
                            rw [obsEq]
                            by_cases hc : excluded.contains
                                (input.localizedRule3OddCumuleneDescriptorBearingObservation result).physicalUnitId = true
                            · rw [if_pos hc] at computed ⊢
                              have observationEq : observation = none := (Option.some.inj computed).symm
                              rw [observationEq]
                              exact ⟨none, rfl, rfl⟩
                            · rw [if_neg hc] at computed ⊢
                              have observationEq : observation =
                                  some (input.localizedRule3OddCumuleneDescriptorBearingObservation result) :=
                                (Option.some.inj computed).symm
                              rw [observationEq]
                              exact ⟨some (input.localizedRule3OddCumuleneDescriptorBearingObservation result), rfl, rfl⟩
                  · simp only [dif_neg planar, if_neg planar] at computed ⊢
                    have observationEq : observation = none :=
                      (Option.some.inj computed).symm
                    rw [observationEq]
                    exact ⟨none, rfl, rfl⟩
        | ringClosure initial closure =>
            simp only [entry] at computed
            simp only [] at computed ⊢
            have ezMap :=
              input.localizedRule3RequiredMonocyclicEZWith?_observation_eq_of_callback_observableRel
                target occurrence view before after rel
            cases ezBefore : input.localizedRule3RequiredMonocyclicEZWith?
                target occurrence view before with
            | some result =>
                simp only [ezBefore] at computed
                cases ezAfter : input.localizedRule3RequiredMonocyclicEZWith?
                    target occurrence view after with
                | none => simp [ezBefore, ezAfter] at ezMap
                | some result' =>
                    have obsEq : input.localizedRule3RequiredMonocyclicEZObservation result' =
                        input.localizedRule3RequiredMonocyclicEZObservation result := by
                      simpa [ezBefore, ezAfter] using ezMap.symm
                    show ∃ fresh,
                      (if excluded.contains
                          (input.localizedRule3RequiredMonocyclicEZObservation result').physicalUnitId = true then
                          some none
                        else some (some (input.localizedRule3RequiredMonocyclicEZObservation result'))) =
                          some fresh ∧
                        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
                          Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation
                    rw [obsEq]
                    by_cases hc : excluded.contains
                        (input.localizedRule3RequiredMonocyclicEZObservation result).physicalUnitId = true
                    · rw [if_pos hc] at computed ⊢
                      have observationEq : observation = none := (Option.some.inj computed).symm
                      rw [observationEq]
                      exact ⟨none, rfl, rfl⟩
                    · rw [if_neg hc] at computed ⊢
                      have observationEq : observation =
                          some (input.localizedRule3RequiredMonocyclicEZObservation result) :=
                        (Option.some.inj computed).symm
                      rw [observationEq]
                      exact ⟨some (input.localizedRule3RequiredMonocyclicEZObservation result), rfl, rfl⟩
            | none =>
                simp only [ezBefore] at computed
                cases ezAfter : input.localizedRule3RequiredMonocyclicEZWith?
                    target occurrence view after with
                | none => exact ⟨observation, computed, rfl⟩
                | some value => simp [ezBefore, ezAfter] at ezMap
  · simp only [dif_neg edge] at computed ⊢
    have observationEq : observation = none := (Option.some.inj computed).symm
    rw [observationEq]
    exact ⟨none, rfl, rfl⟩

/-- **Observable invariance of the short-circuit node.**  On the ordinary route the short-circuit
spatial unit is literally equal under the observable callback relation; otherwise the original
descriptor-bearing node applies. -/
private theorem shortNodeWith_observable_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : LocalizedRule3FrameCallbackObservableRel input before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed :
      input.localizedRule3ShortCircuitNodeWithExec?
        target occurrence view before excluded = some observation) :
    ∃ fresh,
      input.localizedRule3ShortCircuitNodeWithExec?
          target occurrence view after excluded = some fresh ∧
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
          Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation := by
  unfold localizedRule3ShortCircuitNodeWithExec? at computed ⊢
  cases route : input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none =>
      simp only [route] at computed ⊢
      rw [localizedDescriptorBearingRule3NodeWithExec?_eq_original] at computed ⊢
      exact originalNodeWith_observable_eq_of_callback_observableRel input target occurrence view
        before after rel excluded observation computed
  | some certificate =>
      simp only [route] at computed ⊢
      rw [localizedRule3ShortCircuitSpatialUnitWithExec?_eq_localizedRule3ShortCircuitSpatialUnitWith?]
        at computed ⊢
      have unitEq := input.localizedRule3ShortCircuitSpatialUnitWith?_eq_of_callback_observableRel
        target occurrence view before after rel
      rw [← unitEq]
      exact ⟨observation, computed, rfl⟩

/-- **Observable invariance of the extended short-circuit node.**  The odd-axis route transports its
spatial unit verbatim; the ordinary route is the short-circuit node.

This is the public callback-transport interface consumed by the successor module that owns the final
mutual old-to-new refinement (`LocalizedFullyGuardedSuccessPreservation`): it is *not* an
`_refines_old` theorem and assumes nothing beyond the pointwise observable callback relation and a
successful evaluation at the `before` callback. -/
theorem extendedShortNodeWith_observable_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : LocalizedRule3FrameCallbackObservableRel input before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed :
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view before excluded = some observation) :
    ∃ fresh,
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target occurrence view after excluded = some fresh ∧
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
          Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation := by
  unfold localizedRule3ExtendedShortCircuitNodeWithExec? at computed ⊢
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      simp only [routed] at computed ⊢
      exact shortNodeWith_observable_eq_of_callback_observableRel input target occurrence view
        before after rel excluded observation computed
  | some certificate =>
      simp only [routed] at computed ⊢
      have unitEq :=
        input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_of_callback_observableRel
          target occurrence view before after rel
      rw [← unitEq]
      exact ⟨observation, computed, rfl⟩

/-! ## The actual successor as a matching guarded demand recursion

The accepted generic engine `LocalizedFullyTerminalGuardedDemandStability` packages any pair of
key/frame evaluators satisfying the two *definitional* successor equations.  The actual definitions
above satisfy them by `rfl`: the `fuel + 1` key branch hands the adapter exactly
`buildLocalizedFullyTerminalGuardedRule3FrameExec? target view predecessor`, recurses on children
with the same key builder, and the `fuel + 1` frame branch performs the actual two-pass compilation
with the same key builder.  No desired-callback, success, rank or acyclicity premise is introduced. -/

open TetraStereo.Certificate.WeightedDemand

/-- The actual fully guarded mutual key/frame compiler packaged as a
`FullyTerminalGuardedSuccessorRecursion` over its matching guarded demand graph.  Both successor
equations hold definitionally. -/
def buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    FullyTerminalGuardedSuccessorRecursion input target view where
  key := input.buildLocalizedFullyTerminalGuardedRule3KeyExec? target view
  frame := input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view
  key_succ := by
    intro predecessor excluded cursor
    rfl
  frame_succ := by
    intro predecessor cursors
    rfl

/-- **Key stability of the actual fully guarded key.**  On the matching terminal-guarded weighted
demand graph, every covered cursor has the same complete optional key at every two budgets above
its checked rank, for any fixed exclusion list. -/
theorem buildLocalizedFullyTerminalGuardedRule3Key_stable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (cursor : input.LocalizedRerootCursor carrierFuel) (member : cursor ∈ certificate.vertices)
    (first second : Nat) (firstEnough : certificate.height cursor ≤ first)
    (secondEnough : certificate.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.buildLocalizedFullyTerminalGuardedRule3KeyExec? target view first excluded cursor =
      input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
        target view second excluded cursor :=
  fullyTerminalGuardedKey_stable input
    (buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion input target view)
    certificate cursor member first second firstEnough secondEnough excluded

/-- **Frame stability of the actual fully guarded frame.**  Every list of covered cursors has the
same complete optional two-pass frame at every two budgets above the checked list height plus one;
both raw and rebuilt passes, the coupled-topology refusal and every exclusion branch are preserved
because they are part of the actual evaluator. -/
theorem buildLocalizedFullyTerminalGuardedRule3Frame_stable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (covered : ∀ cursor ∈ cursors, cursor ∈ certificate.vertices)
    (first second : Nat)
    (firstEnough : listHeight certificate.height cursors + 1 ≤ first)
    (secondEnough : listHeight certificate.height cursors + 1 ≤ second) :
    input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view first cursors =
      input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view second cursors :=
  fullyTerminalGuardedFrame_stable input
    (buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion input target view)
    certificate cursors covered first second firstEnough secondEnough



theorem buildLocalizedFullyTerminalGuardedRule3Plan_evaluate_eq_above
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {roots : List (input.LocalizedRerootCursor carrierFuel)}
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    FullyTerminalGuardedPlan.evaluate plan
        (buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion input target view) =
      input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view budget roots :=
  FullyTerminalGuardedPlan.evaluate_eq_above plan
    (buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion input target view) budget enough

/-! ## Kernel-authority guards for every public export -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3KeyExec?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3FrameExec?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3KeyExec?_zero_eq_old
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3KeyExec?_zero_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3FrameExec?_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3DescriptorBearingSpatialUnit?_eq_of_priorities
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_of_priorities
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedShortNodeWith_observable_eq_of_callback_observableRel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3SuccessorRecursion
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3Key_stable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3Frame_stable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3Plan_evaluate_eq_above

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
