import TetraStereo.OneCenter.LocalizedRule3ExtendedNodePreservation
import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedRerootShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedRule3FrameRootCoherence
import TetraStereo.OneCenter.LocalizedConstitutionalRule3Coherence
import TetraStereo.OneCenter.LocalizedShortCircuitDescriptor
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitDescriptor

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Successful-value preservation from the ordinary shortcut to the extended shortcut

The ordinary-shortcut recursive Rule-3 evaluator (``buildLocalizedRerootShortCircuitRule3KeyExec?`` /
``buildLocalizedShortCircuitRule3FrameExec?``) already demands a complete frame from its predecessor
budget.  The extended evaluator (``buildLocalizedRerootExtendedShortCircuitRule3KeyExec?`` /
``buildLocalizedExtendedShortCircuitRule3FrameExec?``) adds exactly one extra node branch: a planar
nonordinary odd cumulene axis whose terminal references are chosen by strict constitutional
endpoint priority.

This module proves that every successful ordinary-shortcut key, frame, node observation, and final
descriptor is retained with the identical value by the extended evaluator, at the same
fuel/target/view.  No chemical applicability hypothesis or equal-callback premise is assumed; the
two endpoint-coherence facts required by the odd-axis shortcut are established generally here for
successful ordinary-shortcut frames.
-/

/-- Every successful ordinary-shortcut reroot key retains its cursor's atomic-number observation as
the singleton first sphere and first parent address of Rule 1a, in both the terminal and assembled
outer cases. -/
theorem buildLocalizedRerootShortCircuitRule3KeyExec?_constitutional_rule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
      (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootShortCircuitRule3KeyExec?
          target view fuel excluded cursor = some key →
        key.constitutional.rule1a.head? =
          some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).1)]
  | 0, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootShortCircuitRule3KeyExec? at computed
      cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3StructuralNodeExec cursor.occurrence with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                simp
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootShortCircuitRule3KeyExec? at computed
      cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed : input.localizedRule3ShortCircuitNodeWithExec?
              target cursor.occurrence view
              (input.buildLocalizedShortCircuitRule3FrameExec? target view fuel)
              excluded with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                simp
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootShortCircuitRule3KeyExec?
                      target view fuel excluded) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    simp [OfficialRuleMajorKey.assemble]

/-- The same head fact in terms of the plain cursor root observation. -/
theorem buildLocalizedRerootShortCircuitRule3KeyExec?_constitutional_rule1a_head_observation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootShortCircuitRule3KeyExec?
      target view fuel excluded cursor = some key) :
    key.constitutional.rule1a.head? =
      some [([], input.localizedRerootCursorRootAtomicNumber cursor)] := by
  unfold localizedRerootCursorRootAtomicNumber
  exact input.buildLocalizedRerootShortCircuitRule3KeyExec?_constitutional_rule1a_head
    target view fuel excluded cursor key computed

private theorem mapM_forall₂_shortCircuit {α β : Type*} (f : α → Option β) (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → R a b) :
    ∀ xs ys, xs.mapM f = some ys → List.Forall₂ R xs ys := by
  intro xs
  induction xs with
  | nil => intro ys h; simp at h; subst ys; exact .nil
  | cons a rest ih =>
      intro ys h
      cases ha : f a with
      | none => simp [List.mapM_cons, ha] at h
      | some b =>
          cases hr : rest.mapM f with
          | none => simp [List.mapM_cons, ha, hr] at h
          | some bs =>
              simp [List.mapM_cons, ha, hr] at h
              subst ys
              exact .cons (sound a b ha) (ih bs hr)

/-- The second pass of every successful ordinary-shortcut frame retains the exact constitutional
head for every cursor, irrespective of the excluded physical units. -/
theorem buildLocalizedShortCircuitRule3FrameExec?_rootsExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedShortCircuitRule3FrameExec?
      target view fuel cursors = some frame) : input.LocalizedRule3FrameRootsExact cursors frame := by
  cases fuel with
  | zero => simp [buildLocalizedShortCircuitRule3FrameExec?] at computed
  | succ fuel =>
      unfold buildLocalizedShortCircuitRule3FrameExec? at computed
      cases raw : cursors.mapM
          (input.buildLocalizedRerootShortCircuitRule3KeyExec? target view fuel []) with
      | none => simp [raw] at computed
      | some rawKeys =>
          cases topology : input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
          | none => simp [raw, topology] at computed
          | some resolution =>
              let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys resolution
              cases rebuilt : cursors.mapM
                  (input.buildLocalizedRerootShortCircuitRule3KeyExec? target view fuel excluded) with
              | none => simp [raw, topology, excluded, rebuilt] at computed
              | some keys =>
                  simp [raw, topology, excluded, rebuilt] at computed
                  subst frame
                  exact mapM_forall₂_shortCircuit _ _
                    (input.buildLocalizedRerootShortCircuitRule3KeyExec?_constitutional_rule1a_head_observation
                      target view fuel excluded) cursors keys rebuilt

/-- Successful ordinary-shortcut frames are constitutionally exact: every rebuilt key agrees with
the pure constitutional compilation on all comparison-visible constitutional layers. -/
theorem buildLocalizedShortCircuitRule3FrameExec?_constitutionalExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedShortCircuitRule3FrameExec?
      target view fuel cursors = some frame) :
    input.LocalizedRule3FrameConstitutionalExact cursors frame := by
  have meaning := input.buildLocalizedShortCircuitRule3FrameExec?_sound
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
        (input.shortCircuitRule3Key_constitutional_derived target view fuel _ _ _ head)

/-- The odd-axis shortcut preserves every successful original odd-cumulene geometry, now against
the ordinary-shortcut frame builder.  The two endpoint-coherence premises are derived generally
from the two preceding frame facts. -/
theorem shortCircuitOddSpatial_preserves_shortCircuitFrame_success
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (oldResult : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult fuel)
    (computed : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
      target occurrence view (input.buildLocalizedShortCircuitRule3FrameExec? target view budget) =
        some oldResult) :
    ∃ result, input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view (input.buildLocalizedShortCircuitRule3FrameExec? target view budget) =
        some result ∧ input.localizedRule3ShortCircuitOddSpatialObservation result =
          input.localizedRule3OddCumuleneDescriptorBearingObservation oldResult := by
  let callback := input.buildLocalizedShortCircuitRule3FrameExec? target view budget
  have derived := input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_sound
    target occurrence view callback (fun cursors frame => callback cursors = some frame)
    (fun _ _ h => h) oldResult computed
  have left := derived.2.1
  have right := derived.2.2.1
  apply input.localizedRule3ShortCircuitOddSpatialObservation_eq_of_parameterizedWith
    target occurrence view callback oldResult computed
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.leftCompilation
      (input.buildLocalizedShortCircuitRule3FrameExec?_rootsExact target view budget _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.rightCompilation
      (input.buildLocalizedShortCircuitRule3FrameExec?_rootsExact target view budget _ _
        right.2.2.2.1) right.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.leftCompilation
      (input.buildLocalizedShortCircuitRule3FrameExec?_constitutionalExact target view budget _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.rightCompilation
      (input.buildLocalizedShortCircuitRule3FrameExec?_constitutionalExact target view budget _ _
        right.2.2.2.1) right.2.2.2.2.1

/-- Successful ordinary-shortcut nodes retain their exact optional identity-bearing observation
when odd axes gain the extended shortcut. -/
theorem extendedShortNode_preserves_shortCircuit_callback
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedRule3ShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedShortCircuitRule3FrameExec? target view budget) excluded)
      (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedShortCircuitRule3FrameExec? target view budget) excluded) := by
  let callback := input.buildLocalizedShortCircuitRule3FrameExec? target view budget
  intro observation computed
  change input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view callback excluded = some observation
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
          obtain ⟨result, next, same⟩ := input.shortCircuitOddSpatial_preserves_shortCircuitFrame_success
            target occurrence view budget oldResult oldSpatial
          simp only [spatial] at oldComputed
          by_cases omitted : (input.localizedRule3OddCumuleneDescriptorBearingObservation oldResult).physicalUnitId ∈ excluded
          · simpa [localizedRule3ExtendedShortCircuitNodeWithExec?, routed, next, same,
              callback, omitted] using oldComputed
          · simpa [localizedRule3ExtendedShortCircuitNodeWithExec?, routed, next, same,
              callback, omitted] using oldComputed

/-- Combine local extended-shortcut preservation with a recursively improved callback. -/
theorem extendedShortNode_preserves_shortCircuit_with_refined_callback
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat)
    (after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines
      (input.buildLocalizedShortCircuitRule3FrameExec? target view budget) after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedRule3ShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedShortCircuitRule3FrameExec? target view budget) excluded)
      (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view after excluded) :=
  (input.extendedShortNode_preserves_shortCircuit_callback target occurrence view budget excluded).trans
    (input.extendedShortNodeWith_callback_refines target occurrence view _ after refines excluded)

/-- Simultaneous successful-result preservation for the entire recursive Rule-3 construction, from
the ordinary-shortcut evaluator to the extended evaluator.  Full keys, raw and rebuilt frames,
topology and exclusion metadata are retained at the same fuel. -/
theorem localizedExtendedShort_mutual_success_refinement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    ∀ fuel,
      (∀ excluded cursor, OptionSuccessRefines
        (input.buildLocalizedRerootShortCircuitRule3KeyExec? target view fuel excluded cursor)
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel excluded cursor)) ∧
      (∀ cursors, OptionSuccessRefines
        (input.buildLocalizedShortCircuitRule3FrameExec? target view fuel cursors)
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootShortCircuitRule3KeyExec?,
          buildLocalizedRerootExtendedShortCircuitRule3KeyExec?]
        exact .refl _
      · intro cursors
        exact .refl _
  | succ fuel ih =>
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootShortCircuitRule3KeyExec?,
          buildLocalizedRerootExtendedShortCircuitRule3KeyExec?]
        apply OptionSuccessRefines.bind (.refl _)
        intro children
        apply OptionSuccessRefines.bind
          (input.extendedShortNode_preserves_shortCircuit_with_refined_callback
            target cursor.occurrence view fuel _ ih.2 excluded)
        intro observation
        by_cases empty : children = []
        · simp only [if_pos empty]
          exact .refl _
        · simp only [if_neg empty]
          apply OptionSuccessRefines.bind
            (OptionSuccessRefines.mapM _ _ (ih.1 excluded) children)
          intro childKeys
          exact .refl _
      · intro cursors
        simp only [buildLocalizedShortCircuitRule3FrameExec?,
          buildLocalizedExtendedShortCircuitRule3FrameExec?]
        apply OptionSuccessRefines.bind
          (OptionSuccessRefines.mapM _ _ (ih.1 []) cursors)
        intro rawKeys
        apply OptionSuccessRefines.bind (.refl _)
        intro topology
        apply OptionSuccessRefines.bind
          (OptionSuccessRefines.mapM _ _
            (ih.1 (input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology)) cursors)
        intro keys
        exact .refl _

/-- Every old successful ordinary-shortcut full key survives, including its observation and
provenance records. -/
theorem extendedShortCircuitRule3Key_preserves_shortCircuit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootShortCircuitRule3KeyExec?
      target view fuel excluded cursor = some key) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view fuel excluded cursor = some key :=
  (input.localizedExtendedShort_mutual_success_refinement target view fuel).1 excluded cursor key computed

/-- Both passes of every old successful ordinary-shortcut frame survive with the identical complete
frame. -/
theorem extendedShortCircuitRule3Frame_preserves_shortCircuit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedShortCircuitRule3FrameExec?
      target view fuel cursors = some frame) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view fuel cursors = some frame :=
  (input.localizedExtendedShort_mutual_success_refinement target view fuel).2 cursors frame computed

/-- Optional node observations are also retained, including structural absence and excluded units. -/
theorem extendedShortCircuitRule3Node_preserves_shortCircuit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedShortCircuitRule3NodeExec? target occurrence view fuel excluded)
      (input.localizedExtendedShortCircuitRule3NodeExec? target occurrence view fuel excluded) := by
  cases fuel with
  | zero =>
      simp only [localizedShortCircuitRule3NodeExec?, localizedExtendedShortCircuitRule3NodeExec?]
      exact .refl _
  | succ fuel =>
      exact input.extendedShortNode_preserves_shortCircuit_with_refined_callback
        target occurrence view fuel _
        (input.localizedExtendedShort_mutual_success_refinement target view fuel).2 excluded

/-- The extended four-ligand key frame retains every successful ordinary-shortcut key frame. -/
theorem extendedShortCircuitKeyFrame_preserves_shortCircuitExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    OptionSuccessRefines
      (input.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame? target view base)
      (input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? target view base) := by
  unfold buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame? buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
  apply OptionSuccessRefines.bind
    (input.extendedShortCircuitRule3Frame_preserves_shortCircuit target view _ base.cursors)
  intro frame
  exact .refl _

/-- Ranked geometry evidence survives in full at a fixed dependency view. -/
theorem extendedShortCircuitSpatialEvidence_preserves_shortCircuitExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    OptionSuccessRefines
      (input.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence? target view)
      (input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence? target view) := by
  unfold localizedOccurrenceShortCircuitRule3Through5SpatialEvidence? localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
  apply OptionSuccessRefines.bind (.refl _)
  intro center
  apply OptionSuccessRefines.bind (.refl _)
  intro base
  apply OptionSuccessRefines.bind (input.extendedShortCircuitKeyFrame_preserves_shortCircuitExec target view base)
  intro keys
  exact .refl _

/-- The extended recursive descriptor evaluator retains every ordinary-shortcut descriptor. -/
theorem extendedShortCircuitDescriptor_preserves_shortCircuitExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    OptionSuccessRefines
      (input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view)
      (input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view) := by
  unfold localizedOccurrenceShortCircuitRule3Through5Descriptor? localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
  apply OptionSuccessRefines.bind (input.extendedShortCircuitSpatialEvidence_preserves_shortCircuitExec target view)
  intro evidence
  exact .refl _

/-- Positive agreement with the existing proof-facing semantics at the same dependency view. -/
theorem extendedShortCircuitDescriptor_preserves_shortCircuit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceShortCircuitRule3Through5Descriptor?
      target view = some descriptor) :
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view = some descriptor :=
  input.extendedShortCircuitDescriptor_preserves_shortCircuitExec target view descriptor computed

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
