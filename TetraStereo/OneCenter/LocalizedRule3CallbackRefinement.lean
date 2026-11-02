import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial
import TetraStereo.OneCenter.LocalizedDescriptorBearingRule3Executable

set_option autoImplicit false
namespace TetraStereo.OneCenter
universe u

/-- Every successful value is retained exactly; a previous refusal may gain a result. -/
def OptionSuccessRefines {α : Type*} (before after : Option α) : Prop :=
  ∀ value, before = some value → after = some value

namespace OptionSuccessRefines

theorem refl {α : Type*} (value : Option α) : OptionSuccessRefines value value := fun _ h => h

theorem trans {α : Type*} {a b c : Option α}
    (first : OptionSuccessRefines a b) (second : OptionSuccessRefines b c) :
    OptionSuccessRefines a c := fun value computed => second value (first value computed)

theorem bind {α β : Type u} {before after : Option α}
    {left right : α → Option β} (head : OptionSuccessRefines before after)
    (tail : ∀ value, OptionSuccessRefines (left value) (right value)) :
    OptionSuccessRefines (before >>= left) (after >>= right) := by
  intro result computed
  cases source : before with
  | none => simp [source] at computed
  | some value =>
      have next := head value source
      simpa [next] using tail value result (by simpa [source] using computed)

theorem mapM {α β : Type u} (before after : α → Option β)
    (refines : ∀ value, OptionSuccessRefines (before value) (after value)) :
    ∀ values : List α, OptionSuccessRefines (values.mapM before) (values.mapM after)
  | [] => refl _
  | value :: values => by
      simp only [List.mapM_cons]
      apply bind (refines value)
      intro head
      apply bind (mapM before after refines values)
      intro tail
      exact refl _

end OptionSuccessRefines
namespace CertifiedLocalizedCIPInput

abbrev LocalizedRule3CallbackRefines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∀ cursors, OptionSuccessRefines (before cursors) (after cursors)

/-- Endpoint compilation only consumes successful callback frames; their exact preservation
retains both the Rule3 and Rule4a--5 parts of every successful endpoint. -/
theorem endpointWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after)
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor carrierFuel) :
    OptionSuccessRefines
      (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith? target view before endpoint partner cursor)
      (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith? target view after endpoint partner cursor) := by
  intro frame computed
  have parts := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_computations
    target view before endpoint partner cursor frame computed
  have next := refines [frame.firstCursor, frame.secondCursor] frame.rule3Frame parts.rule3Frame
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith? at computed ⊢
  simpa [parts.candidates, parts.firstCursor, parts.secondCursor,
    parts.rule3Frame, next] using computed

theorem ordinarySpatialWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after) :
    OptionSuccessRefines
      (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith? target occurrence view before)
      (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith? target occurrence view after) := by
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
  apply OptionSuccessRefines.bind (.refl _)
  intro topology
  apply OptionSuccessRefines.bind (input.endpointWith_callback_refines target view before after refines _ _ _)
  intro left
  apply OptionSuccessRefines.bind (input.endpointWith_callback_refines target view before after refines _ _ _)
  intro right
  exact .refl _

theorem oddCumuleneSpatialWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after) :
    OptionSuccessRefines
      (input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith? target occurrence view before)
      (input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith? target occurrence view after) := by
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
  apply OptionSuccessRefines.bind (.refl _)
  intro topology
  apply OptionSuccessRefines.bind (input.endpointWith_callback_refines target view before after refines _ _ _)
  intro left
  apply OptionSuccessRefines.bind (input.endpointWith_callback_refines target view before after refines _ _ _)
  intro right
  exact .refl _

theorem requiredMonocycleWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after) :
    OptionSuccessRefines
      (input.localizedRule3RequiredMonocyclicEZWith? target occurrence view before)
      (input.localizedRule3RequiredMonocyclicEZWith? target occurrence view after) := by
  unfold localizedRule3RequiredMonocyclicEZWith?
  apply OptionSuccessRefines.bind (.refl _)
  intro route
  cases route with
  | fullyCyclicCumulene => exact .refl _
  | ordinaryMonocyclicPolicyGap => exact .refl _
  | ordinaryNonmonocyclic => exact .refl _
  | ordinaryMonocyclicPolicy initial closure policy =>
      dsimp only
      cases policy.policy with
      | permanentlyOmit => exact .refl _
      | requireEZ =>
          apply OptionSuccessRefines.bind (input.endpointWith_callback_refines target view before after refines _ _ _)
          intro left
          apply OptionSuccessRefines.bind (input.endpointWith_callback_refines target view before after refines _ _ _)
          intro right
          exact .refl _

/-- Constitutional tests are callback-independent; only the deferred full frame needs transport. -/
theorem shortEndpointWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after)
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor carrierFuel) :
    OptionSuccessRefines
      (input.localizedRule3ShortCircuitEndpointPriority? target view before endpoint partner cursor)
      (input.localizedRule3ShortCircuitEndpointPriority? target view after endpoint partner cursor) := by
  unfold localizedRule3ShortCircuitEndpointPriority?
  split
  · apply OptionSuccessRefines.bind (.refl _)
    intro first
    apply OptionSuccessRefines.bind (.refl _)
    intro second
    split
    · exact .refl _
    · exact .refl _
    · split
      · exact .refl _
      · exact .refl _
      · apply OptionSuccessRefines.bind (input.endpointWith_callback_refines target view before after refines _ _ _)
        intro frame
        exact .refl _
  · exact .refl _

theorem shortSpatialWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after) :
    OptionSuccessRefines
      (input.localizedRule3ShortCircuitSpatialUnitWith? target occurrence view before)
      (input.localizedRule3ShortCircuitSpatialUnitWith? target occurrence view after) := by
  unfold localizedRule3ShortCircuitSpatialUnitWith?
  apply OptionSuccessRefines.bind (.refl _)
  intro topology
  apply OptionSuccessRefines.bind (input.shortEndpointWith_callback_refines target view before after refines _ _ _)
  intro left
  apply OptionSuccessRefines.bind (input.shortEndpointWith_callback_refines target view before after refines _ _ _)
  intro right
  exact .refl _

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
