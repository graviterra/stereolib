import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6InitialPartition

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact construction boundary for the Rules 1a--5 initial partition
-/

/-- A successful `mapM` preserves the input list length. -/
theorem mapM_length_eq_of_eq_some
    {α β : Type*} (f : α → Option β) :
    ∀ (inputs : List α) (outputs : List β),
      inputs.mapM f = some outputs → outputs.length = inputs.length
  | [], outputs, computed => by
      simp at computed
      subst outputs
      rfl
  | input :: inputs, outputs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : inputs.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              simp [mapM_length_eq_of_eq_some f inputs tail tailComputed]

/-- Exactly the lower-level observations needed to construct the four Rules-1a--5 root keys.
The final length guard is absent because successful `mapM` and the four-root premise prove it
mathematically. -/
def AromaticCanonicalRule3Through5RootInputsResolved
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) : Prop :=
  roots.length = 4 ∧
    ∃ rule3Frame keys,
      source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel roots = some rule3Frame ∧
        roots.mapM
            (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
              rule3Frame.excluded target view fuel) = some keys

/-- Root-key-frame construction succeeds exactly when its explicit lower-level inputs are
resolved; the repeated length check cannot introduce a new failure. -/
theorem buildAromaticCanonicalRule3Through5RootKeyFrame?_isSome_iff_inputsResolved
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    (source.buildAromaticCanonicalRule3Through5RootKeyFrame?
        target view fuel roots).isSome = true ↔
      source.AromaticCanonicalRule3Through5RootInputsResolved
        target view fuel roots := by
  unfold buildAromaticCanonicalRule3Through5RootKeyFrame?
    AromaticCanonicalRule3Through5RootInputsResolved
  constructor
  · intro successful
    by_cases rootsLength : roots.length = 4
    · cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
          fuel roots with
      | none => simp [rootsLength, rule3Computed] at successful
      | some rule3Frame =>
          cases keysComputed : roots.mapM
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
                rule3Frame.excluded target view fuel) with
          | none => simp [rootsLength, rule3Computed, keysComputed] at successful
          | some keys => exact ⟨rootsLength, rule3Frame, keys, rfl, keysComputed⟩
    · simp [rootsLength] at successful
  · rintro ⟨rootsLength, rule3Frame, keys, rule3Computed, keysComputed⟩
    have keysLength : keys.length = 4 := by
      rw [mapM_length_eq_of_eq_some
        (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
          rule3Frame.excluded target view fuel) roots keys keysComputed,
        rootsLength]
    simp [rootsLength, rule3Computed, keysComputed, keysLength]

/-- Initial-partition construction adds only a total sort and adjacency projection, so it has
exactly the same success boundary as root-key-frame construction. -/
theorem buildAromaticCanonicalRule3Through5InitialPartition?_isSome_iff_inputsResolved
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    (source.buildAromaticCanonicalRule3Through5InitialPartition?
        target view fuel roots).isSome = true ↔
      source.AromaticCanonicalRule3Through5RootInputsResolved
        target view fuel roots := by
  rw [← source.buildAromaticCanonicalRule3Through5RootKeyFrame?_isSome_iff_inputsResolved]
  unfold buildAromaticCanonicalRule3Through5InitialPartition?
  cases source.buildAromaticCanonicalRule3Through5RootKeyFrame? target view fuel roots <;> simp

/-- Existential form used by the scheduler totality theorem. -/
theorem exists_buildAromaticCanonicalRule3Through5InitialPartition_iff_inputsResolved
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    (∃ partition, source.buildAromaticCanonicalRule3Through5InitialPartition?
        target view fuel roots = some partition) ↔
      source.AromaticCanonicalRule3Through5RootInputsResolved
        target view fuel roots := by
  rw [← source.buildAromaticCanonicalRule3Through5InitialPartition?_isSome_iff_inputsResolved,
    Option.isSome_iff_exists]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
