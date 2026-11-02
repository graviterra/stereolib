import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CircularAuxiliaryClassification

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact circular-auxiliary boundary for the complete Rule-3 frame

At the proved `2 * (carrierFuel + 1)` bound, both recursive key passes are already total for valid
cursors with resolved Rule-3 spatial observations.  This module proves that the intervening
physical-topology resolver is the only possible remaining refusal: success is exactly uniqueness
of the independent coupled-unit relation, and refusal is exactly two distinct valid coupled pairs.
-/

private theorem exists_rawRule3Keys_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          (2 * (carrierFuel + 1))) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        source.exists_buildAromaticCanonicalUncancelledRule3SpatialKey?_at_twice
          resolved cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_rawRule3Keys_at_twice resolved cursors
          (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- Complete frame success is exactly a generated raw frame whose independent exhaustive
coupled-unit relation is unique. -/
theorem exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_iff_unambiguous_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) :
    (∃ frame, source.buildAromaticCanonicalRule3CanonicalKeyFrame?
        (2 * (carrierFuel + 1)) cursors = some frame) ↔
      ∃ rawKeys,
        cursors.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          (2 * (carrierFuel + 1))) = some rawKeys ∧
        source.DeclarativeAromaticCanonicalRule3TopologyUnambiguous rawKeys := by
  constructor
  · rintro ⟨frame, frameComputed⟩
    unfold buildAromaticCanonicalRule3CanonicalKeyFrame? at frameComputed
    cases rawComputed : cursors.mapM
        (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          (2 * (carrierFuel + 1))) with
    | none => simp [rawComputed] at frameComputed
    | some rawKeys =>
        cases resolutionComputed :
            source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys with
        | none => simp [rawComputed, resolutionComputed] at frameComputed
        | some resolution =>
            refine ⟨rawKeys, rfl, ?_⟩
            apply (source.aromaticCanonicalRule3TopologyUnambiguous_iff_declarative
              rawKeys).mp
            exact ⟨resolution, resolutionComputed⟩
  · rintro ⟨rawKeys, rawComputed, topology⟩
    apply source.exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_at_twice
      resolved cursors valid
    intro otherKeys otherComputed
    have same : otherKeys = rawKeys := by
      exact Option.some.inj (otherComputed.symm.trans rawComputed)
    subst otherKeys
    exact (source.aromaticCanonicalRule3TopologyUnambiguous_iff_declarative
      rawKeys).mpr topology

/-- At the complete finite bound, `none` has one exact chemical meaning: two distinct,
independently valid coupled physical-unit pairs.  Recursive fuel and key construction are excluded
as causes by `resolved` and `valid`. -/
theorem buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_none_iff_ambiguous_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame?
        (2 * (carrierFuel + 1)) cursors = none ↔
      ∃ rawKeys first second,
        cursors.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          (2 * (carrierFuel + 1))) = some rawKeys ∧
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair rawKeys first ∧
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair rawKeys second ∧
        first ≠ second := by
  constructor
  · intro frameRefused
    obtain ⟨rawKeys, rawComputed⟩ :=
      source.exists_rawRule3Keys_at_twice resolved cursors valid
    have resolutionRefused :
        source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys = none := by
      cases resolutionComputed :
          source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys with
      | none => rfl
      | some resolution =>
          have topology :
              source.DeclarativeAromaticCanonicalRule3TopologyUnambiguous rawKeys :=
            (source.aromaticCanonicalRule3TopologyUnambiguous_iff_declarative rawKeys).mp
              ⟨resolution, resolutionComputed⟩
          obtain ⟨frame, frameComputed⟩ :=
            (source.exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_iff_unambiguous_at_twice
              resolved cursors valid).mpr ⟨rawKeys, rawComputed, topology⟩
          rw [frameRefused] at frameComputed
          simp at frameComputed
    obtain ⟨first, second, firstDerived, secondDerived, different⟩ :=
      (source.aromaticCanonicalRule3PhysicalTopologyResolution?_eq_none_iff_ambiguous
        rawKeys).mp resolutionRefused
    exact ⟨rawKeys, first, second, rawComputed, firstDerived, secondDerived, different⟩
  · rintro ⟨rawKeys, first, second, rawComputed,
      firstDerived, secondDerived, different⟩
    have resolutionRefused :
        source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys = none :=
      (source.aromaticCanonicalRule3PhysicalTopologyResolution?_eq_none_iff_ambiguous
        rawKeys).mpr ⟨first, second, firstDerived, secondDerived, different⟩
    simp [buildAromaticCanonicalRule3CanonicalKeyFrame?, rawComputed, resolutionRefused]

/-- The complete bounded frame has an exhaustive source-facing outcome: a constructed canonical
frame or explicit ambiguity witnesses. -/
theorem exists_canonicalRule3Frame_or_exact_ambiguity_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) :
    (∃ frame, source.buildAromaticCanonicalRule3CanonicalKeyFrame?
        (2 * (carrierFuel + 1)) cursors = some frame) ∨
      ∃ rawKeys first second,
        cursors.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          (2 * (carrierFuel + 1))) = some rawKeys ∧
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair rawKeys first ∧
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair rawKeys second ∧
        first ≠ second := by
  cases frameComputed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      (2 * (carrierFuel + 1)) cursors with
  | none =>
      exact Or.inr
        ((source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_none_iff_ambiguous_at_twice
          resolved cursors valid).mp frameComputed)
  | some frame => exact Or.inl ⟨frame, rfl⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
