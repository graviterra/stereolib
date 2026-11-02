import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Declarative applicability of coupled Rule-3 frame topology

The descriptor-bearing frame builder used to require the operational proposition that its
exhaustive topology resolver returned `some`.  That proposition hid the actual mathematical
condition.  This module states the condition independently: all valid exhaustive coupled
matchings of the same four-key frame must identify the same canonically ordered pair of physical
geometrical units.

The proofs below establish exact equivalence with executable resolver success, lift the relation
through raw key construction, and expose total frame-building theorems whose topology premise is
now entirely declarative.
-/

namespace CertifiedLocalizedCIPInput

/-- A finite coupled topology is unambiguous when any two independently valid exhaustive
matchings retain the same canonically ordered physical-unit pair.  The position pairing is already
proved unique once those two unit fields agree. -/
def DeclarativeLocalizedRule3CoupledTopologyUnambiguous
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  ∀ left right,
    input.DeclarativeLocalizedRule3CoupledMatching keys left →
    input.DeclarativeLocalizedRule3CoupledMatching keys right →
    left.firstUnit = right.firstUnit ∧ left.secondUnit = right.secondUnit

/-- Executable coupled-topology resolution succeeds exactly on the declaratively unambiguous
finite frames. -/
theorem localizedRule3CoupledTopologyResolution?_isSome_iff_unambiguous
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.localizedRule3CoupledTopologyResolution? keys).isSome = true ↔
      input.DeclarativeLocalizedRule3CoupledTopologyUnambiguous keys := by
  constructor
  · intro resolved left right leftDerived rightDerived
    have notAmbiguous :
        ¬ (left.firstUnit ≠ right.firstUnit ∨
          left.secondUnit ≠ right.secondUnit) := by
      intro different
      have refused : input.localizedRule3CoupledTopologyResolution? keys = none :=
        (input.localizedRule3CoupledTopologyResolution?_eq_none_iff_distinct_unit_pairs
          keys).mpr
          ⟨left, right,
            (input.mem_localizedRule3CoupledPerfectMatchings_iff keys left).mpr leftDerived,
            (input.mem_localizedRule3CoupledPerfectMatchings_iff keys right).mpr rightDerived,
            different⟩
      simp [refused] at resolved
    constructor
    · by_contra different
      exact notAmbiguous (Or.inl different)
    · by_contra different
      exact notAmbiguous (Or.inr different)
  · intro unambiguous
    cases observed : input.localizedRule3CoupledTopologyResolution? keys with
    | some resolution => rfl
    | none =>
        obtain ⟨left, right, leftPresent, rightPresent, different⟩ :=
          (input.localizedRule3CoupledTopologyResolution?_eq_none_iff_distinct_unit_pairs
            keys).mp observed
        have same := unambiguous left right
          ((input.mem_localizedRule3CoupledPerfectMatchings_iff keys left).mp leftPresent)
          ((input.mem_localizedRule3CoupledPerfectMatchings_iff keys right).mp rightPresent)
        exact (different.elim (fun false => false same.1)
          (fun false => false same.2)).elim

/-- Declarative topology applicability after the raw descriptor-bearing keys have been built. -/
def LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → List (input.LocalizedRerootCursor carrierFuel) → Prop
  | 0, _cursors => False
  | fuel + 1, cursors =>
      ∀ rawKeys,
        cursors.mapM
          (input.buildLocalizedRerootDescriptorBearingRule3Key?
            target view fuel []) = some rawKeys →
        input.DeclarativeLocalizedRule3CoupledTopologyUnambiguous rawKeys

/-- The former operational frame premise is exactly the new declarative uniqueness condition. -/
theorem localizedDescriptorBearingRule3FrameTopologyResolved_iff_declarativelyUnambiguous
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.LocalizedDescriptorBearingRule3FrameTopologyResolved
        target view fuel cursors ↔
      input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
        target view fuel cursors := by
  cases fuel with
  | zero => rfl
  | succ keyFuel =>
      constructor
      · intro resolved rawKeys rawComputed
        obtain ⟨topology, topologyComputed⟩ := resolved rawKeys rawComputed
        apply (input.localizedRule3CoupledTopologyResolution?_isSome_iff_unambiguous
          rawKeys).mp
        simp [topologyComputed]
      · intro unambiguous rawKeys rawComputed
        have resolutionPresent :
            (input.localizedRule3CoupledTopologyResolution? rawKeys).isSome = true :=
          (input.localizedRule3CoupledTopologyResolution?_isSome_iff_unambiguous
            rawKeys).mpr (unambiguous rawKeys rawComputed)
        exact Option.isSome_iff_exists.mp resolutionPresent

/-- Every non-four-cursor frame satisfies the declarative condition automatically. -/
theorem localizedDescriptorBearingRule3FrameDeclarativelyUnambiguous_of_length_ne_four
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (length : cursors.length ≠ 4) :
    input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
      target view (fuel + 1) cursors := by
  apply (input.localizedDescriptorBearingRule3FrameTopologyResolved_iff_declarativelyUnambiguous
    target view (fuel + 1) cursors).mp
  exact input.localizedDescriptorBearingRule3FrameTopologyResolved_of_length_ne_four
    target view fuel cursors length

/-- Frame totality with the operational topology premise replaced by independent uniqueness. -/
theorem exists_buildLocalizedDescriptorBearingRule3Frame?_of_twice_lt_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough
      target view maximumFuel)
    (frameFuel : Nat) (bounded : frameFuel ≤ maximumFuel)
    (covers : 2 * (carrierFuel + 1) < frameFuel)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (unambiguous : input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
      target view frameFuel cursors)
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor) :
    ∃ frame, input.buildLocalizedDescriptorBearingRule3Frame?
      target view frameFuel cursors = some frame := by
  apply input.exists_buildLocalizedDescriptorBearingRule3Frame?_of_twice_lt
    target view resolved frameFuel bounded covers cursors
  · exact
      (input.localizedDescriptorBearingRule3FrameTopologyResolved_iff_declarativelyUnambiguous
        target view frameFuel cursors).mpr unambiguous
  · exact valid

/-- The conservative finite budget is total under resolved node evidence, valid cursors, and the
declarative topology condition; no resolver-success assumption remains. -/
theorem exists_buildLocalizedDescriptorBearingRule3Frame?_at_conservativeFuel_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (unambiguous : input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) cursors)
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor) :
    ∃ frame, input.buildLocalizedDescriptorBearingRule3Frame?
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) cursors =
        some frame := by
  apply input.exists_buildLocalizedDescriptorBearingRule3Frame?_at_conservativeFuel
    target view resolved cursors
  · exact
      (input.localizedDescriptorBearingRule3FrameTopologyResolved_iff_declarativelyUnambiguous
        target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) cursors).mpr
        unambiguous
  · exact valid

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
