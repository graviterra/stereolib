import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CircularFrameTotality
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Totality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Circular-auxiliary integration through the Rule-6 endpoint

This module names exact circular ambiguity at the complete Rule-3 bound and transports it through
the Rules-1a--5 initial partition into the one-shot Rule-6 endpoint.  The initial partition has an
exact `none` characterization.  The final descriptor theorem is intentionally one-way because
Rule 6 has additional legitimate downstream refusal modes.
-/

/-- Two distinct independently valid coupled pairs in the uniquely generated raw Rule-3 frame at
the complete finite bound. -/
def AromaticCanonicalRule3ExactCircularAmbiguityAtTwice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) : Prop :=
  ∃ rawKeys first second,
    roots.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
      (2 * (carrierFuel + 1))) = some rawKeys ∧
    source.DeclarativeAromaticCanonicalRule3CoupledUnitPair rawKeys first ∧
    source.DeclarativeAromaticCanonicalRule3CoupledUnitPair rawKeys second ∧
    first ≠ second

/-- The named circular ambiguity proposition is exactly complete Rule-3 frame refusal. -/
theorem buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_none_iff_exactCircularAmbiguity_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame?
        (2 * (carrierFuel + 1)) roots = none ↔
      source.AromaticCanonicalRule3ExactCircularAmbiguityAtTwice roots := by
  exact source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_none_iff_ambiguous_at_twice
    resolved roots valid

/-- With four valid roots, the Rules-1a--5 partition refuses exactly on circular coupled-topology
ambiguity.  Rule-4/5 recursive key construction introduces no additional failure at this bound. -/
theorem buildAromaticCanonicalRule3Through5InitialPartition?_eq_none_iff_circularAmbiguity_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor) :
    source.buildAromaticCanonicalRule3Through5InitialPartition?
        target view (2 * (carrierFuel + 1)) roots = none ↔
      source.AromaticCanonicalRule3ExactCircularAmbiguityAtTwice roots := by
  constructor
  · intro partitionRefused
    have frameOrAmbiguity :=
      source.exists_canonicalRule3Frame_or_exact_ambiguity_at_twice
        resolved roots valid
    rcases frameOrAmbiguity with frameExists | ambiguity
    · obtain ⟨rawKeys, rawComputed, declarativeTopology⟩ :=
        (source.exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_iff_unambiguous_at_twice
          resolved roots valid).mp frameExists
      have topology : ∀ otherKeys,
          roots.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
            (2 * (carrierFuel + 1))) = some otherKeys →
          source.AromaticCanonicalRule3TopologyUnambiguous otherKeys := by
        intro otherKeys otherComputed
        have same : otherKeys = rawKeys :=
          Option.some.inj (otherComputed.symm.trans rawComputed)
        subst otherKeys
        exact (source.aromaticCanonicalRule3TopologyUnambiguous_iff_declarative
          rawKeys).mpr declarativeTopology
      have inputsResolved :
          source.AromaticCanonicalRule3Through5RootInputsResolved
            target view (2 * (carrierFuel + 1)) roots :=
        source.aromaticCanonicalRule3Through5RootInputsResolved_at_twice
          target view roots rootsLength valid resolved topology
      obtain ⟨partition, partitionComputed⟩ :=
        (source.exists_buildAromaticCanonicalRule3Through5InitialPartition_iff_inputsResolved
          target view (2 * (carrierFuel + 1)) roots).mpr inputsResolved
      rw [partitionRefused] at partitionComputed
      simp at partitionComputed
    · exact ambiguity
  · intro ambiguity
    have frameRefused :
        source.buildAromaticCanonicalRule3CanonicalKeyFrame?
            (2 * (carrierFuel + 1)) roots = none :=
      (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_none_iff_exactCircularAmbiguity_at_twice
        resolved roots valid).mpr ambiguity
    unfold buildAromaticCanonicalRule3Through5InitialPartition?
      buildAromaticCanonicalRule3Through5RootKeyFrame?
    simp [rootsLength, frameRefused]

/-- Entry into Rule 6 is exhaustive at the complete bound: either one canonical Rules-1a--5
partition exists or exact circular ambiguity is retained. -/
theorem exists_rule3Through5InitialPartition_or_circularAmbiguity_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor) :
    (∃ partition, source.buildAromaticCanonicalRule3Through5InitialPartition?
        target view (2 * (carrierFuel + 1)) roots = some partition) ∨
      source.AromaticCanonicalRule3ExactCircularAmbiguityAtTwice roots := by
  cases partitionComputed : source.buildAromaticCanonicalRule3Through5InitialPartition?
      target view (2 * (carrierFuel + 1)) roots with
  | none =>
      exact Or.inr
        ((source.buildAromaticCanonicalRule3Through5InitialPartition?_eq_none_iff_circularAmbiguity_at_twice
          target view roots rootsLength resolved valid).mp partitionComputed)
  | some partition => exact Or.inl ⟨partition, rfl⟩

/-- Exact circular ambiguity necessarily refuses the one-shot Rules-1a--6 descriptor before any
Rule-6 branch can be selected.  No converse is asserted: topology inadmissibility and unresolved
branch judgments remain separate legitimate Rule-6 refusals. -/
theorem aromaticCanonicalRule3Through6Descriptor?_eq_none_of_circularAmbiguity_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity)
    (rootsLength : roots.length = 4)
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor)
    (ambiguous : source.AromaticCanonicalRule3ExactCircularAmbiguityAtTwice roots) :
    source.aromaticCanonicalRule3Through6Descriptor?
        center target view (2 * (carrierFuel + 1)) roots parity = none := by
  have partitionRefused :
      source.buildAromaticCanonicalRule3Through5InitialPartition?
          target view (2 * (carrierFuel + 1)) roots = none :=
    (source.buildAromaticCanonicalRule3Through5InitialPartition?_eq_none_iff_circularAmbiguity_at_twice
      target view roots rootsLength resolved valid).mpr ambiguous
  simp [aromaticCanonicalRule3Through6Descriptor?, rootsLength, partitionRefused]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
