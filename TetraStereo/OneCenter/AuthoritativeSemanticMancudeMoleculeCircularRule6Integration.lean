import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCircularRule6Integration
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6Totality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Molecule-level transport of circular Rule-3 ambiguity

The occurrence-level result is lifted through the endpoint that computes the final occurrence,
ligand frame, parity, scheduled auxiliary state, and dependency view internally.
-/

/-- When the molecule-derived four-root frame has exact circular ambiguity, the scheduled
Rules-1a--6 endpoint refuses before Rule-6 branch selection. -/
theorem aromaticCanonicalScheduledRule3Through6Descriptor?_eq_none_of_circularAmbiguity_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity)
    (rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some roots)
    (parityComputed : source.aromaticCanonicalRerootFrameParity? roots = some parity)
    (rootsLength : roots.length = 4)
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor)
    (ambiguous : source.AromaticCanonicalRule3ExactCircularAmbiguityAtTwice roots) :
    source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics (2 * (carrierFuel + 1)) center = none := by
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  have oneShotRefused :
      source.aromaticCanonicalRule3Through6Descriptor? center.1 target
          (source.aromaticCanonicalDependencyView state target)
          (2 * (carrierFuel + 1)) roots parity = none :=
    source.aromaticCanonicalRule3Through6Descriptor?_eq_none_of_circularAmbiguity_at_twice
      center.1 target (source.aromaticCanonicalDependencyView state target)
      roots parity rootsLength resolved valid ambiguous
  unfold aromaticCanonicalScheduledRule3Through6Descriptor?
  simp [target, rootsComputed, parityComputed, state, oneShotRefused]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
