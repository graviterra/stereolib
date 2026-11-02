import TetraStereo.OneCenter.LocalizedCyclicCumuleneOccurrenceBridge
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3Key

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Descriptor boundary for fully cyclic cumulative topology

The molecule-level bridge can now distinguish an ordinary ring-closing double-bond system from a
fully cyclic cumulene. Ordinary monocycles now use the independently specified P-93 omission or
required `E/Z` path. Fully cyclic cumulenes remain a distinct P-31 parent topology and cannot leak
into that open endpoint-pair descriptor analyzer.
-/

namespace CertifiedLocalizedCIPInput

/-- Every successful molecule-level cyclic route retains the exact local ring-closure computation
from which it arose. -/
theorem localizedRule3RingClosureMoleculeRoute?_eq_some_implies_ringClosure
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (route : input.LocalizedRule3RingClosureMoleculeRoute carrierFuel)
    (computed : input.localizedRule3RingClosureMoleculeRoute? occurrence = some route) :
    ∃ (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (closure : input.LocalizedRerootCursor carrierFuel),
      input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.ringClosure initial closure) := by
  unfold localizedRule3RingClosureMoleculeRoute? at computed
  cases entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence with
  | none => simp [entryComputed] at computed
  | some entry =>
      cases entry with
      | terminalStart initial => simp [entryComputed] at computed
      | internal initial previous => simp [entryComputed] at computed
      | branched initial first second rest => simp [entryComputed] at computed
      | ringClosure initial closure =>
          exact ⟨initial, closure, rfl⟩

/-- A fully cyclic P-31 component cannot be consumed by the ordinary-monocyclic `E/Z` branch of
the descriptor-bearing Rule-3 reader. This is an executable non-emission theorem, not a claim that
IUPAC permanently omits every possible descriptor for fully cyclic cumulenes. -/
theorem localizedDescriptorBearingRule3NodeWith?_eq_none_of_fullyCyclicRoute
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (component : input.LocalizedCyclicCumuleneComponent)
    (routeComputed : input.localizedRule3RingClosureMoleculeRoute? occurrence =
      some (.fullyCyclicCumulene initial closure component)) :
    input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded = none := by
  have authorityComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.fullyCyclicCumulene initial closure component) := by
    simp [localizedRule3CyclicAuthorityRoute?, routeComputed]
  have descriptorNone :=
    input.localizedRule3RequiredMonocyclicEZWith?_eq_none_of_fullyCyclic
      target occurrence view rule3FrameOf initial closure component authorityComputed
  obtain ⟨entryInitial, entryClosure, entryComputed⟩ :=
    input.localizedRule3RingClosureMoleculeRoute?_eq_some_implies_ringClosure
      occurrence (.fullyCyclicCumulene initial closure component) routeComputed
  have entryDerived := input.localizedRule3CumulatedAxisEntry?_sound occurrence
    (.ringClosure entryInitial entryClosure) entryComputed
  have edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
    cases entryDerived with
    | ringClosure topology closureTopology =>
        exact ⟨topology.1, entryInitial.right, entryInitial.left, topology.2.1,
          topology.2.2.1, topology.2.2.2.1⟩
  simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
    descriptorNone, authorityComputed]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
