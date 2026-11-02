import TetraStereo.OneCenter.LocalizedRule3DemandSupport
import TetraStereo.OneCenter.LocalizedRule3EndpointDemandApplicability

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Bridge from pair frame demand support to exact endpoint demand

`LocalizedRule3DemandSupport` proves that demand-sensitive support makes the *actual*
descriptor-bearing frame builder total, and `LocalizedRule3EndpointDemandApplicability` factors
endpoint applicability down to a per-pair `LocalizedRule3ExactPairFrameSupport` certificate for the
two canonical reference cursors one endpoint really selects.  This module joins the two surfaces:
the exact-pair certificate demanded by an endpoint is *derived* from demand support for that very
pair, with the callback instantiated to the actual frame builder at the demanded fuel — no global
`LocalizedDescriptorBearingRule3PairFrameTotal` premise is used or assumed anywhere below.

The three results are:

* `LocalizedRule3ExactPairFrameSupport.of_frameDemandSupport`: frame demand support for the list
  `[firstCursor, secondCursor]` yields the exact-pair certificate for the callback
  `buildLocalizedDescriptorBearingRule3Frame? target view fuel`, using demand frame existence
  (`exists_buildLocalizedDescriptorBearingRule3Frame?_of_demandSupport`) plus the pre-existing
  arity theorem `buildLocalizedDescriptorBearingRule3Frame?_keys_length_eq`.

* `LocalizedRule3ExactPairEndpointDemand.of_frameDemandSupport`: two valid canonical endpoint
  references packaged with that pair demand give the endpoint-level exact-pair demand.

* `exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_frameDemandSupport`: the capstone,
  feeding that demand to the existing endpoint-compiler theorem so the real Rules-1a--5 endpoint
  compiler succeeds when the callback is the demanded frame builder.
-/

namespace CertifiedLocalizedCIPInput

/-- Frame demand support for one pair of cursors makes the *actual* descriptor-bearing frame
builder at that fuel an exact-pair support for the same pair.  The frame witness comes from the
demand-existence theorem and its two-key arity from the existing frame arity theorem; nothing
here quantifies over a validity universe or an arbitrary cursor pair. -/
theorem LocalizedRule3ExactPairFrameSupport.of_frameDemandSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (support : input.LocalizedRule3FrameDemandSupport
      target view fuel [firstCursor, secondCursor]) :
    input.LocalizedRule3ExactPairFrameSupport
      (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
      firstCursor secondCursor := by
  obtain ⟨frame, frameComputed⟩ :=
    input.exists_buildLocalizedDescriptorBearingRule3Frame?_of_demandSupport
      target view fuel [firstCursor, secondCursor] support
  exact ⟨frame, frameComputed, by
    simpa using input.buildLocalizedDescriptorBearingRule3Frame?_keys_length_eq
      target view fuel [firstCursor, secondCursor] frame frameComputed⟩

/-- Two canonical endpoint references together with pair frame demand support for their reference
cursors give the endpoint-level exact-pair demand, with the callback instantiated to the actual
frame builder at the demanded fuel. -/
theorem LocalizedRule3ExactPairEndpointDemand.of_frameDemandSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.Atom)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstCanonical : input.CanonicalLocalizedRule3ReferenceCursor endpointCursor firstCursor first)
    (secondCanonical :
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor secondCursor second)
    (support : input.LocalizedRule3FrameDemandSupport
      target view fuel [firstCursor, secondCursor]) :
    input.LocalizedRule3ExactPairEndpointDemand
      (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
      endpoint partner endpointCursor :=
  ⟨first, second, firstCursor, secondCursor, candidates, firstCanonical, secondCanonical,
    LocalizedRule3ExactPairFrameSupport.of_frameDemandSupport
      input target view fuel firstCursor secondCursor support⟩

/-- Capstone: pair frame demand support for an endpoint's two canonical reference cursors makes the
real Rules-1a--5 endpoint compiler succeed when the Rule-3 callback is the actual frame builder at
the demanded fuel.  This is the existing exact-pair endpoint theorem applied to the demand-derived
certificate. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_frameDemandSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.Atom)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstCanonical : input.CanonicalLocalizedRule3ReferenceCursor endpointCursor firstCursor first)
    (secondCanonical :
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor secondCursor second)
    (support : input.LocalizedRule3FrameDemandSupport
      target view fuel [firstCursor, secondCursor]) :
    ∃ frame,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
        endpoint partner endpointCursor = some frame :=
  input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_exactPairDemand
    target view (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
    endpoint partner endpointCursor
    (LocalizedRule3ExactPairEndpointDemand.of_frameDemandSupport
      input target view fuel endpoint partner endpointCursor first second
      firstCursor secondCursor candidates firstCanonical secondCanonical support)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
