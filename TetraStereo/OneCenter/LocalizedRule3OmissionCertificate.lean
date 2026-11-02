import TetraStereo.OneCenter.LocalizedRule3ShortCircuitNode

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- A topology-determined omission is successful for every endpoint callback and auxiliary view.
It does not mean an axial unit lacks a descriptor; it means this occurrence emits no planar Rule3
observation in the existing semantics. -/
structure LocalizedRule3OmissionCertificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : Type where
  ordinaryAbsent : input.localizedRule3OrdinaryRouteCertificate? occurrence = none
  original : ∀ (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) callback excluded,
    input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view callback excluded = some none

theorem LocalizedRule3OmissionCertificate.computed
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedRule3OmissionCertificate occurrence)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) callback excluded :
    input.localizedRule3ShortCircuitNodeWithExec?
      target occurrence view callback excluded = some none := by
  simp only [localizedRule3ShortCircuitNodeWithExec?, certificate.ordinaryAbsent]
  exact certificate.original target view callback excluded

/-- Discover internal-axis, even-axis terminal and permanent-monocycle omission routes from
molecular topology. No recursive comparison frame or successful descriptor is supplied. -/
def localizedRule3OmissionCertificate?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedRule3OmissionCertificate occurrence) :=
  if edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence then
    match entry : input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | some (.internal initial previousAxis) =>
        some
          { ordinaryAbsent := by simp [localizedRule3OrdinaryRouteCertificate?, edge, entry]
            original := by
              intro target view callback excluded
              rw [input.localizedDescriptorBearingRule3NodeWithExec?_eq_original]
              exact input.localizedDescriptorBearingRule3NodeWith?_of_internalCumulatedAxis
                target occurrence view callback excluded initial previousAxis edge
                ((input.localizedRule3CumulatedAxisEntryExec?_eq_original occurrence).symm.trans entry) }
    | some (.ringClosure initial closure) =>
        match route : input.localizedRule3CyclicAuthorityRouteExec? occurrence with
        | some (.ordinaryMonocyclicPolicy routeInitial routeClosure policyResult) =>
            if omitted : policyResult.policy = .permanentlyOmit then
              some
                { ordinaryAbsent := by simp [localizedRule3OrdinaryRouteCertificate?, edge, entry]
                  original := by
                    intro target view callback excluded
                    rw [input.localizedDescriptorBearingRule3NodeWithExec?_eq_original]
                    exact input.localizedDescriptorBearingRule3NodeWith?_of_omittedMonocycle
                      target occurrence view callback excluded initial closure routeInitial
                      routeClosure policyResult edge
                      ((input.localizedRule3CumulatedAxisEntryExec?_eq_original occurrence).symm.trans entry)
                      ((input.localizedRule3CyclicAuthorityRouteExec?_eq_original occurrence).symm.trans route)
                      omitted }
            else none
        | _ => none
    | some (.terminalStart initial) =>
        match axisComputed : input.localizedRule3CumulatedEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
        | none => none
        | some axis =>
            if notOrdinary : axis.doubleBondCount ≠ 1 then
              if notPlanar : ¬ Odd axis.doubleBondCount then
                some
                  { ordinaryAbsent := by
                      unfold localizedRule3OrdinaryRouteCertificate?
                      rw [dif_pos edge]
                      split <;> simp_all
                      split <;> simp_all
                    original := by
                      intro target view callback excluded
                      rw [input.localizedDescriptorBearingRule3NodeWithExec?_eq_original]
                      exact input.localizedDescriptorBearingRule3NodeWith?_of_evenCumulatedAxis
                        target occurrence view callback excluded initial axis edge
                        ((input.localizedRule3CumulatedAxisEntryExec?_eq_original occurrence).symm.trans entry)
                        ((input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_original _ occurrence).symm.trans
                          axisComputed) notOrdinary notPlanar }
              else none
            else none
    | _ => none
  else none

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
