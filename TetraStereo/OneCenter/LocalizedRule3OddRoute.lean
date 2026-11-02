import TetraStereo.OneCenter.LocalizedRule3ShortCircuitNode

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- A planar nonordinary cumulated axis, independently described by the existing molecular
axis relation. Ordinary one-bond units are handled by the existing shortcut route. -/
def LocalizedRule3OddRoute (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : Prop :=
  input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence ∧
    ∃ axis, input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence axis ∧
      axis.doubleBondCount ≠ 1 ∧ Odd axis.doubleBondCount

structure LocalizedRule3OddRouteCertificate (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : Type where
  valid : input.LocalizedRule3OddRoute occurrence

/-- Recognize exactly the original node's terminal odd-axis branch. The proof fields are
constructed from executable topology inspection, not supplied by a caller. -/
def localizedRule3OddRouteCertificate? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedRule3OddRouteCertificate occurrence) :=
  if edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence then
    match input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | some (.terminalStart _) =>
        match found : input.localizedRule3CumulatedEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
        | none => none
        | some axis =>
            if ordinary : axis.doubleBondCount = 1 then none
            else if odd : Odd axis.doubleBondCount then
              some { valid := ⟨edge, axis,
                input.localizedRule3CumulatedEndpointCursorFrame?_sound
                  (input.localizedRule3CumulatedTraversalFuel fuel) occurrence axis
                  ((input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_original
                    _ occurrence).symm.trans found), ordinary, odd⟩ }
            else none
    | _ => none
  else none

theorem ordinaryRoute_none_of_oddRoute
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (certificate : input.LocalizedRule3OddRouteCertificate occurrence)
    (routed : input.localizedRule3OddRouteCertificate? occurrence = some certificate) :
    input.localizedRule3OrdinaryRouteCertificate? occurrence = none := by
  unfold localizedRule3OddRouteCertificate? at routed
  split at routed
  next edge =>
    split at routed
    next initial entry =>
      split at routed
      next found => contradiction
      next axis found =>
        split at routed
        next ordinary => contradiction
        next notOrdinary =>
          simp only [localizedRule3OrdinaryRouteCertificate?, dif_pos edge]
          split <;> simp_all
          split <;> simp_all
    next => contradiction
  next => contradiction

/-- A selected odd route is the old eager odd-spatial branch with its original exclusion policy. -/
theorem originalNode_eq_odd_of_routeCertificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (certificate : input.LocalizedRule3OddRouteCertificate occurrence)
    (routed : input.localizedRule3OddRouteCertificate? occurrence = some certificate) :
    input.localizedDescriptorBearingRule3NodeWithExec? target occurrence view callback excluded =
      match input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
          target occurrence view callback with
      | none => none
      | some result =>
          let observation := input.localizedRule3OddCumuleneDescriptorBearingObservation result
          if excluded.contains observation.physicalUnitId then some none else some (some observation) := by
  unfold localizedRule3OddRouteCertificate? at routed
  split at routed
  next edge =>
    split at routed
    next initial entry =>
      split at routed
      next found => contradiction
      next axis found =>
        split at routed
        next ordinary => contradiction
        next notOrdinary =>
          split at routed
          next odd =>
            simp only [localizedDescriptorBearingRule3NodeWithExec?, dif_pos edge, entry, found,
              dif_neg notOrdinary, dif_pos odd]
            rfl
          next => contradiction
    next => contradiction
  next => contradiction

theorem shortNode_eq_odd_of_routeCertificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (certificate : input.LocalizedRule3OddRouteCertificate occurrence)
    (routed : input.localizedRule3OddRouteCertificate? occurrence = some certificate) :
    input.localizedRule3ShortCircuitNodeWithExec? target occurrence view callback excluded =
      match input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
          target occurrence view callback with
      | none => none
      | some result =>
          let observation := input.localizedRule3OddCumuleneDescriptorBearingObservation result
          if excluded.contains observation.physicalUnitId then some none else some (some observation) := by
  rw [localizedRule3ShortCircuitNodeWithExec?, input.ordinaryRoute_none_of_oddRoute occurrence certificate routed]
  exact input.originalNode_eq_odd_of_routeCertificate target occurrence view callback excluded certificate routed

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
