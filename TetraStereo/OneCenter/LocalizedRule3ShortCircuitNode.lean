import TetraStereo.OneCenter.LocalizedRule3FrameRootCoherence

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Topological permission for ordinary individual-bond geometry: a branched axis entry or a
complete one-bond terminal axis. This meaning is independent of the shortcut evaluator. -/
def LocalizedRule3OrdinaryRoute (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop :=
  input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence ∧
    ((∃ initial first second rest,
        input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
          (.branched initial first second rest)) ∨
      ∃ axis, input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence axis ∧
        axis.doubleBondCount = 1)

structure LocalizedRule3OrdinaryRouteCertificate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Type where
  valid : input.LocalizedRule3OrdinaryRoute occurrence

/-- Runtime topology inspection constructs its own ordinary-route evidence. -/
def localizedRule3OrdinaryRouteCertificate?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3OrdinaryRouteCertificate occurrence) :=
  if edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence then
    match entry : input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | some (.branched initial first second rest) =>
        some { valid := ⟨edge, Or.inl ⟨initial, first, second, rest,
          input.localizedRule3CumulatedAxisEntry?_sound occurrence _
            ((input.localizedRule3CumulatedAxisEntryExec?_eq_original occurrence).symm.trans entry)⟩⟩ }
    | some (.terminalStart _) =>
        match found : input.localizedRule3CumulatedEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
        | none => none
        | some axis =>
            if ordinary : axis.doubleBondCount = 1 then
              some { valid := ⟨edge, Or.inr ⟨axis,
                input.localizedRule3CumulatedEndpointCursorFrame?_sound
                  (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence axis
                  ((input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_original
                    _ occurrence).symm.trans found), ordinary⟩⟩ }
            else none
    | _ => none
  else none

/-- Only ordinary individual-bond geometry uses the short-circuit endpoint reader. All cyclic,
odd-cumulene, even-cumulene, omission and structural routes retain the original node reader. -/
def localizedRule3ShortCircuitNodeWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  match input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none => input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view callback excluded
  | some _ => do
      let result ← input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence view callback
      let observation := input.localizedRule3ShortCircuitSpatialObservation result
      pure (if excluded.contains observation.physicalUnitId then none else some observation)

/-- Independent successor meaning. Existing derivations remain admissible, and the added route
uses independently specified topology, strict constitutional priorities or full-key evidence,
and exact geometry. No constructor defines meaning as evaluator equality. -/
inductive DeclarativeLocalizedRule3ShortCircuitNodeWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option input.LocalizedRule3SpatialNodeResult → Prop where
  | original {observation}
      (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view FrameMeaning excluded occurrence observation) :
      input.DeclarativeLocalizedRule3ShortCircuitNodeWith
        target view FrameMeaning excluded occurrence observation
  | ordinary (route : input.LocalizedRule3OrdinaryRoute occurrence)
      (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
      (derived : input.DeclarativeLocalizedRule3ShortCircuitSpatialResult
        target occurrence view FrameMeaning result) :
      input.DeclarativeLocalizedRule3ShortCircuitNodeWith
        target view FrameMeaning excluded occurrence
        (if excluded.contains (input.localizedRule3ShortCircuitSpatialObservation result).physicalUnitId
          then none else some (input.localizedRule3ShortCircuitSpatialObservation result))

theorem localizedRule3ShortCircuitNodeWithExec?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackSound : ∀ cursors frame, callback cursors = some frame → FrameMeaning cursors frame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ShortCircuitNodeWithExec?
      target occurrence view callback excluded = some observation) :
    input.DeclarativeLocalizedRule3ShortCircuitNodeWith
      target view FrameMeaning excluded occurrence observation := by
  unfold localizedRule3ShortCircuitNodeWithExec? at computed
  cases routed : input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none =>
      simp only [routed] at computed
      apply DeclarativeLocalizedRule3ShortCircuitNodeWith.original
      exact input.localizedDescriptorBearingRule3NodeWith?_sound target occurrence view callback
        FrameMeaning callbackSound excluded observation
        ((input.localizedDescriptorBearingRule3NodeWithExec?_eq_original
          target occurrence view callback excluded).symm.trans computed)
  | some certificate =>
      cases spatial : input.localizedRule3ShortCircuitSpatialUnitWithExec?
          target occurrence view callback with
      | none => simp [routed, spatial] at computed
      | some result =>
          simp [routed, spatial] at computed
          subst observation
          simpa using (DeclarativeLocalizedRule3ShortCircuitNodeWith.ordinary
            (excluded := excluded) certificate.valid result
            (input.localizedRule3ShortCircuitSpatialUnitWithExec?_sound
              target occurrence view callback FrameMeaning callbackSound result spatial))

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
