import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial
import TetraStereo.OneCenter.LocalizedRule3OriginalSpatialExecutable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! Odd-cumulene endpoint shortcuts with independent topology and exact rational geometry.
No adjacent-endpoint bond test is imposed on the ends of a cumulated chain. -/

def localizedRule3ExtendedSpatialUnitOfPriorities?
  (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
  (leftPriority rightPriority : input.LocalizedRule3EndpointPriority) :
  Option input.LocalizedRule3DescriptorBearingSpatialUnitResult :=
  match leftPriority, rightPriority with
  | .nonstereogenic, _ | _, .nonstereogenic =>
      some { leftPriority, rightPriority, geometry := OfficialRule3Geometry.nonstereogenic }
  | .senior leftReference, .senior rightReference => do
      let leftPoint ← input.spatialPointAt? left
      let rightPoint ← input.spatialPointAt? right
      let leftReferencePoint ← input.spatialPointAt? leftReference
      let rightReferencePoint ← input.spatialPointAt? rightReference
      let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
        leftReferencePoint rightReferencePoint
      some { leftPriority, rightPriority, geometry }


def DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult) : Prop :=
  unit.leftPriority = leftPriority ∧
    unit.rightPriority = rightPriority ∧
    match leftPriority, rightPriority with
    | .nonstereogenic, _ | _, .nonstereogenic =>
        unit.geometry = OfficialRule3Geometry.nonstereogenic
    | .senior leftReference, .senior rightReference =>
        ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
          input.SemanticSpatialPointAt left leftPoint ∧
          input.SemanticSpatialPointAt right rightPoint ∧
          input.SemanticSpatialPointAt leftReference leftReferencePoint ∧
          input.SemanticSpatialPointAt rightReference rightReferencePoint ∧
          RationalRule3SpatialGeometry leftPoint rightPoint
            leftReferencePoint rightReferencePoint unit.geometry

theorem localizedRule3ExtendedSpatialUnitOfPriorities?_sound
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3ExtendedSpatialUnitOfPriorities?
      left right leftPriority rightPriority = some unit) :
    input.DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
      left right leftPriority rightPriority unit := by
  unfold localizedRule3ExtendedSpatialUnitOfPriorities? at computed
  unfold DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
  cases leftPriority with
  | nonstereogenic =>
      cases rightPriority with
      | nonstereogenic =>
          have hUnit : unit =
              { leftPriority := .nonstereogenic, rightPriority := .nonstereogenic,
                geometry := OfficialRule3Geometry.nonstereogenic } := by
            simpa using computed.symm
          subst hUnit
          exact ⟨rfl, rfl, rfl⟩
      | senior rightReference =>
          have hUnit : unit =
              { leftPriority := .nonstereogenic, rightPriority := .senior rightReference,
                geometry := OfficialRule3Geometry.nonstereogenic } := by
            simpa using computed.symm
          subst hUnit
          exact ⟨rfl, rfl, rfl⟩
  | senior leftReference =>
      cases rightPriority with
      | nonstereogenic =>
          have hUnit : unit =
              { leftPriority := .senior leftReference, rightPriority := .nonstereogenic,
                geometry := OfficialRule3Geometry.nonstereogenic } := by
            simpa using computed.symm
          subst hUnit
          exact ⟨rfl, rfl, rfl⟩
      | senior rightReference =>
          cases leftPointComputed : input.spatialPointAt? left with
          | none => simp [leftPointComputed] at computed
          | some leftPoint =>
              cases rightPointComputed : input.spatialPointAt? right with
              | none => simp [leftPointComputed, rightPointComputed] at computed
              | some rightPoint =>
                  cases leftReferencePointComputed :
                      input.spatialPointAt? leftReference with
                  | none =>
                      simp [leftPointComputed, rightPointComputed,
                        leftReferencePointComputed] at computed
                  | some leftReferencePoint =>
                      cases rightReferencePointComputed :
                          input.spatialPointAt? rightReference with
                      | none =>
                          simp [leftPointComputed, rightPointComputed,
                            leftReferencePointComputed,
                            rightReferencePointComputed] at computed
                      | some rightReferencePoint =>
                          cases geometryComputed : rule3GeometryOfSpatialReferences?
                              leftPoint rightPoint leftReferencePoint
                              rightReferencePoint with
                          | none =>
                              simp [leftPointComputed, rightPointComputed,
                                leftReferencePointComputed,
                                rightReferencePointComputed,
                                geometryComputed] at computed
                          | some geometry =>
                              have hUnit : unit =
                                  { leftPriority := .senior leftReference,
                                    rightPriority := .senior rightReference,
                                    geometry } := by
                                simpa [leftPointComputed, rightPointComputed,
                                  leftReferencePointComputed,
                                  rightReferencePointComputed, geometryComputed]
                                  using computed.symm
                              subst hUnit
                              refine ⟨rfl, rfl,
                                leftPoint, rightPoint, leftReferencePoint,
                                rightReferencePoint, ?_, ?_, ?_, ?_, ?_⟩
                              · exact (input.spatialPointAt?_eq_some_iff left
                                  leftPoint).mp leftPointComputed
                              · exact (input.spatialPointAt?_eq_some_iff right
                                  rightPoint).mp rightPointComputed
                              · exact (input.spatialPointAt?_eq_some_iff leftReference
                                  leftReferencePoint).mp leftReferencePointComputed
                              · exact (input.spatialPointAt?_eq_some_iff rightReference
                                  rightReferencePoint).mp rightReferencePointComputed
                              · exact (rule3GeometryOfSpatialReferences?_eq_some_iff
                                  leftPoint rightPoint leftReferencePoint
                                  rightReferencePoint geometry).mp geometryComputed

structure LocalizedRule3ShortCircuitOddSpatialResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel
  leftEndpoint : input.LocalizedRule3ShortCircuitEndpointResult
  rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult
  unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult

def localizedRule3ShortCircuitOddSpatialUnitWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3OddCumuleneEndpointCursorFrameExec?
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence
  let leftEndpoint ← input.localizedRule3ShortCircuitEndpointPriorityExec?
    target view callback topology.initial.left topology.initial.right topology.initial.leftCursor
  let rightEndpoint ← input.localizedRule3ShortCircuitEndpointPriorityExec?
    target view callback topology.right topology.rightPartner topology.rightCursor
  let unit ← input.localizedRule3ExtendedSpatialUnitOfPriorities?
    topology.initial.left topology.right leftEndpoint.priority rightEndpoint.priority
  some { topology, leftEndpoint, rightEndpoint, unit }

def DeclarativeLocalizedRule3ShortCircuitOddSpatialResult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Meaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence result.topology ∧
  input.DeclarativeLocalizedRule3ShortCircuitEndpointResult target view Meaning
    result.topology.initial.left result.topology.initial.right result.topology.initial.leftCursor
    result.leftEndpoint ∧
  input.DeclarativeLocalizedRule3ShortCircuitEndpointResult target view Meaning
    result.topology.right result.topology.rightPartner result.topology.rightCursor
    result.rightEndpoint ∧
  input.DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
    result.topology.initial.left result.topology.right
    result.leftEndpoint.priority result.rightEndpoint.priority result.unit

theorem localizedRule3ShortCircuitOddSpatialUnitWithExec?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Meaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackSound : ∀ cursors frame, callback cursors = some frame → Meaning cursors frame)
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel)
    (computed : input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view callback = some result) :
    input.DeclarativeLocalizedRule3ShortCircuitOddSpatialResult
      target occurrence view Meaning result := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec? at computed
  simp only [localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original,
    ← localizedRule3ShortCircuitEndpointPriority?_eq_localizedRule3ShortCircuitEndpointPriorityExec?] at computed
  cases ht : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [ht] at computed
  | some t =>
    cases hl : input.localizedRule3ShortCircuitEndpointPriority?
        target view callback t.initial.left t.initial.right t.initial.leftCursor with
    | none => simp [ht, hl] at computed
    | some l =>
      cases hr : input.localizedRule3ShortCircuitEndpointPriority?
          target view callback t.right t.rightPartner t.rightCursor with
      | none => simp [ht, hl, hr] at computed
      | some r =>
        cases hu : input.localizedRule3ExtendedSpatialUnitOfPriorities?
            t.initial.left t.right l.priority r.priority with
        | none => simp [ht, hl, hr, hu] at computed
        | some u =>
          simp [ht, hl, hr, hu] at computed
          subst result
          exact ⟨input.localizedRule3OddCumuleneEndpointCursorFrame?_sound _ _ _ ht,
            input.localizedRule3ShortCircuitEndpointPriority?_sound
              target view callback Meaning callbackSound _ _ _ _ hl,
            input.localizedRule3ShortCircuitEndpointPriority?_sound
              target view callback Meaning callbackSound _ _ _ _ hr,
            input.localizedRule3ExtendedSpatialUnitOfPriorities?_sound _ _ _ _ _ hu⟩

def localizedRule3ShortCircuitOddSpatialObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel) :
    input.LocalizedRule3SpatialNodeResult :=
  { left := result.topology.initial.left
    right := result.topology.right
    unit := {
      leftReference := match result.unit.leftPriority with
        | .senior reference => reference
        | .nonstereogenic => result.leftEndpoint.firstCandidate
      rightReference := match result.unit.rightPriority with
        | .senior reference => reference
        | .nonstereogenic => result.rightEndpoint.firstCandidate
      geometry := result.unit.geometry } }

/-- Old successful outputs are preserved under the existing endpoint coherence contracts.
No claim is made that old refusals remain refusals. -/
theorem localizedRule3ShortCircuitOddSpatialObservation_eq_of_parameterizedWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (old : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
      target occurrence view callback = some old)
    (leftExact : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      old.leftCompilation.endpointFrame old.leftCompilation.firstCursor old.leftCompilation.secondCursor)
    (rightExact : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      old.rightCompilation.endpointFrame old.rightCompilation.firstCursor old.rightCompilation.secondCursor)
    (leftConstitutional : input.LocalizedRule3EndpointConstitutionalExact old.leftCompilation)
    (rightConstitutional : input.LocalizedRule3EndpointConstitutionalExact old.rightCompilation) :
    ∃ result, input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view callback = some result ∧
      input.localizedRule3ShortCircuitOddSpatialObservation result =
        input.localizedRule3OddCumuleneDescriptorBearingObservation old := by
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith? at computed
  cases ht : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [ht] at computed
  | some t =>
    cases hl : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view callback t.initial.left t.initial.right t.initial.leftCursor with
    | none => simp [ht, hl] at computed
    | some l =>
      cases hr : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view callback t.right t.rightPartner t.rightCursor with
      | none => simp [ht, hl, hr] at computed
      | some r =>
        cases hu : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
            t.initial.left t.right l.endpointFrame r.endpointFrame with
        | none => simp [ht, hl, hr, hu] at computed
        | some u =>
          simp [ht, hl, hr, hu] at computed
          subst old
          have hls := input.localizedRule3ShortCircuitEndpointPriority?_eq_of_compiled
            target view callback _ _ _ l leftExact leftConstitutional hl
          have hrs := input.localizedRule3ShortCircuitEndpointPriority?_eq_of_compiled
            target view callback _ _ _ r rightExact rightConstitutional hr
          refine ⟨⟨t,
            ⟨input.localizedRule3EndpointPriority l.endpointFrame, l.endpointFrame.first⟩,
            ⟨input.localizedRule3EndpointPriority r.endpointFrame, r.endpointFrame.first⟩,
            u⟩, ?_, ?_⟩
          · unfold localizedRule3ShortCircuitOddSpatialUnitWithExec?
            simp only [localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original,
              ← localizedRule3ShortCircuitEndpointPriority?_eq_localizedRule3ShortCircuitEndpointPriorityExec?,
              ht, hls, hrs, bind, Option.bind]
            change (input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
              t.initial.left t.right l.endpointFrame r.endpointFrame >>= _) = _
            rw [hu]
            rfl
          · rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
