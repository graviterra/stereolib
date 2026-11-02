import TetraStereo.OneCenter.LocalizedRule3ParameterizedEndpoint
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitEndpoint
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitExecutable
import TetraStereo.OneCenter.LocalizedRule3PhysicalTopologyExecutable

set_option autoImplicit false

namespace TetraStereo.OneCenter





































namespace CertifiedLocalizedCIPInput

/-- Pure priority-keyed Rule-3 geometry for one physical double bond.  This is the exact decision
skeleton of `localizedRule3DescriptorBearingSpatialUnit?` with the two complete endpoint selectors
exposed as arguments.  Its only ingredients are the physical bond check, the executable coordinate
reader `spatialPointAt?` and the exact rational classifier, so it is an ordinary `def`. -/
def localizedRule3DescriptorBearingSpatialUnitOfPriorities?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority) :
    Option input.LocalizedRule3DescriptorBearingSpatialUnitResult :=
  if input.moleculeGraph.bond left right = 2 then
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
  else none

/-- The descriptor-bearing unit compiler factors exactly through its priority skeleton: the
complete endpoint selectors are its only endpoint input. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_factorization
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame) :
    input.localizedRule3DescriptorBearingSpatialUnit? left right leftFrame rightFrame =
      input.localizedRule3DescriptorBearingSpatialUnitOfPriorities? left right
        (input.localizedRule3EndpointPriority leftFrame)
        (input.localizedRule3EndpointPriority rightFrame) := by
  unfold localizedRule3DescriptorBearingSpatialUnit?
    localizedRule3DescriptorBearingSpatialUnitOfPriorities?
  rfl

/-- Minimal double-bond unit: the two short-circuit endpoint results together with the projected
descriptor-bearing core (its two complete priorities and the exact rational geometry).  No complete
endpoint key frame is fabricated anywhere in this type. -/
structure LocalizedRule3ShortCircuitSpatialUnitResult (input : CertifiedLocalizedCIPInput) where
  left : input.LocalizedRule3ShortCircuitEndpointResult
  right : input.LocalizedRule3ShortCircuitEndpointResult
  core : input.LocalizedRule3DescriptorBearingSpatialUnitResult
  deriving DecidableEq, Repr

/-- Forget the minimal provenance witnesses, keeping exactly the priority-keyed unit result the old
descriptor-bearing compiler returns. -/
def shortCircuitUnitToDescriptorBearing (input : CertifiedLocalizedCIPInput)
    (unit : input.LocalizedRule3ShortCircuitSpatialUnitResult) :
    input.LocalizedRule3DescriptorBearingSpatialUnitResult :=
  unit.core

/-- Exact geometry of one physical double bond from two minimal endpoint results.  The physical
double-bond check, the coordinate lookups, and the exact classifier are those of the old
descriptor-bearing compiler. -/
def localizedRule3ShortCircuitSpatialUnit?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult) :
    Option input.LocalizedRule3ShortCircuitSpatialUnitResult :=
  (input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
    left right leftEndpoint.priority rightEndpoint.priority).map fun core =>
    { left := leftEndpoint, right := rightEndpoint, core }

/-- On a successful priority skeleton the minimal unit is exactly the two endpoint results carrying
that priority-keyed core. -/
theorem localizedRule3ShortCircuitSpatialUnit?_eq_some_of_priorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (core : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
      left right leftEndpoint.priority rightEndpoint.priority = some core) :
    input.localizedRule3ShortCircuitSpatialUnit? left right leftEndpoint rightEndpoint =
      some { left := leftEndpoint, right := rightEndpoint, core } := by
  unfold localizedRule3ShortCircuitSpatialUnit?
  rw [computed]
  rfl

/-- The minimal unit computation projects onto exactly the priority-keyed skeleton computation. -/
theorem localizedRule3ShortCircuitSpatialUnit?_toDescriptorBearing
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (unit : input.LocalizedRule3ShortCircuitSpatialUnitResult)
    (computed : input.localizedRule3ShortCircuitSpatialUnit?
      left right leftEndpoint rightEndpoint = some unit) :
    input.localizedRule3DescriptorBearingSpatialUnitOfPriorities? left right
        leftEndpoint.priority rightEndpoint.priority =
      some (shortCircuitUnitToDescriptorBearing input unit) := by
  unfold localizedRule3ShortCircuitSpatialUnit? at computed
  cases coreComputed : input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
      left right leftEndpoint.priority rightEndpoint.priority with
  | none => simp [coreComputed] at computed
  | some core =>
      rw [coreComputed] at computed
      have hUnit : unit = { left := leftEndpoint, right := rightEndpoint, core := core } := by
        simpa using computed.symm
      rw [hUnit]
      rfl

/-- Independent complete-priority and exact rational-geometry meaning of the priority-keyed
double-bond classifier.  The geometry clause is the physical double bond itself, the direct
semantic coordinates of the two endpoints and of the two senior references, and the exact rational
`seqcis`/`seqtrans` relation; a nonstereogenic endpoint priority retains the physical bond and
asserts exactly the nonstereogenic geometry. -/
def DeclarativeLocalizedRule3DescriptorBearingSpatialUnitOfPriorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult) : Prop :=
  unit.leftPriority = leftPriority ∧
    unit.rightPriority = rightPriority ∧
    input.moleculeGraph.bond left right = 2 ∧
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

/-- Every successful priority-keyed spatial computation has its independent meaning. -/
theorem localizedRule3DescriptorBearingSpatialUnitOfPriorities?_sound
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
      left right leftPriority rightPriority = some unit) :
    input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnitOfPriorities
      left right leftPriority rightPriority unit := by
  unfold localizedRule3DescriptorBearingSpatialUnitOfPriorities? at computed
  unfold DeclarativeLocalizedRule3DescriptorBearingSpatialUnitOfPriorities
  by_cases doubleBond : input.moleculeGraph.bond left right = 2
  · rw [if_pos doubleBond] at computed
    cases leftPriority with
    | nonstereogenic =>
        cases rightPriority with
        | nonstereogenic =>
            have hUnit : unit =
                { leftPriority := .nonstereogenic, rightPriority := .nonstereogenic,
                  geometry := OfficialRule3Geometry.nonstereogenic } := by
              simpa using computed.symm
            subst hUnit
            exact ⟨rfl, rfl, doubleBond, rfl⟩
        | senior rightReference =>
            have hUnit : unit =
                { leftPriority := .nonstereogenic, rightPriority := .senior rightReference,
                  geometry := OfficialRule3Geometry.nonstereogenic } := by
              simpa using computed.symm
            subst hUnit
            exact ⟨rfl, rfl, doubleBond, rfl⟩
    | senior leftReference =>
        cases rightPriority with
        | nonstereogenic =>
            have hUnit : unit =
                { leftPriority := .senior leftReference, rightPriority := .nonstereogenic,
                  geometry := OfficialRule3Geometry.nonstereogenic } := by
              simpa using computed.symm
            subst hUnit
            exact ⟨rfl, rfl, doubleBond, rfl⟩
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
                                refine ⟨rfl, rfl, doubleBond,
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
  · rw [if_neg doubleBond] at computed
    simp at computed

/-- A successful priority-keyed unit records exactly the two priorities it was given; this is the
first two conjuncts of its independent meaning. -/
theorem localizedRule3DescriptorBearingSpatialUnitOfPriorities?_priorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
      left right leftPriority rightPriority = some unit) :
    unit.leftPriority = leftPriority ∧ unit.rightPriority = rightPriority := by
  have derived := input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_sound
    left right leftPriority rightPriority unit computed
  exact ⟨derived.1, derived.2.1⟩

/-- A successful descriptor-bearing unit records exactly the two complete endpoint priorities it
was given.  This is the bridge that lets the projected unit of an older occurrence result be
compared with the projected unit of the new short-circuit result. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_priorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3DescriptorBearingSpatialUnit?
      left right leftFrame rightFrame = some unit) :
    unit.leftPriority = input.localizedRule3EndpointPriority leftFrame ∧
      unit.rightPriority = input.localizedRule3EndpointPriority rightFrame := by
  rw [input.localizedRule3DescriptorBearingSpatialUnit?_factorization
    left right leftFrame rightFrame] at computed
  exact input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_priorities
    left right (input.localizedRule3EndpointPriority leftFrame)
    (input.localizedRule3EndpointPriority rightFrame) unit computed

namespace DeclarativeLocalizedRule3RootObservation

/-- A fresh root observation is always a strict senior reading: an equal first sphere is `defer` and
is never classified as nonstereogenic by the root comparison alone. -/
theorem exists_senior
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {first second : input.Atom}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    {priority : input.LocalizedRule3EndpointPriority}
    (derived : input.DeclarativeLocalizedRule3RootObservation
      first second firstCursor secondCursor priority) :
    ∃ reference, priority = .senior reference := by
  cases derived with
  | firstSenior _ => exact ⟨first, rfl⟩
  | secondSenior _ => exact ⟨second, rfl⟩

end DeclarativeLocalizedRule3RootObservation

/-- The only source of a nonstereogenic endpoint priority is the deferred complete key frame, which
is reached only after a root tie. A strict root or constitutional reading is never nonstereogenic. -/
theorem declarativeLocalizedRule3ShortCircuitEndpointResult_nonstereogenic_imp_fullKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (derived : input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view Rule3FrameMeaning endpoint partner endpointCursor result)
    (nonstereogenic : result.priority = .nonstereogenic) :
    ∃ frame, input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
        target view Rule3FrameMeaning endpoint partner endpointCursor frame ∧
      result =
        { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
          firstCandidate := frame.endpointFrame.first } := by
  cases derived with
  | rootRule1aStrict actualPair firstReference secondReference fresh =>
      obtain ⟨reference, senior⟩ := fresh.exists_senior
      have strict : LocalizedRule3EndpointPriority.senior reference = .nonstereogenic :=
        senior.symm.trans nonstereogenic
      exact absurd strict (by simp)
  | constitutionalStrict _ _ _ _ _ strict =>
      rcases strict with ⟨_, priority⟩ | ⟨_, priority⟩
      · simp [priority] at nonstereogenic
      · simp [priority] at nonstereogenic
  | fullKey frame derivedFrame deferred =>
      exact ⟨frame, derivedFrame, rfl⟩

/-- Independent meaning of one minimal double-bond unit: both short-circuit endpoint results are
recovered with their independent relations, the physical double bond is present, and the exact
rational geometry is the priority-keyed skeleton applied to the two complete endpoint priorities of
the projected core.  No complete endpoint key frame is required or asserted. -/
def DeclarativeLocalizedRule3ShortCircuitSpatialUnit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (left right : input.Atom)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (unit : input.LocalizedRule3ShortCircuitSpatialUnitResult) : Prop :=
  unit.left = leftEndpoint ∧
    unit.right = rightEndpoint ∧
    input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view Rule3FrameMeaning left right leftCursor leftEndpoint ∧
    input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view Rule3FrameMeaning right left rightCursor rightEndpoint ∧
    input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnitOfPriorities
      left right leftEndpoint.priority rightEndpoint.priority
      (shortCircuitUnitToDescriptorBearing input unit)

/-- Every successful minimal unit computation has its independent meaning, given the two endpoint
relations.  Both endpoint relations are inputs: they are supplied by endpoint soundness under the
same Rule-3 frame callback, never assumed here. -/
theorem localizedRule3ShortCircuitSpatialUnit?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (left right : input.Atom)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (unit : input.LocalizedRule3ShortCircuitSpatialUnitResult)
    (leftDerived : input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view Rule3FrameMeaning left right leftCursor leftEndpoint)
    (rightDerived : input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view Rule3FrameMeaning right left rightCursor rightEndpoint)
    (computed : input.localizedRule3ShortCircuitSpatialUnit?
      left right leftEndpoint rightEndpoint = some unit) :
    input.DeclarativeLocalizedRule3ShortCircuitSpatialUnit target view Rule3FrameMeaning
      left right leftCursor rightCursor leftEndpoint rightEndpoint unit := by
  unfold localizedRule3ShortCircuitSpatialUnit? at computed
  cases coreComputed : input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
      left right leftEndpoint.priority rightEndpoint.priority with
  | none => simp [coreComputed] at computed
  | some core =>
      rw [coreComputed] at computed
      have hUnit : unit = { left := leftEndpoint, right := rightEndpoint, core := core } := by
        simpa using computed.symm
      rw [hUnit]
      refine ⟨rfl, rfl, leftDerived, rightDerived, ?_⟩
      exact input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_sound
        left right leftEndpoint.priority rightEndpoint.priority core coreComputed

/-- The exact rational classifier never manufactures `nonstereogenic`: a successful minimal unit is
nonstereogenic in geometry only if one of the two endpoint priorities already is, i.e. only through
the deferred full-key tie of the endpoint layer. -/
theorem localizedRule3ShortCircuitSpatialUnit?_geometry_nonstereogenic_imp
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (unit : input.LocalizedRule3ShortCircuitSpatialUnitResult)
    (computed : input.localizedRule3ShortCircuitSpatialUnit?
      left right leftEndpoint rightEndpoint = some unit)
    (nonstereogenic : (shortCircuitUnitToDescriptorBearing input unit).geometry =
      OfficialRule3Geometry.nonstereogenic) :
    leftEndpoint.priority = .nonstereogenic ∨ rightEndpoint.priority = .nonstereogenic := by
  have coreComputed := input.localizedRule3ShortCircuitSpatialUnit?_toDescriptorBearing
    left right leftEndpoint rightEndpoint unit computed
  have coreDerived := input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_sound
    left right leftEndpoint.priority rightEndpoint.priority
    (shortCircuitUnitToDescriptorBearing input unit) coreComputed
  cases hLeft : leftEndpoint.priority with
  | nonstereogenic => exact Or.inl rfl
  | senior leftReference =>
      cases hRight : rightEndpoint.priority with
      | nonstereogenic => exact Or.inr rfl
      | senior rightReference =>
          simp only [hLeft, hRight] at coreDerived
          rcases coreDerived with ⟨_, _, _, leftPoint, rightPoint, leftReferencePoint,
            rightReferencePoint, _, _, _, _, spatial⟩
          rw [nonstereogenic] at spatial
          exact spatial.2.elim

/-- Fully short-circuit occurrence result for one physical Rule-3 carrier occurrence: the recovered
topology, the two minimal endpoint results, and the minimal unit.  No complete endpoint key frame is
fabricated. -/
structure LocalizedRule3ShortCircuitSpatialResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel
  leftEndpoint : input.LocalizedRule3ShortCircuitEndpointResult
  rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult
  unit : input.LocalizedRule3ShortCircuitSpatialUnitResult

/-- Recover the physical endpoint topology and classify it from the two short-circuited endpoint
priorities.  This is `noncomputable` only through the topology recovery and the endpoint compiler,
which inherit that status from their own modules. -/
noncomputable def localizedRule3ShortCircuitSpatialUnitWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3PhysicalEndpointCursorFrame? occurrence
  let leftEndpoint ← input.localizedRule3ShortCircuitEndpointPriority?
    target view rule3FrameOf topology.left topology.right topology.leftCursor
  let rightEndpoint ← input.localizedRule3ShortCircuitEndpointPriority?
    target view rule3FrameOf topology.right topology.left topology.rightCursor
  let unit ← input.localizedRule3ShortCircuitSpatialUnit?
    topology.left topology.right leftEndpoint rightEndpoint
  some { topology, leftEndpoint, rightEndpoint, unit }

/-- Independent end-to-end meaning of a successful short-circuit occurrence result. -/
def DeclarativeLocalizedRule3ShortCircuitSpatialResult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence result.topology ∧
    input.DeclarativeLocalizedRule3ShortCircuitSpatialUnit target view Rule3FrameMeaning
      result.topology.left result.topology.right result.topology.leftCursor
      result.topology.rightCursor result.leftEndpoint result.rightEndpoint result.unit

/-- Every successful short-circuit occurrence computation has its independent meaning under any
sound Rule-3 frame callback.  Only the callback contract is used; the older eager full-frame
occurrence relation is not asserted. -/
theorem localizedRule3ShortCircuitSpatialUnitWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (computed : input.localizedRule3ShortCircuitSpatialUnitWith?
      target occurrence view rule3FrameOf = some result) :
    input.DeclarativeLocalizedRule3ShortCircuitSpatialResult
      target occurrence view Rule3FrameMeaning result := by
  unfold localizedRule3ShortCircuitSpatialUnitWith? at computed
  cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => simp [topologyComputed] at computed
  | some topology =>
      cases leftComputed : input.localizedRule3ShortCircuitEndpointPriority?
          target view rule3FrameOf topology.left topology.right topology.leftCursor with
      | none => simp [topologyComputed, leftComputed] at computed
      | some leftEndpoint =>
          cases rightComputed : input.localizedRule3ShortCircuitEndpointPriority?
              target view rule3FrameOf topology.right topology.left topology.rightCursor with
          | none => simp [topologyComputed, leftComputed, rightComputed] at computed
          | some rightEndpoint =>
              cases unitComputed : input.localizedRule3ShortCircuitSpatialUnit?
                  topology.left topology.right leftEndpoint rightEndpoint with
              | none =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    unitComputed] at computed
              | some unit =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    unitComputed] at computed
                  have hResult : result =
                      { topology := topology
                        leftEndpoint := leftEndpoint
                        rightEndpoint := rightEndpoint
                        unit := unit } := by
                    simpa using computed.symm
                  subst hResult
                  exact ⟨
                    input.localizedRule3PhysicalEndpointCursorFrame?_sound
                      occurrence topology topologyComputed,
                    input.localizedRule3ShortCircuitSpatialUnit?_sound
                      target view Rule3FrameMeaning topology.left topology.right
                      topology.leftCursor topology.rightCursor leftEndpoint rightEndpoint unit
                      (input.localizedRule3ShortCircuitEndpointPriority?_sound
                        target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                        topology.left topology.right topology.leftCursor
                        leftEndpoint leftComputed)
                      (input.localizedRule3ShortCircuitEndpointPriority?_sound
                        target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                        topology.right topology.left topology.rightCursor
                        rightEndpoint rightComputed)
                      unitComputed⟩

/-- Project a minimal occurrence result to the established identity-aware Rule-3 observation type.
On a nonstereogenic endpoint the minimal first candidate is retained only as an inert provenance
witness; priority depends solely on `geometry`. -/
def localizedRule3ShortCircuitSpatialObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) :
    input.LocalizedRule3SpatialNodeResult :=
  { left := result.topology.left
    right := result.topology.right
    unit :=
      { leftReference := match result.leftEndpoint.priority with
          | .senior reference => reference
          | .nonstereogenic => result.leftEndpoint.firstCandidate
        rightReference := match result.rightEndpoint.priority with
          | .senior reference => reference
          | .nonstereogenic => result.rightEndpoint.firstCandidate
        geometry := result.unit.core.geometry } }

@[simp] theorem localizedRule3ShortCircuitSpatialObservation_geometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) :
    (input.localizedRule3ShortCircuitSpatialObservation result).unit.geometry =
      result.unit.core.geometry := rfl

/-- On root coherence of both compiled endpoint frames, an older successful parameterized
descriptor-bearing occurrence computation is reproduced by the short-circuit evaluator, with the
same topology, the compiled endpoint priorities, and the same rational unit geometry.  This is a
conservativity statement: no new success is claimed and no old full-frame relation is asserted for
the short-circuit result. -/
theorem localizedRule3ShortCircuitSpatialUnitWith?_of_parameterizedWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (resultOld : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (computedOld : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
      target occurrence view rule3FrameOf = some resultOld)
    (leftCoherent : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      resultOld.leftCompilation.endpointFrame resultOld.leftCompilation.firstCursor
      resultOld.leftCompilation.secondCursor)
    (rightCoherent : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      resultOld.rightCompilation.endpointFrame resultOld.rightCompilation.firstCursor
      resultOld.rightCompilation.secondCursor)
    (leftConstitutional : input.LocalizedRule3EndpointConstitutionalExact resultOld.leftCompilation)
    (rightConstitutional : input.LocalizedRule3EndpointConstitutionalExact resultOld.rightCompilation) :
    ∃ resultNew, input.localizedRule3ShortCircuitSpatialUnitWith?
        target occurrence view rule3FrameOf = some resultNew ∧
      resultNew.topology = resultOld.topology ∧
      resultNew.leftEndpoint.priority = resultOld.unit.leftPriority ∧
      resultNew.rightEndpoint.priority = resultOld.unit.rightPriority ∧
      resultNew.leftEndpoint.firstCandidate = resultOld.leftCompilation.endpointFrame.first ∧
      resultNew.rightEndpoint.firstCandidate = resultOld.rightCompilation.endpointFrame.first ∧
      resultNew.unit.core.geometry = resultOld.unit.geometry := by
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnitWith? at computedOld
  cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => simp [topologyComputed] at computedOld
  | some topology =>
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf topology.left topology.right topology.leftCursor with
      | none => simp [topologyComputed, leftComputed] at computedOld
      | some leftCompilation =>
          cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf topology.right topology.left topology.rightCursor with
          | none => simp [topologyComputed, leftComputed, rightComputed] at computedOld
          | some rightCompilation =>
              cases unitComputed : input.localizedRule3DescriptorBearingSpatialUnit?
                  topology.left topology.right leftCompilation.endpointFrame
                    rightCompilation.endpointFrame with
              | none =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    unitComputed] at computedOld
              | some unit =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    unitComputed] at computedOld
                  have hOld : resultOld =
                      { topology := topology
                        leftCompilation := leftCompilation
                        rightCompilation := rightCompilation
                        unit := unit } := by
                    simpa using computedOld.symm
                  subst hOld
                  have hPrios := input.localizedRule3DescriptorBearingSpatialUnit?_priorities
                    topology.left topology.right leftCompilation.endpointFrame
                    rightCompilation.endpointFrame unit unitComputed
                  have leftShortCircuit :=
                    input.localizedRule3ShortCircuitEndpointPriority?_eq_of_compiled
                      target view rule3FrameOf topology.left topology.right
                      topology.leftCursor leftCompilation leftCoherent leftConstitutional leftComputed
                  have rightShortCircuit :=
                    input.localizedRule3ShortCircuitEndpointPriority?_eq_of_compiled
                      target view rule3FrameOf topology.right topology.left
                      topology.rightCursor rightCompilation rightCoherent rightConstitutional rightComputed
                  have coreComputed : input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
                      topology.left topology.right
                      (input.localizedRule3EndpointPriority leftCompilation.endpointFrame)
                      (input.localizedRule3EndpointPriority rightCompilation.endpointFrame) =
                      some unit := by
                    rw [← input.localizedRule3DescriptorBearingSpatialUnit?_factorization
                      topology.left topology.right leftCompilation.endpointFrame
                      rightCompilation.endpointFrame]
                    exact unitComputed
                  have newUnitComputed :=
                    input.localizedRule3ShortCircuitSpatialUnit?_eq_some_of_priorities
                      topology.left topology.right
                      { priority :=
                          input.localizedRule3EndpointPriority leftCompilation.endpointFrame
                        firstCandidate := leftCompilation.endpointFrame.first }
                      { priority :=
                          input.localizedRule3EndpointPriority rightCompilation.endpointFrame
                        firstCandidate := rightCompilation.endpointFrame.first }
                      unit coreComputed
                  refine ⟨
                    { topology := topology
                      leftEndpoint :=
                        { priority :=
                            input.localizedRule3EndpointPriority leftCompilation.endpointFrame
                          firstCandidate := leftCompilation.endpointFrame.first }
                      rightEndpoint :=
                        { priority :=
                            input.localizedRule3EndpointPriority rightCompilation.endpointFrame
                          firstCandidate := rightCompilation.endpointFrame.first }
                      unit :=
                        { left :=
                            { priority :=
                                input.localizedRule3EndpointPriority
                                  leftCompilation.endpointFrame
                              firstCandidate := leftCompilation.endpointFrame.first }
                          right :=
                            { priority :=
                                input.localizedRule3EndpointPriority
                                  rightCompilation.endpointFrame
                              firstCandidate := rightCompilation.endpointFrame.first }
                          core := unit } },
                    ?_, rfl, ?_, ?_, rfl, rfl, rfl⟩
                  · simp [localizedRule3ShortCircuitSpatialUnitWith?, topologyComputed,
                      leftShortCircuit, rightShortCircuit, newUnitComputed]
                  · exact hPrios.1.symm
                  · exact hPrios.2.symm

/-- Capstone: on root coherence of both compiled endpoint frames, the projected Rule-3 observation
of a short-circuit success is exactly the projected observation of the older successful
descriptor-bearing occurrence computation.  `localizedRule3DescriptorBearingObservation` is the
existing projection onto the identity-aware `LocalizedRule3SpatialNodeResult`. -/
theorem localizedRule3ShortCircuitSpatialObservation_eq_of_parameterizedWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (resultOld : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (computedOld : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
      target occurrence view rule3FrameOf = some resultOld)
    (leftCoherent : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      resultOld.leftCompilation.endpointFrame resultOld.leftCompilation.firstCursor
      resultOld.leftCompilation.secondCursor)
    (rightCoherent : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      resultOld.rightCompilation.endpointFrame resultOld.rightCompilation.firstCursor
      resultOld.rightCompilation.secondCursor)
    (leftConstitutional : input.LocalizedRule3EndpointConstitutionalExact resultOld.leftCompilation)
    (rightConstitutional : input.LocalizedRule3EndpointConstitutionalExact resultOld.rightCompilation) :
    ∃ resultNew, input.localizedRule3ShortCircuitSpatialUnitWith?
        target occurrence view rule3FrameOf = some resultNew ∧
      input.localizedRule3ShortCircuitSpatialObservation resultNew =
        input.localizedRule3DescriptorBearingObservation resultOld := by
  obtain ⟨resultNew, hComputedNew, hTopology, hLeftPriority, hRightPriority,
    hLeftCandidate, hRightCandidate, hGeometry⟩ :=
    input.localizedRule3ShortCircuitSpatialUnitWith?_of_parameterizedWith
      target occurrence view rule3FrameOf resultOld computedOld leftCoherent rightCoherent
      leftConstitutional rightConstitutional
  refine ⟨resultNew, hComputedNew, ?_⟩
  simp only [localizedRule3ShortCircuitSpatialObservation,
    localizedRule3DescriptorBearingObservation,
    hTopology, hLeftPriority, hRightPriority, hLeftCandidate, hRightCandidate, hGeometry]
  unfold localizedRule3ShortCircuitSpatialObservation.match_1
    localizedRule3DescriptorBearingObservation.match_1
  rfl

/-! ## Executable occurrence wrapper

`localizedRule3ShortCircuitSpatialUnitWith?` recovers its physical topology and its two
short-circuit endpoints through selectors that are `noncomputable` in their own modules (the
carrier-membership step is decided by `Classical.choice`).  `LocalizedRule3ShortCircuitExecutable`
supplies plain executable twins of the two endpoint selectors, each proved `=`-equal to its original
at every argument, and they are used below.

The double-bond geometry is deliberately *not* redecided: the twin calls the very same
`localizedRule3ShortCircuitSpatialUnit?`, so its result retains `.unit.core.geometry` unchanged and
the agreement with the original wrapper is a pure transport of the already-proved endpoint twin
equalities.

All three non-executable ingredients are therefore replaced by proved-equal executable twins below,
so the occurrence wrapper itself is an ordinary `def`: no `Classical.choice` is consulted anywhere in
its call tree, and `#eval` can run it. -/

/-- Executable twin of `localizedRule3ShortCircuitSpatialUnitWith?`: same target, occurrence, view
and Rule-3 frame callback, same fail-closed `none` behaviour, and the same
`LocalizedRule3ShortCircuitSpatialResult` shape (in particular the same `.unit.core.geometry`).  All
three recoveries come from the executable twins; the geometry unit is literally shared. -/
def localizedRule3ShortCircuitSpatialUnitWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence
  let leftEndpoint ← input.localizedRule3ShortCircuitEndpointPriorityExec?
    target view rule3FrameOf topology.left topology.right topology.leftCursor
  let rightEndpoint ← input.localizedRule3ShortCircuitEndpointPriorityExec?
    target view rule3FrameOf topology.right topology.left topology.rightCursor
  let unit ← input.localizedRule3ShortCircuitSpatialUnit?
    topology.left topology.right leftEndpoint rightEndpoint
  some { topology, leftEndpoint, rightEndpoint, unit }

/-- The executable occurrence wrapper returns exactly the original short-circuit wrapper at every
target, occurrence, view and callback, including every `none` answer.  The topology recovery and the
two endpoint compilers are exchanged for their proved-equal executable twins; the geometry unit and
the emitted record are literally shared, so no geometry is redecided. -/
theorem localizedRule3ShortCircuitSpatialUnitWithExec?_eq_localizedRule3ShortCircuitSpatialUnitWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3ShortCircuitSpatialUnitWithExec? target occurrence view rule3FrameOf =
      input.localizedRule3ShortCircuitSpatialUnitWith? target occurrence view rule3FrameOf := by
  unfold localizedRule3ShortCircuitSpatialUnitWithExec?
    localizedRule3ShortCircuitSpatialUnitWith?
  simp only [localizedRule3PhysicalEndpointCursorFrameExec?_eq_original,
    ← localizedRule3ShortCircuitEndpointPriority?_eq_localizedRule3ShortCircuitEndpointPriorityExec?]

/-- Soundness of the executable occurrence wrapper, transported from the original wrapper along the
twin equality.  The callback contract is used exactly once, as in the original. -/
theorem localizedRule3ShortCircuitSpatialUnitWithExec?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (computed : input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view rule3FrameOf = some result) :
    input.DeclarativeLocalizedRule3ShortCircuitSpatialResult
      target occurrence view Rule3FrameMeaning result :=
  input.localizedRule3ShortCircuitSpatialUnitWith?_sound
    target occurrence view rule3FrameOf Rule3FrameMeaning rule3FrameSound result
    (localizedRule3ShortCircuitSpatialUnitWithExec?_eq_localizedRule3ShortCircuitSpatialUnitWith?
      input target occurrence view rule3FrameOf ▸ computed)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
