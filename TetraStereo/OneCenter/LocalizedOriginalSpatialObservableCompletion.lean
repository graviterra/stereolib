import TetraStereo.OneCenter.LocalizedOriginalNodeObservableCompletion
import TetraStereo.OneCenter.LocalizedCyclicSemanticCompletion
import TetraStereo.OneCenter.LocalizedEndpointObservableCompletion
import TetraStereo.OneCenter.LocalizedExtendedNodeSemanticCompletion

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput









































































/-! ## The first physical candidate of the parameterized endpoint compiler -/

/-- The first physical candidate retained by a successful parameterized endpoint compilation is
the first entry of the independent substituent list.  The emitted endpoint frame stores literally
the matched substituents, so this is a deterministicity fact about the compiler. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_firstCandidate_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner =
      [first, second])
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf endpoint partner endpointCursor = some frame) :
    frame.endpointFrame.first = first := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith? at computed
  generalize substituentList :
      input.localizedRule3ExplicitSubstituents endpoint partner = substituents at computed
  cases substituents with
  | nil => simp at computed
  | cons firstCandidate rest =>
      cases rest with
      | nil => simp at computed
      | cons secondCandidate tail =>
          cases tail with
          | cons third more => simp at computed
          | nil =>
              cases firstCursorComputed :
                  input.localizedRule3ReferenceCursor? endpointCursor firstCandidate with
              | none => simp [firstCursorComputed] at computed
              | some firstCursor =>
                  cases secondCursorComputed :
                      input.localizedRule3ReferenceCursor? endpointCursor secondCandidate with
                  | none =>
                      simp [firstCursorComputed, secondCursorComputed] at computed
                  | some secondCursor =>
                      let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
                      cases rule3FrameComputed :
                          rule3FrameOf [firstCursor, secondCursor] with
                      | none =>
                          simp [firstCursorComputed, secondCursorComputed,
                            rule3FrameComputed] at computed
                      | some rule3Frame =>
                          generalize keysIdentity : rule3Frame.keys = keys at computed
                          cases keys with
                          | nil =>
                              simp [firstCursorComputed, secondCursorComputed,
                                rule3FrameComputed, keysIdentity] at computed
                          | cons firstRule3 keyTail =>
                              cases keyTail with
                              | nil =>
                                  simp [firstCursorComputed, secondCursorComputed,
                                    rule3FrameComputed, keysIdentity] at computed
                              | cons secondRule3 keyRest =>
                                  cases keyRest with
                                  | cons thirdRule3 more =>
                                      simp [firstCursorComputed, secondCursorComputed,
                                        rule3FrameComputed, keysIdentity] at computed
                                  | nil =>
                                      cases firstRule45Computed :
                                          input.buildLocalizedRerootCompoundRule45Key?
                                            target view fuel firstCursor with
                                      | none =>
                                          simp [firstCursorComputed, secondCursorComputed,
                                            rule3FrameComputed, keysIdentity,
                                            firstRule45Computed, fuel] at computed
                                      | some firstRule45 =>
                                          cases secondRule45Computed :
                                              input.buildLocalizedRerootCompoundRule45Key?
                                                target view fuel secondCursor with
                                          | none =>
                                              simp [firstCursorComputed,
                                                secondCursorComputed,
                                                rule3FrameComputed, keysIdentity,
                                                secondRule45Computed, fuel] at computed
                                          | some secondRule45 =>
                                              simp [firstCursorComputed,
                                                secondCursorComputed,
                                                rule3FrameComputed, keysIdentity,
                                                firstRule45Computed,
                                                secondRule45Computed, fuel] at computed
                                              subst frame
                                              have pairEq :
                                                  [firstCandidate, secondCandidate] =
                                                    [first, second] := by
                                                rw [← substituentList]
                                                exact candidates
                                              have firstEq : firstCandidate = first := by
                                                have decomposed := pairEq
                                                simp only [List.cons.injEq, and_true]
                                                  at decomposed
                                                exact decomposed.1
                                              simpa using firstEq

/-! ## The observation-level endpoint interface -/

/-- Observation-level endpoint compilation completeness.  Every independently derived endpoint
key frame is realized by *some* compiled frame whose complete endpoint priority and whose first
physical candidate agree with the derivation.  The Rule-3 payloads, the Rules-4a--5 keys and the
compiled frame's cursor fields are never constrained. -/
def LocalizedRule3OccurrenceEndpointObservableComplete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop :=
  ∀ (endpoint partner : input.Atom)
      (endpointCursor : input.LocalizedRerootCursor carrierFuel)
      (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel),
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
        target view Rule3FrameMeaning endpoint partner endpointCursor frame →
      ∃ compiled : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel,
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view rule3FrameOf endpoint partner endpointCursor = some compiled ∧
          compiled.endpointFrame.first = frame.endpointFrame.first ∧
          input.localizedRule3EndpointPriority compiled.endpointFrame =
            input.localizedRule3EndpointPriority frame.endpointFrame





theorem LocalizedRule3OccurrenceEndpointObservableComplete.ofCallbackComplete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackComplete : input.LocalizedRule3FrameCallbackCompleteness
      Rule3FrameMeaning rule3FrameOf)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) :
    input.LocalizedRule3OccurrenceEndpointObservableComplete
      target view rule3FrameOf Rule3FrameMeaning := by
  intro endpoint partner endpointCursor frame frameDerived
  have firstReference : input.CanonicalLocalizedRule3ReferenceCursor endpointCursor
      frame.firstCursor frame.endpointFrame.first :=
    input.canonicalLocalizedRule3ReferenceCursor_of_declarative
      endpointCursor frame.firstCursor frame.endpointFrame.first frameDerived.2.1
  have secondReference : input.CanonicalLocalizedRule3ReferenceCursor endpointCursor
      frame.secondCursor frame.endpointFrame.second :=
    input.canonicalLocalizedRule3ReferenceCursor_of_declarative
      endpointCursor frame.secondCursor frame.endpointFrame.second frameDerived.2.2.1
  obtain ⟨actualFrame, actualComputed, -, -, priorityEq⟩ :=
    exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith_observable input
      target view rule3FrameOf Rule3FrameMeaning callbackComplete rule45Agreement
      endpoint partner endpointCursor frame frameDerived firstReference secondReference
  exact
    ⟨actualFrame, actualComputed,
      buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_firstCandidate_eq input
        target view rule3FrameOf endpoint partner frame.endpointFrame.first
        frame.endpointFrame.second endpointCursor frameDerived.1 actualFrame actualComputed,
      priorityEq⟩

/-- Instantiation of the endpoint interface at the actual extended short-circuit frame compiler.
Only predecessor frame completeness and the Rules-4a--5 comparison-record agreement are retained;
the constitutional coherence and canonical-reference inputs are discharged unconditionally by the
frame-completeness bridge. -/
theorem localizedRule3OccurrenceEndpointObservableComplete_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) :
    input.LocalizedRule3OccurrenceEndpointObservableComplete target view
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel) :=
  LocalizedRule3OccurrenceEndpointObservableComplete.ofCallbackComplete input target view
    (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
    (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
    (input.localizedRule3FrameCallbackCompleteness_extended target view frameFuel frameComplete)
    rule45Agreement

/-! ## Spatial unit compilation from endpoint priorities alone -/

/-- Resolve the descriptor-bearing spatial unit of an ordinary physical double bond whenever the
compiled endpoint frames carry the independently derived priorities, the physical bond is a double
bond, and the derived unit meaning holds.  The returned unit has exactly the derived priority
fields and geometry; no spatial coordinate is re-derived. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_eq_some_of_priority
    (input : CertifiedLocalizedCIPInput)
    (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (derivedLeftFrame derivedRightFrame : input.LocalizedRule3EndpointKeyFrame)
    (bond : input.moleculeGraph.bond left right = 2)
    (leftPriorityEq : input.localizedRule3EndpointPriority leftFrame =
      input.localizedRule3EndpointPriority derivedLeftFrame)
    (rightPriorityEq : input.localizedRule3EndpointPriority rightFrame =
      input.localizedRule3EndpointPriority derivedRightFrame)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (leftDerived : input.DeclarativeLocalizedRule3EndpointPriority
      derivedLeftFrame unit.leftPriority)
    (rightDerived : input.DeclarativeLocalizedRule3EndpointPriority
      derivedRightFrame unit.rightPriority)
    (meaning :
      match unit.leftPriority, unit.rightPriority with
      | .nonstereogenic, _ | _, .nonstereogenic =>
          unit.geometry = OfficialRule3Geometry.nonstereogenic
      | .senior leftReference, .senior rightReference =>
          ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
            input.SemanticSpatialPointAt left leftPoint ∧
            input.SemanticSpatialPointAt right rightPoint ∧
            input.SemanticSpatialPointAt leftReference leftReferencePoint ∧
            input.SemanticSpatialPointAt rightReference rightReferencePoint ∧
            RationalRule3SpatialGeometry leftPoint rightPoint
              leftReferencePoint rightReferencePoint unit.geometry) :
    ∃ compiledUnit : input.LocalizedRule3DescriptorBearingSpatialUnitResult,
      input.localizedRule3DescriptorBearingSpatialUnit?
          left right leftFrame rightFrame = some compiledUnit ∧
        compiledUnit.leftPriority = unit.leftPriority ∧
        compiledUnit.rightPriority = unit.rightPriority ∧
        compiledUnit.geometry = unit.geometry := by
  have leftComputed : input.localizedRule3EndpointPriority leftFrame = unit.leftPriority :=
    leftPriorityEq.trans
      ((input.localizedRule3EndpointPriority_eq_iff derivedLeftFrame unit.leftPriority).mpr
        leftDerived)
  have rightComputed : input.localizedRule3EndpointPriority rightFrame = unit.rightPriority :=
    rightPriorityEq.trans
      ((input.localizedRule3EndpointPriority_eq_iff derivedRightFrame unit.rightPriority).mpr
        rightDerived)
  refine
    ⟨{ leftPriority := unit.leftPriority
       rightPriority := unit.rightPriority
       geometry := unit.geometry }, ?_, rfl, rfl, rfl⟩
  cases unit with
  | mk leftPriority rightPriority geometry =>
      unfold localizedRule3DescriptorBearingSpatialUnit?
      rw [if_pos bond, leftComputed, rightComputed]
      cases leftPriority with
      | nonstereogenic =>
          simp at meaning
          subst geometry
          rfl
      | senior leftReference =>
          cases rightPriority with
          | nonstereogenic =>
              simp at meaning
              subst geometry
              rfl
          | senior rightReference =>
              simp only
              rcases meaning with
                ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
                  leftSemantic, rightSemantic, leftReferenceSemantic,
                  rightReferenceSemantic, spatial⟩
              simp [(input.spatialPointAt?_eq_some_iff left leftPoint).mpr leftSemantic,
                (input.spatialPointAt?_eq_some_iff right rightPoint).mpr rightSemantic,
                (input.spatialPointAt?_eq_some_iff leftReference leftReferencePoint).mpr
                  leftReferenceSemantic,
                (input.spatialPointAt?_eq_some_iff rightReference rightReferencePoint).mpr
                  rightReferenceSemantic,
                (rule3GeometryOfSpatialReferences?_eq_some_iff leftPoint rightPoint
                  leftReferencePoint rightReferencePoint geometry).mpr spatial]

/-- The extended planar-unit analogue: the extended classifier has no terminal-to-terminal bond
check, so only the compiled endpoint priorities and the extended unit meaning are required. -/
theorem localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_some_of_priority
    (input : CertifiedLocalizedCIPInput)
    (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (derivedLeftFrame derivedRightFrame : input.LocalizedRule3EndpointKeyFrame)
    (leftPriorityEq : input.localizedRule3EndpointPriority leftFrame =
      input.localizedRule3EndpointPriority derivedLeftFrame)
    (rightPriorityEq : input.localizedRule3EndpointPriority rightFrame =
      input.localizedRule3EndpointPriority derivedRightFrame)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (leftDerived : input.DeclarativeLocalizedRule3EndpointPriority
      derivedLeftFrame unit.leftPriority)
    (rightDerived : input.DeclarativeLocalizedRule3EndpointPriority
      derivedRightFrame unit.rightPriority)
    (meaning :
      match unit.leftPriority, unit.rightPriority with
      | .nonstereogenic, _ | _, .nonstereogenic =>
          unit.geometry = OfficialRule3Geometry.nonstereogenic
      | .senior leftReference, .senior rightReference =>
          ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
            input.SemanticSpatialPointAt left leftPoint ∧
            input.SemanticSpatialPointAt right rightPoint ∧
            input.SemanticSpatialPointAt leftReference leftReferencePoint ∧
            input.SemanticSpatialPointAt rightReference rightReferencePoint ∧
            RationalRule3SpatialGeometry leftPoint rightPoint
              leftReferencePoint rightReferencePoint unit.geometry) :
    ∃ compiledUnit : input.LocalizedRule3DescriptorBearingSpatialUnitResult,
      input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
          left right leftFrame rightFrame = some compiledUnit ∧
        compiledUnit.leftPriority = unit.leftPriority ∧
        compiledUnit.rightPriority = unit.rightPriority ∧
        compiledUnit.geometry = unit.geometry := by
  have leftComputed : input.localizedRule3EndpointPriority leftFrame = unit.leftPriority :=
    leftPriorityEq.trans
      ((input.localizedRule3EndpointPriority_eq_iff derivedLeftFrame unit.leftPriority).mpr
        leftDerived)
  have rightComputed : input.localizedRule3EndpointPriority rightFrame = unit.rightPriority :=
    rightPriorityEq.trans
      ((input.localizedRule3EndpointPriority_eq_iff derivedRightFrame unit.rightPriority).mpr
        rightDerived)
  refine
    ⟨{ leftPriority := unit.leftPriority
       rightPriority := unit.rightPriority
       geometry := unit.geometry }, ?_, rfl, rfl, rfl⟩
  cases unit with
  | mk leftPriority rightPriority geometry =>
      unfold localizedRule3ExtendedDescriptorBearingSpatialUnit?
      rw [leftComputed, rightComputed]
      cases leftPriority with
      | nonstereogenic =>
          simp at meaning
          subst geometry
          rfl
      | senior leftReference =>
          cases rightPriority with
          | nonstereogenic =>
              simp at meaning
              subst geometry
              rfl
          | senior rightReference =>
              simp only
              rcases meaning with
                ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
                  leftSemantic, rightSemantic, leftReferenceSemantic,
                  rightReferenceSemantic, spatial⟩
              simp [(input.spatialPointAt?_eq_some_iff left leftPoint).mpr leftSemantic,
                (input.spatialPointAt?_eq_some_iff right rightPoint).mpr rightSemantic,
                (input.spatialPointAt?_eq_some_iff leftReference leftReferencePoint).mpr
                  leftReferenceSemantic,
                (input.spatialPointAt?_eq_some_iff rightReference rightReferencePoint).mpr
                  rightReferenceSemantic,
                (rule3GeometryOfSpatialReferences?_eq_some_iff leftPoint rightPoint
                  leftReferencePoint rightReferencePoint geometry).mpr spatial]

/-! ## Observation equality from the compiled unit -/

/-- Two ordinary spatial results built on the same physical topology have the same projected
observation once their unit priorities, geometry and nonstereogenic first-candidate fallbacks
agree.  Senior references are the priority payloads themselves. -/
theorem localizedRule3DescriptorBearingObservation_eq_of_unit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (compiledLeft derivedLeft compiledRight derivedRight :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (compiledUnit derivedUnit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (leftPriorityEq : compiledUnit.leftPriority = derivedUnit.leftPriority)
    (rightPriorityEq : compiledUnit.rightPriority = derivedUnit.rightPriority)
    (geometryEq : compiledUnit.geometry = derivedUnit.geometry)
    (leftFirstEq : compiledLeft.endpointFrame.first = derivedLeft.endpointFrame.first)
    (rightFirstEq : compiledRight.endpointFrame.first = derivedRight.endpointFrame.first) :
    input.localizedRule3DescriptorBearingObservation
        { topology := topology
          leftCompilation := compiledLeft
          rightCompilation := compiledRight
          unit := compiledUnit } =
      input.localizedRule3DescriptorBearingObservation
        { topology := topology
          leftCompilation := derivedLeft
          rightCompilation := derivedRight
          unit := derivedUnit } := by
  unfold localizedRule3DescriptorBearingObservation
  simp only [leftPriorityEq, rightPriorityEq, geometryEq, leftFirstEq, rightFirstEq]

/-- The cyclic observation analogue.  The physical atoms come from the same `initial` cursor
frame and the descriptor is retained. -/
theorem localizedRule3RequiredMonocyclicEZObservation_eq_of_unit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
    (descriptor : BlueBookP93.Acyclic.Descriptor)
    (compiledLeft derivedLeft compiledRight derivedRight :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (compiledUnit derivedUnit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (leftPriorityEq : compiledUnit.leftPriority = derivedUnit.leftPriority)
    (rightPriorityEq : compiledUnit.rightPriority = derivedUnit.rightPriority)
    (geometryEq : compiledUnit.geometry = derivedUnit.geometry)
    (leftFirstEq : compiledLeft.endpointFrame.first = derivedLeft.endpointFrame.first)
    (rightFirstEq : compiledRight.endpointFrame.first = derivedRight.endpointFrame.first) :
    input.localizedRule3RequiredMonocyclicEZObservation
        { initial := initial
          closure := closure
          policyResult := policyResult
          leftCompilation := compiledLeft
          rightCompilation := compiledRight
          unit := compiledUnit
          descriptor := descriptor } =
      input.localizedRule3RequiredMonocyclicEZObservation
        { initial := initial
          closure := closure
          policyResult := policyResult
          leftCompilation := derivedLeft
          rightCompilation := derivedRight
          unit := derivedUnit
          descriptor := descriptor } := by
  unfold localizedRule3RequiredMonocyclicEZObservation
  simp only [leftPriorityEq, rightPriorityEq, geometryEq, leftFirstEq, rightFirstEq]

/-- The odd-cumulene observation analogue.  The physical atoms come from the same terminal
topology. -/
theorem localizedRule3OddCumuleneDescriptorBearingObservation_eq_of_unit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (compiledLeft derivedLeft compiledRight derivedRight :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (compiledUnit derivedUnit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (leftPriorityEq : compiledUnit.leftPriority = derivedUnit.leftPriority)
    (rightPriorityEq : compiledUnit.rightPriority = derivedUnit.rightPriority)
    (geometryEq : compiledUnit.geometry = derivedUnit.geometry)
    (leftFirstEq : compiledLeft.endpointFrame.first = derivedLeft.endpointFrame.first)
    (rightFirstEq : compiledRight.endpointFrame.first = derivedRight.endpointFrame.first) :
    input.localizedRule3OddCumuleneDescriptorBearingObservation
        { topology := topology
          leftCompilation := compiledLeft
          rightCompilation := compiledRight
          unit := compiledUnit } =
      input.localizedRule3OddCumuleneDescriptorBearingObservation
        { topology := topology
          leftCompilation := derivedLeft
          rightCompilation := derivedRight
          unit := derivedUnit } := by
  unfold localizedRule3OddCumuleneDescriptorBearingObservation
  simp only [leftPriorityEq, rightPriorityEq, geometryEq, leftFirstEq, rightFirstEq]

/-! ## Odd-cumulene topology recognition -/

/-- Precise odd-cumulene topology recognition statement: every independently derived terminal
frame is returned by the executable recognizer at the cumulated traversal fuel.  It fixes nothing
beyond the exact topology already carried by the derivation. -/
def LocalizedRule3OddCumuleneTopologyRecognition
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop :=
  ∀ topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel,
    input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence topology →
      input.localizedRule3OddCumuleneEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology

/-- The topology recognition premise is discharged unconditionally by the green odd-route
completeness `localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_at_traversalFuel_of_declarative`. -/
theorem localizedRule3OddCumuleneTopologyRecognition_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.LocalizedRule3OddCumuleneTopologyRecognition occurrence :=
  fun topology derived =>
    input.localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_at_traversalFuel_of_declarative
      occurrence topology derived

/-! ## The three spatial observation completeness theorems -/

/-- Ordinary descriptor-bearing spatial observation completeness.  Given the observation-level
endpoint interface, every independently derived occurrence result is compiled to an actual result
whose projected observation is identical.  The compiled result keeps the same physical topology,
the same priorities and the same geometry as the derivation, while its endpoint payloads may
differ. -/
theorem localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpointComplete : input.LocalizedRule3OccurrenceEndpointObservableComplete
      target view rule3FrameOf Rule3FrameMeaning)
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
      target occurrence view Rule3FrameMeaning result) :
    ∃ compiled : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel,
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
          target occurrence view rule3FrameOf = some compiled ∧
        input.localizedRule3DescriptorBearingObservation compiled =
          input.localizedRule3DescriptorBearingObservation result := by
  rcases result with ⟨topology, leftCompilation, rightCompilation, unit⟩
  rcases derived with
    ⟨topologyDerived, leftFrameDerived, rightFrameDerived, unitDerived⟩
  have topologyComputed :=
    input.localizedCyclicPhysicalEndpointCursorFrame?_eq_some_of_declarative
      occurrence topology topologyDerived
  obtain ⟨compiledLeft, leftComputed, leftFirstEq, leftPriorityEq⟩ :=
    endpointComplete topology.left topology.right topology.leftCursor
      leftCompilation leftFrameDerived
  obtain ⟨compiledRight, rightComputed, rightFirstEq, rightPriorityEq⟩ :=
    endpointComplete topology.right topology.left topology.rightCursor
      rightCompilation rightFrameDerived
  obtain ⟨compiledUnit, unitComputed, compiledUnitLeftPriority,
    compiledUnitRightPriority, compiledUnitGeometry⟩ :=
    localizedRule3DescriptorBearingSpatialUnit?_eq_some_of_priority input
      topology.left topology.right compiledLeft.endpointFrame
      compiledRight.endpointFrame leftCompilation.endpointFrame
      rightCompilation.endpointFrame unitDerived.2.2.1 leftPriorityEq rightPriorityEq
      unit unitDerived.2.2.2.1 unitDerived.2.2.2.2.1 unitDerived.2.2.2.2.2
  refine
    ⟨{ topology := topology
       leftCompilation := compiledLeft
       rightCompilation := compiledRight
       unit := compiledUnit }, ?_, ?_⟩
  · simp [localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?, topologyComputed,
      leftComputed, rightComputed, unitComputed]
  · exact
      localizedRule3DescriptorBearingObservation_eq_of_unit input topology
        compiledLeft leftCompilation compiledRight rightCompilation
        compiledUnit unit compiledUnitLeftPriority compiledUnitRightPriority
        compiledUnitGeometry leftFirstEq rightFirstEq

/-- Required monocyclic `E/Z` observation completeness.  The executable route is recognized
exactly, the policy is forced to `requireEZ` by the independent assignment, and the compiled unit
and descriptor are produced from the derived priorities, geometry refinement and assignment. -/
theorem localizedRule3RequiredMonocyclicEZWith?_observation_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpointComplete : input.LocalizedRule3OccurrenceEndpointObservableComplete
      target view rule3FrameOf Rule3FrameMeaning)
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
      target occurrence view Rule3FrameMeaning result) :
    ∃ compiled : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel,
      input.localizedRule3RequiredMonocyclicEZWith?
          target occurrence view rule3FrameOf = some compiled ∧
        input.localizedRule3RequiredMonocyclicEZObservation compiled =
          input.localizedRule3RequiredMonocyclicEZObservation result := by
  rcases result with
    ⟨initial, closure, policyResult, leftCompilation, rightCompilation, unit, descriptor⟩
  have required : policyResult.policy =
      BlueBookP93.Cyclic.DoubleBondDescriptorPolicy.requireEZ :=
    DeclarativeLocalizedRule3RequiredMonocyclicEZWith.policy_requireEZ input derived
  rcases derived with
    ⟨routeDerived, leftFrameDerived, rightFrameDerived, unitDerived, cyclicDerived⟩
  have routeComputed :=
    input.localizedRule3CyclicAuthorityRoute?_complete occurrence
      (.ordinaryMonocyclicPolicy initial closure policyResult) routeDerived
  obtain ⟨compiledLeft, leftComputed, leftFirstEq, leftPriorityEq⟩ :=
    endpointComplete initial.left initial.right initial.leftCursor
      leftCompilation leftFrameDerived
  obtain ⟨compiledRight, rightComputed, rightFirstEq, rightPriorityEq⟩ :=
    endpointComplete initial.right initial.left initial.rightCursor
      rightCompilation rightFrameDerived
  obtain ⟨compiledUnit, unitComputed, compiledUnitLeftPriority,
    compiledUnitRightPriority, compiledUnitGeometry⟩ :=
    localizedRule3DescriptorBearingSpatialUnit?_eq_some_of_priority input
      initial.left initial.right compiledLeft.endpointFrame compiledRight.endpointFrame
      leftCompilation.endpointFrame rightCompilation.endpointFrame unitDerived.2.2.1
      leftPriorityEq rightPriorityEq unit unitDerived.2.2.2.1 unitDerived.2.2.2.2.1
      unitDerived.2.2.2.2.2
  obtain ⟨cyclicGeometry, geometryRefines, assignment⟩ := cyclicDerived
  have geometryComputed :
      monocyclicSeniorLigandGeometryOfRule3? compiledUnit.geometry = some cyclicGeometry := by
    rw [compiledUnitGeometry]
    exact
      (monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff unit.geometry
        cyclicGeometry).mpr geometryRefines
  have descriptorComputed :
      BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
          policyResult.carrier.ring.card policyResult.doubleBondCount cyclicGeometry =
        some descriptor :=
    (BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?_eq_some_iff
      policyResult.carrier.ring.card policyResult.doubleBondCount cyclicGeometry
      descriptor).mpr assignment
  refine
    ⟨{ initial := initial
       closure := closure
       policyResult := policyResult
       leftCompilation := compiledLeft
       rightCompilation := compiledRight
       unit := compiledUnit
       descriptor := descriptor }, ?_, ?_⟩
  · simp [localizedRule3RequiredMonocyclicEZWith?, routeComputed, required,
      leftComputed, rightComputed, unitComputed, geometryComputed, descriptorComputed]
  · exact
      localizedRule3RequiredMonocyclicEZObservation_eq_of_unit input initial closure
        policyResult descriptor compiledLeft leftCompilation compiledRight
        rightCompilation compiledUnit unit compiledUnitLeftPriority
        compiledUnitRightPriority compiledUnitGeometry leftFirstEq rightFirstEq

/-- Odd-cumulene descriptor-bearing observation completeness.  The terminal topology is obtained
unconditionally from the green odd-route completeness; the two terminal endpoint pairs and the
extended planar unit are then compiled exactly as in the ordinary case. -/
theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_observation_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpointComplete : input.LocalizedRule3OccurrenceEndpointObservableComplete
      target view rule3FrameOf Rule3FrameMeaning)
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
      target occurrence view Rule3FrameMeaning result) :
    ∃ compiled : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel,
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
          target occurrence view rule3FrameOf = some compiled ∧
        input.localizedRule3OddCumuleneDescriptorBearingObservation compiled =
          input.localizedRule3OddCumuleneDescriptorBearingObservation result := by
  rcases result with ⟨topology, leftCompilation, rightCompilation, unit⟩
  rcases derived with
    ⟨topologyDerived, leftFrameDerived, rightFrameDerived, unitDerived⟩
  have topologyComputed :=
    localizedRule3OddCumuleneTopologyRecognition_of_declarative input occurrence
      topology topologyDerived
  obtain ⟨compiledLeft, leftComputed, leftFirstEq, leftPriorityEq⟩ :=
    endpointComplete topology.initial.left topology.initial.right
      topology.initial.leftCursor leftCompilation leftFrameDerived
  obtain ⟨compiledRight, rightComputed, rightFirstEq, rightPriorityEq⟩ :=
    endpointComplete topology.right topology.rightPartner topology.rightCursor
      rightCompilation rightFrameDerived
  obtain ⟨compiledUnit, unitComputed, compiledUnitLeftPriority,
    compiledUnitRightPriority, compiledUnitGeometry⟩ :=
    localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_some_of_priority input
      topology.initial.left topology.right compiledLeft.endpointFrame
      compiledRight.endpointFrame leftCompilation.endpointFrame
      rightCompilation.endpointFrame leftPriorityEq rightPriorityEq unit
      unitDerived.2.2.1 unitDerived.2.2.2.1 unitDerived.2.2.2.2
  refine
    ⟨{ topology := topology
       leftCompilation := compiledLeft
       rightCompilation := compiledRight
       unit := compiledUnit }, ?_, ?_⟩
  · simp [localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?, topologyComputed,
      leftComputed, rightComputed, unitComputed]
  · exact
      localizedRule3OddCumuleneDescriptorBearingObservation_eq_of_unit input topology
        compiledLeft leftCompilation compiledRight rightCompilation
        compiledUnit unit compiledUnitLeftPriority compiledUnitRightPriority
        compiledUnitGeometry leftFirstEq rightFirstEq

/-! ## Extended-frame instantiations of the three readers -/

/-- Ordinary spatial observation completeness for the actual extended short-circuit frame
compiler, retaining only predecessor frame completeness and Rule-45 comparison-record agreement. -/
theorem localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_complete_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
      target occurrence view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel) result) :
    ∃ compiled : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel,
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith? target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel) =
        some compiled ∧
        input.localizedRule3DescriptorBearingObservation compiled =
          input.localizedRule3DescriptorBearingObservation result :=
  localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_complete input
    target occurrence view _ _
    (localizedRule3OccurrenceEndpointObservableComplete_extended input target view frameFuel
      frameComplete rule45Agreement)
    result derived

/-- Required monocyclic `E/Z` observation completeness for the actual extended short-circuit frame
compiler. -/
theorem localizedRule3RequiredMonocyclicEZWith?_observation_complete_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith target occurrence view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel) result) :
    ∃ compiled : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel,
      input.localizedRule3RequiredMonocyclicEZWith? target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel) =
        some compiled ∧
        input.localizedRule3RequiredMonocyclicEZObservation compiled =
          input.localizedRule3RequiredMonocyclicEZObservation result :=
  localizedRule3RequiredMonocyclicEZWith?_observation_complete input target occurrence view _ _
    (localizedRule3OccurrenceEndpointObservableComplete_extended input target view frameFuel
      frameComplete rule45Agreement)
    result derived

/-- Odd-cumulene observation completeness for the actual extended short-circuit frame compiler. -/
theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_observation_complete_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
      target occurrence view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel) result) :
    ∃ compiled : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel,
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith? target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel) =
        some compiled ∧
        input.localizedRule3OddCumuleneDescriptorBearingObservation compiled =
          input.localizedRule3OddCumuleneDescriptorBearingObservation result :=
  localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_observation_complete input
    target occurrence view _ _
    (localizedRule3OccurrenceEndpointObservableComplete_extended input target view frameFuel
      frameComplete rule45Agreement)
    result derived

/-! ## Bundle assembly -/

/-- The three spatial observation-level fields of the original-node obligations, as produced by
the composition theorems above. -/
structure LocalizedOriginalSpatialObservableFields
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop where
  /-- A proved ordinary/spatial unit is compiled to an actual result carrying the same projected
  observation. -/
  spatialObservationComplete : ∀ result,
    input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3DescriptorBearingObservation compiled =
            input.localizedRule3DescriptorBearingObservation result
  /-- A proved required monocyclic `E/Z` unit is compiled to an actual result carrying the same
  projected observation. -/
  cyclicObservationComplete : ∀ result,
    input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3RequiredMonocyclicEZWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3RequiredMonocyclicEZObservation compiled =
            input.localizedRule3RequiredMonocyclicEZObservation result
  /-- A proved odd-cumulene unit is compiled to an actual result carrying the same projected
  observation. -/
  oddCumuleneObservationComplete : ∀ result,
    input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3OddCumuleneDescriptorBearingObservation compiled =
            input.localizedRule3OddCumuleneDescriptorBearingObservation result

/-- The three observation fields from the endpoint interface.  The odd topology recognition is
discharged internally. -/
def localizedOriginalSpatialObservableFields_ofProducers
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpointComplete : input.LocalizedRule3OccurrenceEndpointObservableComplete
      target view rule3FrameOf Rule3FrameMeaning) :
    input.LocalizedOriginalSpatialObservableFields
      target occurrence view rule3FrameOf Rule3FrameMeaning where
  spatialObservationComplete := fun result derived =>
    input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_complete
      target occurrence view rule3FrameOf Rule3FrameMeaning endpointComplete result derived
  cyclicObservationComplete := fun result derived =>
    input.localizedRule3RequiredMonocyclicEZWith?_observation_complete
      target occurrence view rule3FrameOf Rule3FrameMeaning endpointComplete result derived
  oddCumuleneObservationComplete := fun result derived =>
    input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_observation_complete
      target occurrence view rule3FrameOf Rule3FrameMeaning endpointComplete result derived

/-- The six non-spatial component fields of the original-node obligations: entry shape, axis
double-bond count and omission policy category.  They are independent of the shared Rule-3 frame
callback and of the spatial compilers. -/
structure LocalizedOriginalEntryAxisRoutingFields
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop where
  /-- A proved terminal-start entry is the entry the classifier returns. -/
  terminalEntryComplete : ∀ initial,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.terminalStart initial) →
      input.localizedRule3CumulatedAxisEntry? occurrence = some (.terminalStart initial)
  /-- A proved internal entry is the entry the classifier returns. -/
  internalEntryComplete : ∀ initial previousAxis,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.internal initial previousAxis) →
      input.localizedRule3CumulatedAxisEntry? occurrence = some (.internal initial previousAxis)
  /-- A proved ring-closing entry is the entry the classifier returns. -/
  ringEntryComplete : ∀ initial closure,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.ringClosure initial closure) →
      input.localizedRule3CumulatedAxisEntry? occurrence = some (.ringClosure initial closure)
  /-- A proved branched entry is recognized as *some* branched entry at the same physical frame. -/
  branchedEntryObservable : ∀ initial first second rest,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.branched initial first second rest) →
      ∃ actualFirst actualSecond actualRest,
        input.localizedRule3CumulatedAxisEntry? occurrence =
          some (.branched initial actualFirst actualSecond actualRest)
  /-- A proved terminal-start axis is walked to an actual frame with the same double-bond count. -/
  axisDoubleBondCountComplete : ∀ axis,
    input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence axis →
      ∃ compiled,
        input.localizedRule3CumulatedEndpointCursorFrame?
            (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some compiled ∧
          compiled.doubleBondCount = axis.doubleBondCount
  /-- A proved permanently-omitted monocycle is recognized by the actual cyclic route as an
  ordinary-monocyclic-policy route with the same policy *category*. -/
  omissionCategoryComplete : ∀ initial closure policyResult,
    input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
        (.ordinaryMonocyclicPolicy initial closure policyResult) →
      policyResult.policy = .permanentlyOmit →
      ∃ actualInitial actualClosure actualPolicyResult,
        input.localizedRule3CyclicAuthorityRoute? occurrence =
            some (.ordinaryMonocyclicPolicy actualInitial actualClosure actualPolicyResult) ∧
          actualPolicyResult.policy = .permanentlyOmit

/-- Assemble the nine observation-level obligations from the six routing fields and the three
spatial fields. -/
def localizedOriginalNodeObservableCompletionObligations_ofFields
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (routing : input.LocalizedOriginalEntryAxisRoutingFields occurrence)
    (spatial : input.LocalizedOriginalSpatialObservableFields
      target occurrence view rule3FrameOf Rule3FrameMeaning) :
    input.LocalizedOriginalNodeObservableCompletionObligations
      target occurrence view rule3FrameOf Rule3FrameMeaning where
  terminalEntryComplete := routing.terminalEntryComplete
  internalEntryComplete := routing.internalEntryComplete
  ringEntryComplete := routing.ringEntryComplete
  branchedEntryObservable := routing.branchedEntryObservable
  axisDoubleBondCountComplete := routing.axisDoubleBondCountComplete
  spatialObservationComplete := spatial.spatialObservationComplete
  cyclicObservationComplete := spatial.cyclicObservationComplete
  oddCumuleneObservationComplete := spatial.oddCumuleneObservationComplete
  omissionCategoryComplete := routing.omissionCategoryComplete

/-- The full `NodeCompleteAt` interface of the original node reader from a single endpoint
observation interface, valid for every occurrence, and the six per-occurrence routing fields.
The odd topology recognition is discharged internally. -/
theorem localizedOriginalNodeObservableCompleteAt_of_producers
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpointComplete : input.LocalizedRule3OccurrenceEndpointObservableComplete
      target view rule3FrameOf Rule3FrameMeaning)
    (routing : ∀ (occurrence : input.LocalizedCIPOccurrence carrierFuel),
      input.LocalizedOriginalEntryAxisRoutingFields occurrence) :
    input.LocalizedOriginalNodeObservableCompleteAt
      target view rule3FrameOf Rule3FrameMeaning :=
  input.localizedOriginalNodeObservableCompleteAt_of_obligations
    target view rule3FrameOf Rule3FrameMeaning (fun occurrence =>
      localizedOriginalNodeObservableCompletionObligations_ofFields input
        target occurrence view rule3FrameOf Rule3FrameMeaning
        (routing occurrence)
        (localizedOriginalSpatialObservableFields_ofProducers input
          target occurrence view rule3FrameOf Rule3FrameMeaning endpointComplete))

/-- Extended-frame assembly: the original `NodeCompleteAt` interface at the actual extended
short-circuit frame compiler, from predecessor frame completeness, Rule-45 comparison-record
agreement and the six routing fields. -/
theorem localizedOriginalNodeObservableCompleteAt_of_extendedProducers
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (routing : ∀ (occurrence : input.LocalizedCIPOccurrence carrierFuel),
      input.LocalizedOriginalEntryAxisRoutingFields occurrence) :
    input.LocalizedOriginalNodeObservableCompleteAt target view
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel) :=
  input.localizedOriginalNodeObservableCompleteAt_of_producers target view _ _
    (localizedRule3OccurrenceEndpointObservableComplete_extended input target view frameFuel
      frameComplete rule45Agreement)
    routing

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
