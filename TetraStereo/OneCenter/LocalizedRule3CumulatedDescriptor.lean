import TetraStereo.OneCenter.LocalizedRule3CumulatedChain
import TetraStereo.OneCenter.LocalizedRule3ParameterizedEndpoint

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Descriptor-bearing Rule 3 for odd cumulenes

An odd cumulene is one extended planar geometrical unit.  Its terminal substituents are ranked by
the same complete occurrence-local Rules-1a--5 keys as an ordinary double bond, but its terminal
atoms need not be directly bonded.  This module therefore separates the endpoint-priority and
exact spatial calculation from the ordinary-double-bond adjacency check, then combines it with
the proved odd terminal-to-terminal cursor topology.
-/

namespace CertifiedLocalizedCIPInput

/-- Descriptor-bearing endpoint and exact terminal geometry semantics for an extended planar
unit.  The surrounding cumulene relation, rather than a fictitious terminal-to-terminal bond,
supplies the physical topology. -/
def DeclarativeLocalizedRule3ExtendedDescriptorBearingSpatialUnit
    (input : CertifiedLocalizedCIPInput)
    (left leftPartner rightPartner right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (LeftKeyMeaning RightKeyMeaning :
      input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (result : input.LocalizedRule3DescriptorBearingSpatialUnitResult) : Prop :=
  input.DeclarativeLocalizedRule3EndpointKeyFrame
      left leftPartner LeftKeyMeaning leftFrame ∧
    input.DeclarativeLocalizedRule3EndpointKeyFrame
      right rightPartner RightKeyMeaning rightFrame ∧
    input.DeclarativeLocalizedRule3EndpointPriority leftFrame result.leftPriority ∧
    input.DeclarativeLocalizedRule3EndpointPriority rightFrame result.rightPriority ∧
    match result.leftPriority, result.rightPriority with
    | .nonstereogenic, _ | _, .nonstereogenic =>
        result.geometry = OfficialRule3Geometry.nonstereogenic
    | .senior leftReference, .senior rightReference =>
        ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
          input.SemanticSpatialPointAt left leftPoint ∧
          input.SemanticSpatialPointAt right rightPoint ∧
          input.SemanticSpatialPointAt leftReference leftReferencePoint ∧
          input.SemanticSpatialPointAt rightReference rightReferencePoint ∧
          RationalRule3SpatialGeometry leftPoint rightPoint
            leftReferencePoint rightReferencePoint result.geometry

/-- Resolve an extended planar unit after terminal topology has already been certified. -/
noncomputable def localizedRule3ExtendedDescriptorBearingSpatialUnit?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame) :
    Option input.LocalizedRule3DescriptorBearingSpatialUnitResult :=
  let leftPriority := input.localizedRule3EndpointPriority leftFrame
  let rightPriority := input.localizedRule3EndpointPriority rightFrame
  match leftPriority, rightPriority with
  | .nonstereogenic, _ | _, .nonstereogenic =>
      some { leftPriority, rightPriority, geometry := .nonstereogenic }
  | .senior leftReference, .senior rightReference => do
      let leftPoint ← input.spatialPointAt? left
      let rightPoint ← input.spatialPointAt? right
      let leftReferencePoint ← input.spatialPointAt? leftReference
      let rightReferencePoint ← input.spatialPointAt? rightReference
      let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
        leftReferencePoint rightReferencePoint
      some { leftPriority, rightPriority, geometry }

/-- Successful extended-unit classification is justified by complete endpoint keys and the
independent exact rational terminal geometry. -/
theorem localizedRule3ExtendedDescriptorBearingSpatialUnit?_sound
    (input : CertifiedLocalizedCIPInput)
    (left leftPartner rightPartner right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (LeftKeyMeaning RightKeyMeaning :
      input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (leftValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      left leftPartner LeftKeyMeaning leftFrame)
    (rightValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      right rightPartner RightKeyMeaning rightFrame)
    (result : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
      left right leftFrame rightFrame = some result) :
    input.DeclarativeLocalizedRule3ExtendedDescriptorBearingSpatialUnit
      left leftPartner rightPartner right leftFrame rightFrame
      LeftKeyMeaning RightKeyMeaning result := by
  unfold localizedRule3ExtendedDescriptorBearingSpatialUnit? at computed
  generalize leftPriorityIdentity :
      input.localizedRule3EndpointPriority leftFrame = leftPriority at computed
  generalize rightPriorityIdentity :
      input.localizedRule3EndpointPriority rightFrame = rightPriority at computed
  cases leftPriority with
  | nonstereogenic =>
      simp at computed
      subst result
      exact ⟨leftValid, rightValid,
        (input.localizedRule3EndpointPriority_eq_iff leftFrame _).mp
          leftPriorityIdentity,
        (input.localizedRule3EndpointPriority_eq_iff rightFrame _).mp
          rightPriorityIdentity, rfl⟩
  | senior leftReference =>
      cases rightPriority with
      | nonstereogenic =>
          simp at computed
          subst result
          exact ⟨leftValid, rightValid,
            (input.localizedRule3EndpointPriority_eq_iff leftFrame _).mp
              leftPriorityIdentity,
            (input.localizedRule3EndpointPriority_eq_iff rightFrame _).mp
              rightPriorityIdentity, rfl⟩
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
                              simp [leftPointComputed, rightPointComputed,
                                leftReferencePointComputed,
                                rightReferencePointComputed,
                                geometryComputed] at computed
                              subst result
                              exact ⟨leftValid, rightValid,
                                (input.localizedRule3EndpointPriority_eq_iff
                                  leftFrame _).mp leftPriorityIdentity,
                                (input.localizedRule3EndpointPriority_eq_iff
                                  rightFrame _).mp rightPriorityIdentity,
                                ⟨leftPoint, rightPoint, leftReferencePoint,
                                  rightReferencePoint,
                                  (input.spatialPointAt?_eq_some_iff
                                    left leftPoint).mp leftPointComputed,
                                  (input.spatialPointAt?_eq_some_iff
                                    right rightPoint).mp rightPointComputed,
                                  (input.spatialPointAt?_eq_some_iff
                                    leftReference leftReferencePoint).mp
                                      leftReferencePointComputed,
                                  (input.spatialPointAt?_eq_some_iff
                                    rightReference rightReferencePoint).mp
                                      rightReferencePointComputed,
                                  (rule3GeometryOfSpatialReferences?_eq_some_iff
                                    leftPoint rightPoint leftReferencePoint
                                    rightReferencePoint geometry).mp
                                      geometryComputed⟩⟩

/-- On independently valid terminal frames, executable success for an extended planar unit is
exactly complete endpoint priority plus the independent exact rational spatial relation. -/
theorem localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (left leftPartner rightPartner right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (LeftKeyMeaning RightKeyMeaning :
      input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (leftValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      left leftPartner LeftKeyMeaning leftFrame)
    (rightValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      right rightPartner RightKeyMeaning rightFrame)
    (result : input.LocalizedRule3DescriptorBearingSpatialUnitResult) :
    input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
        left right leftFrame rightFrame = some result ↔
      input.DeclarativeLocalizedRule3ExtendedDescriptorBearingSpatialUnit
        left leftPartner rightPartner right leftFrame rightFrame
        LeftKeyMeaning RightKeyMeaning result := by
  constructor
  · exact input.localizedRule3ExtendedDescriptorBearingSpatialUnit?_sound
      left leftPartner rightPartner right leftFrame rightFrame
      LeftKeyMeaning RightKeyMeaning leftValid rightValid result
  · rintro ⟨_leftValid, _rightValid, leftDerived, rightDerived, meaning⟩
    cases result with
    | mk leftPriority rightPriority geometry =>
        have leftComputed :=
          (input.localizedRule3EndpointPriority_eq_iff
            leftFrame leftPriority).mpr leftDerived
        have rightComputed :=
          (input.localizedRule3EndpointPriority_eq_iff
            rightFrame rightPriority).mpr rightDerived
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
                rcases meaning with ⟨leftPoint, rightPoint, leftReferencePoint,
                  rightReferencePoint, leftSemantic, rightSemantic,
                  leftReferenceSemantic, rightReferenceSemantic, spatial⟩
                simp [(input.spatialPointAt?_eq_some_iff left leftPoint).mpr leftSemantic,
                  (input.spatialPointAt?_eq_some_iff right rightPoint).mpr rightSemantic,
                  (input.spatialPointAt?_eq_some_iff
                    leftReference leftReferencePoint).mpr leftReferenceSemantic,
                  (input.spatialPointAt?_eq_some_iff
                    rightReference rightReferencePoint).mpr rightReferenceSemantic,
                  (rule3GeometryOfSpatialReferences?_eq_some_iff
                    leftPoint rightPoint leftReferencePoint
                    rightReferencePoint geometry).mpr spatial]

/-- On independently valid terminal frames, extended-unit refusal is exact: it occurs precisely
when no result satisfies the complete endpoint-priority and rational-spatial semantics. -/
theorem localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_none_iff
    (input : CertifiedLocalizedCIPInput)
    (left leftPartner rightPartner right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (LeftKeyMeaning RightKeyMeaning :
      input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (leftValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      left leftPartner LeftKeyMeaning leftFrame)
    (rightValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      right rightPartner RightKeyMeaning rightFrame) :
    input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
        left right leftFrame rightFrame = none ↔
      ¬ ∃ result, input.DeclarativeLocalizedRule3ExtendedDescriptorBearingSpatialUnit
        left leftPartner rightPartner right leftFrame rightFrame
        LeftKeyMeaning RightKeyMeaning result := by
  constructor
  · intro computed ⟨result, semantic⟩
    have successful :=
      (input.localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_some_iff
        left leftPartner rightPartner right leftFrame rightFrame
        LeftKeyMeaning RightKeyMeaning leftValid rightValid result).mpr semantic
    rw [computed] at successful
    contradiction
  · intro noSemantic
    cases computed : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
        left right leftFrame rightFrame with
    | none => rfl
    | some result =>
        exfalso
        apply noSemantic
        exact ⟨result,
          (input.localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_some_iff
            left leftPartner rightPartner right leftFrame rightFrame
            LeftKeyMeaning RightKeyMeaning leftValid rightValid result).mp computed⟩

/-- Complete descriptor-bearing result for one odd cumulene. -/
structure LocalizedRule3OddCumuleneDescriptorBearingSpatialResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel
  leftCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult

/-- The finite molecular atom count bounds a nonrepeating physical cumulene traversal; a cycle or
otherwise unresolved continuation remains fail-closed. -/
def localizedRule3CumulatedTraversalFuel
    (_input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) : Nat :=
  localizedOccurrenceRerootEvaluationFuel carrierFuel

/-- Compile both terminal candidate pairs through the caller-supplied smaller Rule-3 frame and
classify the exact terminal geometry. -/
noncomputable def localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3OddCumuleneEndpointCursorFrame?
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence
  let leftCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    target view rule3FrameOf topology.initial.left topology.initial.right
      topology.initial.leftCursor
  let rightCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    target view rule3FrameOf topology.right topology.rightPartner topology.rightCursor
  let unit ← input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
    topology.initial.left topology.right
    leftCompilation.endpointFrame rightCompilation.endpointFrame
  some { topology, leftCompilation, rightCompilation, unit }

/-- A successful descriptor-bearing odd-cumulene compilation retains exactly the endpoint
topology returned by its occurrence-local odd-chain constructor. -/
theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_topology
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
      target occurrence view rule3FrameOf = some result) :
    input.localizedRule3OddCumuleneEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence =
      some result.topology := by
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith? at computed
  cases topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [topologyComputed] at computed
  | some topology =>
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf topology.initial.left topology.initial.right
            topology.initial.leftCursor with
      | none => simp [topologyComputed, leftComputed] at computed
      | some leftCompilation =>
          cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf topology.right topology.rightPartner
                topology.rightCursor with
          | none => simp [topologyComputed, leftComputed, rightComputed] at computed
          | some rightCompilation =>
              cases unitComputed : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
                  topology.initial.left topology.right leftCompilation.endpointFrame
                    rightCompilation.endpointFrame with
              | none =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    unitComputed] at computed
              | some unit =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    unitComputed] at computed
                  subst result
                  simp

/-- Independent complete topology, endpoint-key, and geometry meaning of an odd-cumulene result. -/
def DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence result.topology ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.topology.initial.left
      result.topology.initial.right result.topology.initial.leftCursor
      result.leftCompilation ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.topology.right result.topology.rightPartner
      result.topology.rightCursor result.rightCompilation ∧
    input.DeclarativeLocalizedRule3ExtendedDescriptorBearingSpatialUnit
      result.topology.initial.left result.topology.initial.right
      result.topology.rightPartner result.topology.right
      result.leftCompilation.endpointFrame result.rightCompilation.endpointFrame
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          result.topology.initial.leftCursor cursor reference ∧
        ((cursor = result.leftCompilation.firstCursor ∧
            key = result.leftCompilation.endpointFrame.firstKey) ∨
         (cursor = result.leftCompilation.secondCursor ∧
            key = result.leftCompilation.endpointFrame.secondKey)))
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          result.topology.rightCursor cursor reference ∧
        ((cursor = result.rightCompilation.firstCursor ∧
            key = result.rightCompilation.endpointFrame.firstKey) ∨
         (cursor = result.rightCompilation.secondCursor ∧
            key = result.rightCompilation.endpointFrame.secondKey)))
      result.unit

/-- The odd-cumulene compiler is sound for every independently sound smaller Rule-3 callback. -/
theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
      target occurrence view rule3FrameOf = some result) :
    input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
      target occurrence view Rule3FrameMeaning result := by
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith? at computed
  cases topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [topologyComputed] at computed
  | some topology =>
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf topology.initial.left topology.initial.right
            topology.initial.leftCursor with
      | none => simp [topologyComputed, leftComputed] at computed
      | some leftCompilation =>
          cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf topology.right topology.rightPartner
                topology.rightCursor with
          | none => simp [topologyComputed, leftComputed, rightComputed] at computed
          | some rightCompilation =>
              cases unitComputed : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
                  topology.initial.left topology.right leftCompilation.endpointFrame
                    rightCompilation.endpointFrame with
              | none =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    unitComputed] at computed
              | some unit =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    unitComputed] at computed
                  subst result
                  have leftDerived :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                      topology.initial.left topology.initial.right
                      topology.initial.leftCursor leftCompilation leftComputed
                  have rightDerived :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                      topology.right topology.rightPartner topology.rightCursor
                      rightCompilation rightComputed
                  exact ⟨
                    input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
                      (input.localizedRule3CumulatedTraversalFuel carrierFuel)
                      occurrence topology
                      topologyComputed,
                    leftDerived,
                    rightDerived,
                    input.localizedRule3ExtendedDescriptorBearingSpatialUnit?_sound
                      topology.initial.left topology.initial.right
                      topology.rightPartner topology.right
                      leftCompilation.endpointFrame rightCompilation.endpointFrame _ _
                      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
                        input target view Rule3FrameMeaning topology.initial.left
                        topology.initial.right topology.initial.leftCursor
                        leftCompilation leftDerived)
                      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
                        input target view Rule3FrameMeaning topology.right topology.rightPartner
                        topology.rightCursor rightCompilation rightDerived)
                      unit unitComputed⟩

/-- Project an odd cumulene to the identity-aware Rule-3 observation used by recursive keys. -/
def localizedRule3OddCumuleneDescriptorBearingObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel) :
    input.LocalizedRule3SpatialNodeResult :=
  let leftReference := match result.unit.leftPriority with
    | .senior reference => reference
    | .nonstereogenic => result.leftCompilation.endpointFrame.first
  let rightReference := match result.unit.rightPriority with
    | .senior reference => reference
    | .nonstereogenic => result.rightCompilation.endpointFrame.first
  { left := result.topology.initial.left
    right := result.topology.right
    unit := { leftReference, rightReference, geometry := result.unit.geometry } }

@[simp] theorem localizedRule3OddCumuleneDescriptorBearingObservation_geometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel) :
    (input.localizedRule3OddCumuleneDescriptorBearingObservation result).unit.geometry =
      result.unit.geometry := by
  rfl

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
