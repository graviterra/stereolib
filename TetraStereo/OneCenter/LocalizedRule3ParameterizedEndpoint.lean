import TetraStereo.OneCenter.LocalizedRule3OccurrenceDescriptorReference

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Parameterized occurrence-local Rule-3 endpoint compilation

The concrete descriptor-bearing endpoint compiler previously called the strict-reference Rule-3
frame builder internally.  This module makes that dependency explicit: a caller supplies the
common two-cursor Rule-3 frame builder and an independent relation describing its output.  The
Rules-4a--5 portion and the physical occurrence topology remain fixed and proved here.

This is the recursion seam required by the next module.  A decreasing descriptor-bearing builder
can now call the endpoint logic with its own strictly smaller Rule-3 construction instead of
silently re-entering the older strict-reference analyzer.
-/

namespace CertifiedLocalizedCIPInput

/-- Independent meaning of a caller-supplied common Rule-3 frame builder. -/
abbrev LocalizedRule3FrameMeaning
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) :=
  List (input.LocalizedRerootCursor carrierFuel) →
    input.LocalizedRule3CanonicalKeyFrame → Prop

/-- Compile an endpoint with an explicit Rule-3 frame dependency. -/
noncomputable def buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    Option (input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] => do
      let firstCursor ← input.localizedRule3ReferenceCursor? endpointCursor first
      let secondCursor ← input.localizedRule3ReferenceCursor? endpointCursor second
      let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
      let rule3Frame ← rule3FrameOf [firstCursor, secondCursor]
      match rule3Frame.keys with
      | [firstRule3, secondRule3] => do
          let firstRule45 ← input.buildLocalizedRerootCompoundRule45Key?
            target view fuel firstCursor
          let secondRule45 ← input.buildLocalizedRerootCompoundRule45Key?
            target view fuel secondCursor
          some
            { firstCursor
              secondCursor
              rule3Frame
              endpointFrame :=
                { first
                  second
                  firstKey := { rule3 := firstRule3, rule45 := firstRule45 }
                  secondKey := { rule3 := secondRule3, rule45 := secondRule45 } } }
      | _ => none
  | _ => none

/-- Independent account of the parameterized endpoint compilation. -/
def DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) : Prop :=
  input.localizedRule3ExplicitSubstituents endpoint partner =
      [frame.endpointFrame.first, frame.endpointFrame.second] ∧
    input.DeclarativeLocalizedRule3ReferenceCursor endpointCursor
      frame.firstCursor frame.endpointFrame.first ∧
    input.DeclarativeLocalizedRule3ReferenceCursor endpointCursor
      frame.secondCursor frame.endpointFrame.second ∧
    Rule3FrameMeaning [frame.firstCursor, frame.secondCursor] frame.rule3Frame ∧
    frame.rule3Frame.keys =
      [frame.endpointFrame.firstKey.rule3, frame.endpointFrame.secondKey.rule3] ∧
    input.DeclarativeLocalizedRerootCompoundRule45Key
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      frame.firstCursor frame.endpointFrame.firstKey.rule45 ∧
    input.DeclarativeLocalizedRerootCompoundRule45Key
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      frame.secondCursor frame.endpointFrame.secondKey.rule45

/-- The parameterized compiler is sound for every independently sound Rule-3 frame callback. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf endpoint partner endpointCursor = some frame) :
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith? at computed
  generalize candidatesIdentity :
      input.localizedRule3ExplicitSubstituents endpoint partner = candidates at computed
  cases candidates with
  | nil => simp at computed
  | cons first rest =>
      cases rest with
      | nil => simp at computed
      | cons second tail =>
          cases tail with
          | cons third more => simp at computed
          | nil =>
              cases firstCursorComputed :
                  input.localizedRule3ReferenceCursor? endpointCursor first with
              | none => simp [firstCursorComputed] at computed
              | some firstCursor =>
                  cases secondCursorComputed :
                      input.localizedRule3ReferenceCursor? endpointCursor second with
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
                                              exact ⟨candidatesIdentity,
                                                input.localizedRule3ReferenceCursor?_sound
                                                  endpointCursor firstCursor first
                                                  firstCursorComputed,
                                                input.localizedRule3ReferenceCursor?_sound
                                                  endpointCursor secondCursor second
                                                  secondCursorComputed,
                                                rule3FrameSound
                                                  [firstCursor, secondCursor]
                                                  rule3Frame rule3FrameComputed,
                                                keysIdentity,
                                                input.buildLocalizedRerootCompoundRule45Key?_sound
                                                  target view fuel firstCursor firstRule45
                                                  firstRule45Computed,
                                                input.buildLocalizedRerootCompoundRule45Key?_sound
                                                  target view fuel secondCursor secondRule45
                                                  secondRule45Computed⟩

/-- Canonical evidence sufficient for a parameterized endpoint compilation.  Reference cursors
are uniquely selected in the exact cut neighborhood; the shared Rule-3 frame has the caller's
independent meaning; and both Rules-4a--5 keys have their canonical exact meaning. -/
def CanonicalLocalizedRule3OccurrenceEndpointKeyFrameWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) : Prop :=
  input.localizedRule3ExplicitSubstituents endpoint partner =
      [frame.endpointFrame.first, frame.endpointFrame.second] ∧
    input.CanonicalLocalizedRule3ReferenceCursor endpointCursor
      frame.firstCursor frame.endpointFrame.first ∧
    input.CanonicalLocalizedRule3ReferenceCursor endpointCursor
      frame.secondCursor frame.endpointFrame.second ∧
    Rule3FrameMeaning [frame.firstCursor, frame.secondCursor] frame.rule3Frame ∧
    frame.rule3Frame.keys =
      [frame.endpointFrame.firstKey.rule3, frame.endpointFrame.secondKey.rule3] ∧
    input.CanonicalLocalizedRerootCompoundRule45Key
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      frame.firstCursor frame.endpointFrame.firstKey.rule45 ∧
    input.CanonicalLocalizedRerootCompoundRule45Key
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      frame.secondCursor frame.endpointFrame.secondKey.rule45

/-- Canonical endpoint evidence is sufficient for execution whenever the supplied common Rule-3
frame implementation is complete for its stated independent meaning. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_complete_of_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameComplete : ∀ cursors frame,
      Rule3FrameMeaning cursors frame → rule3FrameOf cursors = some frame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (canonical : input.CanonicalLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf endpoint partner endpointCursor = some frame := by
  rcases canonical with ⟨candidates, firstReference, secondReference,
    rule3Frame, keys, firstRule45, secondRule45⟩
  have firstReferenceComputed :=
    (input.localizedRule3ReferenceCursor?_eq_some_iff endpointCursor
      frame.firstCursor frame.endpointFrame.first).mpr firstReference
  have secondReferenceComputed :=
    (input.localizedRule3ReferenceCursor?_eq_some_iff endpointCursor
      frame.secondCursor frame.endpointFrame.second).mpr secondReference
  have rule3FrameComputed := rule3FrameComplete
    [frame.firstCursor, frame.secondCursor] frame.rule3Frame rule3Frame
  have firstRule45Computed :=
    (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      frame.firstCursor frame.endpointFrame.firstKey.rule45).mpr firstRule45
  have secondRule45Computed :=
    (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      frame.secondCursor frame.endpointFrame.secondKey.rule45).mpr secondRule45
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
  rw [candidates]
  simp [firstReferenceComputed, secondReferenceComputed, rule3FrameComputed, keys,
    firstRule45Computed, secondRule45Computed]

/-- Once an endpoint has exactly two unique physical reference cursors and the shared Rule-3
callback returns two keys, the Rules-4a--5 fuel theorem makes endpoint compilation total. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_two_canonical_references
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor firstCursor first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor secondCursor second)
    (rule3FrameExists : ∃ rule3Frame,
      rule3FrameOf [firstCursor, secondCursor] = some rule3Frame ∧
        rule3Frame.keys.length = 2) :
    ∃ frame, input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf endpoint partner endpointCursor = some frame := by
  obtain ⟨rule3Frame, rule3FrameComputed, keyCount⟩ := rule3FrameExists
  obtain ⟨firstRule3, secondRule3, keys⟩ := List.length_eq_two.mp keyCount
  obtain ⟨firstRule45, firstRule45Computed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      target view firstCursor (firstReference.valid input endpointCursor firstCursor first)
  obtain ⟨secondRule45, secondRule45Computed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      target view secondCursor (secondReference.valid input endpointCursor secondCursor second)
  have firstReferenceComputed :=
    (input.localizedRule3ReferenceCursor?_eq_some_iff
      endpointCursor firstCursor first).mpr firstReference
  have secondReferenceComputed :=
    (input.localizedRule3ReferenceCursor?_eq_some_iff
      endpointCursor secondCursor second).mpr secondReference
  refine ⟨
    { firstCursor
      secondCursor
      rule3Frame
      endpointFrame :=
        { first
          second
          firstKey := { rule3 := firstRule3, rule45 := firstRule45 }
          secondKey := { rule3 := secondRule3, rule45 := secondRule45 } } }, ?_⟩
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
  rw [candidates]
  simp [firstReferenceComputed, secondReferenceComputed, rule3FrameComputed, keys,
    localizedOccurrenceRerootEvaluationFuel, firstRule45Computed, secondRule45Computed]

namespace DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith

/-- The parameterized concrete frame supplies the abstract endpoint-key meaning used by the pure
priority and spatial layer. -/
theorem endpointFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (derived : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame) :
    input.DeclarativeLocalizedRule3EndpointKeyFrame endpoint partner
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          endpointCursor cursor reference ∧
        ((cursor = frame.firstCursor ∧ key = frame.endpointFrame.firstKey) ∨
         (cursor = frame.secondCursor ∧ key = frame.endpointFrame.secondKey)))
      frame.endpointFrame := by
  rcases derived with ⟨candidates, firstReference, secondReference,
    _rule3Frame, _keys, _firstRule45, _secondRule45⟩
  exact ⟨candidates,
    ⟨frame.firstCursor, firstReference, Or.inl ⟨rfl, rfl⟩⟩,
    ⟨frame.secondCursor, secondReference, Or.inr ⟨rfl, rfl⟩⟩⟩

end DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith

/-- Descriptor-bearing occurrence analysis with an explicit common Rule-3 frame dependency. -/
noncomputable def localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3PhysicalEndpointCursorFrame? occurrence
  let leftCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    target view rule3FrameOf topology.left topology.right topology.leftCursor
  let rightCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    target view rule3FrameOf topology.right topology.left topology.rightCursor
  let unit ← input.localizedRule3DescriptorBearingSpatialUnit?
    topology.left topology.right
    leftCompilation.endpointFrame rightCompilation.endpointFrame
  some { topology, leftCompilation, rightCompilation, unit }

/-- Independent meaning of the parameterized descriptor-bearing occurrence result. -/
def DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame
      occurrence result.topology ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.topology.left result.topology.right
      result.topology.leftCursor result.leftCompilation ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.topology.right result.topology.left
      result.topology.rightCursor result.rightCompilation ∧
    input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
      result.topology.left result.topology.right
      result.leftCompilation.endpointFrame result.rightCompilation.endpointFrame
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          result.topology.leftCursor cursor reference ∧
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

/-- The parameterized occurrence analyzer is sound for any sound common Rule-3 callback. -/
theorem localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
      target occurrence view rule3FrameOf = some result) :
    input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
      target occurrence view Rule3FrameMeaning result := by
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnitWith? at computed
  cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => simp [topologyComputed] at computed
  | some topology =>
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf topology.left topology.right topology.leftCursor with
      | none => simp [topologyComputed, leftComputed] at computed
      | some leftCompilation =>
          cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf topology.right topology.left topology.rightCursor with
          | none => simp [topologyComputed, leftComputed, rightComputed] at computed
          | some rightCompilation =>
              cases unitComputed : input.localizedRule3DescriptorBearingSpatialUnit?
                  topology.left topology.right leftCompilation.endpointFrame
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
                      topology.left topology.right topology.leftCursor
                      leftCompilation leftComputed
                  have rightDerived :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                      topology.right topology.left topology.rightCursor
                      rightCompilation rightComputed
                  exact ⟨
                    input.localizedRule3PhysicalEndpointCursorFrame?_sound
                      occurrence topology topologyComputed,
                    leftDerived,
                    rightDerived,
                    input.localizedRule3DescriptorBearingSpatialUnit?_sound
                      topology.left topology.right
                      leftCompilation.endpointFrame rightCompilation.endpointFrame
                      _ _
                      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
                        input target view Rule3FrameMeaning topology.left topology.right
                        topology.leftCursor leftCompilation leftDerived)
                      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
                        input target view Rule3FrameMeaning topology.right topology.left
                        topology.rightCursor rightCompilation rightDerived)
                      unit unitComputed⟩

/-- Project the descriptor-bearing occurrence result to the established identity-aware Rule-3
observation type.  On a nonstereogenic endpoint the canonical first candidate is retained only as
an inert provenance witness; priority depends solely on `geometry`. -/
def localizedRule3DescriptorBearingObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel) :
    input.LocalizedRule3SpatialNodeResult :=
  let leftReference := match result.unit.leftPriority with
    | .senior reference => reference
    | .nonstereogenic => result.leftCompilation.endpointFrame.first
  let rightReference := match result.unit.rightPriority with
    | .senior reference => reference
    | .nonstereogenic => result.rightCompilation.endpointFrame.first
  { left := result.topology.left
    right := result.topology.right
    unit := { leftReference, rightReference, geometry := result.unit.geometry } }

@[simp] theorem localizedRule3DescriptorBearingObservation_geometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel) :
    (input.localizedRule3DescriptorBearingObservation result).unit.geometry =
      result.unit.geometry := by
  rfl

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
