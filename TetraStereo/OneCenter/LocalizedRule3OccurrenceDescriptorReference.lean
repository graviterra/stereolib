import TetraStereo.OneCenter.LocalizedRule3OccurrenceReferenceCursor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Concrete occurrence-local descriptor-bearing Rule-3 references

This module connects the occurrence-path cursor recovery to the complete cumulative key boundary.
The two physical substituent cursors at an endpoint are compiled together under one canonical
Rule-3 exclusion policy, and each is independently compiled through Rules 4a--5 under the target's
strict dependency view.  The resulting endpoint frame therefore supports descriptor-bearing and
cyclic branches without atom-global descriptor lookup.

The nested Rule-3 observations inside these keys still use the currently proved spatial reader.
Replacing that reader by this descriptor-bearing construction is a subsequent well-founded mutual
recursion step; the theorem surface here makes that remaining boundary explicit rather than
claiming it away.
-/

namespace CertifiedLocalizedCIPInput

/-- Concrete compilation artifact for the two physical substituents at one double-bond endpoint. -/
structure LocalizedRule3OccurrenceEndpointKeyFrame
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  firstCursor : input.LocalizedRerootCursor carrierFuel
  secondCursor : input.LocalizedRerootCursor carrierFuel
  rule3Frame : input.LocalizedRule3CanonicalKeyFrame
  endpointFrame : input.LocalizedRule3EndpointKeyFrame

/-- Independent meaning of one occurrence-local cumulative reference key. -/
def DeclarativeLocalizedRule3OccurrenceReferenceKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (reference : input.Atom)
    (key : input.LocalizedOccurrenceRule3Through5Key) : Prop :=
  ∃ cursor excluded,
    input.DeclarativeLocalizedRule3ReferenceCursor
      endpointCursor cursor reference ∧
    input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept
      excluded (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      cursor key.rule3 ∧
    input.DeclarativeLocalizedRerootCompoundRule45Key
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      cursor key.rule45

/-- Compile the exact molecular candidate pair through the common Rule-3 policy and Rules 4a--5. -/
noncomputable def buildLocalizedRule3OccurrenceEndpointKeyFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    Option (input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] => do
      let firstCursor ← input.localizedRule3ReferenceCursor? endpointCursor first
      let secondCursor ← input.localizedRule3ReferenceCursor? endpointCursor second
      let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
      let rule3Frame ← input.buildLocalizedRule3CanonicalKeyFrame?
        fuel [firstCursor, secondCursor]
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

/-- Independent account of candidate identity, occurrence cursors, common Rule-3 policy, and both
Rules-4a--5 derivations. -/
def DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) : Prop :=
  input.localizedRule3ExplicitSubstituents endpoint partner =
      [frame.endpointFrame.first, frame.endpointFrame.second] ∧
    input.DeclarativeLocalizedRule3ReferenceCursor endpointCursor
      frame.firstCursor frame.endpointFrame.first ∧
    input.DeclarativeLocalizedRule3ReferenceCursor endpointCursor
      frame.secondCursor frame.endpointFrame.second ∧
    input.DeclarativeLocalizedRule3CanonicalKeyFrame
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      [frame.firstCursor, frame.secondCursor] frame.rule3Frame ∧
    frame.rule3Frame.keys =
      [frame.endpointFrame.firstKey.rule3, frame.endpointFrame.secondKey.rule3] ∧
    input.DeclarativeLocalizedRerootCompoundRule45Key
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      frame.firstCursor frame.endpointFrame.firstKey.rule45 ∧
    input.DeclarativeLocalizedRerootCompoundRule45Key
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      frame.secondCursor frame.endpointFrame.secondKey.rule45

/-- Successful concrete endpoint compilation accounts for every topology and cumulative-key
component independently. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrame?
      target view endpoint partner endpointCursor = some frame) :
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame
      target view endpoint partner endpointCursor frame := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrame? at computed
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
                          input.buildLocalizedRule3CanonicalKeyFrame?
                            fuel [firstCursor, secondCursor] with
                      | none =>
                          simp [firstCursorComputed, secondCursorComputed,
                            rule3FrameComputed, fuel] at computed
                      | some rule3Frame =>
                          generalize keysIdentity : rule3Frame.keys = keys at computed
                          cases keys with
                          | nil =>
                              simp [firstCursorComputed, secondCursorComputed,
                                rule3FrameComputed, keysIdentity, fuel] at computed
                          | cons firstRule3 keyTail =>
                              cases keyTail with
                              | nil =>
                                  simp [firstCursorComputed, secondCursorComputed,
                                    rule3FrameComputed, keysIdentity, fuel] at computed
                              | cons secondRule3 keyRest =>
                                  cases keyRest with
                                  | cons thirdRule3 more =>
                                      simp [firstCursorComputed, secondCursorComputed,
                                        rule3FrameComputed, keysIdentity, fuel] at computed
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
                                                input.buildLocalizedRule3CanonicalKeyFrame?_sound
                                                  fuel [firstCursor, secondCursor]
                                                  rule3Frame rule3FrameComputed,
                                                keysIdentity,
                                                input.buildLocalizedRerootCompoundRule45Key?_sound
                                                  target view fuel firstCursor firstRule45
                                                  firstRule45Computed,
                                                input.buildLocalizedRerootCompoundRule45Key?_sound
                                                  target view fuel secondCursor secondRule45
                                                  secondRule45Computed⟩

namespace DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame

/-- A concrete occurrence endpoint frame discharges the abstract key-meaning premise required by
the descriptor-bearing endpoint selector. -/
theorem endpointFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (derived : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame
      target view endpoint partner endpointCursor frame) :
    input.DeclarativeLocalizedRule3EndpointKeyFrame endpoint partner
      (input.DeclarativeLocalizedRule3OccurrenceReferenceKey
        target view endpointCursor)
      frame.endpointFrame := by
  rcases derived with ⟨candidates, firstReference, secondReference,
    rule3Frame, keys, firstRule45, secondRule45⟩
  have rule3Derivations := rule3Frame.2.2.2
  rw [keys] at rule3Derivations
  cases rule3Derivations with
  | cons firstRule3 tail =>
      cases tail with
      | cons secondRule3 empty =>
          cases empty
          exact ⟨candidates,
            ⟨frame.firstCursor, frame.rule3Frame.excluded,
              firstReference, firstRule3, firstRule45⟩,
            ⟨frame.secondCursor, frame.rule3Frame.excluded,
              secondReference, secondRule3, secondRule45⟩⟩

end DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame

/-- Fully compiled descriptor-bearing result for one physical Rule-3 carrier occurrence. -/
structure LocalizedRule3OccurrenceDescriptorBearingSpatialResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel
  leftCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult

/-- Recover both endpoint paths, compile both candidate pairs, and classify the physical unit. -/
noncomputable def localizedRule3OccurrenceDescriptorBearingSpatialUnit?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3PhysicalEndpointCursorFrame? occurrence
  let leftCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrame?
    target view topology.left topology.right topology.leftCursor
  let rightCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrame?
    target view topology.right topology.left topology.rightCursor
  let unit ← input.localizedRule3DescriptorBearingSpatialUnit?
    topology.left topology.right
    leftCompilation.endpointFrame rightCompilation.endpointFrame
  some { topology, leftCompilation, rightCompilation, unit }

/-- Independent end-to-end meaning of a successful occurrence-local descriptor-bearing unit. -/
def DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame
      occurrence result.topology ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame
      target view result.topology.left result.topology.right
      result.topology.leftCursor result.leftCompilation ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame
      target view result.topology.right result.topology.left
      result.topology.rightCursor result.rightCompilation ∧
    input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
      result.topology.left result.topology.right
      result.leftCompilation.endpointFrame result.rightCompilation.endpointFrame
      (input.DeclarativeLocalizedRule3OccurrenceReferenceKey
        target view result.topology.leftCursor)
      (input.DeclarativeLocalizedRule3OccurrenceReferenceKey
        target view result.topology.rightCursor)
      result.unit

/-- Every emitted descriptor-bearing occurrence unit is backed by exact carrier topology,
complete candidate keys, and the independent endpoint/spatial relation. -/
theorem localizedRule3OccurrenceDescriptorBearingSpatialUnit?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OccurrenceDescriptorBearingSpatialUnit?
      target occurrence view = some result) :
    input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnit
      target occurrence view result := by
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnit? at computed
  cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => simp [topologyComputed] at computed
  | some topology =>
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrame?
          target view topology.left topology.right topology.leftCursor with
      | none => simp [topologyComputed, leftComputed] at computed
      | some leftCompilation =>
          cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrame?
              target view topology.right topology.left topology.rightCursor with
          | none =>
              simp [topologyComputed, leftComputed, rightComputed] at computed
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
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrame?_sound
                      target view topology.left topology.right topology.leftCursor
                      leftCompilation leftComputed
                  have rightDerived :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrame?_sound
                      target view topology.right topology.left topology.rightCursor
                      rightCompilation rightComputed
                  exact ⟨
                    input.localizedRule3PhysicalEndpointCursorFrame?_sound
                      occurrence topology topologyComputed,
                    leftDerived,
                    rightDerived,
                    input.localizedRule3DescriptorBearingSpatialUnit?_sound
                      topology.left topology.right
                      leftCompilation.endpointFrame rightCompilation.endpointFrame
                      (input.DeclarativeLocalizedRule3OccurrenceReferenceKey
                        target view topology.leftCursor)
                      (input.DeclarativeLocalizedRule3OccurrenceReferenceKey
                        target view topology.rightCursor)
                      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame.endpointFrame
                        input target view topology.left topology.right topology.leftCursor
                        leftCompilation leftDerived)
                      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrame.endpointFrame
                        input target view topology.right topology.left topology.rightCursor
                        rightCompilation rightDerived)
                      unit unitComputed⟩

/-- A complete tie in the concretely compiled left endpoint propagates to an emitted
nonstereogenic physical unit; it is not converted back into an unresolved occurrence. -/
theorem localizedRule3OccurrenceDescriptorBearingSpatialUnit?_of_left_nonstereogenic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (leftCompilation rightCompilation :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (topologyComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence =
      some topology)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrame?
      target view topology.left topology.right topology.leftCursor =
        some leftCompilation)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrame?
      target view topology.right topology.left topology.rightCursor =
        some rightCompilation)
    (leftTied : input.localizedRule3EndpointPriority
      leftCompilation.endpointFrame = .nonstereogenic) :
    input.localizedRule3OccurrenceDescriptorBearingSpatialUnit?
        target occurrence view =
      some
        { topology
          leftCompilation
          rightCompilation
          unit :=
            { leftPriority := .nonstereogenic
              rightPriority := input.localizedRule3EndpointPriority
                rightCompilation.endpointFrame
              geometry := .nonstereogenic } } := by
  have unitComputed :=
    input.localizedRule3DescriptorBearingSpatialUnit?_of_left_nonstereogenic
      topology.left topology.right leftCompilation.endpointFrame
      rightCompilation.endpointFrame
      ((input.localizedRule3PhysicalEndpointCursorFrame?_sound
        occurrence topology topologyComputed).2.2.2.1)
      leftTied
  simp [localizedRule3OccurrenceDescriptorBearingSpatialUnit?,
    topologyComputed, leftComputed, rightComputed, unitComputed]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
