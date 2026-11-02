import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3Key
import TetraStereo.OneCenter.P92StereogenicUnitSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Localized even-cumulene axial descriptors

P-93.4.2.2 routes a terminal-to-terminal cumulene with an even number of consecutive double
bonds to axial chirality.  This module joins that provision to the exact occurrence-local topology
and recursive Rules-1a--5 endpoint keys.  No caller supplies a final descriptor: exact rational
coordinates determine the clockwise/anticlockwise sense after the senior reference at each end
has been derived.
-/

namespace CartesianPoint3

/-- Signed axial torsion numerator for senior terminal references.  Looking from `axisStart`
toward `axisEnd`, a negative value is a clockwise turn from the start senior reference to the end
senior reference; a positive value is anticlockwise. -/
def axialChiralityMeasure
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) : ℚ :=
  let axis := displacement axisStart axisEnd
  let startArm := displacement axisStart startHigh
  let endArm := displacement axisEnd endHigh
  RationalVector3.dot axis (RationalVector3.cross startArm endArm)

/-- Reversing the named direction of the physical axis, while exchanging its corresponding
terminal senior references, leaves the exact axial chirality measure unchanged.  Thus the sign
is a property of the oriented reference configuration, not of an arbitrary endpoint naming. -/
theorem axialChiralityMeasure_swap
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) :
    axialChiralityMeasure axisEnd axisStart endHigh startHigh =
      axialChiralityMeasure axisStart axisEnd startHigh endHigh := by
  simp [axialChiralityMeasure, displacement, RationalVector3.dot,
    RationalVector3.cross]
  ring

end CartesianPoint3

/-- Exact production axial descriptor from already ranked terminal references.  Coplanar or
collinear reference arms have zero measure and are refused. -/
def axialDescriptorOfSpatialReferences?
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) : Option AxialDescriptor :=
  let measure := CartesianPoint3.axialChiralityMeasure axisStart axisEnd startHigh endHigh
  if measure < 0 then some .Ra
  else if 0 < measure then some .Sa
  else none

/-- Independent P-92.1.2.1.2 reading of the exact rational axial measure. -/
def RationalAxialSpatialDescriptor
    (axisStart axisEnd startHigh endHigh : CartesianPoint3)
    (descriptor : AxialDescriptor) : Prop :=
  match descriptor with
  | .Ra => CartesianPoint3.axialChiralityMeasure axisStart axisEnd startHigh endHigh < 0
  | .Sa => 0 < CartesianPoint3.axialChiralityMeasure axisStart axisEnd startHigh endHigh

/-- The independent rational axial semantics is invariant under reversal of the named axis. -/
theorem rationalAxialSpatialDescriptor_swap
    (axisStart axisEnd startHigh endHigh : CartesianPoint3)
    (descriptor : AxialDescriptor) :
    RationalAxialSpatialDescriptor axisEnd axisStart endHigh startHigh descriptor ↔
      RationalAxialSpatialDescriptor axisStart axisEnd startHigh endHigh descriptor := by
  cases descriptor <;>
    simp [RationalAxialSpatialDescriptor, CartesianPoint3.axialChiralityMeasure_swap]

/-- The executable exact descriptor calculation has the same endpoint-reversal invariance. -/
theorem axialDescriptorOfSpatialReferences?_swap
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) :
    axialDescriptorOfSpatialReferences? axisEnd axisStart endHigh startHigh =
      axialDescriptorOfSpatialReferences? axisStart axisEnd startHigh endHigh := by
  simp [axialDescriptorOfSpatialReferences?, CartesianPoint3.axialChiralityMeasure_swap]

/-- The executable sign test is exactly the independent rational axial relation. -/
theorem axialDescriptorOfSpatialReferences?_eq_some_iff
    (axisStart axisEnd startHigh endHigh : CartesianPoint3)
    (descriptor : AxialDescriptor) :
    axialDescriptorOfSpatialReferences? axisStart axisEnd startHigh endHigh =
        some descriptor ↔
      RationalAxialSpatialDescriptor axisStart axisEnd startHigh endHigh descriptor := by
  let measure := CartesianPoint3.axialChiralityMeasure axisStart axisEnd startHigh endHigh
  cases descriptor with
  | Ra =>
      unfold axialDescriptorOfSpatialReferences? RationalAxialSpatialDescriptor
      by_cases negative : measure < 0
      · simp [measure, negative]
      · rw [if_neg negative]
        by_cases positive : 0 < measure <;> simp [measure, negative, positive]
  | Sa =>
      unfold axialDescriptorOfSpatialReferences? RationalAxialSpatialDescriptor
      by_cases negative : measure < 0
      · have notPositive : ¬ 0 < measure := not_lt_of_ge negative.le
        simp [measure, negative, notPositive]
      · rw [if_neg negative]
        by_cases positive : 0 < measure <;> simp [measure, positive]

/-- Production `Rₐ/Sₐ` and the independently transcribed P-92 turn rule agree. -/
def AxialDescriptor.toBlueBookP92 : AxialDescriptor → BlueBookP92.AxialDescriptor
  | .Ra => .Ra
  | .Sa => .Sa

@[simp] theorem axialDescriptor_clockwise_conformance :
    AxialDescriptor.toBlueBookP92 .Ra =
      BlueBookP92.axialDescriptor .clockwise :=
  rfl

@[simp] theorem axialDescriptor_anticlockwise_conformance :
    AxialDescriptor.toBlueBookP92 .Sa =
      BlueBookP92.axialDescriptor .anticlockwise :=
  rfl

namespace CertifiedLocalizedCIPInput

/-- An open, terminal-to-terminal even cumulene.  Ordinary one-bond alkenes are excluded. -/
def DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence frame ∧
    1 < frame.doubleBondCount ∧ Even frame.doubleBondCount

/-- Detect the even-cumulene subfamily of the exact open-axis frame. -/
noncomputable def localizedEvenCumuleneEndpointCursorFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel) := do
  let frame ← input.localizedRule3CumulatedEndpointCursorFrame? traversalFuel occurrence
  if _even : 1 < frame.doubleBondCount ∧ Even frame.doubleBondCount then some frame
  else none

/-- Every detected even frame has exact terminal topology and even nonordinary bond count. -/
theorem localizedEvenCumuleneEndpointCursorFrame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (computed : input.localizedEvenCumuleneEndpointCursorFrame?
      traversalFuel occurrence = some frame) :
    input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame occurrence frame := by
  unfold localizedEvenCumuleneEndpointCursorFrame? at computed
  cases frameComputed : input.localizedRule3CumulatedEndpointCursorFrame?
      traversalFuel occurrence with
  | none => simp [frameComputed] at computed
  | some candidate =>
      by_cases even : 1 < candidate.doubleBondCount ∧ Even candidate.doubleBondCount
      · simp [frameComputed, even] at computed
        subst frame
        exact ⟨input.localizedRule3CumulatedEndpointCursorFrame?_sound
          traversalFuel occurrence candidate frameComputed, even⟩
      · simp [frameComputed, even] at computed

/-- Strict high/low order of the two complete endpoint keys. -/
inductive DeclarativeLocalizedAxialEndpointPair
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    input.Atom × input.Atom → Prop
  | firstSenior
      (strict : input.compareLocalizedOccurrenceRule3Through5Keys
        frame.firstKey frame.secondKey = Ordering.gt) :
      input.DeclarativeLocalizedAxialEndpointPair frame (frame.first, frame.second)
  | secondSenior
      (strict : input.compareLocalizedOccurrenceRule3Through5Keys
        frame.firstKey frame.secondKey = Ordering.lt) :
      input.DeclarativeLocalizedAxialEndpointPair frame (frame.second, frame.first)

/-- Return `(high, low)` only when the complete endpoint keys are strictly ordered. -/
def localizedAxialEndpointPair?
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) : Option (input.Atom × input.Atom) :=
  match input.compareLocalizedOccurrenceRule3Through5Keys frame.firstKey frame.secondKey with
  | .gt => some (frame.first, frame.second)
  | .lt => some (frame.second, frame.first)
  | .eq => none

/-- Executable high/low selection is exactly strict complete-key ordering. -/
theorem localizedAxialEndpointPair?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (pair : input.Atom × input.Atom) :
    input.localizedAxialEndpointPair? frame = some pair ↔
      input.DeclarativeLocalizedAxialEndpointPair frame pair := by
  unfold localizedAxialEndpointPair?
  generalize compared : input.compareLocalizedOccurrenceRule3Through5Keys
    frame.firstKey frame.secondKey = ordering
  cases ordering with
  | lt =>
      constructor
      · intro computed
        simp at computed
        subst pair
        exact DeclarativeLocalizedAxialEndpointPair.secondSenior compared
      · intro derived
        cases derived
        · simp_all
        · rfl
  | eq =>
      constructor
      · simp
      · intro derived
        cases derived <;> simp_all
  | gt =>
      constructor
      · intro computed
        simp at computed
        subst pair
        exact DeclarativeLocalizedAxialEndpointPair.firstSenior compared
      · intro derived
        cases derived
        · rfl
        · simp_all

/-- Construct an axial assignment only after both terminal candidate pairs have been strictly
ordered and exact spatial evidence gives a nonzero handedness.  The low references are retained
in the public unit even though, after priority has fixed each pair, the two senior references are
sufficient to read the elongated-tetrahedron sense. -/
noncomputable def localizedAxialAssignmentOfEndpointFrames?
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame) :
    Option (AxialAssignment input.Atom) := do
  let (startHigh, startLow) ← input.localizedAxialEndpointPair? startFrame
  let (endHigh, endLow) ← input.localizedAxialEndpointPair? endFrame
  let axisStartPoint ← input.spatialPointAt? axisStart
  let axisEndPoint ← input.spatialPointAt? axisEnd
  let startHighPoint ← input.spatialPointAt? startHigh
  let endHighPoint ← input.spatialPointAt? endHigh
  let descriptor ← axialDescriptorOfSpatialReferences?
    axisStartPoint axisEndPoint startHighPoint endHighPoint
  some
    { unit := { axisStart, axisEnd, startHigh, startLow, endHigh, endLow }
      descriptor }

/-- Independent meaning of the pure axial assignment layer: strict complete-key ordering fixes
both high/low pairs, semantic coordinates supply the four geometrical references, and the exact
rational sign relation fixes the emitted descriptor. -/
def DeclarativeLocalizedAxialAssignmentOfEndpointFrames
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame)
    (assignment : AxialAssignment input.Atom) : Prop :=
  input.DeclarativeLocalizedAxialEndpointPair startFrame
      (assignment.unit.startHigh, assignment.unit.startLow) ∧
    input.DeclarativeLocalizedAxialEndpointPair endFrame
      (assignment.unit.endHigh, assignment.unit.endLow) ∧
    assignment.unit.axisStart = axisStart ∧
    assignment.unit.axisEnd = axisEnd ∧
    ∃ axisStartPoint axisEndPoint startHighPoint endHighPoint,
      input.SemanticSpatialPointAt axisStart axisStartPoint ∧
      input.SemanticSpatialPointAt axisEnd axisEndPoint ∧
      input.SemanticSpatialPointAt assignment.unit.startHigh startHighPoint ∧
      input.SemanticSpatialPointAt assignment.unit.endHigh endHighPoint ∧
      RationalAxialSpatialDescriptor axisStartPoint axisEndPoint
        startHighPoint endHighPoint assignment.descriptor

/-- Every pure executable assignment satisfies the independent priority, semantic-coordinate,
and rational P-92 geometry relation. -/
theorem localizedAxialAssignmentOfEndpointFrames?_sound
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame)
    (assignment : AxialAssignment input.Atom)
    (computed : input.localizedAxialAssignmentOfEndpointFrames?
      axisStart axisEnd startFrame endFrame = some assignment) :
    input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
      axisStart axisEnd startFrame endFrame assignment := by
  unfold localizedAxialAssignmentOfEndpointFrames? at computed
  cases startPairComputed : input.localizedAxialEndpointPair? startFrame with
  | none => simp [startPairComputed] at computed
  | some startPair =>
      rcases startPair with ⟨startHigh, startLow⟩
      cases endPairComputed : input.localizedAxialEndpointPair? endFrame with
      | none => simp [startPairComputed, endPairComputed] at computed
      | some endPair =>
          rcases endPair with ⟨endHigh, endLow⟩
          cases axisStartPointComputed : input.spatialPointAt? axisStart with
          | none =>
              simp [startPairComputed, endPairComputed,
                axisStartPointComputed] at computed
          | some axisStartPoint =>
              cases axisEndPointComputed : input.spatialPointAt? axisEnd with
              | none =>
                  simp [startPairComputed, endPairComputed,
                    axisStartPointComputed, axisEndPointComputed] at computed
              | some axisEndPoint =>
                  cases startHighPointComputed : input.spatialPointAt? startHigh with
                  | none =>
                      simp [startPairComputed, endPairComputed,
                        axisStartPointComputed, axisEndPointComputed,
                        startHighPointComputed] at computed
                  | some startHighPoint =>
                      cases endHighPointComputed : input.spatialPointAt? endHigh with
                      | none =>
                          simp [startPairComputed, endPairComputed,
                            axisStartPointComputed, axisEndPointComputed,
                            endHighPointComputed] at computed
                      | some endHighPoint =>
                          cases descriptorComputed :
                              axialDescriptorOfSpatialReferences? axisStartPoint
                                axisEndPoint startHighPoint endHighPoint with
                          | none =>
                              simp [startPairComputed, endPairComputed,
                                axisStartPointComputed, axisEndPointComputed,
                                startHighPointComputed, endHighPointComputed,
                                descriptorComputed] at computed
                          | some descriptor =>
                              simp [startPairComputed, endPairComputed,
                                axisStartPointComputed, axisEndPointComputed,
                                startHighPointComputed, endHighPointComputed,
                                descriptorComputed] at computed
                              subst assignment
                              exact ⟨
                                (input.localizedAxialEndpointPair?_eq_some_iff
                                  startFrame (startHigh, startLow)).mp startPairComputed,
                                (input.localizedAxialEndpointPair?_eq_some_iff
                                  endFrame (endHigh, endLow)).mp endPairComputed,
                                rfl,
                                rfl,
                                ⟨axisStartPoint, axisEndPoint, startHighPoint, endHighPoint,
                                  (input.spatialPointAt?_eq_some_iff
                                    axisStart axisStartPoint).mp axisStartPointComputed,
                                  (input.spatialPointAt?_eq_some_iff
                                    axisEnd axisEndPoint).mp axisEndPointComputed,
                                  (input.spatialPointAt?_eq_some_iff
                                    startHigh startHighPoint).mp startHighPointComputed,
                                  (input.spatialPointAt?_eq_some_iff
                                    endHigh endHighPoint).mp endHighPointComputed,
                                  (axialDescriptorOfSpatialReferences?_eq_some_iff
                                    axisStartPoint axisEndPoint startHighPoint
                                    endHighPoint descriptor).mp descriptorComputed⟩⟩

/-- The pure endpoint-priority and geometry layer is complete as well as sound: it returns a
particular assignment exactly when that assignment satisfies the independent strict-priority,
semantic-coordinate, and rational P-92 sign relation. -/
theorem localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame)
    (assignment : AxialAssignment input.Atom) :
    input.localizedAxialAssignmentOfEndpointFrames?
        axisStart axisEnd startFrame endFrame = some assignment ↔
      input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
        axisStart axisEnd startFrame endFrame assignment := by
  constructor
  · exact input.localizedAxialAssignmentOfEndpointFrames?_sound
      axisStart axisEnd startFrame endFrame assignment
  · rintro ⟨startDerived, endDerived, axisStartEq, axisEndEq,
      axisStartPoint, axisEndPoint, startHighPoint, endHighPoint,
      axisStartSemantic, axisEndSemantic, startHighSemantic, endHighSemantic,
      descriptorDerived⟩
    have startComputed :=
      (input.localizedAxialEndpointPair?_eq_some_iff startFrame
        (assignment.unit.startHigh, assignment.unit.startLow)).mpr startDerived
    have endComputed :=
      (input.localizedAxialEndpointPair?_eq_some_iff endFrame
        (assignment.unit.endHigh, assignment.unit.endLow)).mpr endDerived
    have axisStartComputed :=
      (input.spatialPointAt?_eq_some_iff axisStart axisStartPoint).mpr axisStartSemantic
    have axisEndComputed :=
      (input.spatialPointAt?_eq_some_iff axisEnd axisEndPoint).mpr axisEndSemantic
    have startHighComputed :=
      (input.spatialPointAt?_eq_some_iff
        assignment.unit.startHigh startHighPoint).mpr startHighSemantic
    have endHighComputed :=
      (input.spatialPointAt?_eq_some_iff
        assignment.unit.endHigh endHighPoint).mpr endHighSemantic
    have descriptorComputed :=
      (axialDescriptorOfSpatialReferences?_eq_some_iff
        axisStartPoint axisEndPoint startHighPoint endHighPoint assignment.descriptor).mpr
          descriptorDerived
    cases assignment with
    | mk unit descriptor =>
        cases unit with
        | mk assignmentAxisStart assignmentAxisEnd startHigh startLow endHigh endLow =>
            dsimp only at axisStartEq axisEndEq
            dsimp only at startComputed endComputed startHighComputed endHighComputed descriptorComputed ⊢
            subst assignmentAxisStart
            subst assignmentAxisEnd
            simp [localizedAxialAssignmentOfEndpointFrames?, startComputed, endComputed,
              axisStartComputed, axisEndComputed, startHighComputed, endHighComputed,
              descriptorComputed]

/-- Refusal at the pure final layer is also exact: `none` means that no assignment satisfies the
independent strict-priority, semantic-coordinate, and nonzero P-92 geometry relation. -/
theorem localizedAxialAssignmentOfEndpointFrames?_eq_none_iff
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame) :
    input.localizedAxialAssignmentOfEndpointFrames?
        axisStart axisEnd startFrame endFrame = none ↔
      ∀ assignment,
        ¬ input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
          axisStart axisEnd startFrame endFrame assignment := by
  constructor
  · intro refused assignment derived
    have computed :=
      (input.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
        axisStart axisEnd startFrame endFrame assignment).mpr derived
    rw [refused] at computed
    contradiction
  · intro absent
    cases computed : input.localizedAxialAssignmentOfEndpointFrames?
        axisStart axisEnd startFrame endFrame with
    | none => rfl
    | some assignment =>
        exact (absent assignment
          ((input.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
            axisStart axisEnd startFrame endFrame assignment).mp computed)).elim

/-- Complete compiled result for one open even cumulene. -/
structure LocalizedEvenCumuleneAxialResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  topology : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel
  leftCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  assignment : AxialAssignment input.Atom

/-- Detect an open even cumulene, compile both terminal pairs through complete occurrence-local
Rules 1a--5, and assign its exact axial descriptor. -/
noncomputable def localizedEvenCumuleneAxialAssignmentWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedEvenCumuleneAxialResult carrierFuel) := do
  let topology ← input.localizedEvenCumuleneEndpointCursorFrame?
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence
  let leftCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    target view rule3FrameOf topology.initial.left topology.initial.right
      topology.initial.leftCursor
  let rightCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    target view rule3FrameOf topology.right topology.rightPartner topology.rightCursor
  let assignment ← input.localizedAxialAssignmentOfEndpointFrames?
    topology.initial.left topology.right
    leftCompilation.endpointFrame rightCompilation.endpointFrame
  some { topology, leftCompilation, rightCompilation, assignment }

/-- Independent topology, endpoint-key, and exact P-92 geometry meaning of the complete result. -/
def DeclarativeLocalizedEvenCumuleneAxialAssignmentWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedEvenCumuleneAxialResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
      occurrence result.topology ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.topology.initial.left
      result.topology.initial.right result.topology.initial.leftCursor
      result.leftCompilation ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.topology.right result.topology.rightPartner
      result.topology.rightCursor result.rightCompilation ∧
    input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
      result.topology.initial.left result.topology.right
      result.leftCompilation.endpointFrame result.rightCompilation.endpointFrame
      result.assignment

/-- The full even-cumulene compiler is sound for every independently sound smaller Rule-3
callback.  Thus no final `Rₐ/Sₐ` assertion enters as an unproved annotation. -/
theorem localizedEvenCumuleneAxialAssignmentWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedEvenCumuleneAxialResult carrierFuel)
    (computed : input.localizedEvenCumuleneAxialAssignmentWith?
      target occurrence view rule3FrameOf = some result) :
    input.DeclarativeLocalizedEvenCumuleneAxialAssignmentWith
      target occurrence view Rule3FrameMeaning result := by
  unfold localizedEvenCumuleneAxialAssignmentWith? at computed
  cases topologyComputed : input.localizedEvenCumuleneEndpointCursorFrame?
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
              cases assignmentComputed : input.localizedAxialAssignmentOfEndpointFrames?
                  topology.initial.left topology.right leftCompilation.endpointFrame
                    rightCompilation.endpointFrame with
              | none =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    assignmentComputed] at computed
              | some assignment =>
                  simp [topologyComputed, leftComputed, rightComputed,
                    assignmentComputed] at computed
                  subst result
                  exact ⟨
                    input.localizedEvenCumuleneEndpointCursorFrame?_sound
                      (input.localizedRule3CumulatedTraversalFuel carrierFuel)
                      occurrence topology topologyComputed,
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                      topology.initial.left topology.initial.right
                      topology.initial.leftCursor leftCompilation leftComputed,
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                      topology.right topology.rightPartner topology.rightCursor
                      rightCompilation rightComputed,
                    input.localizedAxialAssignmentOfEndpointFrames?_sound
                      topology.initial.left topology.right leftCompilation.endpointFrame
                      rightCompilation.endpointFrame assignment assignmentComputed⟩

/-- Conservative recursion index for the concrete descriptor-bearing endpoint evaluator.  It is
the same finite square bound used by the replacement localized Rules-1a--5 descriptor path. -/
def localizedEvenCumuleneAxialRule3EvaluationFuel (carrierFuel : Nat) : Nat :=
  let span := 2 * (carrierFuel + 1) + 1
  span * span

/-- Concrete even-cumulene evaluator.  Unlike the parameterized seam above, this function installs
the proved well-founded descriptor-bearing Rule-3 frame builder used by the replacement
Rules-1a--5 path. -/
noncomputable def localizedEvenCumuleneAxialAssignment?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedEvenCumuleneAxialResult carrierFuel) :=
  input.localizedEvenCumuleneAxialAssignmentWith? target occurrence view
    (input.buildLocalizedDescriptorBearingRule3Frame? target view
      (localizedEvenCumuleneAxialRule3EvaluationFuel carrierFuel))

/-- Independent meaning of the concrete result, specialized to the well-founded replacement
Rule-3 derivation at the selected finite index. -/
def DeclarativeLocalizedEvenCumuleneAxialAssignment
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (result : input.LocalizedEvenCumuleneAxialResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedEvenCumuleneAxialAssignmentWith target occurrence view
    (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
      (localizedEvenCumuleneAxialRule3EvaluationFuel carrierFuel)) result

/-- The callback-free evaluator inherits the complete topology, priority, and geometry proof. -/
theorem localizedEvenCumuleneAxialAssignment?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (result : input.LocalizedEvenCumuleneAxialResult carrierFuel)
    (computed : input.localizedEvenCumuleneAxialAssignment?
      target occurrence view = some result) :
    input.DeclarativeLocalizedEvenCumuleneAxialAssignment
      target occurrence view result := by
  exact input.localizedEvenCumuleneAxialAssignmentWith?_sound
    target occurrence view
    (input.buildLocalizedDescriptorBearingRule3Frame? target view
      (localizedEvenCumuleneAxialRule3EvaluationFuel carrierFuel))
    (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
      (localizedEvenCumuleneAxialRule3EvaluationFuel carrierFuel))
    (fun cursors frame frameComputed =>
      input.buildLocalizedDescriptorBearingRule3Frame?_sound target view
        (localizedEvenCumuleneAxialRule3EvaluationFuel carrierFuel)
        cursors frame frameComputed)
    result computed

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
