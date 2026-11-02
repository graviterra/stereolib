import TetraStereo.OneCenter.LocalizedDescriptorBearingSchedulerAffineInvariance

/-!
# Affine invariance of the open-even-cumulene axial analyzer

This module transports the complete open-even-cumulene result: perceived endpoint topology,
recursive descriptor-bearing endpoint compilations, exact axial geometry, scheduled dependency
state, and public whole-molecule assignments.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

@[simp] theorem localizedEvenCumuleneEndpointCursorFrame?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (traversalFuel : Nat) (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedEvenCumuleneEndpointCursorFrame?
        traversalFuel (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedEvenCumuleneEndpointCursorFrame? traversalFuel occurrence).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedEvenCumuleneEndpointCursorFrame?
  rw [localizedRule3CumulatedEndpointCursorFrame?_mapSpatialPoints]
  cases frameEq : input.localizedRule3CumulatedEndpointCursorFrame?
      traversalFuel occurrence with
  | none => rfl
  | some frame =>
      dsimp
      by_cases even : 1 < frame.doubleBondCount ∧ Even frame.doubleBondCount <;>
        simp [LocalizedRule3CumulatedEndpointCursorFrame.doubleBondCount,
          LocalizedRule3CumulatedEndpointCursorFrame.mapSpatialPoints, even]

@[simp] theorem localizedAxialEndpointPair?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedAxialEndpointPair?
        (frame.mapSpatialPoints mapPoint) =
      input.localizedAxialEndpointPair? frame := by
  unfold localizedAxialEndpointPair?
  simp only [LocalizedRule3EndpointKeyFrame.mapSpatialPoints]
  rw [compareLocalizedOccurrenceRule3Through5Keys_mapSpatialPoints]
  apply Option.ext
  intro pair
  rfl

/-- Endpoint ordering, coordinate lookup, axial sign, and construction of the public assignment
all commute with an orientation-preserving affine map. -/
theorem localizedAxialAssignmentOfEndpointFrames?_orientationPreservingAffine
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    (input.mapSpatialPoints transform.applyPoint).localizedAxialAssignmentOfEndpointFrames?
        axisStart axisEnd
        (startFrame.mapSpatialPoints transform.applyPoint)
        (endFrame.mapSpatialPoints transform.applyPoint) =
      input.localizedAxialAssignmentOfEndpointFrames?
        axisStart axisEnd startFrame endFrame := by
  unfold localizedAxialAssignmentOfEndpointFrames?
  rw [localizedAxialEndpointPair?_mapSpatialPoints,
    localizedAxialEndpointPair?_mapSpatialPoints]
  cases startPairEq : input.localizedAxialEndpointPair? startFrame with
  | none => simp [startPairEq]
  | some startPair =>
      rcases startPair with ⟨startHigh, startLow⟩
      dsimp
      cases endPairEq : input.localizedAxialEndpointPair? endFrame with
      | none => simp [startPairEq, endPairEq]
      | some endPair =>
          rcases endPair with ⟨endHigh, endLow⟩
          dsimp
          simp only [spatialPointAt?_mapSpatialPoints]
          cases axisStartPointEq : input.spatialPointAt? axisStart with
          | none => simp [startPairEq, endPairEq, axisStartPointEq]
          | some axisStartPoint =>
              cases axisEndPointEq : input.spatialPointAt? axisEnd with
              | none =>
                  simp [startPairEq, endPairEq, axisStartPointEq, axisEndPointEq]
              | some axisEndPoint =>
                  cases startHighPointEq : input.spatialPointAt? startHigh with
                  | none =>
                      simp [startPairEq, endPairEq, axisStartPointEq, axisEndPointEq,
                        startHighPointEq]
                  | some startHighPoint =>
                      cases endHighPointEq : input.spatialPointAt? endHigh with
                      | none =>
                          simp [startPairEq, endPairEq, axisStartPointEq, axisEndPointEq,
                            startHighPointEq, endHighPointEq]
                      | some endHighPoint =>
                          simp only [startPairEq, endPairEq, axisStartPointEq,
                            axisEndPointEq, startHighPointEq, endHighPointEq,
                            Option.map_some, Option.bind_some]
                          rw [axialDescriptorOfSpatialReferences?_orientationPreservingAffine
                            transform orientationPreserving axisStartPoint axisEndPoint
                              startHighPoint endHighPoint]

/-- Canonical transport of the complete compiled result. -/
def LocalizedEvenCumuleneAxialResult.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (result : input.LocalizedEvenCumuleneAxialResult fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedEvenCumuleneAxialResult fuel :=
  { topology := result.topology.mapSpatialPoints mapPoint
    leftCompilation := result.leftCompilation.mapSpatialPoints mapPoint
    rightCompilation := result.rightCompilation.mapSpatialPoints mapPoint
    assignment := result.assignment }

/-- The callback-free production compiler for one open even cumulene is affine-natural. -/
theorem localizedEvenCumuleneAxialAssignment?_orientationPreservingAffine
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    (input.mapSpatialPoints transform.applyPoint).localizedEvenCumuleneAxialAssignment?
        (target.mapSpatialPoints transform.applyPoint)
        (occurrence.mapSpatialPoints transform.applyPoint)
        (view.mapSpatialPoints transform.applyPoint) =
      (input.localizedEvenCumuleneAxialAssignment? target occurrence view).map
        (fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedEvenCumuleneAxialAssignment?
    localizedEvenCumuleneAxialAssignmentWith?
  have determinantNonzero : transform.determinant ≠ 0 := ne_of_gt orientationPreserving
  simp only [localizedRule3CumulatedTraversalFuel]
  rw [localizedEvenCumuleneEndpointCursorFrame?_mapSpatialPoints]
  cases topologyEq : input.localizedEvenCumuleneEndpointCursorFrame?
      (localizedOccurrenceRerootEvaluationFuel fuel) occurrence with
  | none => simp [topologyEq]
  | some topology =>
      dsimp
      simp only [LocalizedRule3CumulatedEndpointCursorFrame.mapSpatialPoints,
        LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
      rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
        input target view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view
            (localizedEvenCumuleneAxialRule3EvaluationFuel fuel))
          transform.applyPoint
          ((input.mapSpatialPoints transform.applyPoint)
            |>.buildLocalizedDescriptorBearingRule3Frame?
              (target.mapSpatialPoints transform.applyPoint)
              (view.mapSpatialPoints transform.applyPoint)
              (localizedEvenCumuleneAxialRule3EvaluationFuel fuel))
          (fun cursors => buildLocalizedDescriptorBearingRule3Frame?_affine
            input target view (localizedEvenCumuleneAxialRule3EvaluationFuel fuel)
              cursors transform determinantNonzero)]
      cases leftEq : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view
            (localizedEvenCumuleneAxialRule3EvaluationFuel fuel))
          topology.initial.left topology.initial.right topology.initial.leftCursor with
      | none => rfl
      | some leftCompilation =>
          simp only [Option.map_some, Option.bind_some]
          rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
            input target view
              (input.buildLocalizedDescriptorBearingRule3Frame? target view
                (localizedEvenCumuleneAxialRule3EvaluationFuel fuel))
              transform.applyPoint
              ((input.mapSpatialPoints transform.applyPoint)
                |>.buildLocalizedDescriptorBearingRule3Frame?
                  (target.mapSpatialPoints transform.applyPoint)
                  (view.mapSpatialPoints transform.applyPoint)
                  (localizedEvenCumuleneAxialRule3EvaluationFuel fuel))
              (fun cursors => buildLocalizedDescriptorBearingRule3Frame?_affine
                input target view (localizedEvenCumuleneAxialRule3EvaluationFuel fuel)
                  cursors transform determinantNonzero)]
          cases rightEq : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view
              (input.buildLocalizedDescriptorBearingRule3Frame? target view
                (localizedEvenCumuleneAxialRule3EvaluationFuel fuel))
              topology.right topology.rightPartner topology.rightCursor with
          | none => rfl
          | some rightCompilation =>
              simp only [Option.map_some, Option.bind_some,
                LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
                LocalizedRule3CumulatedEndpointCursorFrame.mapSpatialPoints]
              rw [localizedAxialAssignmentOfEndpointFrames?_orientationPreservingAffine
                input topology.initial.left topology.right
                  leftCompilation.endpointFrame rightCompilation.endpointFrame transform
                  orientationPreserving]
              cases assignmentEq : input.localizedAxialAssignmentOfEndpointFrames?
                  topology.initial.left topology.right leftCompilation.endpointFrame
                    rightCompilation.endpointFrame <;>
                simp [LocalizedEvenCumuleneAxialResult.mapSpatialPoints,
                  LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
                  LocalizedRule3CumulatedEndpointCursorFrame.mapSpatialPoints,
                  LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints,
                  assignmentEq]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
