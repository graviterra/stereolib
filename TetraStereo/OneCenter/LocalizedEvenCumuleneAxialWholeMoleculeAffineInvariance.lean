import TetraStereo.OneCenter.LocalizedAxialPerceptionAffineInvariance
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAffineInvariance

/-!
# Whole-molecule affine invariance for open even cumulenes

This closes the gap between constitution-only chain perception and the already transported
one-axis compiler, including the production scheduler state and exact output-list order.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

theorem localizedEvenAxialChains_attach_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedEvenAxialChains.attach =
      input.localizedEvenAxialChains.attach.map
        (fun axis => LocalizedEvenAxialChain.mapSpatialPoints axis mapPoint) := by
  apply List.ext_getElem
  · simp [localizedEvenAxialChains_mapSpatialPoints]
  · intro index mappedPresent sourcePresent
    apply Subtype.ext
    simp [localizedEvenAxialChains_mapSpatialPoints,
      LocalizedEvenAxialChain.mapSpatialPoints]

@[simp] theorem localizedEvenAxialRootOccurrence_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedEvenAxialRootOccurrence fuel
        (LocalizedEvenAxialChain.mapSpatialPoints axis mapPoint) =
      (input.localizedEvenAxialRootOccurrence fuel axis).mapSpatialPoints mapPoint := by
  apply Subtype.ext
  rfl

@[simp] theorem localizedEvenAxialFirstChildOccurrence_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedEvenAxialFirstChildOccurrence fuel
        (LocalizedEvenAxialChain.mapSpatialPoints axis mapPoint) =
      (input.localizedEvenAxialFirstChildOccurrence fuel axis).mapSpatialPoints mapPoint := by
  apply Subtype.ext
  rfl

/-- Canonical transport of a public whole-molecule even-axis assignment. -/
def LocalizedEvenAxialSpatialAssignment.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedEvenAxialSpatialAssignment fuel :=
  { axis := LocalizedEvenAxialChain.mapSpatialPoints assignment.axis mapPoint
    result := assignment.result.mapSpatialPoints mapPoint }

theorem localizedEvenAxialSpatialAssignmentAtWithState?_affine
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedEvenAxialChain)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    (input.mapSpatialPoints transform.applyPoint
      |>.localizedEvenAxialSpatialAssignmentAtWithState? fuel
        (state.mapSpatialPoints transform.applyPoint)
        (LocalizedEvenAxialChain.mapSpatialPoints axis transform.applyPoint)) =
      (input.localizedEvenAxialSpatialAssignmentAtWithState? fuel state axis).map
        (fun assignment => assignment.mapSpatialPoints transform.applyPoint) := by
  unfold localizedEvenAxialSpatialAssignmentAtWithState?
  rw [localizedEvenAxialRootOccurrence_mapSpatialPoints,
    localizedEvenAxialFirstChildOccurrence_mapSpatialPoints]
  dsimp only
  rw [localizedDependencyView_state_mapSpatialPoints]
  rw [localizedEvenCumuleneAxialAssignment?_orientationPreservingAffine
    input (input.localizedEvenAxialRootOccurrence fuel axis)
      (input.localizedEvenAxialFirstChildOccurrence fuel axis)
      (input.localizedDependencyView state
        (input.localizedEvenAxialRootOccurrence fuel axis))
      transform orientationPreserving]
  cases input.localizedEvenCumuleneAxialAssignment?
      (input.localizedEvenAxialRootOccurrence fuel axis)
      (input.localizedEvenAxialFirstChildOccurrence fuel axis)
      (input.localizedDependencyView state
        (input.localizedEvenAxialRootOccurrence fuel axis)) <;>
    simp [LocalizedEvenAxialSpatialAssignment.mapSpatialPoints]

private theorem filterMap_evenAxial_affine
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    ∀ axes : List input.LocalizedEvenAxialChain,
      (axes.map fun axis => LocalizedEvenAxialChain.mapSpatialPoints axis
        transform.applyPoint).filterMap
          (fun axis =>
            (input.mapSpatialPoints transform.applyPoint
              |>.localizedEvenAxialSpatialAssignmentAtWithState? fuel
                (state.mapSpatialPoints transform.applyPoint) axis)) =
        (axes.filterMap fun axis =>
          input.localizedEvenAxialSpatialAssignmentAtWithState? fuel state axis).map
            (fun assignment => assignment.mapSpatialPoints transform.applyPoint)
  | [] => rfl
  | axis :: axes => by
      simp only [List.map_cons, List.filterMap_cons]
      rw [localizedEvenAxialSpatialAssignmentAtWithState?_affine
        input fuel state axis transform orientationPreserving]
      cases input.localizedEvenAxialSpatialAssignmentAtWithState? fuel state axis <;>
        simp [filterMap_evenAxial_affine input fuel state transform
          orientationPreserving axes]

theorem analyzeLocalizedEvenCumuleneAxialWithState_affine
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    (input.mapSpatialPoints transform.applyPoint
      |>.analyzeLocalizedEvenCumuleneAxialWithState fuel
        (state.mapSpatialPoints transform.applyPoint)) =
      (input.analyzeLocalizedEvenCumuleneAxialWithState fuel state).map
        (fun assignment => assignment.mapSpatialPoints transform.applyPoint) := by
  unfold analyzeLocalizedEvenCumuleneAxialWithState
  rw [localizedEvenAxialChains_attach_mapSpatialPoints]
  exact filterMap_evenAxial_affine input fuel state transform orientationPreserving
    input.localizedEvenAxialChains.attach

/-- The complete scheduled whole-molecule open-even-cumulene output is affine-invariant. -/
theorem analyzeLocalizedEvenCumuleneAxial_affine
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    (input.mapSpatialPoints transform.applyPoint
      |>.analyzeLocalizedEvenCumuleneAxial fuel) =
      (input.analyzeLocalizedEvenCumuleneAxial fuel).map
        (fun assignment => assignment.mapSpatialPoints transform.applyPoint) := by
  unfold analyzeLocalizedEvenCumuleneAxial
  rw [localizedDescriptorBearingRule3Through5SchedulerState_affine
    input fuel transform orientationPreserving]
  exact analyzeLocalizedEvenCumuleneAxialWithState_affine input fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    transform orientationPreserving

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
