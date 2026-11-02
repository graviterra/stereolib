import TetraStereo.OneCenter.CIPDescriptorBearingPipelineAffineInvariance
import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5FixedPoint

/-!
# Affine invariance of the descriptor-bearing occurrence fixed point

The local Rules-1a--5 evaluator has already been proved natural under every exact rational
orientation-preserving affine change of coordinates.  This file lifts that result through the
mutually dependent occurrence semantics.

The lift does not inspect, reorder, or replay the scheduler.  Instead it transports a complete
state across the proved occurrence bijection, proves pointwise that the transported state is a
fixed point of the mapped evaluator, and invokes the independently established uniqueness of the
CIP model.  Thus scheduler implementation details cannot enter the mathematical conclusion.
-/

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open DeclarativeCIP

/-- Transport a complete optional auxiliary-label state across coordinate mapping. -/
noncomputable def LocalizedAuxiliaryState.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedAuxiliaryState fuel :=
  fun occurrence => state (occurrence.unmapSpatialPoints mapPoint)

@[simp] theorem LocalizedAuxiliaryState.mapSpatialPoints_apply
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    state.mapSpatialPoints mapPoint (occurrence.mapSpatialPoints mapPoint) =
      state occurrence := by
  simp [LocalizedAuxiliaryState.mapSpatialPoints]

/-- Restricting a transported total state gives exactly the previously defined transport of its
proof-restricted dependency view. -/
theorem localizedDependencyView_state_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedDependencyView
        (state.mapSpatialPoints mapPoint) (target.mapSpatialPoints mapPoint) =
      (input.localizedDependencyView state target).mapSpatialPoints mapPoint := by
  funext source dependency
  rfl

/-- An orientation-preserving affine image of any descriptor-bearing Rules-1a--5 CIP model is a
CIP model of the affinely mapped molecule. -/
theorem localizedOccurrenceDescriptorBearingRule3Through5Model_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
        state)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    ((input.mapSpatialPoints transform.applyPoint).localizedAuxiliaryOccurrenceSystem
      ((input.mapSpatialPoints transform.applyPoint)
        |>.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
      (state.mapSpatialPoints transform.applyPoint) := by
  let sourceSystem := input.localizedAuxiliaryOccurrenceSystem
    (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)
  let mappedInput := input.mapSpatialPoints transform.applyPoint
  let mappedSystem := mappedInput.localizedAuxiliaryOccurrenceSystem
    (mappedInput.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)
  have sourceFixed : sourceSystem.executableStateStep state = state :=
    (sourceSystem.cipModel_iff_executableStateStep_fixed
      (input.localizedAuxiliaryDerivationStepCorrespondence
        (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel))
      state).mp model
  apply (mappedSystem.cipModel_iff_executableStateStep_fixed
    (mappedInput.localizedAuxiliaryDerivationStepCorrespondence
      (mappedInput.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel))
    (state.mapSpatialPoints transform.applyPoint)).mpr
  funext mappedTarget
  let target := mappedTarget.unmapSpatialPoints transform.applyPoint
  have mappedTargetEq : target.mapSpatialPoints transform.applyPoint = mappedTarget := by
    exact LocalizedCIPOccurrence.map_unmapSpatialPoints transform.applyPoint mappedTarget
  have sourceAtTarget := congrFun sourceFixed target
  change mappedInput.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
      mappedTarget
      (mappedInput.localizedDependencyView
        (state.mapSpatialPoints transform.applyPoint) mappedTarget) =
    state.mapSpatialPoints transform.applyPoint mappedTarget
  rw [← mappedTargetEq]
  rw [localizedDependencyView_state_mapSpatialPoints]
  rw [localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_orientationPreservingAffine
    input target (input.localizedDependencyView state target)
      transform orientationPreserving]
  simpa [LocalizedAuxiliaryState.mapSpatialPoints, sourceSystem,
    localizedAuxiliaryOccurrenceSystem, localizedExecutableStep,
    localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics] using sourceAtTarget

/-- Model uniqueness is equivariant: the unique model of the mapped molecule is exactly the
transport of the unique model of the source molecule. -/
theorem uniqueLocalizedOccurrenceDescriptorBearingRule3Through5Model_affine
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
        state)
    (transform : RationalAffineFrameTransform)
    (mappedState : (input.mapSpatialPoints transform.applyPoint).LocalizedAuxiliaryState fuel)
    (mappedModel : ((input.mapSpatialPoints transform.applyPoint)
      |>.localizedAuxiliaryOccurrenceSystem
        ((input.mapSpatialPoints transform.applyPoint)
          |>.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
      mappedState)
    (orientationPreserving : 0 < transform.determinant) :
    mappedState = state.mapSpatialPoints transform.applyPoint := by
  let mappedInput := input.mapSpatialPoints transform.applyPoint
  have transportedModel :=
    input.localizedOccurrenceDescriptorBearingRule3Through5Model_mapSpatialPoints
      state model transform orientationPreserving
  obtain ⟨canonical, canonicalModel, unique⟩ :=
    mappedInput.existsUnique_localizedOccurrenceDescriptorBearingRule3Through5Model fuel
  exact (unique mappedState mappedModel).trans
    (unique (state.mapSpatialPoints transform.applyPoint) transportedModel).symm

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
