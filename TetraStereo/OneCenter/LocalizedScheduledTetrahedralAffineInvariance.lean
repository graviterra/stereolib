import TetraStereo.OneCenter.LocalizedDescriptorBearingSchedulerAffineInvariance

/-!
# Affine invariance of scheduled whole-molecule tetrahedral output

This file carries the scheduler-state theorem through the final-center projection and the public
whole-molecule tetrahedral analyzer.  It proves equality of complete output lists after the
canonical transport of their dependent assignment type, including every success and refusal.
-/

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

@[simp] theorem tetrahedralCenterSet_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).tetrahedralCenterSet = input.tetrahedralCenterSet := by
  rfl

@[simp] theorem canonicalTetrahedralCenters_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).canonicalTetrahedralCenters =
      input.canonicalTetrahedralCenters := by
  rfl

@[simp] theorem localizedFinalOccurrence_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedFinalOccurrence fuel center =
      (input.localizedFinalOccurrence fuel center).mapSpatialPoints mapPoint := by
  apply Subtype.ext
  rfl

/-- Canonical transport of a public scheduled tetrahedral assignment. -/
def LocalizedScheduledTetrahedralSpatialAssignment.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedScheduledTetrahedralSpatialAssignment fuel :=
  { center := assignment.center
    descriptor := assignment.descriptor }

/-- A final-center scheduler read commutes with an orientation-preserving affine map. -/
theorem localizedScheduledTetrahedralSpatialAssignmentAt?_affine
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    (input.mapSpatialPoints transform.applyPoint
      |>.localizedScheduledTetrahedralSpatialAssignmentAt? fuel center) =
      (input.localizedScheduledTetrahedralSpatialAssignmentAt? fuel center).map
        (fun assignment => assignment.mapSpatialPoints transform.applyPoint) := by
  unfold localizedScheduledTetrahedralSpatialAssignmentAt?
  rw [localizedDescriptorBearingRule3Through5SchedulerState_affine
    input fuel transform orientationPreserving]
  rw [localizedFinalOccurrence_mapSpatialPoints]
  cases stateAtCenter :
      input.localizedDescriptorBearingRule3Through5SchedulerState fuel
        (input.localizedFinalOccurrence fuel center) <;>
    simp [LocalizedAuxiliaryState.mapSpatialPoints,
      LocalizedScheduledTetrahedralSpatialAssignment.mapSpatialPoints, stateAtCenter]

private theorem filterMap_scheduledTetrahedral_affine
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    ∀ centers : List input.TetrahedralCenter,
      centers.filterMap (fun center =>
          (input.mapSpatialPoints transform.applyPoint
            |>.localizedScheduledTetrahedralSpatialAssignmentAt? fuel center)) =
        (centers.filterMap fun center =>
          input.localizedScheduledTetrahedralSpatialAssignmentAt? fuel center).map
            (fun assignment => assignment.mapSpatialPoints transform.applyPoint)
  | [] => rfl
  | center :: centers => by
      rw [List.filterMap_cons, List.filterMap_cons,
        localizedScheduledTetrahedralSpatialAssignmentAt?_affine
          input fuel center transform orientationPreserving]
      cases input.localizedScheduledTetrahedralSpatialAssignmentAt? fuel center <;>
        simp [filterMap_scheduledTetrahedral_affine input fuel transform
          orientationPreserving centers]

/-- The complete scheduled tetrahedral output list is invariant under every exact rational
orientation-preserving affine coordinate change, modulo canonical assignment transport. -/
theorem analyzeLocalizedScheduledTetrahedralSpatial_affine
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    (input.mapSpatialPoints transform.applyPoint
      |>.analyzeLocalizedScheduledTetrahedralSpatial fuel) =
      (input.analyzeLocalizedScheduledTetrahedralSpatial fuel).map
        (fun assignment => assignment.mapSpatialPoints transform.applyPoint) := by
  unfold analyzeLocalizedScheduledTetrahedralSpatial
  rw [canonicalTetrahedralCenters_mapSpatialPoints]
  exact filterMap_scheduledTetrahedral_affine input fuel transform
    orientationPreserving input.canonicalTetrahedralCenters

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
