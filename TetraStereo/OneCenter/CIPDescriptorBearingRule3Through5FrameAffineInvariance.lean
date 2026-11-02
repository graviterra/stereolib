import TetraStereo.OneCenter.CIPRule3DescriptorBearingRecursiveBuilderAffineInvariance
import TetraStereo.OneCenter.CIPRule3Through5FrameAffineInvariance
import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5Descriptor

set_option autoImplicit false

/-!
# Affine invariance of the descriptor-bearing Rules-1a--5 frame

This joins the production descriptor-bearing Rule-3 compiler to the coordinate-independent
Rules 4a--5 compiler and proves naturality of the actual four-ligand key frame consumed by the
tetrahedral descriptor pipeline.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

private theorem mapM_buildLocalizedRerootCompoundRule45Key_descriptorBearing_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      (cursors.map fun cursor => cursor.mapSpatialPoints mapPoint).mapM
          ((input.mapSpatialPoints mapPoint).buildLocalizedRerootCompoundRule45Key?
            (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint) fuel) =
        (cursors.mapM
          (input.buildLocalizedRerootCompoundRule45Key? target view fuel)).map
            (List.map fun key => key.mapSpatialPoints mapPoint)
  | [] => rfl
  | cursor :: cursors => by
      simp only [List.map_cons, List.mapM_cons]
      rw [buildLocalizedRerootCompoundRule45Key?_mapSpatialPoints]
      rw [mapM_buildLocalizedRerootCompoundRule45Key_descriptorBearing_mapSpatialPoints
        input target view fuel mapPoint cursors]
      cases input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor <;>
        cases cursors.mapM
          (input.buildLocalizedRerootCompoundRule45Key? target view fuel) <;> rfl

theorem buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
          (input.mapSpatialPoints transform.applyPoint)
          (target.mapSpatialPoints transform.applyPoint)
          (view.mapSpatialPoints transform.applyPoint)
          (base.mapSpatialPoints transform.applyPoint) =
      (input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
        target view base).map
          (fun frame => frame.mapSpatialPoints transform.applyPoint) := by
  change
    buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
        (input.mapSpatialPoints transform.applyPoint)
      (target.mapSpatialPoints transform.applyPoint)
      (view.mapSpatialPoints transform.applyPoint)
      ({ cursors := base.cursors.map fun cursor =>
            cursor.mapSpatialPoints transform.applyPoint
         length_eq := by simpa using base.length_eq } :
        (input.mapSpatialPoints transform.applyPoint).LocalizedOccurrenceFourLigandFrame
          carrierFuel) = _
  unfold buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
  dsimp only
  rw [buildLocalizedDescriptorBearingRule3Frame?_affine
    input target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      base.cursors transform determinantNonzero]
  cases rule3Eq : input.buildLocalizedDescriptorBearingRule3Frame?
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) base.cursors with
  | none => rfl
  | some rule3Frame =>
      simp only [Option.map_some]
      rw [mapM_buildLocalizedRerootCompoundRule45Key_descriptorBearing_mapSpatialPoints]
      by_cases sourceLength : rule3Frame.keys.length = 4
      · have mappedLength :
            (rule3Frame.mapSpatialPoints transform.applyPoint).keys.length = 4 := by
          simpa [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints] using sourceLength
        simp [sourceLength, mappedLength]
        cases rule45Eq : base.cursors.mapM
            (input.buildLocalizedRerootCompoundRule45Key? target view
              (localizedOccurrenceRerootEvaluationFuel carrierFuel)) with
        | none => rfl
        | some rule45Keys =>
            simp only [Option.map_some, Option.bind_some]
            by_cases rule45Length : rule45Keys.length = 4
            · have mappedRule45Length :
                  (rule45Keys.map fun key =>
                    key.mapSpatialPoints transform.applyPoint).length = 4 := by
                simpa using rule45Length
              simp only [dif_pos rule45Length, dif_pos mappedRule45Length]
              congr
            · simp [rule45Length]
      · have notMappedLength :
            ¬ (rule3Frame.mapSpatialPoints transform.applyPoint).keys.length = 4 := by
          simpa [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints] using sourceLength
        simp [sourceLength, notMappedLength]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
