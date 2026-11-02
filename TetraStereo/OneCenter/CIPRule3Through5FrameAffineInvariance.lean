import TetraStereo.OneCenter.CIPRule45DependencyViewAffineInvariance

/-!
# Affine naturality of the joined occurrence-local Rules-1a--5 frame
-/

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def LocalizedOccurrenceFourLigandFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedOccurrenceFourLigandFrame carrierFuel :=
  { cursors := frame.cursors.map fun cursor => cursor.mapSpatialPoints mapPoint
    length_eq := by simpa using frame.length_eq }

def LocalizedOccurrenceRule3Through5KeyFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedOccurrenceRule3Through5KeyFrame carrierFuel :=
  { rule3Frame := frame.rule3Frame.mapSpatialPoints mapPoint
    rule3Length := by
      simpa [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints] using frame.rule3Length
    rule45Keys := frame.rule45Keys.map fun key => key.mapSpatialPoints mapPoint
    rule45Length := by simpa using frame.rule45Length }

private theorem mapM_buildLocalizedRerootCompoundRule45Key?_mapSpatialPoints
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
      rw [mapM_buildLocalizedRerootCompoundRule45Key?_mapSpatialPoints
        input target view fuel mapPoint cursors]
      cases input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor <;>
        cases cursors.mapM
          (input.buildLocalizedRerootCompoundRule45Key? target view fuel) <;> rfl

theorem buildLocalizedOccurrenceRule3Through5KeyFrame?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).buildLocalizedOccurrenceRule3Through5KeyFrame?
          (target.mapSpatialPoints transform.applyPoint)
          (view.mapSpatialPoints transform.applyPoint)
          (base.mapSpatialPoints transform.applyPoint) =
      (input.buildLocalizedOccurrenceRule3Through5KeyFrame?
        target view base).map
          (fun frame => frame.mapSpatialPoints transform.applyPoint) := by
  change
    (input.mapSpatialPoints transform.applyPoint).buildLocalizedOccurrenceRule3Through5KeyFrame?
      (target.mapSpatialPoints transform.applyPoint)
      (view.mapSpatialPoints transform.applyPoint)
      ({ cursors := base.cursors.map fun cursor =>
            cursor.mapSpatialPoints transform.applyPoint
         length_eq := by simpa using base.length_eq } :
        (input.mapSpatialPoints transform.applyPoint).LocalizedOccurrenceFourLigandFrame
          carrierFuel) = _
  unfold buildLocalizedOccurrenceRule3Through5KeyFrame?
  dsimp only
  rw [buildLocalizedRule3CanonicalKeyFrame?_affine
    input (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      base.cursors transform determinantNonzero]
  cases rule3Eq : input.buildLocalizedRule3CanonicalKeyFrame?
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) base.cursors with
  | none => rfl
  | some rule3Frame =>
      simp only [Option.map_some]
      rw [mapM_buildLocalizedRerootCompoundRule45Key?_mapSpatialPoints]
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
            · have notMappedRule45Length :
                  ¬ (rule45Keys.map fun key =>
                    key.mapSpatialPoints transform.applyPoint).length = 4 := by
                simpa using rule45Length
              simp [rule45Length]
      · have notMappedLength :
            ¬ (rule3Frame.mapSpatialPoints transform.applyPoint).keys.length = 4 := by
          simpa [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints] using sourceLength
        simp [sourceLength, notMappedLength]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
