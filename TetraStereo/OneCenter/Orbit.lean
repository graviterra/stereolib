import TetraStereo.OneCenter.Classification

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

noncomputable section

namespace TetrahedralGeometry

namespace Realization

/-- Two nondegenerate realizations are orientation-preserving affine equivalent when one is an
orientation-preserving affine image of the other. -/
def OrientationPreservingAffineEquivalent (g h : Realization) : Prop :=
  OrientationPreservingAffineImage g.1 h.1

/-- Two nondegenerate realizations are orientation-reversing affine equivalent when one is an
orientation-reversing affine image of the other. -/
def OrientationReversingAffineEquivalent (g h : Realization) : Prop :=
  OrientationReversingAffineImage g.1 h.1

/-- The linear part of the unique affine transition from `g` to `h`, expressed in standard-model
coordinates. -/
def affineTransitionLinear (g h : Realization) : Matrix (Fin 3) (Fin 3) ℝ :=
  (AffineCoordinates.ofGeometry g.1).linear⁻¹ * (AffineCoordinates.ofGeometry h.1).linear

/-- The translation part of the unique affine transition from `g` to `h`, expressed in
standard-model coordinates. -/
def affineTransitionTranslation (g h : Realization) : EuclideanSpace ℝ (Fin 3) :=
  (AffineCoordinates.ofGeometry h.1).translation -
    applyMatrix (affineTransitionLinear g h) (AffineCoordinates.ofGeometry g.1).translation

@[simp] theorem det_affineCoordinates_ne_zero (g : Realization) :
    Matrix.det (AffineCoordinates.ofGeometry g.1).linear ≠ 0 := by
  simpa [AffineCoordinates.ofGeometry, Nondegenerate, orientedVolume_eq_edgeMatrix_det] using g.2

theorem affineTransition_eq (g h : Realization) :
    TetrahedralGeometry.mapAffine g.1 (affineTransitionLinear g h) (affineTransitionTranslation g h) =
      h.1 := by
  let pg := AffineCoordinates.ofGeometry g.1
  let ph := AffineCoordinates.ofGeometry h.1
  have hgUnit : IsUnit (Matrix.det pg.linear) :=
    isUnit_iff_ne_zero.mpr (det_affineCoordinates_ne_zero g)
  have hlinear :
      pg.linear * affineTransitionLinear g h = ph.linear := by
    change pg.linear * (pg.linear⁻¹ * ph.linear) = ph.linear
    have hmul :
        (pg.linear * pg.linear⁻¹) * ph.linear = (1 : Matrix (Fin 3) (Fin 3) ℝ) * ph.linear := by
      exact congrArg (fun M => M * ph.linear) (pg.linear.mul_nonsing_inv hgUnit)
    simpa [Matrix.mul_assoc] using hmul
  have htranslation :
      applyMatrix (affineTransitionLinear g h) pg.translation + affineTransitionTranslation g h =
        ph.translation := by
    ext j
    dsimp [affineTransitionTranslation, pg, ph]
    simp [sub_eq_add_neg]
  calc
    TetrahedralGeometry.mapAffine g.1 (affineTransitionLinear g h) (affineTransitionTranslation g h)
        = TetrahedralGeometry.mapAffine pg.realize
            (affineTransitionLinear g h) (affineTransitionTranslation g h) := by
              rw [← AffineCoordinates.realize_ofGeometry g.1]
    _ = TetrahedralGeometry.mapAffine modelGeometry
          (pg.linear * affineTransitionLinear g h)
          (applyMatrix (affineTransitionLinear g h) pg.translation +
            affineTransitionTranslation g h) := by
              simp [AffineCoordinates.realize, pg, TetrahedralGeometry.mapAffine_mapAffine]
    _ = TetrahedralGeometry.mapAffine modelGeometry ph.linear ph.translation := by
              rw [hlinear, htranslation]
    _ = h.1 := by
          rw [← AffineCoordinates.realize_ofGeometry h.1]
          simp [AffineCoordinates.realize, ph]

@[simp] theorem det_affineTransitionLinear (g h : Realization) :
    Matrix.det (affineTransitionLinear g h) =
      (Matrix.det (AffineCoordinates.ofGeometry g.1).linear)⁻¹ *
        Matrix.det (AffineCoordinates.ofGeometry h.1).linear := by
  rw [affineTransitionLinear, Matrix.det_mul, Matrix.det_nonsing_inv]
  simp

theorem pos_of_realSign_eq_one {x : ℝ} (hx : Real.sign x = 1) : 0 < x := by
  obtain hneg | rfl | hpos := lt_trichotomy x 0
  · have : (-1 : ℝ) = 1 := by simpa [Real.sign_of_neg hneg] using hx
    norm_num at this
  · simp at hx
  · exact hpos

theorem neg_of_realSign_eq_neg_one {x : ℝ} (hx : Real.sign x = -1) : x < 0 := by
  obtain hneg | rfl | hpos := lt_trichotomy x 0
  · exact hneg
  · simp at hx
  · have : (1 : ℝ) = -1 := by simpa [Real.sign_of_pos hpos] using hx
    norm_num at this

theorem orientationPreservingAffineEquivalent_of_handedness_eq
    {g h : Realization} (hgh : handedness g.1 = handedness h.1) :
    OrientationPreservingAffineEquivalent g h := by
  refine ⟨affineTransitionLinear g h, affineTransitionTranslation g h, ?_,
    (affineTransition_eq g h).symm⟩
  let dg := Matrix.det (AffineCoordinates.ofGeometry g.1).linear
  let dh := Matrix.det (AffineCoordinates.ofGeometry h.1).linear
  have hsg : Real.sign dg = handedness g.1 := by
    simpa [dg] using (handedness_eq_sign_det_affineCoordinates g.1).symm
  have hsh : Real.sign dh = handedness h.1 := by
    simpa [dh] using (handedness_eq_sign_det_affineCoordinates h.1).symm
  rcases g.handedness_eq_one_or_eq_neg_one with hg | hg
  · have hh : handedness h.1 = 1 := by rw [← hgh, hg]
    have hdg : 0 < dg := pos_of_realSign_eq_one (by simpa [hg] using hsg)
    have hdh : 0 < dh := pos_of_realSign_eq_one (by simpa [hh] using hsh)
    change 0 < Matrix.det (affineTransitionLinear g h)
    rw [det_affineTransitionLinear]
    exact mul_pos (inv_pos.mpr hdg) hdh
  · have hh : handedness h.1 = -1 := by rw [← hgh, hg]
    have hdg : dg < 0 := neg_of_realSign_eq_neg_one (by simpa [hg] using hsg)
    have hdh : dh < 0 := neg_of_realSign_eq_neg_one (by simpa [hh] using hsh)
    change 0 < Matrix.det (affineTransitionLinear g h)
    rw [det_affineTransitionLinear]
    exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr hdg) hdh

theorem orientationReversingAffineEquivalent_of_handedness_eq_neg
    {g h : Realization} (hgh : handedness h.1 = -handedness g.1) :
    OrientationReversingAffineEquivalent g h := by
  refine ⟨affineTransitionLinear g h, affineTransitionTranslation g h, ?_,
    (affineTransition_eq g h).symm⟩
  let dg := Matrix.det (AffineCoordinates.ofGeometry g.1).linear
  let dh := Matrix.det (AffineCoordinates.ofGeometry h.1).linear
  have hsg : Real.sign dg = handedness g.1 := by
    simpa [dg] using (handedness_eq_sign_det_affineCoordinates g.1).symm
  have hsh : Real.sign dh = handedness h.1 := by
    simpa [dh] using (handedness_eq_sign_det_affineCoordinates h.1).symm
  rcases g.handedness_eq_one_or_eq_neg_one with hg | hg
  · have hh : handedness h.1 = -1 := by simpa [hg] using hgh
    have hdg : 0 < dg := pos_of_realSign_eq_one (by simpa [hg] using hsg)
    have hdh : dh < 0 := neg_of_realSign_eq_neg_one (by simpa [hh] using hsh)
    change Matrix.det (affineTransitionLinear g h) < 0
    rw [det_affineTransitionLinear]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hdg) hdh
  · have hh : handedness h.1 = 1 := by simpa [hg] using hgh
    have hdg : dg < 0 := neg_of_realSign_eq_neg_one (by simpa [hg] using hsg)
    have hdh : 0 < dh := pos_of_realSign_eq_one (by simpa [hh] using hsh)
    change Matrix.det (affineTransitionLinear g h) < 0
    rw [det_affineTransitionLinear]
    exact mul_neg_of_neg_of_pos (inv_lt_zero.mpr hdg) hdh

theorem orientationPreservingAffineEquivalent_iff
    (g h : Realization) :
    OrientationPreservingAffineEquivalent g h ↔ handedness g.1 = handedness h.1 := by
  constructor
  · intro hgh
    simpa [OrientationPreservingAffineEquivalent, eq_comm] using
      handedness_eq_of_orientationPreservingAffineImage hgh
  · intro hgh
    exact orientationPreservingAffineEquivalent_of_handedness_eq hgh

theorem orientationReversingAffineEquivalent_iff
    (g h : Realization) :
    OrientationReversingAffineEquivalent g h ↔ handedness h.1 = -handedness g.1 := by
  constructor
  · intro hgh
    simpa [OrientationReversingAffineEquivalent] using
      handedness_neg_eq_of_orientationReversingAffineImage hgh
  · intro hgh
    exact orientationReversingAffineEquivalent_of_handedness_eq_neg hgh

theorem orientationPreservingAffineEquivalent_refl (g : Realization) :
    OrientationPreservingAffineEquivalent g g :=
  (orientationPreservingAffineEquivalent_iff g g).2 rfl

theorem orientationPreservingAffineEquivalent_symm {g h : Realization}
    (hgh : OrientationPreservingAffineEquivalent g h) :
    OrientationPreservingAffineEquivalent h g :=
  (orientationPreservingAffineEquivalent_iff h g).2
    ((orientationPreservingAffineEquivalent_iff g h).1 hgh).symm

theorem orientationPreservingAffineEquivalent_trans {g h k : Realization}
    (hgh : OrientationPreservingAffineEquivalent g h)
    (hhk : OrientationPreservingAffineEquivalent h k) :
    OrientationPreservingAffineEquivalent g k :=
  (orientationPreservingAffineEquivalent_iff g k).2
    (((orientationPreservingAffineEquivalent_iff g h).1 hgh).trans
      ((orientationPreservingAffineEquivalent_iff h k).1 hhk))

theorem affineEquivalent (g h : Realization) :
    OrientationPreservingAffineEquivalent g h ∨
      OrientationReversingAffineEquivalent g h := by
  rcases g.handedness_eq_one_or_eq_neg_one with hg | hg
  · rcases h.handedness_eq_one_or_eq_neg_one with hh | hh
    · left
      exact orientationPreservingAffineEquivalent_of_handedness_eq (by simp [hg, hh])
    · right
      exact orientationReversingAffineEquivalent_of_handedness_eq_neg (by simp [hg, hh])
  · rcases h.handedness_eq_one_or_eq_neg_one with hh | hh
    · right
      exact orientationReversingAffineEquivalent_of_handedness_eq_neg (by simp [hg, hh])
    · left
      exact orientationPreservingAffineEquivalent_of_handedness_eq (by simp [hg, hh])

end Realization

end TetrahedralGeometry

end

end OneCenter
end TetraStereo
