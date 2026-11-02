import TetraStereo.OneCenter.Euclidean

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

noncomputable section

namespace TetrahedralGeometry
namespace Realization

/-- A realization is *achiral* (in the rigid Euclidean sense) if it is properly Euclidean
congruent to an orientation-reversing Euclidean image of itself. -/
def Achiral (g : Realization) : Prop :=
  ∃ h : Realization, OrientationReversingEuclideanImage g h ∧
    OrientationPreservingEuclideanEquivalent g h

/-- A realization is *chiral* if it is not achiral. -/
def Chiral (g : Realization) : Prop :=
  ¬ Achiral g

theorem not_orientationPreservingEuclideanEquivalent_of_orientationReversingEuclideanImage
    {g h : Realization} (hgh : OrientationReversingEuclideanImage g h) :
    ¬ OrientationPreservingEuclideanEquivalent g h := by
  intro hpres
  have hpos := handedness_eq_of_orientationPreservingEuclideanEquivalent hpres
  have hneg := handedness_eq_neg_of_orientationReversingEuclideanImage hgh
  have hcontra : handedness g.1 = -handedness g.1 := by
    calc
      handedness g.1 = handedness h.1 := hpos
      _ = -handedness g.1 := hneg
  rcases g.handedness_eq_one_or_eq_neg_one with hg | hg
  · have : (1 : ℝ) = -1 := by simpa [hg] using hcontra
    norm_num at this
  · have : (-1 : ℝ) = 1 := by simpa [hg] using hcontra
    norm_num at this

/-- Every nondegenerate tetrahedral realization with its vertex ordering fixed is rigidly chiral:
it cannot be properly Euclidean congruent to any orientation-reversing image of itself. -/
theorem chiral (g : Realization) : Chiral g := by
  intro hachiral
  rcases hachiral with ⟨h, hrev, hpres⟩
  exact (not_orientationPreservingEuclideanEquivalent_of_orientationReversingEuclideanImage hrev)
    hpres

/-- The handedness classifier on proper Euclidean congruence classes agrees with the affine
chirality-class classifier after forgetting down to affine chirality. -/
theorem classifyProperEuclideanClass_eq_classHandedness_toAffineChiralityClass
    (c : ProperEuclideanClass) :
    classifyProperEuclideanClass c = classHandedness (toAffineChiralityClass c) := by
  refine Quotient.inductionOn c ?_
  intro g
  simp

end Realization
end TetrahedralGeometry

end

end OneCenter
end TetraStereo
