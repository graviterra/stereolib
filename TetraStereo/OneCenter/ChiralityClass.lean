import TetraStereo.OneCenter.Orbit
import TetraStereo.OneCenter.Toy

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

noncomputable section

namespace TetrahedralGeometry

namespace Realization

/-! ## Setoid and quotient type -/

def realizationSetoid : Setoid Realization where
  r := OrientationPreservingAffineEquivalent
  iseqv := ⟨orientationPreservingAffineEquivalent_refl,
            orientationPreservingAffineEquivalent_symm,
            orientationPreservingAffineEquivalent_trans⟩

/-- The quotient of nondegenerate realizations by orientation-preserving affine equivalence. -/
abbrev AffineChiralityClass := Quotient realizationSetoid

/-- Backward-compatible name for the current affine chirality quotient. -/
abbrev ChiralityClass := AffineChiralityClass

/-! ## Canonical representatives -/

def canonicalRealization (sigma : Frame) : Realization :=
  ⟨canonicalGeometry sigma, canonicalGeometry_nondegenerate sigma⟩

@[simp] theorem handedness_canonicalRealization (sigma : Frame) :
    handedness (canonicalRealization sigma).1 = permHandedness sigma :=
  canonicalHandedness_matches_parity sigma

def plusRealization : Realization := canonicalRealization rightHandedFrame
def minusRealization : Realization := canonicalRealization leftHandedFrame

@[simp] theorem handedness_plusRealization : handedness plusRealization.1 = 1 := by
  simp [plusRealization]

@[simp] theorem handedness_minusRealization : handedness minusRealization.1 = -1 := by
  simp [minusRealization]

def chiralPlus : ChiralityClass := Quotient.mk realizationSetoid plusRealization
def chiralMinus : ChiralityClass := Quotient.mk realizationSetoid minusRealization

/-! ## Forward map: ChiralityClass → StereoQ -/

def classifyRealization (g : Realization) : StereoQ :=
  if handedness g.1 = 1 then qPlus else qMinus

@[simp] theorem classifyRealization_of_pos {g : Realization} (hg : handedness g.1 = 1) :
    classifyRealization g = qPlus := by
  simp [classifyRealization, hg]

@[simp] theorem classifyRealization_of_neg {g : Realization} (hg : handedness g.1 = -1) :
    classifyRealization g = qMinus := by
  simp [classifyRealization, hg]
  norm_num

theorem classifyRealization_respectsEquivalence (g h : Realization)
    (hgh : OrientationPreservingAffineEquivalent g h) :
    classifyRealization g = classifyRealization h := by
  have heq := (orientationPreservingAffineEquivalent_iff g h).1 hgh
  simp [classifyRealization, heq]

def classifyChirality : ChiralityClass → StereoQ :=
  Quotient.lift classifyRealization classifyRealization_respectsEquivalence

/-- The handedness of a chirality class, valued in the two-point chirality type. -/
abbrev classHandedness : ChiralityClass → StereoQ := classifyChirality

@[simp] theorem classifyChirality_mk (g : Realization) :
    classifyChirality (Quotient.mk realizationSetoid g) = classifyRealization g := rfl

@[simp] theorem classHandedness_mk (g : Realization) :
    classHandedness (Quotient.mk realizationSetoid g) = classifyRealization g := rfl

/-! ## Inverse map: StereoQ → ChiralityClass -/

def embedFrame (sigma : Frame) : ChiralityClass :=
  Quotient.mk realizationSetoid (canonicalRealization sigma)

theorem embedFrame_respectsEquivalence (sigma tau : Frame)
    (hst : SameClass sigma tau) : embedFrame sigma = embedFrame tau := by
  apply Quotient.sound
  rw [realizationSetoid]
  show OrientationPreservingAffineEquivalent
    (canonicalRealization sigma) (canonicalRealization tau)
  exact (orientationPreservingAffineEquivalent_iff _ _).2
    ((sameCanonicalHandedness_iff_sameClass sigma tau).2 hst)

def embedChirality : StereoQ → ChiralityClass :=
  Quotient.lift embedFrame embedFrame_respectsEquivalence

/-! ## Round-trip proofs -/

theorem classifyChirality_embedChirality (q : StereoQ) :
    classifyChirality (embedChirality q) = q := by
  refine Quotient.inductionOn q ?_
  intro sigma
  show classifyRealization (canonicalRealization sigma) = Quotient.mk frameSetoid sigma
  rcases permHandedness_eq_one_or_eq_neg_one sigma with hsigma | hsigma
  · have hc : classifyRealization (canonicalRealization sigma) = qPlus := by
      simp [classifyRealization, hsigma]
    rw [hc, qPlus]
    exact @Quotient.sound _ frameSetoid _ _ (show SameClass rightHandedFrame sigma by
      rw [SameClass, permHandedness_rightHandedFrame, hsigma])
  · have hne : handedness (canonicalRealization sigma).1 ≠ 1 := by
      simp [hsigma]; norm_num
    have hc : classifyRealization (canonicalRealization sigma) = qMinus := by
      unfold classifyRealization; exact if_neg hne
    rw [hc, qMinus]
    exact @Quotient.sound _ frameSetoid _ _ (show SameClass leftHandedFrame sigma by
      rw [SameClass, permHandedness_leftHandedFrame, hsigma])

theorem embedChirality_classifyChirality (c : ChiralityClass) :
    embedChirality (classifyChirality c) = c := by
  refine Quotient.inductionOn c ?_
  intro g
  show embedChirality (classifyRealization g) = Quotient.mk realizationSetoid g
  rcases g.handedness_eq_one_or_eq_neg_one with hg | hg
  · have hc : classifyRealization g = qPlus := by
      simp [classifyRealization, hg]
    rw [hc]
    show embedFrame rightHandedFrame = Quotient.mk realizationSetoid g
    exact @Quotient.sound _ realizationSetoid _ _
      ((orientationPreservingAffineEquivalent_iff _ _).2 (by simp [hg]))
  · have hne : handedness g.1 ≠ 1 := by simp [hg]; norm_num
    have hc : classifyRealization g = qMinus := by
      unfold classifyRealization; exact if_neg hne
    rw [hc]
    show embedFrame leftHandedFrame = Quotient.mk realizationSetoid g
    exact @Quotient.sound _ realizationSetoid _ _
      ((orientationPreservingAffineEquivalent_iff _ _).2 (by simp [hg]))

/-! ## The equivalence -/

def chiralityEquiv : ChiralityClass ≃ StereoQ where
  toFun := classifyChirality
  invFun := embedChirality
  left_inv := embedChirality_classifyChirality
  right_inv := classifyChirality_embedChirality

/-! ## Derived theorems -/

@[simp] theorem classifyChirality_chiralPlus : classifyChirality chiralPlus = qPlus := by
  show classifyRealization plusRealization = qPlus
  simp [classifyRealization]

@[simp] theorem classifyChirality_chiralMinus : classifyChirality chiralMinus = qMinus := by
  show classifyRealization minusRealization = qMinus
  simp [classifyRealization]
  norm_num

theorem chiralPlus_ne_chiralMinus : chiralPlus ≠ chiralMinus :=
  fun h => qPlus_ne_qMinus (by rw [← classifyChirality_chiralPlus,
    ← classifyChirality_chiralMinus, h])

theorem chiralityClass_two_point (c : ChiralityClass) :
    c = chiralPlus ∨ c = chiralMinus := by
  have h := chiralityEquiv.surjective (chiralityEquiv c)
  rcases quotient_two_point (classifyChirality c) with hq | hq
  · left
    have : classifyChirality c = classifyChirality chiralPlus := by
      rw [hq, classifyChirality_chiralPlus]
    exact chiralityEquiv.injective this
  · right
    have : classifyChirality c = classifyChirality chiralMinus := by
      rw [hq, classifyChirality_chiralMinus]
    exact chiralityEquiv.injective this

theorem exactly_two_chirality_classes :
    ∃ a b : ChiralityClass, a ≠ b ∧ ∀ c : ChiralityClass, c = a ∨ c = b :=
  ⟨chiralPlus, chiralMinus, chiralPlus_ne_chiralMinus, chiralityClass_two_point⟩

theorem classifyChirality_bijective : Function.Bijective classifyChirality :=
  chiralityEquiv.bijective

end Realization

end TetrahedralGeometry

end

end OneCenter
end TetraStereo
