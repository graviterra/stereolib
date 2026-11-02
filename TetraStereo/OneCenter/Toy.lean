import TetraStereo.OneCenter.StandardModel
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

/-- The toy one-center frame space is just the permutation group on the four attachment sites. -/
abbrev Frame := Equiv.Perm (Fin 4)

/-- Two frames represent the same toy stereochemical class when they have the same sign. -/
def SameClass (sigma tau : Frame) : Prop := permHandedness sigma = permHandedness tau

theorem sameClass_refl (sigma : Frame) : SameClass sigma sigma := rfl

theorem sameClass_symm {sigma tau : Frame} : SameClass sigma tau → SameClass tau sigma := by
  intro h
  exact h.symm

theorem sameClass_trans {sigma tau upsilon : Frame} :
    SameClass sigma tau → SameClass tau upsilon → SameClass sigma upsilon := by
  intro hst htu
  exact hst.trans htu

def frameSetoid : Setoid Frame where
  r := SameClass
  iseqv := ⟨sameClass_refl, sameClass_symm, sameClass_trans⟩

abbrev StereoQ := Quotient frameSetoid

def rightHandedFrame : Frame := 1

def leftHandedFrame : Frame := Equiv.swap (0 : Fin 4) 1

def qPlus : StereoQ := Quotient.mk frameSetoid rightHandedFrame

def qMinus : StereoQ := Quotient.mk frameSetoid leftHandedFrame

@[simp] theorem permHandedness_rightHandedFrame :
    permHandedness rightHandedFrame = 1 := by
  simp [rightHandedFrame]

@[simp] theorem permHandedness_leftHandedFrame :
    permHandedness leftHandedFrame = -1 := by
  simp [leftHandedFrame, permHandedness]

theorem frame_in_right_or_left_class (sigma : Frame) :
    SameClass sigma rightHandedFrame ∨ SameClass sigma leftHandedFrame := by
  rcases permHandedness_eq_one_or_eq_neg_one sigma with hsigma | hsigma
  · left
    simpa [SameClass, rightHandedFrame] using hsigma
  · right
    simpa [SameClass, leftHandedFrame, permHandedness] using hsigma

theorem classes_distinct : ¬ SameClass rightHandedFrame leftHandedFrame := by
  norm_num [SameClass, rightHandedFrame, leftHandedFrame, permHandedness]

theorem quotient_two_point (q : StereoQ) : q = qPlus ∨ q = qMinus := by
  refine Quotient.inductionOn q ?_
  intro sigma
  rcases frame_in_right_or_left_class sigma with hsigma | hsigma
  · left
    exact Quotient.sound hsigma
  · right
    exact Quotient.sound hsigma

theorem qPlus_ne_qMinus : qPlus ≠ qMinus := by
  intro h
  apply classes_distinct
  exact Quotient.exact h

theorem exactly_two_classes :
    ∃ a b : StereoQ, a ≠ b ∧ ∀ q : StereoQ, q = a ∨ q = b := by
  refine ⟨qPlus, qMinus, qPlus_ne_qMinus, ?_⟩
  intro q
  exact quotient_two_point q

/-- The canonical realization associated to a local frame. -/
def canonicalGeometry (sigma : Frame) : TetrahedralGeometry :=
  TetrahedralGeometry.reindex modelGeometry sigma

@[simp] theorem canonicalGeometry_nondegenerate (sigma : Frame) :
    Nondegenerate (canonicalGeometry sigma) := by
  simp [canonicalGeometry]

theorem canonicalHandedness_matches_parity (sigma : Frame) :
    handedness (canonicalGeometry sigma) = permHandedness sigma := by
  rcases permHandedness_eq_one_or_eq_neg_one sigma with hsigma | hsigma
  · calc
      handedness (canonicalGeometry sigma) = handedness modelGeometry := by
        rw [canonicalGeometry]
        exact TetrahedralGeometry.handedness_reindex_even modelGeometry sigma hsigma
      _ = 1 := modelGeometry_handedness
      _ = permHandedness sigma := by
        simp [hsigma]
  · calc
      handedness (canonicalGeometry sigma) = -handedness modelGeometry := by
        rw [canonicalGeometry]
        exact TetrahedralGeometry.handedness_reindex_odd modelGeometry sigma hsigma
      _ = -1 := by simp [modelGeometry_handedness]
      _ = permHandedness sigma := by
        simp [hsigma]

theorem sameCanonicalHandedness_iff_sameClass (sigma tau : Frame) :
    handedness (canonicalGeometry sigma) = handedness (canonicalGeometry tau) ↔
      SameClass sigma tau := by
  simp [canonicalHandedness_matches_parity, SameClass]

end OneCenter
end TetraStereo
