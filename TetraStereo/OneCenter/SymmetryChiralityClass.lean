import TetraStereo.OneCenter.ChiralityClass
import TetraStereo.OneCenter.Symmetry

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

noncomputable section

namespace TetrahedralGeometry
namespace Realization

/-- Reindex a nondegenerate realization by a permutation of the four vertices. -/
def reindex (g : Realization) (σ : Equiv.Perm (Fin 4)) : Realization :=
  ⟨TetrahedralGeometry.reindex g.1 σ,
    (TetrahedralGeometry.nondegenerate_reindex (g := g.1) (sigma := σ)).2 g.2⟩

@[simp] theorem coe_reindex (g : Realization) (σ : Equiv.Perm (Fin 4)) :
    (reindex g σ : TetrahedralGeometry) = TetrahedralGeometry.reindex g.1 σ := rfl

@[simp] theorem reindex_one (g : Realization) : reindex g (1 : Equiv.Perm (Fin 4)) = g := by
  apply Subtype.ext
  ext i j
  simp [reindex, TetrahedralGeometry.reindex]

@[simp] theorem reindex_mul (g : Realization) (σ τ : Equiv.Perm (Fin 4)) :
    reindex (reindex g σ) τ = reindex g (σ * τ) := by
  apply Subtype.ext
  ext i j
  simp [reindex, TetrahedralGeometry.reindex]

@[simp] theorem reindex_canonicalRealization (σ : Frame) (τ : Equiv.Perm (Fin 4)) :
    reindex (canonicalRealization σ) τ = canonicalRealization (σ * τ) := by
  apply Subtype.ext
  ext i j
  simp [reindex, canonicalRealization, canonicalGeometry, TetrahedralGeometry.reindex]

theorem orientationPreservingAffineEquivalent_reindex (g h : Realization)
    (σ : Equiv.Perm (Fin 4)) (hgh : OrientationPreservingAffineEquivalent g h) :
    OrientationPreservingAffineEquivalent (reindex g σ) (reindex h σ) := by
  rcases hgh with ⟨A, b, hA, hEq⟩
  refine ⟨A, b, hA, ?_⟩
  calc
    TetrahedralGeometry.reindex h.1 σ
        = TetrahedralGeometry.reindex (TetrahedralGeometry.mapAffine g.1 A b) σ := by
              simp [hEq]
    _ = TetrahedralGeometry.mapAffine (TetrahedralGeometry.reindex g.1 σ) A b := by
          simp [TetrahedralGeometry.reindex_mapAffine]

end Realization
end TetrahedralGeometry

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

open TetrahedralGeometry.Realization

/-- Two realized tetrahedral centers are equivalent after allowing center symmetries:
reindex the second realization by a symmetry-induced permutation of the four ligands, then apply an
orientation-preserving affine equivalence. -/
def SameStereoRealization (m : OneCenterMolecule V) (g h : TetrahedralGeometry.Realization) : Prop :=
  ∃ e : m.CenterAut,
    TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent g
      (TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e))

theorem sameStereoRealization_refl (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) :
    m.SameStereoRealization g g := by
  refine ⟨1, ?_⟩
  simpa using TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_refl g

theorem sameStereoRealization_symm (m : OneCenterMolecule V) {g h : TetrahedralGeometry.Realization} :
    m.SameStereoRealization g h → m.SameStereoRealization h g := by
  intro hgh
  rcases hgh with ⟨e, hge⟩
  refine ⟨e⁻¹, ?_⟩
  have hsymm :
      TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
        (TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e)) g :=
    TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_symm hge
  have hreindexed :
      TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
        (TetrahedralGeometry.Realization.reindex
          (TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e)) (m.ligandPermHom e)⁻¹)
        (TetrahedralGeometry.Realization.reindex g (m.ligandPermHom e)⁻¹) :=
    TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_reindex
      (g := TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e)) (h := g)
      ((m.ligandPermHom e)⁻¹) hsymm
  have hinv : (m.ligandPermHom e)⁻¹ = m.ligandPermHom (e⁻¹) := by
    simp
  have hreindexed' :
      TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent h
        (TetrahedralGeometry.Realization.reindex g (m.ligandPermHom e)⁻¹) := by
    simpa using hreindexed
  -- Avoid a `simp` loop between `map_inv` and the local rewrite `hinv`.
  -- Rewrite the goal target using `hinv.symm`, then use `hreindexed'`.
  rw [hinv.symm]
  exact hreindexed'

theorem sameStereoRealization_trans (m : OneCenterMolecule V)
    {g h k : TetrahedralGeometry.Realization} :
    m.SameStereoRealization g h → m.SameStereoRealization h k → m.SameStereoRealization g k := by
  intro hgh hhk
  rcases hgh with ⟨e, hge⟩
  rcases hhk with ⟨f, hhf⟩
  refine ⟨f * e, ?_⟩
  have hhf' :
      TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
        (TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e))
        (TetrahedralGeometry.Realization.reindex
          (TetrahedralGeometry.Realization.reindex k (m.ligandPermHom f)) (m.ligandPermHom e)) :=
    TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_reindex
      (g := h) (h := TetrahedralGeometry.Realization.reindex k (m.ligandPermHom f))
      (m.ligandPermHom e) hhf
  have hhf'' :
      TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
        (TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e))
        (TetrahedralGeometry.Realization.reindex k (m.ligandPermHom (f * e))) := by
    simpa [TetrahedralGeometry.Realization.reindex_mul, m.ligandPermHom.map_mul] using hhf'
  exact TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_trans hge hhf''

/-- The setoid on realizations induced by `SameStereoRealization`. -/
def stereoRealizationSetoid (m : OneCenterMolecule V) : Setoid TetrahedralGeometry.Realization where
  r := m.SameStereoRealization
  iseqv :=
    ⟨m.sameStereoRealization_refl, m.sameStereoRealization_symm, m.sameStereoRealization_trans⟩

/-- The affine stereochemical quotient of nondegenerate realizations after accounting for center
symmetries. -/
abbrev AffineStereoQ (m : OneCenterMolecule V) := Quotient (m.stereoRealizationSetoid)

/-- Classify a realized center into the symmetry-aware stereochemical quotient.

This collapses the two handedness classes when the molecule has an odd center symmetry. -/
def classifyStereoRealization (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) :
    m.StereoQ :=
  if handedness g.1 = 1 then m.qPlus else m.qMinus

theorem classifyStereoRealization_respectsSameStereoRealization (m : OneCenterMolecule V)
    (g h : TetrahedralGeometry.Realization) (hgh : m.SameStereoRealization g h) :
    m.classifyStereoRealization g = m.classifyStereoRealization h := by
  rcases hgh with ⟨e, hge⟩
  rcases permHandedness_eq_one_or_eq_neg_one (m.ligandPermHom e) with he | he
  · have hhand :
        handedness g.1 = handedness h.1 := by
      have hhand' :
          handedness g.1 =
            handedness (TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e)).1 :=
        (TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_iff g
              (TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e))).1 hge
      have hre :
          handedness (TetrahedralGeometry.Realization.reindex h (m.ligandPermHom e)).1 =
            handedness h.1 := by
        simpa [TetrahedralGeometry.Realization.reindex] using
          (TetrahedralGeometry.handedness_reindex_even (g := h.1) (sigma := m.ligandPermHom e) he)
      exact hhand'.trans hre
    rcases g.handedness_eq_one_or_eq_neg_one with hg | hg
    · have hh : handedness h.1 = 1 := by
        simpa [hg] using hhand.symm
      simp [classifyStereoRealization, hg, hh]
    · have hh : handedness h.1 = -1 := by
        simpa [hg] using hhand.symm
      simp [classifyStereoRealization, hg, hh]
  · have hodd : m.AchiralBySymmetry := ⟨e, he⟩
    haveI : Subsingleton m.StereoQ :=
      m.subsingleton_stereoQ_of_achiralBySymmetry hodd
    exact Subsingleton.elim _ _

/-- The quotient classifier `AffineStereoQ → StereoQ`. -/
def classifyAffineStereo (m : OneCenterMolecule V) : m.AffineStereoQ → m.StereoQ :=
  Quotient.lift (m.classifyStereoRealization)
    (m.classifyStereoRealization_respectsSameStereoRealization)

@[simp] theorem classifyAffineStereo_mk (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) :
    m.classifyAffineStereo (Quotient.mk (m.stereoRealizationSetoid) g) =
      m.classifyStereoRealization g := rfl

/-! ### The equivalence with the frame-level symmetry quotient -/

def embedFrame (m : OneCenterMolecule V) (σ : Frame) : m.AffineStereoQ :=
  Quotient.mk (m.stereoRealizationSetoid) (TetrahedralGeometry.Realization.canonicalRealization σ)

theorem embedFrame_respectsSameStereo (m : OneCenterMolecule V) (σ τ : Frame)
    (hst : m.SameStereo σ τ) : m.embedFrame σ = m.embedFrame τ := by
  apply Quotient.sound
  rcases hst with ⟨e, hpar⟩
  refine ⟨e, ?_⟩
  apply TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_of_handedness_eq
  -- `simp` turns this into exactly the parity hypothesis `hpar`.
  simpa using hpar

def embedAffineStereo (m : OneCenterMolecule V) : m.StereoQ → m.AffineStereoQ :=
  Quotient.lift (m.embedFrame) (m.embedFrame_respectsSameStereo)

theorem classifyAffineStereo_embedAffineStereo (m : OneCenterMolecule V) (q : m.StereoQ) :
    m.classifyAffineStereo (m.embedAffineStereo q) = q := by
  refine Quotient.inductionOn q ?_
  intro σ
  show m.classifyStereoRealization (TetrahedralGeometry.Realization.canonicalRealization σ) =
      Quotient.mk (m.stereoSetoid) σ
  rcases permHandedness_eq_one_or_eq_neg_one σ with hσ | hσ
  · have hl :
        m.classifyStereoRealization (TetrahedralGeometry.Realization.canonicalRealization σ) =
          m.qPlus := by
        simp [classifyStereoRealization, hσ]
    have hr : Quotient.mk (m.stereoSetoid) σ = m.qPlus := by
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simp [hσ]
    calc
      m.classifyStereoRealization (TetrahedralGeometry.Realization.canonicalRealization σ)
          = m.qPlus := hl
      _ = Quotient.mk (m.stereoSetoid) σ := hr.symm
  · have hl :
        m.classifyStereoRealization (TetrahedralGeometry.Realization.canonicalRealization σ) =
          m.qMinus := by
        simp [classifyStereoRealization, hσ]
        norm_num
    have hr : Quotient.mk (m.stereoSetoid) σ = m.qMinus := by
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simp [hσ]
    calc
      m.classifyStereoRealization (TetrahedralGeometry.Realization.canonicalRealization σ)
          = m.qMinus := hl
      _ = Quotient.mk (m.stereoSetoid) σ := hr.symm

theorem embedAffineStereo_classifyAffineStereo (m : OneCenterMolecule V) (c : m.AffineStereoQ) :
    m.embedAffineStereo (m.classifyAffineStereo c) = c := by
  refine Quotient.inductionOn c ?_
  intro g
  show m.embedAffineStereo (m.classifyStereoRealization g) =
      Quotient.mk (m.stereoRealizationSetoid) g
  rcases g.handedness_eq_one_or_eq_neg_one with hg | hg
  · have hc : m.classifyStereoRealization g = m.qPlus := by
      simp [classifyStereoRealization, hg]
    rw [hc]
    apply Quotient.sound
    refine ⟨1, ?_⟩
    -- Canonical `+` has handedness `1`, so it is orientation-preserving affine equivalent to `g`.
    have hEq :
        handedness (TetrahedralGeometry.Realization.canonicalRealization (1 : Frame)).1 =
          handedness g.1 := by
      simp [hg]
    have hEquiv :
        TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
          (TetrahedralGeometry.Realization.canonicalRealization (1 : Frame)) g :=
      TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_of_handedness_eq hEq
    simpa [TetrahedralGeometry.Realization.reindex, classifyStereoRealization] using hEquiv
  · have hc : m.classifyStereoRealization g = m.qMinus := by
      simp [classifyStereoRealization, hg]
      norm_num
    rw [hc]
    apply Quotient.sound
    refine ⟨1, ?_⟩
    -- Canonical `-` has handedness `-1`, so it is orientation-preserving affine equivalent to `g`.
    have hEq :
        handedness (TetrahedralGeometry.Realization.canonicalRealization (leftHandedFrame)).1 =
          handedness g.1 := by
      simp [hg]
    have hEquiv :
        TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
          (TetrahedralGeometry.Realization.canonicalRealization leftHandedFrame) g :=
      TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_of_handedness_eq hEq
    simpa [TetrahedralGeometry.Realization.reindex, classifyStereoRealization] using hEquiv

/-- The symmetry-aware affine stereochemical quotient is equivalent to the frame-level quotient. -/
def affineStereoEquiv (m : OneCenterMolecule V) : m.AffineStereoQ ≃ m.StereoQ where
  toFun := m.classifyAffineStereo
  invFun := m.embedAffineStereo
  left_inv := m.embedAffineStereo_classifyAffineStereo
  right_inv := m.classifyAffineStereo_embedAffineStereo

/-- If the molecule has an odd center symmetry, the symmetry-aware affine stereochemical quotient is
a singleton. -/
theorem subsingleton_affineStereoQ_of_achiralBySymmetry (m : OneCenterMolecule V)
    (hodd : m.AchiralBySymmetry) : Subsingleton (m.AffineStereoQ) := by
  classical
  haveI : Subsingleton m.StereoQ := m.subsingleton_stereoQ_of_achiralBySymmetry hodd
  refine ⟨?_⟩
  intro a b
  apply (m.affineStereoEquiv).injective
  exact Subsingleton.elim _ _

/-- If the molecule has only even center symmetries, the symmetry-aware affine stereochemical
quotient has exactly two classes. -/
theorem affineStereoQ_exactly_two_classes_of_chiralBySymmetry (m : OneCenterMolecule V)
    (heven : m.ChiralBySymmetry) :
    ∃ a b : m.AffineStereoQ, a ≠ b ∧ ∀ q : m.AffineStereoQ, q = a ∨ q = b := by
  classical
  rcases m.stereoQ_exactly_two_classes_of_chiralBySymmetry heven with ⟨a, b, hab, hcover⟩
  refine ⟨(m.affineStereoEquiv).symm a, (m.affineStereoEquiv).symm b, ?_, ?_⟩
  · intro hEq
    apply hab
    have : a = b := by
      have := congrArg (m.affineStereoEquiv) hEq
      simpa using this
    exact this
  · intro q
    have h := hcover ((m.affineStereoEquiv) q)
    rcases h with hq | hq
    · left
      have := congrArg (m.affineStereoEquiv).symm hq
      simpa using this
    · right
      have := congrArg (m.affineStereoEquiv).symm hq
      simpa using this

end OneCenterMolecule

end
