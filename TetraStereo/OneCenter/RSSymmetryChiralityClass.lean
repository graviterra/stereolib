import TetraStereo.OneCenter.RS
import TetraStereo.OneCenter.CIPSymmetry
import TetraStereo.OneCenter.SymmetryChiralityClass

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace OneCenterMolecule

open TetrahedralGeometry
open TetrahedralGeometry.Realization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `R/S` descriptor is invariant under orientation-preserving affine equivalence. -/
theorem rs_eq_of_orientationPreservingAffineEquivalent (m : OneCenterMolecule V)
    {g h : TetrahedralGeometry.Realization}
    (hgh : OrientationPreservingAffineEquivalent g h) :
    m.rs g = m.rs h := by
  classical
  -- Reindex both realizations by the fixed CIP permutation, then use handedness preservation.
  have hre :
      OrientationPreservingAffineEquivalent (reindex g m.cipPermutation) (reindex h m.cipPermutation) :=
    orientationPreservingAffineEquivalent_reindex (g := g) (h := h) m.cipPermutation hgh
  have hhand :
      handedness (TetrahedralGeometry.reindex g.1 m.cipPermutation) =
        handedness (TetrahedralGeometry.reindex h.1 m.cipPermutation) := by
    -- `simp` transports handedness through the `Realization.reindex` coercion.
    simpa [TetrahedralGeometry.Realization.reindex] using
      (orientationPreservingAffineEquivalent_iff (reindex g m.cipPermutation)
          (reindex h m.cipPermutation)).1 hre
  simp [OneCenterMolecule.rs, RS.ofHandedness, hhand]

/-- Under CIP-stereogenicity, `rs` respects the symmetry-aware realization equivalence relation
(`SameStereoRealization`), hence descends to `AffineStereoQ`. -/
theorem rs_eq_of_sameStereoRealization_of_stereogenicByCIP (m : OneCenterMolecule V)
    (hst : m.StereogenicByCIP) {g h : TetrahedralGeometry.Realization}
    (hgh : m.SameStereoRealization g h) :
    m.rs g = m.rs h := by
  rcases hgh with ⟨e, hge⟩
  have he1 : m.ligandPermHom e = 1 :=
    m.ligandPermHom_eq_one_of_stereogenicByCIP hst e
  have hge' : OrientationPreservingAffineEquivalent g h := by
    -- Rewrite `reindex h (ligandPermHom e)` to `h`.
    simpa [he1] using hge
  exact m.rs_eq_of_orientationPreservingAffineEquivalent hge'

/-- The induced `R/S` descriptor on the symmetry-aware affine stereochemical quotient, assuming
the molecule is CIP-stereogenic. -/
noncomputable def rsAffine (m : OneCenterMolecule V) (hst : m.StereogenicByCIP) :
    m.AffineStereoQ → RS :=
  Quotient.lift (fun g => m.rs g) (by
    intro g h hgh
    exact m.rs_eq_of_sameStereoRealization_of_stereogenicByCIP hst hgh)

@[simp] theorem rsAffine_mk (m : OneCenterMolecule V) (hst : m.StereogenicByCIP)
    (g : TetrahedralGeometry.Realization) :
    m.rsAffine hst (Quotient.mk (m.stereoRealizationSetoid) g) = m.rs g := rfl

/-- `rs` on canonical realizations is a purely combinatorial parity test after CIP reindexing. -/
theorem rs_canonicalRealization (m : OneCenterMolecule V) (σ : Frame) :
    m.rs (canonicalRealization σ) =
      RS.ofHandedness (permHandedness (σ * m.cipPermutation)) := by
  classical
  have hhand :
      handedness (TetrahedralGeometry.reindex (canonicalRealization σ).1 m.cipPermutation) =
        permHandedness (σ * m.cipPermutation) := by
    have h :=
      congrArg (fun g : TetrahedralGeometry.Realization => handedness g.1)
        (reindex_canonicalRealization (σ := σ) (τ := m.cipPermutation))
    simpa [handedness_canonicalRealization, TetrahedralGeometry.Realization.reindex] using h
  simp [OneCenterMolecule.rs, RS.ofHandedness, hhand]

theorem rs_plusRealization (m : OneCenterMolecule V) :
    m.rs plusRealization = RS.ofHandedness (permHandedness m.cipPermutation) := by
  simpa [plusRealization, rightHandedFrame] using (m.rs_canonicalRealization (σ := rightHandedFrame))

theorem rs_minusRealization (m : OneCenterMolecule V) :
    m.rs minusRealization = RS.swap (RS.ofHandedness (permHandedness m.cipPermutation)) := by
  have hneg :
      permHandedness (leftHandedFrame * m.cipPermutation) = -permHandedness m.cipPermutation := by
    simp [leftHandedFrame, permHandedness_mul]
  have hh :
      permHandedness m.cipPermutation = (1 : ℝ) ∨ permHandedness m.cipPermutation = (-1 : ℝ) :=
    permHandedness_eq_one_or_eq_neg_one m.cipPermutation
  calc
    m.rs minusRealization
        = RS.ofHandedness (permHandedness (leftHandedFrame * m.cipPermutation)) := by
            simpa [minusRealization] using (m.rs_canonicalRealization (σ := leftHandedFrame))
    _ = RS.ofHandedness (-permHandedness m.cipPermutation) := by
          simp [hneg]
    _ = RS.swap (RS.ofHandedness (permHandedness m.cipPermutation)) := by
          simpa using RS.ofHandedness_neg (permHandedness m.cipPermutation) hh

end OneCenterMolecule

end
end OneCenter
end TetraStereo
