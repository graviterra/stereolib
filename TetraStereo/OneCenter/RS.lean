import TetraStereo.OneCenter.CIPCycleCut
import TetraStereo.OneCenter.Euclidean
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

noncomputable section

/-- A minimal `R/S`-style two-point descriptor. -/
inductive RS where
  | R : RS
  | S : RS
deriving DecidableEq, Repr

namespace RS

/-- Map real tetrahedral handedness to an `R/S` descriptor.

Calibration (IUPAC P-92.1.2.1; preferred viewing side remote from the lowest-precedence ligand,
`tmp/chemical-fidelity-20261018/primary-sources/P9.txt` lines 406 and 794): the four vertices are
supplied in descending CIP priority order `1 > 2 > 3 > 4`.  In the standard right-handed Cartesian
frame (`x` right, `y` up, `z` toward the viewer) the `R` case -- highest-to-lowest path clockwise
when viewed from the side remote from the lowest-priority ligand -- has negative oriented volume,
so the real handedness (`Real.sign` of the oriented volume) is `-1`.

Hence this calibration maps `-1 ↦ R` and `1 ↦ S`.

The definition is total.  Any value other than `-1` and `1` (in particular the degenerate value
`0`) takes the explicit fallback `S`; descriptor callers only use nondegenerate handedness, which
is always `1` or `-1`. -/
def ofHandedness (h : ℝ) : RS :=
  if h = -1 then RS.R
  else if h = 1 then RS.S
  else RS.S

@[simp] theorem ofHandedness_neg_one : RS.ofHandedness (-1) = RS.R := by
  simp [ofHandedness]

@[simp] theorem ofHandedness_one : RS.ofHandedness 1 = RS.S := by
  have h : ¬ ((1 : ℝ) = -1) := by norm_num
  simp [ofHandedness, h]

def swap : RS → RS
  | RS.R => RS.S
  | RS.S => RS.R

theorem ofHandedness_neg (h : ℝ) (hh : h = 1 ∨ h = -1) :
    RS.ofHandedness (-h) = RS.swap (RS.ofHandedness h) := by
  rcases hh with rfl | rfl
  · simp [swap]
  · simp [swap]

end RS

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The tetrahedral geometry given by the positions of the four atoms directly attached to the
stereocenter. -/
def tetrahedralGeometry (m : OneCenterMolecule V) (pos : V → EuclideanSpace ℝ (Fin 3)) :
    TetrahedralGeometry where
  vertex i := pos (m.ligandAtom i)

/-- The raw `R/S` descriptor of a *nondegenerate* realized tetrahedral center, using the current
simplified CIP-like priority key.

Definition: sort the four ligand atoms by descending CIP priority, reindex the tetrahedral
geometry by that permutation, and read off the handedness sign.

This raw descriptor is deterministic even when CIP priorities tie, because `cipPermutation` has a
fixed index tie-breaker.  Prefer `rsOfResolved` or `rs?` for descriptor-level statements.

This is still not fully CIP-correct (e.g. subtleties about stereogenicity inside substituents
are not modeled), but the underlying key does account for multiple bonds and cycles at the level
of expansion multiplicity. -/
def rs (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) : RS :=
  RS.ofHandedness (handedness (reindex g.1 (m.cipPermutation)))

/-- The raw `R/S` descriptor using the cycle-cut CIP key.  As with `rs`, this is deterministic
even when priorities tie; use `rsCycleCutOfResolved` or `rsCycleCut?` for descriptor-level
statements. -/
def rsCycleCut (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) : RS :=
  RS.ofHandedness (handedness (reindex g.1 (m.cipPermutationCycleCut)))

/-- The `R/S` descriptor with explicit evidence that CIP priorities are resolved. -/
def rsOfResolved (m : OneCenterMolecule V) (h : m.ResolvedCIP)
    (g : TetrahedralGeometry.Realization) : RS :=
  RS.ofHandedness (handedness (reindex g.1 (m.cipPermutationOfResolved h)))

/-- The cycle-cut `R/S` descriptor with explicit evidence that cycle-cut CIP priorities are
resolved. -/
def rsCycleCutOfResolved (m : OneCenterMolecule V) (h : m.ResolvedCIPCycleCut)
    (g : TetrahedralGeometry.Realization) : RS :=
  RS.ofHandedness (handedness (reindex g.1 (m.cipPermutationCycleCutOfResolved h)))

@[simp] theorem rsOfResolved_eq_rs (m : OneCenterMolecule V) (h : m.ResolvedCIP)
    (g : TetrahedralGeometry.Realization) :
    m.rsOfResolved h g = m.rs g := rfl

@[simp] theorem rsCycleCutOfResolved_eq_rsCycleCut (m : OneCenterMolecule V)
    (h : m.ResolvedCIPCycleCut) (g : TetrahedralGeometry.Realization) :
    m.rsCycleCutOfResolved h g = m.rsCycleCut g := rfl

/-- Safe `R/S`: returns `none` when the center is not CIP-resolved. -/
noncomputable def rs? (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) :
    Option RS :=
  by
    classical
    exact if h : m.ResolvedCIP then some (m.rsOfResolved h g) else none

/-- Safe cycle-cut `R/S`: returns `none` when the center is not cycle-cut CIP-resolved. -/
noncomputable def rsCycleCut? (m : OneCenterMolecule V)
    (g : TetrahedralGeometry.Realization) : Option RS :=
  by
    classical
    exact
      if h : m.ResolvedCIPCycleCut then
        some (m.rsCycleCutOfResolved h g)
      else
        none

theorem rs?_eq_some_rs_of_resolvedCIP (m : OneCenterMolecule V) (h : m.ResolvedCIP)
    (g : TetrahedralGeometry.Realization) :
    m.rs? g = some (m.rs g) := by
  classical
  simp [rs?, h]

theorem rsCycleCut?_eq_some_rsCycleCut_of_resolvedCIPCycleCut
    (m : OneCenterMolecule V) (h : m.ResolvedCIPCycleCut)
    (g : TetrahedralGeometry.Realization) :
    m.rsCycleCut? g = some (m.rsCycleCut g) := by
  classical
  simp [rsCycleCut?, h]

theorem rs?_eq_none_of_not_resolvedCIP (m : OneCenterMolecule V) (h : ¬ m.ResolvedCIP)
    (g : TetrahedralGeometry.Realization) :
    m.rs? g = none := by
  classical
  simp [rs?, h]

theorem rsCycleCut?_eq_none_of_not_resolvedCIPCycleCut
    (m : OneCenterMolecule V) (h : ¬ m.ResolvedCIPCycleCut)
    (g : TetrahedralGeometry.Realization) :
    m.rsCycleCut? g = none := by
  classical
  simp [rsCycleCut?, h]

/-! ### Preferred descriptor-facing aliases -/

/-- Descriptor-facing `R/S` descriptor.

The descriptor-facing path uses cycle-cut CIP priorities; the raw `rs` remains available for
comparison against older/raw CIP development. -/
abbrev rsCIP (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) : RS :=
  m.rsCycleCut g

/-- Descriptor-facing `R/S` descriptor with explicit resolved descriptor-priority evidence. -/
abbrev rsCIPOfResolved (m : OneCenterMolecule V) (h : m.ResolvedCIPDescriptor)
    (g : TetrahedralGeometry.Realization) : RS :=
  m.rsCycleCutOfResolved h g

/-- Safe descriptor-facing `R/S`: returns `none` when descriptor CIP priorities tie. -/
abbrev rsCIP? (m : OneCenterMolecule V)
    (g : TetrahedralGeometry.Realization) : Option RS :=
  m.rsCycleCut? g

theorem rsCIP?_eq_some_rsCIP_of_resolvedCIPDescriptor
    (m : OneCenterMolecule V) (h : m.ResolvedCIPDescriptor)
    (g : TetrahedralGeometry.Realization) :
    m.rsCIP? g = some (m.rsCIP g) := by
  exact m.rsCycleCut?_eq_some_rsCycleCut_of_resolvedCIPCycleCut h g

theorem rs_eq_rsCycleCut_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement)
    (g : TetrahedralGeometry.Realization) :
    m.rs g = m.rsCycleCut g := by
  simp [rs, rsCycleCut, m.cipPermutation_eq_cipPermutationCycleCut_of_rawCycleCutKeyAgreement h]

theorem rs?_eq_rsCycleCut?_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement)
    (g : TetrahedralGeometry.Realization) :
    m.rs? g = m.rsCycleCut? g := by
  classical
  have hresolved := m.resolvedCIP_iff_resolvedCIPCycleCut_of_rawCycleCutKeyAgreement h
  by_cases hr : m.ResolvedCIP
  · have hrc : m.ResolvedCIPCycleCut := hresolved.1 hr
    simp [rs?, rsCycleCut?, hr, hrc, m.rs_eq_rsCycleCut_of_rawCycleCutKeyAgreement h g]
  · have hrc : ¬ m.ResolvedCIPCycleCut := by
      intro hrc
      exact hr (hresolved.2 hrc)
    simp [rs?, rsCycleCut?, hr, hrc]

theorem rs_eq_rsCycleCut_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike)
    (g : TetrahedralGeometry.Realization) :
    m.rs g = m.rsCycleCut g :=
  m.rs_eq_rsCycleCut_of_rawCycleCutKeyAgreement (m.rawCycleCutKeyAgreement_of_treeLike htree) g

theorem rs?_eq_rsCycleCut?_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike)
    (g : TetrahedralGeometry.Realization) :
    m.rs? g = m.rsCycleCut? g :=
  m.rs?_eq_rsCycleCut?_of_rawCycleCutKeyAgreement (m.rawCycleCutKeyAgreement_of_treeLike htree) g

@[simp] theorem rs_map_of_orientationPreservingEuclideanMotion
    (m : OneCenterMolecule V) (μ : OrientationPreservingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rs (μ • g) = m.rs g := by
  -- Proper Euclidean motions preserve handedness; the CIP permutation is purely combinatorial.
  have hhand :
      handedness
          ((reindex (g : TetrahedralGeometry) m.cipPermutation).mapAffine
              (μ.1.linear) (μ.1.translation)) =
        handedness (reindex (g : TetrahedralGeometry) m.cipPermutation) := by
    simpa [EuclideanMotion.smul_def] using
      μ.handedness_map_eq (g := reindex (g : TetrahedralGeometry) m.cipPermutation)
  simp [OneCenterMolecule.rs, RS.ofHandedness, EuclideanMotion.smul_def, hhand]

@[simp] theorem rs_map_of_orientationReversingEuclideanMotion
    (m : OneCenterMolecule V) (μ : OrientationReversingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rs (μ • g) = RS.swap (m.rs g) := by
  have hhand :
      handedness
          ((reindex (g : TetrahedralGeometry) m.cipPermutation).mapAffine
              (μ.1.linear) (μ.1.translation)) =
        -handedness (reindex (g : TetrahedralGeometry) m.cipPermutation) := by
    simpa [EuclideanMotion.smul_def] using
      μ.handedness_map_eq_neg (g := reindex (g : TetrahedralGeometry) m.cipPermutation)
  have hh :
      handedness (reindex (g : TetrahedralGeometry) m.cipPermutation) = 1 ∨
        handedness (reindex (g : TetrahedralGeometry) m.cipPermutation) = -1 := by
    have hnd :
        TetrahedralGeometry.Nondegenerate
          (reindex (g : TetrahedralGeometry) m.cipPermutation) := by
      exact
        (TetrahedralGeometry.nondegenerate_reindex
          (g := (g : TetrahedralGeometry)) (sigma := m.cipPermutation)).2 g.2
    simpa using (show TetrahedralGeometry.Realization from ⟨_, hnd⟩).handedness_eq_one_or_eq_neg_one
  -- Orientation-reversing motions negate handedness, hence swap the `R/S` value for nondegenerate centers.
  have hswap :
      RS.ofHandedness (-handedness (reindex (g : TetrahedralGeometry) m.cipPermutation)) =
        RS.swap (RS.ofHandedness (handedness (reindex (g : TetrahedralGeometry) m.cipPermutation))) := by
    simpa using
      RS.ofHandedness_neg (handedness (reindex (g : TetrahedralGeometry) m.cipPermutation)) hh
  calc
    m.rs (μ • g)
        = RS.ofHandedness (-handedness (reindex (g : TetrahedralGeometry) m.cipPermutation)) := by
            simp [OneCenterMolecule.rs, RS.ofHandedness, EuclideanMotion.smul_def, hhand]
    _ = RS.swap (RS.ofHandedness (handedness (reindex (g : TetrahedralGeometry) m.cipPermutation))) := by
          simpa using hswap
    _ = RS.swap (m.rs g) := by
          rfl

@[simp] theorem rsCycleCut_map_of_orientationPreservingEuclideanMotion
    (m : OneCenterMolecule V) (μ : OrientationPreservingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rsCycleCut (μ • g) = m.rsCycleCut g := by
  have hhand :
      handedness
          ((reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut).mapAffine
              (μ.1.linear) (μ.1.translation)) =
        handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut) := by
    simpa [EuclideanMotion.smul_def] using
      μ.handedness_map_eq (g := reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut)
  simp [OneCenterMolecule.rsCycleCut, RS.ofHandedness, EuclideanMotion.smul_def, hhand]

@[simp] theorem rsCycleCut_map_of_orientationReversingEuclideanMotion
    (m : OneCenterMolecule V) (μ : OrientationReversingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rsCycleCut (μ • g) = RS.swap (m.rsCycleCut g) := by
  have hhand :
      handedness
          ((reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut).mapAffine
              (μ.1.linear) (μ.1.translation)) =
        -handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut) := by
    simpa [EuclideanMotion.smul_def] using
      μ.handedness_map_eq_neg (g := reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut)
  have hh :
      handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut) = 1 ∨
        handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut) = -1 := by
    have hnd :
        TetrahedralGeometry.Nondegenerate
          (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut) := by
      exact
        (TetrahedralGeometry.nondegenerate_reindex
          (g := (g : TetrahedralGeometry)) (sigma := m.cipPermutationCycleCut)).2 g.2
    simpa using (show TetrahedralGeometry.Realization from ⟨_, hnd⟩).handedness_eq_one_or_eq_neg_one
  have hswap :
      RS.ofHandedness (-handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut)) =
        RS.swap (RS.ofHandedness (handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut))) := by
    simpa using
      RS.ofHandedness_neg (handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut)) hh
  calc
    m.rsCycleCut (μ • g)
        = RS.ofHandedness (-handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut)) := by
            simp [OneCenterMolecule.rsCycleCut, RS.ofHandedness, EuclideanMotion.smul_def, hhand]
    _ = RS.swap (RS.ofHandedness (handedness (reindex (g : TetrahedralGeometry) m.cipPermutationCycleCut))) := by
          simpa using hswap
    _ = RS.swap (m.rsCycleCut g) := by
          rfl

@[simp] theorem rsOfResolved_map_of_orientationPreservingEuclideanMotion
    (m : OneCenterMolecule V) (h : m.ResolvedCIP) (μ : OrientationPreservingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rsOfResolved h (μ • g) = m.rsOfResolved h g := by
  simpa using m.rs_map_of_orientationPreservingEuclideanMotion μ g

@[simp] theorem rsOfResolved_map_of_orientationReversingEuclideanMotion
    (m : OneCenterMolecule V) (h : m.ResolvedCIP) (μ : OrientationReversingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rsOfResolved h (μ • g) = RS.swap (m.rsOfResolved h g) := by
  simpa using m.rs_map_of_orientationReversingEuclideanMotion μ g

@[simp] theorem rsCycleCutOfResolved_map_of_orientationPreservingEuclideanMotion
    (m : OneCenterMolecule V) (h : m.ResolvedCIPCycleCut)
    (μ : OrientationPreservingEuclideanMotion) (g : TetrahedralGeometry.Realization) :
    m.rsCycleCutOfResolved h (μ • g) = m.rsCycleCutOfResolved h g := by
  simpa using m.rsCycleCut_map_of_orientationPreservingEuclideanMotion μ g

@[simp] theorem rsCycleCutOfResolved_map_of_orientationReversingEuclideanMotion
    (m : OneCenterMolecule V) (h : m.ResolvedCIPCycleCut)
    (μ : OrientationReversingEuclideanMotion) (g : TetrahedralGeometry.Realization) :
    m.rsCycleCutOfResolved h (μ • g) = RS.swap (m.rsCycleCutOfResolved h g) := by
  simpa using m.rsCycleCut_map_of_orientationReversingEuclideanMotion μ g

@[simp] theorem rs?_map_of_orientationPreservingEuclideanMotion
    (m : OneCenterMolecule V) (μ : OrientationPreservingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rs? (μ • g) = m.rs? g := by
  classical
  by_cases h : m.ResolvedCIP
  · simpa [rs?, h] using m.rs_map_of_orientationPreservingEuclideanMotion μ g
  · simp [rs?, h]

@[simp] theorem rs?_map_of_orientationReversingEuclideanMotion
    (m : OneCenterMolecule V) (μ : OrientationReversingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rs? (μ • g) = (m.rs? g).map RS.swap := by
  classical
  by_cases h : m.ResolvedCIP
  · simpa [rs?, h] using m.rs_map_of_orientationReversingEuclideanMotion μ g
  · simp [rs?, h]

@[simp] theorem rsCycleCut?_map_of_orientationPreservingEuclideanMotion
    (m : OneCenterMolecule V) (μ : OrientationPreservingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rsCycleCut? (μ • g) = m.rsCycleCut? g := by
  classical
  by_cases h : m.ResolvedCIPCycleCut
  · simpa [rsCycleCut?, h] using m.rsCycleCut_map_of_orientationPreservingEuclideanMotion μ g
  · simp [rsCycleCut?, h]

@[simp] theorem rsCycleCut?_map_of_orientationReversingEuclideanMotion
    (m : OneCenterMolecule V) (μ : OrientationReversingEuclideanMotion)
    (g : TetrahedralGeometry.Realization) :
    m.rsCycleCut? (μ • g) = (m.rsCycleCut? g).map RS.swap := by
  classical
  by_cases h : m.ResolvedCIPCycleCut
  · simpa [rsCycleCut?, h] using m.rsCycleCut_map_of_orientationReversingEuclideanMotion μ g
  · simp [rsCycleCut?, h]

end OneCenterMolecule

end

end OneCenter
end TetraStereo
