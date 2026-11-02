/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.Geometry
import TetraStereo.OneCenter.OrganicStereoAmbientMotions
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open scoped Matrix
open TetrahedralGeometry

noncomputable section

/-!
# Conformation trajectories and the oriented-volume obstruction

This module proves, for genuinely continuous trajectories of real molecular conformations, the
elementary dynamics facts behind the "four-point handedness is not a topological invariant"
obstruction.  Everything is stated on the *existing* real oriented-volume API of
`TetraStereo.OneCenter.Geometry`: `TetrahedralGeometry.orientedVolume` is the determinant of the
`4 × 4` homogeneous matrix whose `i`-th row is `(x_i, y_i, z_i, 1)`.  No caller-supplied scalar
measure is used.

## Results

* `continuous_orientedVolume_tetrahedron`: the oriented volume of four continuously moving real
  points is continuous in time.
* `ConformationTrajectory.continuous_volume`: the same statement for any four atoms of a
  pointwise-continuous trajectory of real `MolecularConformation`s.
* `exists_zero_of_opposite_sign`, `ConformationTrajectory.exists_zero_volume_of_opposite_sign`:
  a continuous real function on `unitInterval` whose endpoint values have opposite signs has an
  intermediate zero in time.
* `sign_eq_of_continuous_ne_zero`, `ConformationTrajectory.sign_volume_eq_of_ne_zero`: on a
  trajectory whose oriented volume never vanishes, `Real.sign` of the oriented volume is constant
  in time (explicitly conditioned on nonvanishing).
* Explicit fixture with `p0(t) = (1/2, 1/2, 1 - 2t)`, `p1 = (0,0,0)`, `p2 = (1,0,0)`,
  `p3 = (0,1,0)`: the oriented volume is exactly `1 - 2t` under the repository convention, hence
  `+1` at time `0` and `-1` at time `1`; all four atoms remain pairwise distinct throughout, and
  at time `1/2` the four points are distinct but coplanar (all have `z = 0`), so the volume
  crosses zero without any point collision.
* An independent, fully constructed `AmbientMotion` shear
  `F_t(x,y,z) = (x, y, z - 32 t x (x-1) y (y-1))` with explicit inverse
  `G_t(x,y,z) = (x, y, z + 32 t x (x-1) y (y-1))`.  Both maps are continuous homeomorphisms,
  jointly continuous forward and backward in `(t, x)`, and `F_0` is the identity.  The motion
  fixes `p1`, `p2`, `p3` and sends the height-`1` point `(1/2,1/2,1)` to height `1 - 2t`; its
  endpoint therefore sends the positively oriented initial quadruple to a negatively oriented
  one.  Thus an arbitrary ambient homeomorphism motion does *not* preserve four-point handedness,
  even though this particular motion is a diffeomorphism with pointwise Jacobian determinant
  `1`: the discrete four-vertex determinant is not a topological invariant of the embedded
  quadruple.

## Scope

This is an obstruction statement about supplied ambient motions and the discrete oriented-volume
determinant.  No energy barrier, kinetic pathway, CIP priority, knot classification, or claim that
every physical molecular trajectory is an ambient isotopy is made or needed.  No result assumes a
nonvanishing volume in order to prove a zero crossing.
-/

/-! ## The four-point tetrahedron associated with four real points -/

/-- The tetrahedron whose four vertices are the given real points, in the given order.  The order
matters: it fixes the sign of the oriented volume. -/
def tetrahedron (p0 p1 p2 p3 : Real3) : TetrahedralGeometry :=
  ⟨![p0, p1, p2, p3]⟩

@[simp] theorem tetrahedron_vertex (p0 p1 p2 p3 : Real3) (i : Fin 4) :
    (tetrahedron p0 p1 p2 p3).vertex i = ![p0, p1, p2, p3] i := rfl

/-! ## The intermediate value argument

These two lemmas are the analytic core: a continuous real-valued function on the connected unit
interval cannot go from one strict sign to the other without vanishing.  They are proved before
the trajectory structure so that the sign-constancy theorem below can use them directly. -/

/-- If the values of a continuous real function at two times have opposite signs, then the
function vanishes at some intermediate time. -/
theorem exists_zero_of_opposite_sign
    {f : unitInterval → ℝ} (hf : Continuous f) {a b : unitInterval}
    (hopp : f a * f b < 0) : ∃ c : unitInterval, f c = 0 := by
  rcases mul_neg_iff.mp hopp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- `0 < f a` and `f b < 0`: apply the intermediate value theorem from `b` to `a`.
    have hmem : (0 : ℝ) ∈ Set.Icc (f b) (f a) := ⟨le_of_lt hb, le_of_lt ha⟩
    obtain ⟨c, hc⟩ := intermediate_value_univ b a hf hmem
    exact ⟨c, hc⟩
  · -- `f a < 0` and `0 < f b`: apply the intermediate value theorem from `a` to `b`.
    have hmem : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
    obtain ⟨c, hc⟩ := intermediate_value_univ a b hf hmem
    exact ⟨c, hc⟩

/-- A continuous real function on the unit interval that never vanishes has constant sign. -/
theorem sign_eq_of_continuous_ne_zero
    {f : unitInterval → ℝ} (hf : Continuous f) (hne : ∀ t, f t ≠ 0)
    (t : unitInterval) : Real.sign (f t) = Real.sign (f 0) := by
  have h0 : f 0 ≠ 0 := hne 0
  rcases lt_or_gt_of_ne h0 with h0neg | h0pos
  · have ht : f t < 0 := by
      rcases lt_or_gt_of_ne (hne t) with htneg | htpos
      · exact htneg
      · obtain ⟨c, hc⟩ :=
          exists_zero_of_opposite_sign hf (a := 0) (b := t)
            (mul_neg_of_neg_of_pos h0neg htpos)
        exact absurd hc (hne c)
    rw [Real.sign_of_neg ht, Real.sign_of_neg h0neg]
  · have ht : 0 < f t := by
      rcases lt_or_gt_of_ne (hne t) with htneg | htpos
      · obtain ⟨c, hc⟩ :=
          exists_zero_of_opposite_sign hf (a := 0) (b := t)
            (mul_neg_of_pos_of_neg h0pos htneg)
        exact absurd hc (hne c)
      · exact htpos
    rw [Real.sign_of_pos ht, Real.sign_of_pos h0pos]

/-! ## Continuity of the oriented volume -/

/-- The oriented volume of four continuously moving real points is continuous in time.  This is
proved against the actual determinant `TetrahedralGeometry.orientedVolume`, not a supplied scalar
function: the homogeneous matrix has entries that are either coordinate projections of the four
continuous curves or the constant `1`. -/
theorem continuous_orientedVolume_tetrahedron
    {p0 p1 p2 p3 : unitInterval → Real3}
    (h0 : Continuous p0) (h1 : Continuous p1)
    (h2 : Continuous p2) (h3 : Continuous p3) :
    Continuous fun t =>
      orientedVolume (tetrahedron (p0 t) (p1 t) (p2 t) (p3 t)) := by
  have hmatrix : Continuous fun t : unitInterval =>
      homogeneousMatrix (tetrahedron (p0 t) (p1 t) (p2 t) (p3 t)) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [homogeneousMatrix, homogeneousRow, tetrahedron]
    all_goals
      first
      | exact continuous_const
      | exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) _).comp h0
      | exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) _).comp h1
      | exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) _).comp h2
      | exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) _).comp h3
  simpa only [orientedVolume] using hmatrix.matrix_det

/-! ## Continuous trajectories of real conformations -/

/-- A continuous trajectory of real molecular conformations, in the independent form of
pointwise-continuous atom coordinates.  No topology on the atom index is required: continuity is
requested separately for each atom, which is exactly the data consumed by the four-point volume
theorems below. -/
structure ConformationTrajectory (V : Type*) where
  /-- The real conformation at each time. -/
  trajectory : unitInterval → MolecularConformation V
  /-- Every atom follows a continuous trajectory in time. -/
  continuous_atom : ∀ atom : V, Continuous fun t => trajectory t atom

namespace ConformationTrajectory

variable {V : Type*}

/-- The oriented volume of the ordered quadruple `(a, b, c, d)` of atoms, as a real function of
time.  It is the genuine homogeneous-coordinate determinant of the four moving real points. -/
def volume (γ : ConformationTrajectory V) (a b c d : V) : unitInterval → ℝ :=
  fun t =>
    orientedVolume
      (tetrahedron (γ.trajectory t a) (γ.trajectory t b)
        (γ.trajectory t c) (γ.trajectory t d))

/-- The oriented volume of any four atoms of a pointwise-continuous trajectory is continuous in
time. -/
theorem continuous_volume (γ : ConformationTrajectory V) (a b c d : V) :
    Continuous (γ.volume a b c d) :=
  continuous_orientedVolume_tetrahedron
    (γ.continuous_atom a) (γ.continuous_atom b)
    (γ.continuous_atom c) (γ.continuous_atom d)

/-- The volume functional only depends on the pointwise trajectory. -/
theorem volume_congr {γ δ : ConformationTrajectory V}
    (h : ∀ t, γ.trajectory t = δ.trajectory t) (a b c d : V) :
    γ.volume a b c d = δ.volume a b c d := by
  funext t
  simp [volume, h t]

/-- Along a trajectory of four atoms whose oriented volume never vanishes, the sign of the
oriented volume is constant in time.  The nonvanishing hypothesis is explicit: this is exactly the
hypothesis under which a continuous real function cannot change sign without crossing zero. -/
theorem sign_volume_eq_of_ne_zero (γ : ConformationTrajectory V) (a b c d : V)
    (hne : ∀ t, γ.volume a b c d t ≠ 0) (t : unitInterval) :
    Real.sign (γ.volume a b c d t) = Real.sign (γ.volume a b c d 0) := by
  let f := γ.volume a b c d
  have hf : Continuous f := γ.continuous_volume a b c d
  change Real.sign (f t) = Real.sign (f 0)
  exact sign_eq_of_continuous_ne_zero hf hne t

/-- Opposite endpoint signs of the oriented volume force a zero-volume intermediate time, with no
nonvanishing hypothesis. -/
theorem exists_zero_volume_of_opposite_sign (γ : ConformationTrajectory V) (a b c d : V)
    (hopp : γ.volume a b c d 0 * γ.volume a b c d 1 < 0) :
    ∃ t : unitInterval, γ.volume a b c d t = 0 :=
  exists_zero_of_opposite_sign (γ.continuous_volume a b c d) hopp

end ConformationTrajectory

/-! ## Basic unit-interval values -/

/-- The midpoint time `1/2`. -/
def halfTime : unitInterval := ⟨1 / 2, by norm_num⟩

@[simp] theorem halfTime_val : (halfTime : ℝ) = 1 / 2 := rfl
@[simp] theorem unitInterval_zero_val : ((0 : unitInterval) : ℝ) = 0 := rfl
@[simp] theorem unitInterval_one_val : ((1 : unitInterval) : ℝ) = 1 := rfl

/-! ## The explicit fixture and its oriented volume

The fixture uses the repository's actual orientation convention
`orientedVolume = det [x_i y_i z_i 1]`.  With the ordered vertices
`p0(t), p1, p2, p3` the volume is exactly `1 - 2t`: positive at time `0` and negative at time `1`.
-/

/-- The first (moving) vertex `p0(t) = (1/2, 1/2, 1 - 2t)`. -/
def fixtureP0 (t : unitInterval) : Real3 :=
  WithLp.toLp 2 fun i : Fin 3 => ![(1 / 2 : ℝ), (1 / 2 : ℝ), 1 - 2 * (t : ℝ)] i

/-- The second vertex `p1 = (0, 0, 0)`. -/
def fixtureP1 : Real3 :=
  WithLp.toLp 2 fun i : Fin 3 => ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] i

/-- The third vertex `p2 = (1, 0, 0)`. -/
def fixtureP2 : Real3 :=
  WithLp.toLp 2 fun i : Fin 3 => ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] i

/-- The fourth vertex `p3 = (0, 1, 0)`. -/
def fixtureP3 : Real3 :=
  WithLp.toLp 2 fun i : Fin 3 => ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] i

@[simp] theorem fixtureP0_zero (t : unitInterval) : fixtureP0 t 0 = 1 / 2 := by
  simp [fixtureP0]

@[simp] theorem fixtureP0_one (t : unitInterval) : fixtureP0 t 1 = 1 / 2 := by
  simp [fixtureP0]

@[simp] theorem fixtureP0_two (t : unitInterval) : fixtureP0 t 2 = 1 - 2 * (t : ℝ) := by
  simp [fixtureP0]

@[simp] theorem fixtureP1_zero : fixtureP1 0 = 0 := by simp [fixtureP1]
@[simp] theorem fixtureP1_one : fixtureP1 1 = 0 := by simp [fixtureP1]
@[simp] theorem fixtureP1_two : fixtureP1 2 = 0 := by simp [fixtureP1]

@[simp] theorem fixtureP2_zero : fixtureP2 0 = 1 := by simp [fixtureP2]
@[simp] theorem fixtureP2_one : fixtureP2 1 = 0 := by simp [fixtureP2]
@[simp] theorem fixtureP2_two : fixtureP2 2 = 0 := by simp [fixtureP2]

@[simp] theorem fixtureP3_zero : fixtureP3 0 = 0 := by simp [fixtureP3]
@[simp] theorem fixtureP3_one : fixtureP3 1 = 1 := by simp [fixtureP3]
@[simp] theorem fixtureP3_two : fixtureP3 2 = 0 := by simp [fixtureP3]

/-- The fixture tetrahedron at time `t`. -/
def fixtureTetrahedron (t : unitInterval) : TetrahedralGeometry :=
  tetrahedron (fixtureP0 t) fixtureP1 fixtureP2 fixtureP3

/-- Under the repository convention, the oriented volume of the fixture is exactly `1 - 2t`.
This is an actual determinant computation through the existing `edgeMatrix` /
`Matrix.det_fin_three` API, not a definitional wrapper. -/
theorem fixtureVolume (t : unitInterval) :
    orientedVolume (fixtureTetrahedron t) = 1 - 2 * (t : ℝ) := by
  rw [orientedVolume_eq_edgeMatrix_det]
  rw [Matrix.det_fin_three]
  simp [fixtureTetrahedron, tetrahedron, edgeMatrix]

/-- The first vertex is continuous in time. -/
theorem continuous_fixtureP0 : Continuous fixtureP0 := by
  have hcoord : Continuous fun t : unitInterval => fun i : Fin 3 =>
      ![(1 / 2 : ℝ), (1 / 2 : ℝ), 1 - 2 * (t : ℝ)] i := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> continuity
  have hto : Continuous (fun f : Fin 3 → ℝ => WithLp.toLp (p := 2) f) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)
  simpa only [fixtureP0, Function.comp_apply] using hto.comp hcoord

/-! ## Pairwise distinctness of the four fixture atoms -/

theorem fixtureP0_ne_fixtureP1 (t : unitInterval) : fixtureP0 t ≠ fixtureP1 := by
  intro h
  have := congrArg (fun p : Real3 => p 0) h
  simp only [fixtureP0_zero, fixtureP1_zero] at this
  norm_num at this

theorem fixtureP0_ne_fixtureP2 (t : unitInterval) : fixtureP0 t ≠ fixtureP2 := by
  intro h
  have := congrArg (fun p : Real3 => p 0) h
  simp only [fixtureP0_zero, fixtureP2_zero] at this
  norm_num at this

theorem fixtureP0_ne_fixtureP3 (t : unitInterval) : fixtureP0 t ≠ fixtureP3 := by
  intro h
  have := congrArg (fun p : Real3 => p 0) h
  simp only [fixtureP0_zero, fixtureP3_zero] at this
  norm_num at this

theorem fixtureP1_ne_fixtureP2 : fixtureP1 ≠ fixtureP2 := by
  intro h
  have := congrArg (fun p : Real3 => p 0) h
  simp only [fixtureP1_zero, fixtureP2_zero] at this
  norm_num at this

theorem fixtureP1_ne_fixtureP3 : fixtureP1 ≠ fixtureP3 := by
  intro h
  have := congrArg (fun p : Real3 => p 1) h
  simp only [fixtureP1_one, fixtureP3_one] at this
  norm_num at this

theorem fixtureP2_ne_fixtureP3 : fixtureP2 ≠ fixtureP3 := by
  intro h
  have := congrArg (fun p : Real3 => p 0) h
  simp only [fixtureP2_zero, fixtureP3_zero] at this
  norm_num at this

/-- The time-`t` configuration of the fixture, as a concrete pointwise-continuous trajectory. -/
def fixtureTrajectory : ConformationTrajectory (Fin 4) where
  trajectory t := ![fixtureP0 t, fixtureP1, fixtureP2, fixtureP3]
  continuous_atom := by
    intro i
    fin_cases i
    · simpa using continuous_fixtureP0
    · simpa using (continuous_const : Continuous fun _ : unitInterval => fixtureP1)
    · simpa using (continuous_const : Continuous fun _ : unitInterval => fixtureP2)
    · simpa using (continuous_const : Continuous fun _ : unitInterval => fixtureP3)

/-- All four fixture atoms are pairwise distinct at every time. -/
theorem fixtureTrajectory_injective (t : unitInterval) :
    Function.Injective (fixtureTrajectory.trajectory t) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [fixtureTrajectory, fixtureP0_ne_fixtureP1 t, fixtureP0_ne_fixtureP2 t,
      fixtureP0_ne_fixtureP3 t, fixtureP1_ne_fixtureP2, fixtureP1_ne_fixtureP3,
      fixtureP2_ne_fixtureP3, Ne.symm (fixtureP0_ne_fixtureP1 t),
      Ne.symm (fixtureP0_ne_fixtureP2 t), Ne.symm (fixtureP0_ne_fixtureP3 t),
      Ne.symm fixtureP1_ne_fixtureP2, Ne.symm fixtureP1_ne_fixtureP3,
      Ne.symm fixtureP2_ne_fixtureP3]

/-- The fixture volume as a function of time. -/
theorem fixtureTrajectory_volume (t : unitInterval) :
    fixtureTrajectory.volume 0 1 2 3 t = 1 - 2 * (t : ℝ) := by
  have h := fixtureVolume t
  simpa [ConformationTrajectory.volume, fixtureTrajectory, fixtureTetrahedron, tetrahedron]
    using h

/-- The fixture exhibits a genuine sign change of the oriented volume. -/
theorem fixtureTrajectory_opposite_endpoint_signs :
    fixtureTrajectory.volume 0 1 2 3 0 * fixtureTrajectory.volume 0 1 2 3 1 < 0 := by
  rw [fixtureTrajectory_volume, fixtureTrajectory_volume]
  norm_num [unitInterval_zero_val, unitInterval_one_val]

/-- Consequently the fixture crosses zero oriented volume at an intermediate time. -/
theorem fixtureTrajectory_exists_zero_volume :
    ∃ t : unitInterval, fixtureTrajectory.volume 0 1 2 3 t = 0 :=
  fixtureTrajectory.exists_zero_volume_of_opposite_sign 0 1 2 3
    fixtureTrajectory_opposite_endpoint_signs

/-! ## The shear ambient motion

`F_t(x,y,z) = (x, y, z - 32 t x (x-1) y (y-1))`, with inverse
`G_t(x,y,z) = (x, y, z + 32 t x (x-1) y (y-1))`.  The two maps are mutually inverse because the
defect depends only on the first two coordinates, which both maps preserve. -/

/-- The shear defect `32 t x (x-1) y (y-1)` depends only on the first two coordinates. -/
def shearDefect (t : unitInterval) (p : Real3) : ℝ :=
  32 * (t : ℝ) * p 0 * (p 0 - 1) * p 1 * (p 1 - 1)

/-- The forward shear `F_t`. -/
def shearForward (t : unitInterval) (p : Real3) : Real3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    ![(p 0 : ℝ), (p 1 : ℝ), (p 2 : ℝ) - shearDefect t p] i

/-- The inverse shear `G_t`. -/
def shearInverse (t : unitInterval) (p : Real3) : Real3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    ![(p 0 : ℝ), (p 1 : ℝ), (p 2 : ℝ) + shearDefect t p] i

@[simp] theorem shearForward_zero (t : unitInterval) (p : Real3) :
    shearForward t p 0 = p 0 := by simp [shearForward]

@[simp] theorem shearForward_one (t : unitInterval) (p : Real3) :
    shearForward t p 1 = p 1 := by simp [shearForward]

@[simp] theorem shearForward_two (t : unitInterval) (p : Real3) :
    shearForward t p 2 = p 2 - shearDefect t p := by simp [shearForward]

@[simp] theorem shearInverse_zero (t : unitInterval) (p : Real3) :
    shearInverse t p 0 = p 0 := by simp [shearInverse]

@[simp] theorem shearInverse_one (t : unitInterval) (p : Real3) :
    shearInverse t p 1 = p 1 := by simp [shearInverse]

@[simp] theorem shearInverse_two (t : unitInterval) (p : Real3) :
    shearInverse t p 2 = p 2 + shearDefect t p := by simp [shearInverse]

/-- The defect is unchanged by the forward shear, because the first two coordinates are. -/
@[simp] theorem shearDefect_shearForward (t : unitInterval) (p : Real3) :
    shearDefect t (shearForward t p) = shearDefect t p := by
  simp [shearDefect]

/-- The defect is unchanged by the inverse shear, because the first two coordinates are. -/
@[simp] theorem shearDefect_shearInverse (t : unitInterval) (p : Real3) :
    shearDefect t (shearInverse t p) = shearDefect t p := by
  simp [shearDefect]

/-- The forward and inverse shears are mutually inverse (one direction). -/
theorem shearInverse_forward (t : unitInterval) (p : Real3) :
    shearInverse t (shearForward t p) = p := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [shearInverse, shearForward]
  · simp [shearInverse, shearForward]
  · simp [shearInverse, shearForward, shearDefect]
    try ring

/-- The forward and inverse shears are mutually inverse (the other direction). -/
theorem shearForward_inverse (t : unitInterval) (p : Real3) :
    shearForward t (shearInverse t p) = p := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [shearForward, shearInverse]
  · simp [shearForward, shearInverse]
  · simp [shearForward, shearInverse, shearDefect]
    try ring

/-- Joint continuity of the shear defect in time and position. -/
@[continuity]
theorem continuous_shearDefect :
    Continuous fun pair : unitInterval × Real3 => shearDefect pair.1 pair.2 := by
  unfold shearDefect
  have ht : Continuous fun pair : unitInterval × Real3 => (pair.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have h0 : Continuous fun pair : unitInterval × Real3 => pair.2 0 :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 0).comp continuous_snd
  have h1 : Continuous fun pair : unitInterval × Real3 => pair.2 1 :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 1).comp continuous_snd
  exact ((((continuous_const.mul ht).mul h0).mul (h0.sub continuous_const)).mul h1).mul
    (h1.sub continuous_const)

/-- Joint continuity of the forward shear. -/
theorem continuous_shearForward :
    Continuous fun pair : unitInterval × Real3 => shearForward pair.1 pair.2 := by
  have hcoord : Continuous fun pair : unitInterval × Real3 => fun i : Fin 3 =>
      ![(pair.2 0 : ℝ), (pair.2 1 : ℝ),
        (pair.2 2 : ℝ) - shearDefect pair.1 pair.2] i := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp
    all_goals
      first
      | exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 0).comp continuous_snd
      | exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 1).comp continuous_snd
      | exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 2).comp
          continuous_snd).sub continuous_shearDefect
  have hto : Continuous (fun f : Fin 3 → ℝ => WithLp.toLp (p := 2) f) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)
  simpa only [shearForward, Function.comp_apply] using hto.comp hcoord

/-- Joint continuity of the inverse shear. -/
theorem continuous_shearInverse :
    Continuous fun pair : unitInterval × Real3 => shearInverse pair.1 pair.2 := by
  have hcoord : Continuous fun pair : unitInterval × Real3 => fun i : Fin 3 =>
      ![(pair.2 0 : ℝ), (pair.2 1 : ℝ),
        (pair.2 2 : ℝ) + shearDefect pair.1 pair.2] i := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp
    all_goals
      first
      | exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 0).comp continuous_snd
      | exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 1).comp continuous_snd
      | exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 2).comp
          continuous_snd).add continuous_shearDefect
  have hto : Continuous (fun f : Fin 3 → ℝ => WithLp.toLp (p := 2) f) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)
  simpa only [shearInverse, Function.comp_apply] using hto.comp hcoord

/-- The shear at time `t` is a homeomorphism of real three-space. -/
def shearHomeomorph (t : unitInterval) : Real3 ≃ₜ Real3 where
  toFun := shearForward t
  invFun := shearInverse t
  left_inv := shearInverse_forward t
  right_inv := shearForward_inverse t
  continuous_toFun := by
    have h := continuous_shearForward.comp
      ((continuous_const : Continuous fun _ : Real3 => t).prodMk continuous_id)
    simpa [Function.comp_def] using h
  continuous_invFun := by
    have h := continuous_shearInverse.comp
      ((continuous_const : Continuous fun _ : Real3 => t).prodMk continuous_id)
    simpa [Function.comp_def] using h

/-- The shear as a genuine ambient motion over the unit interval, starting at the identity. -/
def shearMotion : AmbientMotion where
  map := shearHomeomorph
  continuous_uncurried := by
    simpa [shearHomeomorph] using continuous_shearForward
  continuous_uncurried_inv := by
    simpa [shearHomeomorph] using continuous_shearInverse
  starts_identity := by
    ext p
    rename_i i
    fin_cases i <;> simp [shearHomeomorph, shearForward, shearDefect]

/-- The initial first vertex `p0(0) = (1/2, 1/2, 1)`. -/
def fixtureInitialP0 : Real3 := fixtureP0 0

/-- The defect at the initial first vertex is exactly `2t`. -/
theorem shearDefect_fixtureInitialP0 (t : unitInterval) :
    shearDefect t (fixtureP0 0) = 2 * (t : ℝ) := by
  simp only [shearDefect, fixtureP0_zero, fixtureP0_one]
  ring

/-- The shear sends the initial first vertex to the fixture point at the same time: the height
`1` becomes `1 - 2t`. -/
theorem shearForward_fixtureInitialP0 (t : unitInterval) :
    shearForward t (fixtureP0 0) = fixtureP0 t := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [shearForward, fixtureP0]
  · simp [shearForward, fixtureP0]
  · simp [shearForward, fixtureP0, shearDefect]
    try ring

/-- The motion fixes `p1 = (0,0,0)` for every time. -/
theorem shearForward_fixtureP1 (t : unitInterval) :
    shearForward t fixtureP1 = fixtureP1 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [shearForward, shearDefect, fixtureP1]

/-- The motion fixes `p2 = (1,0,0)` for every time. -/
theorem shearForward_fixtureP2 (t : unitInterval) :
    shearForward t fixtureP2 = fixtureP2 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [shearForward, shearDefect, fixtureP2]

/-- The motion fixes `p3 = (0,1,0)` for every time. -/
theorem shearForward_fixtureP3 (t : unitInterval) :
    shearForward t fixtureP3 = fixtureP3 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [shearForward, shearDefect, fixtureP3]

/-- The motion's endpoint sends the initial first vertex to the time-`1` fixture point. -/
theorem shearMotion_endpoint_fixtureInitialP0 :
    shearMotion.endpoint fixtureInitialP0 = fixtureP0 1 := by
  simpa [AmbientMotion.endpoint, shearMotion, shearHomeomorph, fixtureInitialP0] using
    shearForward_fixtureInitialP0 1

/-- The endpoint of the shear motion fixes `p1`. -/
theorem shearMotion_endpoint_fixtureP1 :
    shearMotion.endpoint fixtureP1 = fixtureP1 := by
  simpa [AmbientMotion.endpoint, shearMotion, shearHomeomorph] using shearForward_fixtureP1 1

/-- The endpoint of the shear motion fixes `p2`. -/
theorem shearMotion_endpoint_fixtureP2 :
    shearMotion.endpoint fixtureP2 = fixtureP2 := by
  simpa [AmbientMotion.endpoint, shearMotion, shearHomeomorph] using shearForward_fixtureP2 1

/-- The endpoint of the shear motion fixes `p3`. -/
theorem shearMotion_endpoint_fixtureP3 :
    shearMotion.endpoint fixtureP3 = fixtureP3 := by
  simpa [AmbientMotion.endpoint, shearMotion, shearHomeomorph] using shearForward_fixtureP3 1

/-! ## The transported trajectory

The shear motion transports the initial configuration `(p0(0), p1, p2, p3)` to the fixture
configuration `(p0(t), p1, p2, p3)` at every time.  This is a genuine ambient-motion trajectory,
not a diagonal curve action: each atom is moved by the single time-`t` homeomorphism. -/

/-- The initial four-atom configuration `(p0(0), p1, p2, p3)`. -/
def fixtureInitialConformation : MolecularConformation (Fin 4) :=
  ![fixtureInitialP0, fixtureP1, fixtureP2, fixtureP3]

/-- At every time the ambient motion transports the initial configuration to the fixture
configuration. -/
theorem shearMotion_applyAt_initial (t : unitInterval) :
    shearMotion.applyAt t fixtureInitialConformation =
      ![fixtureP0 t, fixtureP1, fixtureP2, fixtureP3] := by
  funext i
  fin_cases i <;>
    simp [AmbientMotion.applyAt, shearMotion, shearHomeomorph, fixtureInitialConformation,
      fixtureInitialP0, shearForward_fixtureInitialP0, shearForward_fixtureP1,
      shearForward_fixtureP2, shearForward_fixtureP3]

/-- The shear trajectory: the initial conformation transported by the ambient motion. -/
def shearTrajectory : ConformationTrajectory (Fin 4) where
  trajectory t := shearMotion.applyAt t fixtureInitialConformation
  continuous_atom := by
    intro i
    simpa using (shearMotion.atomTrajectory fixtureInitialConformation i).continuous

/-- The shear trajectory is exactly the explicit fixture trajectory. -/
theorem shearTrajectory_eq_fixture (t : unitInterval) :
    shearTrajectory.trajectory t = fixtureTrajectory.trajectory t :=
  shearMotion_applyAt_initial t

/-- All four transported atoms remain pairwise distinct at every time. -/
theorem shearTrajectory_atom_injective (t : unitInterval) :
    Function.Injective (shearTrajectory.trajectory t) := by
  rw [shearTrajectory_eq_fixture t]
  exact fixtureTrajectory_injective t

/-- The oriented volume along the transported trajectory is `1 - 2t`. -/
theorem shearTrajectory_volume (t : unitInterval) :
    shearTrajectory.volume 0 1 2 3 t = 1 - 2 * (t : ℝ) := by
  rw [show shearTrajectory.volume 0 1 2 3 = fixtureTrajectory.volume 0 1 2 3 from
    ConformationTrajectory.volume_congr shearTrajectory_eq_fixture 0 1 2 3]
  exact fixtureTrajectory_volume t

/-- The transported trajectory has opposite endpoint signs, with no collision of points. -/
theorem shearTrajectory_opposite_endpoint_signs :
    shearTrajectory.volume 0 1 2 3 0 * shearTrajectory.volume 0 1 2 3 1 < 0 := by
  rw [shearTrajectory_volume, shearTrajectory_volume]
  norm_num [unitInterval_zero_val, unitInterval_one_val]

/-- The zero-volume intermediate time is furnished by the general theorem. -/
theorem shearTrajectory_exists_zero_volume :
    ∃ t : unitInterval, shearTrajectory.volume 0 1 2 3 t = 0 :=
  shearTrajectory.exists_zero_volume_of_opposite_sign 0 1 2 3
    shearTrajectory_opposite_endpoint_signs

/-- At time `1/2` the transported volume is zero. -/
theorem shearTrajectory_volume_half :
    shearTrajectory.volume 0 1 2 3 halfTime = 0 := by
  rw [shearTrajectory_volume]
  norm_num [halfTime_val]

/-- The oriented volume along the transported trajectory vanishes exactly at `t = 1/2`. -/
theorem shearTrajectory_volume_eq_zero_iff (t : unitInterval) :
    shearTrajectory.volume 0 1 2 3 t = 0 ↔ t = halfTime := by
  rw [shearTrajectory_volume]
  constructor
  · intro h
    apply Subtype.ext
    have ht : (t : ℝ) = 1 / 2 := by linarith
    simpa [halfTime] using ht
  · intro h
    rw [h]
    norm_num [halfTime_val]

/-- At the zero-volume time the four atoms are all in the plane `z = 0`: they are distinct but
coplanar.  This is the collision-free crossing of a coplanar configuration. -/
theorem shearTrajectory_half_coplanar :
    (shearTrajectory.trajectory halfTime 0) 2 = 0 ∧
      (shearTrajectory.trajectory halfTime 1) 2 = 0 ∧
      (shearTrajectory.trajectory halfTime 2) 2 = 0 ∧
      (shearTrajectory.trajectory halfTime 3) 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [shearTrajectory_eq_fixture, fixtureTrajectory, fixtureP0, fixtureP1, fixtureP2,
      fixtureP3, halfTime_val]

/-- The collision-free coplanar crossing, bundled. -/
theorem shearTrajectory_crosses_coplanar_without_collision :
    Function.Injective (shearTrajectory.trajectory halfTime) ∧
      shearTrajectory.volume 0 1 2 3 halfTime = 0 ∧
      (∀ i : Fin 4, (shearTrajectory.trajectory halfTime i) 2 = 0) := by
  refine ⟨shearTrajectory_atom_injective halfTime, shearTrajectory_volume_half, ?_⟩
  intro i
  fin_cases i
  · exact shearTrajectory_half_coplanar.1
  · exact shearTrajectory_half_coplanar.2.1
  · exact shearTrajectory_half_coplanar.2.2.1
  · exact shearTrajectory_half_coplanar.2.2.2

/-! ## The endpoint does not preserve four-point handedness -/

/-- The initial quadruple has oriented volume `+1`. -/
theorem fixtureInitial_volume :
    orientedVolume (tetrahedron fixtureInitialP0 fixtureP1 fixtureP2 fixtureP3) = 1 := by
  have h := fixtureVolume (0 : unitInterval)
  simp only [unitInterval_zero_val] at h
  norm_num at h
  simpa [fixtureTetrahedron, tetrahedron, fixtureInitialP0] using h

/-- The endpoint action sends the initial quadruple to one of oriented volume `-1`. -/
theorem shearMotion_endpoint_volume :
    orientedVolume
      (tetrahedron (shearMotion.endpoint fixtureInitialP0) fixtureP1 fixtureP2 fixtureP3) = -1 := by
  rw [shearMotion_endpoint_fixtureInitialP0]
  have h := fixtureVolume (1 : unitInterval)
  simp only [unitInterval_one_val] at h
  norm_num at h
  simpa [fixtureTetrahedron, tetrahedron] using h

/-- The shear ambient motion changes the sign of the discrete oriented volume of the quadruple.
The same four labelled atoms, transported by a genuine ambient motion starting at the identity,
end with the opposite handedness even though no pair of atoms ever collides. -/
theorem shearMotion_endpoint_reverses_four_point_volume :
    orientedVolume
        (tetrahedron (shearMotion.endpoint fixtureInitialP0) fixtureP1 fixtureP2 fixtureP3) = -1 ∧
      orientedVolume (tetrahedron fixtureInitialP0 fixtureP1 fixtureP2 fixtureP3) = 1 :=
  ⟨shearMotion_endpoint_volume, fixtureInitial_volume⟩

/-- There exists an ambient homeomorphism motion, starting at the identity, whose endpoint maps a
positively oriented labelled quadruple of distinct points to a negatively oriented one. -/
theorem exists_ambient_motion_endpoint_reversing_four_point_volume :
    ∃ motion : AmbientMotion,
      orientedVolume
          (tetrahedron (motion.endpoint fixtureInitialP0) fixtureP1 fixtureP2 fixtureP3) = -1 ∧
        orientedVolume (tetrahedron fixtureInitialP0 fixtureP1 fixtureP2 fixtureP3) = 1 :=
  ⟨shearMotion, shearMotion_endpoint_reverses_four_point_volume⟩

/-- The endpoint reverses the sign of the oriented volume even though the shear is a
diffeomorphism with pointwise Jacobian determinant `1`.  The information that fails to be
preserved is the sign of the discrete four-vertex determinant, not the local orientation of the
ambient map. -/
theorem shearMotion_endpoint_reverses_real_sign :
    Real.sign
        (orientedVolume
          (tetrahedron (shearMotion.endpoint fixtureInitialP0) fixtureP1 fixtureP2 fixtureP3)) =
        -1 ∧
      Real.sign (orientedVolume (tetrahedron fixtureInitialP0 fixtureP1 fixtureP2 fixtureP3)) =
        1 := by
  rw [shearMotion_endpoint_volume, fixtureInitial_volume]
  constructor
  · rw [Real.sign_of_neg (by norm_num : (-1 : ℝ) < 0)]
  · rw [Real.sign_of_pos (by norm_num : (0 : ℝ) < 1)]

end

end OneCenter
end TetraStereo
