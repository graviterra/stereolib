import TetraStereo.KernelOnly
import TetraStereo.OneCenter.Pseudoasymmetry
import TetraStereo.OneCenter.Geometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace PseudoTetrahedralViewingFidelity

noncomputable section

/-!
  Source-viewing fidelity for lowercase pseudoasymmetric descriptors.

  ## What this module proves

  `PseudoRS.ofSign` is calibrated to the IUPAC source convention: viewed from the side remote from
  the lowest-precedence ligand, a clockwise `highest → left → right` order is lowercase `r`.  In
  the standard right-handed frame (`x` right, `y` up, `z` toward the viewer) that clockwise order
  has **negative** signed screen area and therefore **negative** oriented volume, so the determinant
  handedness `-1` must map to `r` and `+1` to `s`.

  This module does not merely restate that sign table.  It extracts the handedness from an actual
  tetrahedral realization by factoring the oriented volume into the viewing height and the signed
  screen area of the three high-priority vertices.  `SourceViewingFrame` packages exactly the
  source-viewing situation (three high-priority vertices on the viewer side, the lowest-priority
  vertex remote, positive height, clockwise projection).  The bridge theorems then relate the
  *geometric* handedness and the *two enantiomorphic ligand-priority cases* to the existing
  lowercase producer `pseudoDescriptor`.

  ## Scope

  The frame is a geometric statement about priority slots `[highest, left, right, lowest]`; it does
  not claim that the tetrahedral fixture in
  `TetraStereo/Examples/PseudoasymmetricTrihydroxyglutaricAcid.lean` is a Cartesian realization of
  the molecular graph.  That fixture remains abstract permutation data.
-/

/-- A concrete point of `R^3` in the right-handed frame used throughout the repository. -/
def point (x y z : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![x, y, z]

/-- Twice the signed area of the `x`-`y` projection of the vertices `0, 1, 2`, in the order
`0 → 1 → 2`.  Positive means counterclockwise when the screen is viewed with `x` right and `y`
up; negative means clockwise.  The `z` coordinates are the viewing depth and do not enter. -/
def screenTwiceArea (g : TetrahedralGeometry) : ℝ :=
  g.vertex 0 0 * (g.vertex 1 1 - g.vertex 2 1)
    - g.vertex 0 1 * (g.vertex 1 0 - g.vertex 2 0)
    + (g.vertex 1 0 * g.vertex 2 1 - g.vertex 2 0 * g.vertex 1 1)

/-- The source-viewing orientation predicate: the high-priority face appears clockwise. -/
def ClockwiseViewedFromLowest (g : TetrahedralGeometry) : Prop :=
  screenTwiceArea g < 0

/-- `Real.sign x = -1` is exactly negativity. -/
theorem realSign_eq_neg_one_iff {x : ℝ} : Real.sign x = -1 ↔ x < 0 := by
  constructor
  · intro h
    by_contra hnon
    have hnonneg : 0 ≤ x := le_of_not_gt hnon
    rcases lt_or_eq_of_le hnonneg with hpos | hzero
    · rw [Real.sign_of_pos hpos] at h
      norm_num at h
    · rw [← hzero, Real.sign_zero] at h
      norm_num at h
  · exact Real.sign_of_neg

/-- `Real.sign x = 1` is exactly positivity. -/
theorem realSign_eq_one_iff {x : ℝ} : Real.sign x = 1 ↔ 0 < x := by
  constructor
  · intro h
    by_contra hnon
    have hnonpos : x ≤ 0 := le_of_not_gt hnon
    rcases lt_or_eq_of_le hnonpos with hneg | hzero
    · rw [Real.sign_of_neg hneg] at h
      norm_num at h
    · rw [hzero, Real.sign_zero] at h
      norm_num at h
  · exact Real.sign_of_pos

/-- The oriented volume is the viewing height times the signed screen area.  The height is the
`z`-difference between the high-priority face and the lowest-priority vertex; the screen area is
computed in the `x`-`y` plane and is independent of depth. -/
theorem orientedVolume_eq_viewHeight_mul_screenTwiceArea
    (g : TetrahedralGeometry) (top bottom : ℝ)
    (vertex_zero_height : g.vertex 0 2 = top)
    (vertex_one_height : g.vertex 1 2 = top)
    (vertex_two_height : g.vertex 2 2 = top)
    (vertex_three_height : g.vertex 3 2 = bottom) :
    TetrahedralGeometry.orientedVolume g = (top - bottom) * screenTwiceArea g := by
  have hc0 : Fin.castSucc (0 : Fin 3) = (0 : Fin 4) := rfl
  have hc1 : Fin.castSucc (1 : Fin 3) = (1 : Fin 4) := rfl
  have hc2 : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := rfl
  rw [TetrahedralGeometry.orientedVolume_eq_edgeMatrix_det, Matrix.det_fin_three]
  simp [TetrahedralGeometry.edgeMatrix, screenTwiceArea, hc0, hc1, hc2,
    vertex_zero_height, vertex_one_height, vertex_two_height, vertex_three_height]
  ring

/-- Geometric handedness is the sign of the oriented volume. -/
theorem handedness_eq_neg_one_iff_volume_neg (g : TetrahedralGeometry) :
    TetrahedralGeometry.handedness g = -1 ↔ TetrahedralGeometry.orientedVolume g < 0 := by
  rw [TetrahedralGeometry.handedness]
  exact realSign_eq_neg_one_iff

/-- Geometric handedness `+1` is positive oriented volume. -/
theorem handedness_eq_one_iff_volume_pos (g : TetrahedralGeometry) :
    TetrahedralGeometry.handedness g = 1 ↔ 0 < TetrahedralGeometry.orientedVolume g := by
  rw [TetrahedralGeometry.handedness]
  exact realSign_eq_one_iff

/-- Handedness in terms of the viewing product, without assuming a positive height. -/
theorem handedness_eq_neg_one_iff_viewProduct_neg
    (g : TetrahedralGeometry) (top bottom : ℝ)
    (vertex_zero_height : g.vertex 0 2 = top)
    (vertex_one_height : g.vertex 1 2 = top)
    (vertex_two_height : g.vertex 2 2 = top)
    (vertex_three_height : g.vertex 3 2 = bottom) :
    TetrahedralGeometry.handedness g = -1 ↔ (top - bottom) * screenTwiceArea g < 0 := by
  rw [TetrahedralGeometry.handedness,
    orientedVolume_eq_viewHeight_mul_screenTwiceArea g top bottom vertex_zero_height
      vertex_one_height vertex_two_height vertex_three_height]
  exact realSign_eq_neg_one_iff

/-- Handedness in terms of the viewing product, without assuming a positive height. -/
theorem handedness_eq_one_iff_viewProduct_pos
    (g : TetrahedralGeometry) (top bottom : ℝ)
    (vertex_zero_height : g.vertex 0 2 = top)
    (vertex_one_height : g.vertex 1 2 = top)
    (vertex_two_height : g.vertex 2 2 = top)
    (vertex_three_height : g.vertex 3 2 = bottom) :
    TetrahedralGeometry.handedness g = 1 ↔ 0 < (top - bottom) * screenTwiceArea g := by
  rw [TetrahedralGeometry.handedness,
    orientedVolume_eq_viewHeight_mul_screenTwiceArea g top bottom vertex_zero_height
      vertex_one_height vertex_two_height vertex_three_height]
  exact realSign_eq_one_iff

/-- **Source-viewing bridge.**  If the three high-priority vertices lie on the viewer side
(positive height) and the projected order `highest → left → right` is clockwise, then the
determinant handedness is `-1`, exactly the sign that `PseudoRS.ofSign` reads as lowercase `r`.
The converse is also proved: positive determinant handedness cannot be clockwise in this frame. -/
theorem handedness_eq_neg_one_iff_screenTwiceArea_neg
    (g : TetrahedralGeometry) (top bottom : ℝ)
    (vertex_zero_height : g.vertex 0 2 = top)
    (vertex_one_height : g.vertex 1 2 = top)
    (vertex_two_height : g.vertex 2 2 = top)
    (vertex_three_height : g.vertex 3 2 = bottom)
    (positive_height : 0 < top - bottom) :
    TetrahedralGeometry.handedness g = -1 ↔ screenTwiceArea g < 0 := by
  rw [handedness_eq_neg_one_iff_viewProduct_neg g top bottom vertex_zero_height
    vertex_one_height vertex_two_height vertex_three_height]
  constructor
  · intro hproduct
    by_contra hnon
    have hnonneg : 0 ≤ screenTwiceArea g := le_of_not_gt hnon
    have hprodnonneg : 0 ≤ (top - bottom) * screenTwiceArea g :=
      mul_nonneg positive_height.le hnonneg
    exact (not_lt_of_ge hprodnonneg) hproduct
  · exact fun hscreen => mul_neg_of_pos_of_neg positive_height hscreen

/-- Source-viewing bridge in the `+1` direction. -/
theorem handedness_eq_one_iff_screenTwiceArea_pos
    (g : TetrahedralGeometry) (top bottom : ℝ)
    (vertex_zero_height : g.vertex 0 2 = top)
    (vertex_one_height : g.vertex 1 2 = top)
    (vertex_two_height : g.vertex 2 2 = top)
    (vertex_three_height : g.vertex 3 2 = bottom)
    (positive_height : 0 < top - bottom) :
    TetrahedralGeometry.handedness g = 1 ↔ 0 < screenTwiceArea g := by
  rw [handedness_eq_one_iff_viewProduct_pos g top bottom vertex_zero_height
    vertex_one_height vertex_two_height vertex_three_height]
  constructor
  · intro hproduct
    by_contra hnon
    have hnonpos : screenTwiceArea g ≤ 0 := le_of_not_gt hnon
    have hprodnonpos : (top - bottom) * screenTwiceArea g ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos positive_height.le hnonpos
    exact (not_lt_of_ge hprodnonpos) hproduct
  · exact fun hscreen => mul_pos positive_height hscreen

/-- The source-viewing situation as a structure: the three high-priority vertices are on the
viewer side of the lowest-priority vertex, and their projected order is clockwise. -/
structure SourceViewingFrame where
  geometry : TetrahedralGeometry
  top : ℝ
  bottom : ℝ
  vertex_zero_height : geometry.vertex 0 2 = top
  vertex_one_height : geometry.vertex 1 2 = top
  vertex_two_height : geometry.vertex 2 2 = top
  vertex_three_height : geometry.vertex 3 2 = bottom
  positive_height : 0 < top - bottom
  clockwise : ClockwiseViewedFromLowest geometry

namespace SourceViewingFrame

variable (F : SourceViewingFrame)

/-- In a source-viewing frame the geometric handedness is `-1`, the `r` sign. -/
theorem handedness : TetrahedralGeometry.handedness F.geometry = -1 :=
  (handedness_eq_neg_one_iff_screenTwiceArea_neg F.geometry F.top F.bottom
    F.vertex_zero_height F.vertex_one_height F.vertex_two_height F.vertex_three_height
    F.positive_height).2 F.clockwise

/-- A source-viewing frame is nondegenerate. -/
theorem nondegenerate : TetrahedralGeometry.Nondegenerate F.geometry := by
  intro hzero
  have hsign : TetrahedralGeometry.handedness F.geometry = 0 := by
    simp [TetrahedralGeometry.handedness, hzero]
  rw [F.handedness] at hsign
  norm_num at hsign

/-- The geometric handedness is not the degenerate fallback `0`. -/
theorem handedness_ne_zero : TetrahedralGeometry.handedness F.geometry ≠ 0 := by
  rw [F.handedness]
  norm_num

/-- The oriented volume is nonzero. -/
theorem orientedVolume_ne_zero : TetrahedralGeometry.orientedVolume F.geometry ≠ 0 := by
  intro hzero
  exact F.nondegenerate hzero

/-- **General pair bridge.**  The lowercase producer read with the actual geometric handedness
reduces to `ofSign` applied to the negative Rule-5 pair sign.  This is not a restatement of the
sign table: the center sign is `handedness F.geometry`, computed from the viewing geometry, and
the pair sign is the Rule-5 sign of the two enantiomorphic ligand descriptors. -/
theorem pseudoDescriptor_eq_ofSign_neg_pairSign (left right : RS) :
    pseudoDescriptor (TetrahedralGeometry.handedness F.geometry) left right =
      PseudoRS.ofSign (-(rule5PairSign left right)) := by
  rw [F.handedness]
  simp [pseudoDescriptor, pseudoasymmetricSign]

/-- The same bridge expressed through the Rule-5 comparison ordering actually used by the engine. -/
theorem pseudoDescriptor_eq_ofSign_neg_orderingSign (left right : RS) :
    pseudoDescriptor (TetrahedralGeometry.handedness F.geometry) left right =
      PseudoRS.ofSign (-(orderingSign (rule5PairOrdering left right))) := by
  rw [orderingSign_rule5PairOrdering]
  exact F.pseudoDescriptor_eq_ofSign_neg_pairSign left right

/-- The conditional source case `[highest achiral, left R, right S, lowest]`: clockwise
source-viewing gives `r`. -/
theorem pseudoDescriptor_R_S_eq_r :
    pseudoDescriptor (TetrahedralGeometry.handedness F.geometry) RS.R RS.S = PseudoRS.r := by
  rw [F.pseudoDescriptor_eq_ofSign_neg_pairSign]
  simp [rule5PairSign]

/-- The enantiomorphic priority case `[highest achiral, left S, right R, lowest]` gives `s`. -/
theorem pseudoDescriptor_S_R_eq_s :
    pseudoDescriptor (TetrahedralGeometry.handedness F.geometry) RS.S RS.R = PseudoRS.s := by
  rw [F.pseudoDescriptor_eq_ofSign_neg_pairSign]
  simp [rule5PairSign]

/-- Lowercase descriptors are mirror invariant: the geometric sign changes and the enantiomorphic
labels swap, so the descriptor is unchanged. -/
theorem mirror_invariant (left right : RS) :
    pseudoDescriptor (-(TetrahedralGeometry.handedness F.geometry))
      (RS.swap left) (RS.swap right) =
        pseudoDescriptor (TetrahedralGeometry.handedness F.geometry) left right :=
  pseudoDescriptor_mirror (TetrahedralGeometry.handedness F.geometry) left right

end SourceViewingFrame




def sourceViewingWitness : TetrahedralGeometry where
  vertex :=
    ![point 0 1 1, point 1 (-1) 1, point (-1) (-1) 1, point 0 0 (-1)]

@[simp] theorem sourceViewingWitness_vertex_zero_height :
    sourceViewingWitness.vertex 0 2 = 1 := by
  simp [sourceViewingWitness, point, PiLp.toLp_apply]

@[simp] theorem sourceViewingWitness_vertex_one_height :
    sourceViewingWitness.vertex 1 2 = 1 := by
  simp [sourceViewingWitness, point, PiLp.toLp_apply]

@[simp] theorem sourceViewingWitness_vertex_two_height :
    sourceViewingWitness.vertex 2 2 = 1 := by
  simp [sourceViewingWitness, point, PiLp.toLp_apply]

@[simp] theorem sourceViewingWitness_vertex_three_height :
    sourceViewingWitness.vertex 3 2 = -1 := by
  simp [sourceViewingWitness, point, PiLp.toLp_apply]

/-- The projected high-priority face of the witness has signed twice-area `-4`: clockwise. -/
theorem sourceViewingWitness_screenTwiceArea :
    screenTwiceArea sourceViewingWitness = -4 := by
  change (0 : ℝ) * ((-1) - (-1)) - 1 * (1 - (-1)) +
    (1 * (-1) - (-1) * (-1)) = -4
  norm_num

/-- The witness is clockwise as viewed from the lowest-priority ligand. -/
theorem sourceViewingWitness_clockwise :
    ClockwiseViewedFromLowest sourceViewingWitness := by
  rw [ClockwiseViewedFromLowest, sourceViewingWitness_screenTwiceArea]
  norm_num


theorem sourceViewingWitness_volume :
    TetrahedralGeometry.orientedVolume sourceViewingWitness = -8 := by
  rw [orientedVolume_eq_viewHeight_mul_screenTwiceArea sourceViewingWitness 1 (-1)
    sourceViewingWitness_vertex_zero_height sourceViewingWitness_vertex_one_height
    sourceViewingWitness_vertex_two_height sourceViewingWitness_vertex_three_height]
  rw [sourceViewingWitness_screenTwiceArea]
  norm_num

/-- The witness handedness is `-1`, the source lowercase `r` sign. -/
theorem sourceViewingWitness_handedness :
    TetrahedralGeometry.handedness sourceViewingWitness = -1 := by
  rw [TetrahedralGeometry.handedness, sourceViewingWitness_volume]
  exact Real.sign_of_neg (by norm_num)

/-- The witness is nondegenerate. -/
theorem sourceViewingWitness_nondegenerate :
    TetrahedralGeometry.Nondegenerate sourceViewingWitness := by
  rw [TetrahedralGeometry.Nondegenerate, sourceViewingWitness_volume]
  norm_num

/-- The witness packaged as a genuine source-viewing frame. -/
def sourceViewingWitnessFrame : SourceViewingFrame where
  geometry := sourceViewingWitness
  top := 1
  bottom := -1
  vertex_zero_height := sourceViewingWitness_vertex_zero_height
  vertex_one_height := sourceViewingWitness_vertex_one_height
  vertex_two_height := sourceViewingWitness_vertex_two_height
  vertex_three_height := sourceViewingWitness_vertex_three_height
  positive_height := by norm_num
  clockwise := sourceViewingWitness_clockwise

/-- Kernel-checked source result: the witness with priority pair `R,S` receives `r`, not `s`. -/
theorem sourceViewingWitness_descriptor_R_S_eq_r :
    pseudoDescriptor (TetrahedralGeometry.handedness sourceViewingWitness) RS.R RS.S =
      PseudoRS.r :=
  sourceViewingWitnessFrame.pseudoDescriptor_R_S_eq_r

/-- The enantiomorphic priority pair `S,R` receives `s`. -/
theorem sourceViewingWitness_descriptor_S_R_eq_s :
    pseudoDescriptor (TetrahedralGeometry.handedness sourceViewingWitness) RS.S RS.R =
      PseudoRS.s :=
  sourceViewingWitnessFrame.pseudoDescriptor_S_R_eq_s

/-- Meaningful kernel guard: using the uncalibrated positive center sign `+1` on the witness's
actual `R,S` priority pair misclassifies the descriptor.  The geometric handedness is `-1`, so the
correct result is `r`; the naive `+1` reading yields `s`. -/
theorem naive_positive_centerSign_misclassifies :
    pseudoDescriptor 1 RS.R RS.S ≠
      pseudoDescriptor (TetrahedralGeometry.handedness sourceViewingWitness) RS.R RS.S := by
  rw [sourceViewingWitness_handedness]
  simp [pseudoDescriptor, pseudoasymmetricSign]

/-- Kernel guard: the witness's handedness is not the degenerate fallback. -/
theorem sourceViewingWitness_handedness_ne_zero :
    TetrahedralGeometry.handedness sourceViewingWitness ≠ 0 := by
  rw [sourceViewingWitness_handedness]
  norm_num

end

end PseudoTetrahedralViewingFidelity
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.orientedVolume_eq_viewHeight_mul_screenTwiceArea
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.handedness_eq_neg_one_iff_screenTwiceArea_neg
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.handedness_eq_one_iff_screenTwiceArea_pos
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.SourceViewingFrame.handedness
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.SourceViewingFrame.nondegenerate
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.SourceViewingFrame.pseudoDescriptor_R_S_eq_r
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.SourceViewingFrame.pseudoDescriptor_S_R_eq_s
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.SourceViewingFrame.mirror_invariant
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.sourceViewingWitness_volume
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.sourceViewingWitness_handedness
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.sourceViewingWitness_descriptor_R_S_eq_r
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.sourceViewingWitness_descriptor_S_R_eq_s
assert_kernel_only TetraStereo.OneCenter.PseudoTetrahedralViewingFidelity.naive_positive_centerSign_misclassifies
