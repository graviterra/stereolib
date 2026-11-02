import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CIPTetrahedralViewingCalibration

/-!
# Independent viewing calibration for tetrahedral `R/S` descriptors

This module calibrates the exact tetrahedral descriptor relation against the IUPAC
Prelog--Helmchen chirality rule (P-92.1.2.1, primary source `P9.txt` lines 406 and 794):
with the four ligands in descending priority order `a > b > c > d`, the reader looks at the
model from the side remote from `d` (the lowest-priority ligand points away from the reader)
and reads `a → b → c`.  If that turn is clockwise the centre is `R`; if anticlockwise it is `S`.
The sphere-I `HCBrClF` example at line 794 states the calibration explicitly: the descending
order `Br > Cl > F > H` describes a clockwise direction and the configuration is `R`.

The screen frame used below is the standard right-handed frame with `x` pointing right, `y`
pointing up and `z` pointing towards the reader.  The first three points lie on a plane
`z = h` parallel to the screen and the fourth lies at `z = k` with `k < h`, so the fourth
(lowest-priority) ligand is farther from the reader than the screen plane.

The main algebraic result is

`orientedVolume first second third fourth = (h - k) * twiceSignedArea2D first second third`,

which is proved here from the coordinate definition of the existing
`CartesianPoint3.orientedVolume` and is not assumed.  Consequently, for `k < h`, the sign of
the existing oriented volume is exactly the sign of the screen turn.

## The corrected physical producer

The production definitions now implement exactly this calibration:

* `CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?` maps negative volume to `R` and
  positive volume to `S` (and refuses zero);
* `CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor` certifies `R` exactly by negative
  volume and `S` exactly by positive volume;
* `RS.ofHandedness (-1) = RS.R` and `RS.ofHandedness 1 = RS.S`.

The direct source-conformance theorems below state, without any descriptor swap,

`descriptorOfOrientedVolume? (orientedVolume f s t u) = some descriptor ↔
 SourceCalibratedDescriptor [f, s, t, u] descriptor`,

and its list-facing and declarative counterparts.  The bridge theorem
`sourceCalibrated_conforms_real_handedness` additionally identifies the source-calibrated
descriptor with `RS.ofHandedness` of the real tetrahedral handedness.

## Exact regression

For the standard coordinates

* priority 1 `= (0, 1, 1)`
* priority 2 `= (1, -1, 1)`
* priority 3 `= (-1, -1, 1)`
* priority 4 `= (0, 0, -1)`

the screen triangle `1 → 2 → 3` is clockwise (signed double area `-4`) and the oriented
volume is `-8`.  The source calibration, the executable producer and the declarative
relation therefore all read `R`; the declarative relation does not certify `S`.  These facts
are collected in `counterexample_regression`.  The pre-repair module (in which the executable
map and the declarative relation instead returned `S`) is preserved unchanged as a historical
artifact under
`tmp/chemical-fidelity-20261018/tetrahedral-before-repair-evidence/`; it is not a description
of the current definitions.

This is a **local four-point viewing calibration**.  The whole-molecule public pipeline and
normalization by an arbitrary Euclidean view frame are separate obligations and are *not*
claimed here.  Every theorem below is stated under the explicit viewing normalization
`first.z = second.z = third.z = h`, `fourth.z = k`, `k < h` (or for the point-level
existential relations that carry those witnesses themselves).
-/

/-! ## Exact planar signed area -/

/-- Twice the signed area of the oriented screen triangle `first → second → third`.  In the
standard screen frame (`x` right, `y` up) this is positive for an anticlockwise turn and
negative for a clockwise turn. -/
def twiceSignedArea2D (first second third : CartesianPoint3) : ℚ :=
  (second.x - first.x) * (third.y - first.y) -
    (second.y - first.y) * (third.x - first.x)

/-- The cross-product form used above is the shoelace double area. -/
theorem twiceSignedArea2D_eq_shoelace (first second third : CartesianPoint3) :
    twiceSignedArea2D first second third =
      (first.x * second.y - second.x * first.y) +
        (second.x * third.y - third.x * second.y) +
          (third.x * first.y - first.x * third.y) := by
  unfold twiceSignedArea2D
  ring

/-- The ordinary signed area of the oriented screen triangle, i.e. half of
`twiceSignedArea2D`. -/
def signedArea2D (first second third : CartesianPoint3) : ℚ :=
  twiceSignedArea2D first second third / 2

/-- The double area is twice the ordinary signed area. -/
theorem twiceSignedArea2D_eq_two_mul_signedArea2D (first second third : CartesianPoint3) :
    twiceSignedArea2D first second third = 2 * signedArea2D first second third := by
  unfold signedArea2D
  ring

/-- The ordered screen turn is clockwise.  This is the geometric reading of a negative signed
area in the standard right-handed screen frame. -/
def ClockwiseOnScreen (first second third : CartesianPoint3) : Prop :=
  twiceSignedArea2D first second third < 0

/-- The ordered screen turn is anticlockwise. -/
def AnticlockwiseOnScreen (first second third : CartesianPoint3) : Prop :=
  0 < twiceSignedArea2D first second third

/-- The three screen points are collinear, so no turn is defined. -/
def ScreenDegenerate (first second third : CartesianPoint3) : Prop :=
  twiceSignedArea2D first second third = 0

/-- The three possible executable readings of a screen triangle. -/
inductive ScreenTurn where
  | clockwise
  | anticlockwise
  | degenerate
  deriving DecidableEq, Repr

/-- Executable screen-turn classification from the exact signed double area. -/
def screenTurn (first second third : CartesianPoint3) : ScreenTurn :=
  if twiceSignedArea2D first second third < 0 then ScreenTurn.clockwise
  else if 0 < twiceSignedArea2D first second third then ScreenTurn.anticlockwise
  else ScreenTurn.degenerate

@[simp] theorem screenTurn_eq_clockwise_iff (first second third : CartesianPoint3) :
    screenTurn first second third = ScreenTurn.clockwise ↔
      ClockwiseOnScreen first second third := by
  unfold screenTurn ClockwiseOnScreen
  by_cases areaNegative : twiceSignedArea2D first second third < 0
  · simp [areaNegative]
  · by_cases areaPositive : 0 < twiceSignedArea2D first second third
    · simp [areaNegative, areaPositive]
    · simp [areaNegative, areaPositive]

@[simp] theorem screenTurn_eq_anticlockwise_iff (first second third : CartesianPoint3) :
    screenTurn first second third = ScreenTurn.anticlockwise ↔
      AnticlockwiseOnScreen first second third := by
  unfold screenTurn AnticlockwiseOnScreen
  by_cases areaNegative : twiceSignedArea2D first second third < 0
  · have areaNonpositive : twiceSignedArea2D first second third ≤ 0 := le_of_lt areaNegative
    simp [areaNegative, areaNonpositive]
  · by_cases areaPositive : 0 < twiceSignedArea2D first second third
    · simp [areaNegative, areaPositive]
    · simp [areaNegative, areaPositive]

@[simp] theorem screenTurn_eq_degenerate_iff (first second third : CartesianPoint3) :
    screenTurn first second third = ScreenTurn.degenerate ↔
      ScreenDegenerate first second third := by
  unfold screenTurn ScreenDegenerate
  by_cases areaNegative : twiceSignedArea2D first second third < 0
  · have areaNeZero : twiceSignedArea2D first second third ≠ 0 := ne_of_lt areaNegative
    simp [areaNegative, areaNeZero]
  · by_cases areaPositive : 0 < twiceSignedArea2D first second third
    · have areaNeZero : twiceSignedArea2D first second third ≠ 0 := ne_of_gt areaPositive
      simp [areaNegative, areaPositive, areaNeZero]
    · have areaZero : twiceSignedArea2D first second third = 0 :=
        le_antisymm (not_lt.mp areaPositive) (not_lt.mp areaNegative)
      simp [areaZero]

/-! ## The oriented volume of a screen-normalized tetrahedron -/

/-- For three points on the screen-parallel plane `z = h` and a fourth point at `z = k`, the
existing exact oriented volume (anchored at the fourth point) is the screen separation
`h - k` times twice the signed screen area of the first three points.  The `x` and `y`
coordinates of the fourth point cancel, so they are arbitrary. -/
theorem orientedVolume_eq_screenSeparation_mul_twiceSignedArea2D
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k) :
    CartesianPoint3.orientedVolume first second third fourth =
      (h - k) * twiceSignedArea2D first second third := by
  unfold CartesianPoint3.orientedVolume twiceSignedArea2D
  rw [firstHeight, secondHeight, thirdHeight, fourthDepth]
  ring

/-- The same identity in terms of the ordinary signed screen area. -/
theorem orientedVolume_eq_two_mul_screenSeparation_mul_signedArea2D
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k) :
    CartesianPoint3.orientedVolume first second third fourth =
      2 * (h - k) * signedArea2D first second third := by
  rw [orientedVolume_eq_screenSeparation_mul_twiceSignedArea2D first second third fourth h k
    firstHeight secondHeight thirdHeight fourthDepth,
    twiceSignedArea2D_eq_two_mul_signedArea2D]
  ring

/-- Clockwise screen area is exactly negative oriented volume when the fourth point is behind
the screen plane (`k < h`). -/
theorem orientedVolume_neg_iff_clockwise
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) :
    CartesianPoint3.orientedVolume first second third fourth < 0 ↔
      ClockwiseOnScreen first second third := by
  unfold ClockwiseOnScreen
  rw [orientedVolume_eq_screenSeparation_mul_twiceSignedArea2D first second third fourth h k
    firstHeight secondHeight thirdHeight fourthDepth]
  exact ⟨fun volumeNegative =>
      Left.neg_of_mul_neg_right volumeNegative (le_of_lt (sub_pos.mpr behind)),
    fun areaNegative => mul_neg_of_pos_of_neg (sub_pos.mpr behind) areaNegative⟩

/-- Anticlockwise screen area is exactly positive oriented volume when the fourth point is
behind the screen plane. -/
theorem orientedVolume_pos_iff_anticlockwise
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) :
    0 < CartesianPoint3.orientedVolume first second third fourth ↔
      AnticlockwiseOnScreen first second third := by
  unfold AnticlockwiseOnScreen
  rw [orientedVolume_eq_screenSeparation_mul_twiceSignedArea2D first second third fourth h k
    firstHeight secondHeight thirdHeight fourthDepth]
  exact mul_pos_iff_of_pos_left (sub_pos.mpr behind)

/-- Degenerate screen area is exactly zero oriented volume when the fourth point is behind the
screen plane. -/
theorem orientedVolume_eq_zero_iff_degenerate
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) :
    CartesianPoint3.orientedVolume first second third fourth = 0 ↔
      ScreenDegenerate first second third := by
  unfold ScreenDegenerate
  rw [orientedVolume_eq_screenSeparation_mul_twiceSignedArea2D first second third fourth h k
    firstHeight secondHeight thirdHeight fourthDepth]
  exact ⟨fun volumeZero =>
      (mul_eq_zero_iff_left (ne_of_gt (sub_pos.mpr behind))).mp volumeZero,
    fun areaZero => by rw [areaZero, mul_zero]⟩

/-! ## Source-calibrated relation -/

/-- Source-calibrated `R/S` relation read directly from the screen turn, with the
lowest-priority ligand (the fourth point) behind the screen plane.  The first three points are
on a common screen-parallel plane.  Clockwise `a → b → c` reads `R`, anticlockwise reads `S`,
exactly as in P-92.1.2.1 and the `HCBrClF` sphere-I example of the primary source. -/
def SourceCalibratedDescriptor (points : List CartesianPoint3) (descriptor : RS) : Prop :=
  ∃ (first second third fourth : CartesianPoint3),
    points = [first, second, third, fourth] ∧
      first.z = second.z ∧ second.z = third.z ∧ fourth.z < first.z ∧
        ((descriptor = RS.R ∧ screenTurn first second third = ScreenTurn.clockwise) ∨
         (descriptor = RS.S ∧ screenTurn first second third = ScreenTurn.anticlockwise))

/-- Source-calibrated refusal for a collinear (degenerate) screen triangle under the same
viewing normalization. -/
def SourceCalibratedDegenerate (points : List CartesianPoint3) : Prop :=
  ∃ (first second third fourth : CartesianPoint3),
    points = [first, second, third, fourth] ∧
      first.z = second.z ∧ second.z = third.z ∧ fourth.z < first.z ∧
        screenTurn first second third = ScreenTurn.degenerate

/-- The viewing-normalized volume-sign relation: negative oriented volume reads `R`, positive
oriented volume reads `S`.  The existential `h`, `k` witnesses record the viewing
normalization under which this relation is used.  This is exactly the semantics implemented
by the corrected production `RationalTetrahedralDescriptor`. -/
def CorrectedTetrahedralDescriptor (points : List CartesianPoint3)
    (descriptor : RS) : Prop :=
  ∃ (first second third fourth : CartesianPoint3) (h k : ℚ),
    points = [first, second, third, fourth] ∧
      first.z = h ∧ second.z = h ∧ third.z = h ∧ fourth.z = k ∧ k < h ∧
        ((descriptor = RS.R ∧
            CartesianPoint3.orientedVolume first second third fourth < 0) ∨
         (descriptor = RS.S ∧
            0 < CartesianPoint3.orientedVolume first second third fourth))

/-- Decomposition lemma for four-element lists. -/
private theorem list4_eq_iff {α : Type*} {a b c d e f g h : α} :
    ([a, b, c, d] : List α) = [e, f, g, h] ↔
      a = e ∧ b = f ∧ c = g ∧ d = h := by
  simp [List.cons.injEq]

/-- Fixed-list unfolding of the source-calibrated relation. -/
theorem sourceCalibratedDescriptor_cons_iff
    (first second third fourth : CartesianPoint3) (descriptor : RS) :
    SourceCalibratedDescriptor [first, second, third, fourth] descriptor ↔
      first.z = second.z ∧ second.z = third.z ∧ fourth.z < first.z ∧
        ((descriptor = RS.R ∧ screenTurn first second third = ScreenTurn.clockwise) ∨
         (descriptor = RS.S ∧ screenTurn first second third = ScreenTurn.anticlockwise)) := by
  constructor
  · rintro ⟨first', second', third', fourth', pointsEq, heightOne, heightTwo, depth, turn⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := list4_eq_iff.mp pointsEq
    exact ⟨heightOne, heightTwo, depth, turn⟩
  · rintro ⟨heightOne, heightTwo, depth, turn⟩
    exact ⟨first, second, third, fourth, rfl, heightOne, heightTwo, depth, turn⟩

/-- Fixed-list unfolding of source-calibrated degeneracy. -/
theorem sourceCalibratedDegenerate_cons_iff
    (first second third fourth : CartesianPoint3) :
    SourceCalibratedDegenerate [first, second, third, fourth] ↔
      first.z = second.z ∧ second.z = third.z ∧ fourth.z < first.z ∧
        screenTurn first second third = ScreenTurn.degenerate := by
  constructor
  · rintro ⟨first', second', third', fourth', pointsEq, heightOne, heightTwo, depth, turn⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := list4_eq_iff.mp pointsEq
    exact ⟨heightOne, heightTwo, depth, turn⟩
  · rintro ⟨heightOne, heightTwo, depth, turn⟩
    exact ⟨first, second, third, fourth, rfl, heightOne, heightTwo, depth, turn⟩

/-- The source-calibrated relation, rewritten to screen-area signs under an explicit viewing
normalization. -/
theorem sourceCalibratedDescriptor_cons_iff_of_viewing
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) (descriptor : RS) :
    SourceCalibratedDescriptor [first, second, third, fourth] descriptor ↔
      ((descriptor = RS.R ∧ twiceSignedArea2D first second third < 0) ∨
       (descriptor = RS.S ∧ 0 < twiceSignedArea2D first second third)) := by
  have firstSecondHeight : first.z = second.z := firstHeight.trans secondHeight.symm
  have secondThirdHeight : second.z = third.z := secondHeight.trans thirdHeight.symm
  have fourthBehind : fourth.z < first.z := by
    calc
      fourth.z = k := fourthDepth
      _ < h := behind
      _ = first.z := firstHeight.symm
  rw [sourceCalibratedDescriptor_cons_iff]
  constructor
  · rintro ⟨_, _, _, turn⟩
    rcases turn with ⟨descriptorEq, clockwise⟩ | ⟨descriptorEq, anticlockwise⟩
    · exact Or.inl ⟨descriptorEq, (screenTurn_eq_clockwise_iff first second third).mp clockwise⟩
    · exact Or.inr
        ⟨descriptorEq, (screenTurn_eq_anticlockwise_iff first second third).mp anticlockwise⟩
  · rintro turn
    rcases turn with ⟨descriptorEq, clockwise⟩ | ⟨descriptorEq, anticlockwise⟩
    · exact ⟨firstSecondHeight, secondThirdHeight, fourthBehind,
        Or.inl ⟨descriptorEq, (screenTurn_eq_clockwise_iff first second third).mpr clockwise⟩⟩
    · exact ⟨firstSecondHeight, secondThirdHeight, fourthBehind,
        Or.inr
          ⟨descriptorEq, (screenTurn_eq_anticlockwise_iff first second third).mpr anticlockwise⟩⟩

/-- The source-calibrated relation under viewing normalization is exactly the
viewing-normalized volume-sign relation: negative oriented volume reads `R`, positive
oriented volume reads `S`, and the four points form a clockwise/anticlockwise screen triangle
accordingly. -/
theorem sourceCalibrated_iff_corrected
    (points : List CartesianPoint3) (descriptor : RS) :
    SourceCalibratedDescriptor points descriptor ↔
      CorrectedTetrahedralDescriptor points descriptor := by
  constructor
  · rintro ⟨first, second, third, fourth, pointsEq, firstSecondHeight,
      secondThirdHeight, fourthBehind, turn⟩
    have secondHeight : second.z = first.z := firstSecondHeight.symm
    have thirdHeight : third.z = first.z := secondThirdHeight.symm.trans firstSecondHeight.symm
    have volumeNegativeIff :=
      orientedVolume_neg_iff_clockwise first second third fourth first.z fourth.z
        rfl secondHeight thirdHeight rfl fourthBehind
    have volumePositiveIff :=
      orientedVolume_pos_iff_anticlockwise first second third fourth first.z fourth.z
        rfl secondHeight thirdHeight rfl fourthBehind
    refine ⟨first, second, third, fourth, first.z, fourth.z, pointsEq, rfl, secondHeight,
      thirdHeight, rfl, fourthBehind, ?_⟩
    rcases turn with ⟨descriptorEq, clockwise⟩ | ⟨descriptorEq, anticlockwise⟩
    · exact Or.inl ⟨descriptorEq,
        volumeNegativeIff.mpr ((screenTurn_eq_clockwise_iff first second third).mp clockwise)⟩
    · exact Or.inr ⟨descriptorEq,
        volumePositiveIff.mpr
          ((screenTurn_eq_anticlockwise_iff first second third).mp anticlockwise)⟩
  · rintro ⟨first, second, third, fourth, h, k, pointsEq, firstHeight, secondHeight,
      thirdHeight, fourthDepth, behind, sign⟩
    have firstSecondHeight : first.z = second.z := firstHeight.trans secondHeight.symm
    have secondThirdHeight : second.z = third.z := secondHeight.trans thirdHeight.symm
    have fourthBehind : fourth.z < first.z := by
      calc
        fourth.z = k := fourthDepth
        _ < h := behind
        _ = first.z := firstHeight.symm
    have volumeNegativeIff :=
      orientedVolume_neg_iff_clockwise first second third fourth h k
        firstHeight secondHeight thirdHeight fourthDepth behind
    have volumePositiveIff :=
      orientedVolume_pos_iff_anticlockwise first second third fourth h k
        firstHeight secondHeight thirdHeight fourthDepth behind
    refine ⟨first, second, third, fourth, pointsEq, firstSecondHeight, secondThirdHeight,
      fourthBehind, ?_⟩
    rcases sign with ⟨descriptorEq, volumeNegative⟩ | ⟨descriptorEq, volumePositive⟩
    · exact Or.inl ⟨descriptorEq,
        (screenTurn_eq_clockwise_iff first second third).mpr
          (volumeNegativeIff.mp volumeNegative)⟩
    · exact Or.inr ⟨descriptorEq,
        (screenTurn_eq_anticlockwise_iff first second third).mpr
          (volumePositiveIff.mp volumePositive)⟩

/-- The degenerate case: under the same viewing normalization, source-calibrated refusal is
exactly zero oriented volume. -/
theorem sourceCalibratedDegenerate_iff_orientedVolume_eq_zero_of_viewing
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) :
    SourceCalibratedDegenerate [first, second, third, fourth] ↔
      CartesianPoint3.orientedVolume first second third fourth = 0 := by
  have firstSecondHeight : first.z = second.z := firstHeight.trans secondHeight.symm
  have secondThirdHeight : second.z = third.z := secondHeight.trans thirdHeight.symm
  have fourthBehind : fourth.z < first.z := by
    calc
      fourth.z = k := fourthDepth
      _ < h := behind
      _ = first.z := firstHeight.symm
  rw [sourceCalibratedDegenerate_cons_iff]
  constructor
  · rintro ⟨_, _, _, turn⟩
    exact (orientedVolume_eq_zero_iff_degenerate first second third fourth h k
      firstHeight secondHeight thirdHeight fourthDepth behind).mpr
        ((screenTurn_eq_degenerate_iff first second third).mp turn)
  · intro volumeZero
    exact ⟨firstSecondHeight, secondThirdHeight, fourthBehind,
      (screenTurn_eq_degenerate_iff first second third).mpr
        ((orientedVolume_eq_zero_iff_degenerate first second third fourth h k
          firstHeight secondHeight thirdHeight fourthDepth behind).mp volumeZero)⟩

/-! ## Source conformance of the corrected production producer -/

/-- Fixed-list unfolding of the production declarative rational relation.  The corrected
definition certifies `R` exactly on negative oriented volume and `S` exactly on positive
oriented volume. -/
theorem rationalTetrahedralDescriptor_cons_iff
    (first second third fourth : CartesianPoint3) (descriptor : RS) :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [first, second, third, fourth] descriptor ↔
      (match descriptor with
       | RS.R => CartesianPoint3.orientedVolume first second third fourth < 0
       | RS.S => 0 < CartesianPoint3.orientedVolume first second third fourth) := by
  constructor
  · rintro ⟨first', second', third', fourth', pointsEq, sign⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := list4_eq_iff.mp pointsEq
    exact sign
  · intro sign
    exact ⟨first, second, third, fourth, rfl, sign⟩

/-- The production executable descriptor and the production declarative relation agree
exactly on a fixed four-tuple, with no viewing normalization needed: both read negative
volume as `R` and positive volume as `S`. -/
theorem rationalTetrahedralDescriptor_iff_descriptorOfOrientedVolume
    (first second third fourth : CartesianPoint3) (descriptor : RS) :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [first, second, third, fourth] descriptor ↔
      CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
          (CartesianPoint3.orientedVolume first second third fourth) = some descriptor := by
  rw [rationalTetrahedralDescriptor_cons_iff]
  cases descriptor with
  | R =>
      change (CartesianPoint3.orientedVolume first second third fourth < 0) ↔
        CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
          (CartesianPoint3.orientedVolume first second third fourth) = some RS.R
      exact ⟨fun volumeNegative =>
          (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_R_iff
            (CartesianPoint3.orientedVolume first second third fourth)).mpr volumeNegative,
        fun descriptorEq =>
          (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_R_iff
            (CartesianPoint3.orientedVolume first second third fourth)).mp descriptorEq⟩
  | S =>
      change (0 < CartesianPoint3.orientedVolume first second third fourth) ↔
        CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
          (CartesianPoint3.orientedVolume first second third fourth) = some RS.S
      exact ⟨fun volumePositive =>
          (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_S_iff
            (CartesianPoint3.orientedVolume first second third fourth)).mpr volumePositive,
        fun descriptorEq =>
          (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_S_iff
            (CartesianPoint3.orientedVolume first second third fourth)).mp descriptorEq⟩

/-- Under the stated viewing normalization, the production declarative relation is exactly
the source-calibrated relation.  There is no `R/S` swap. -/
theorem rationalTetrahedralDescriptor_iff_corrected_under_viewing
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) (descriptor : RS) :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [first, second, third, fourth] descriptor ↔
      CorrectedTetrahedralDescriptor [first, second, third, fourth] descriptor := by
  cases descriptor with
  | R =>
      rw [rationalTetrahedralDescriptor_cons_iff]
      change (CartesianPoint3.orientedVolume first second third fourth < 0) ↔
        CorrectedTetrahedralDescriptor [first, second, third, fourth] RS.R
      constructor
      · intro volumeNegative
        exact ⟨first, second, third, fourth, h, k, rfl, firstHeight, secondHeight,
          thirdHeight, fourthDepth, behind, Or.inl ⟨rfl, volumeNegative⟩⟩
      · rintro ⟨first', second', third', fourth', h', k', pointsEq, _, _, _, _, _, sign⟩
        obtain ⟨rfl, rfl, rfl, rfl⟩ := list4_eq_iff.mp pointsEq
        rcases sign with ⟨_, volumeNegative⟩ | ⟨impossible, _⟩
        · exact volumeNegative
        · exact absurd impossible (by simp)
  | S =>
      rw [rationalTetrahedralDescriptor_cons_iff]
      change (0 < CartesianPoint3.orientedVolume first second third fourth) ↔
        CorrectedTetrahedralDescriptor [first, second, third, fourth] RS.S
      constructor
      · intro volumePositive
        exact ⟨first, second, third, fourth, h, k, rfl, firstHeight, secondHeight,
          thirdHeight, fourthDepth, behind, Or.inr ⟨rfl, volumePositive⟩⟩
      · rintro ⟨first', second', third', fourth', h', k', pointsEq, _, _, _, _, _, sign⟩
        obtain ⟨rfl, rfl, rfl, rfl⟩ := list4_eq_iff.mp pointsEq
        rcases sign with ⟨impossible, _⟩ | ⟨_, volumePositive⟩
        · exact absurd impossible (by simp)
        · exact volumePositive

/-- Under the stated viewing normalization, the source-calibrated relation and the production
declarative relation coincide exactly.  This is the direct source-conformance statement: the
corrected producer certifies the descriptor that the source rule reads. -/
theorem sourceCalibrated_iff_rationalDescriptor_under_viewing
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) (descriptor : RS) :
    SourceCalibratedDescriptor [first, second, third, fourth] descriptor ↔
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [first, second, third, fourth] descriptor :=
  (sourceCalibrated_iff_corrected [first, second, third, fourth] descriptor).trans
    (rationalTetrahedralDescriptor_iff_corrected_under_viewing first second third fourth h k
      firstHeight secondHeight thirdHeight fourthDepth behind descriptor).symm

/-- General source-conformance theorem for the production executable descriptor: on every
viewing-normalized four-point centre, `descriptorOfOrientedVolume?` returns a descriptor
exactly when the source-calibrated rule reads that same descriptor.  No swap occurs. -/
theorem descriptorOfOrientedVolume?_eq_some_iff_source
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) (descriptor : RS) :
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume first second third fourth) = some descriptor ↔
      SourceCalibratedDescriptor [first, second, third, fourth] descriptor := by
  rw [sourceCalibratedDescriptor_cons_iff_of_viewing first second third fourth h k
    firstHeight secondHeight thirdHeight fourthDepth behind]
  have volumeNegativeIff :=
    orientedVolume_neg_iff_clockwise first second third fourth h k
      firstHeight secondHeight thirdHeight fourthDepth behind
  have volumePositiveIff :=
    orientedVolume_pos_iff_anticlockwise first second third fourth h k
      firstHeight secondHeight thirdHeight fourthDepth behind
  cases descriptor with
  | R =>
      rw [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_R_iff]
      constructor
      · intro volumeNegative
        exact Or.inl ⟨rfl, volumeNegativeIff.mp volumeNegative⟩
      · rintro (⟨_, clockwise⟩ | ⟨impossible, _⟩)
        · exact volumeNegativeIff.mpr clockwise
        · exact absurd impossible (by simp)
  | S =>
      rw [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_S_iff]
      constructor
      · intro volumePositive
        exact Or.inr ⟨rfl, volumePositiveIff.mp volumePositive⟩
      · rintro (⟨impossible, _⟩ | ⟨_, anticlockwise⟩)
        · exact absurd impossible (by simp)
        · exact volumePositiveIff.mpr anticlockwise

/-- List-facing form of the general source-conformance theorem for the executable
priority-ordered point pipeline. -/
theorem descriptorOfPriorityOrderedPoints?_eq_some_iff_source
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) (descriptor : RS) :
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
        [first, second, third, fourth] = some descriptor ↔
      SourceCalibratedDescriptor [first, second, third, fourth] descriptor := by
  have pointReading :
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
          [first, second, third, fourth] =
        CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
          (CartesianPoint3.orientedVolume first second third fourth) := rfl
  rw [pointReading,
    descriptorOfOrientedVolume?_eq_some_iff_source first second third fourth h k
      firstHeight secondHeight thirdHeight fourthDepth behind]

/-- Degenerate source conformance: under the viewing normalization, the executable producer
refuses exactly the collinear screen triangles. -/
theorem descriptorOfOrientedVolume?_eq_none_iff_degenerate_under_viewing
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) :
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume first second third fourth) = none ↔
      ScreenDegenerate first second third := by
  rw [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_none_iff,
    orientedVolume_eq_zero_iff_degenerate first second third fourth h k
      firstHeight secondHeight thirdHeight fourthDepth behind]

/-- Degenerate source conformance in source-relation form: refusal is exactly the
source-calibrated degenerate reading. -/
theorem descriptorOfOrientedVolume?_eq_none_iff_sourceDegenerate
    (first second third fourth : CartesianPoint3) (h k : ℚ)
    (firstHeight : first.z = h) (secondHeight : second.z = h)
    (thirdHeight : third.z = h) (fourthDepth : fourth.z = k)
    (behind : k < h) :
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume first second third fourth) = none ↔
      SourceCalibratedDegenerate [first, second, third, fourth] := by
  rw [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_none_iff,
    sourceCalibratedDegenerate_iff_orientedVolume_eq_zero_of_viewing first second third fourth
      h k firstHeight secondHeight thirdHeight fourthDepth behind]

/-- Every source-calibrated descriptor equals `RS.ofHandedness` of the real tetrahedral
handedness of the same four points.  Together with `RS.ofHandedness (-1) = RS.R` and
`RS.ofHandedness 1 = RS.S`, this identifies the corrected producer with the real-valued
tetrahedral handedness semantics. -/
theorem sourceCalibrated_conforms_real_handedness
    {points : List CartesianPoint3} {descriptor : RS}
    (correct : SourceCalibratedDescriptor points descriptor) :
    ∃ first second third fourth,
      points = [first, second, third, fourth] ∧
      descriptor = RS.ofHandedness
        (TetrahedralGeometry.handedness
          (CartesianPoint3.toRealTetrahedralGeometry first second third fourth)) := by
  obtain ⟨first, second, third, fourth, pointsEq, firstSecondHeight, secondThirdHeight,
    fourthBehind, turn⟩ := correct
  have corrected : CorrectedTetrahedralDescriptor points descriptor :=
    (sourceCalibrated_iff_corrected points descriptor).mp
      ⟨first, second, third, fourth, pointsEq, firstSecondHeight, secondThirdHeight,
        fourthBehind, turn⟩
  obtain ⟨f, s, t, u, h, k, pointsEq, firstHeight, secondHeight, thirdHeight, fourthDepth,
    behind, sign⟩ := corrected
  rw [pointsEq]
  exact CertifiedLocalizedCIPInput.rationalTetrahedralDescriptor_conforms_real_handedness
    ((rationalTetrahedralDescriptor_iff_corrected_under_viewing f s t u h k
      firstHeight secondHeight thirdHeight fourthDepth behind descriptor).mpr
      ⟨f, s, t, u, h, k, rfl, firstHeight, secondHeight, thirdHeight, fourthDepth, behind,
        sign⟩)

/-! ## Exact regression configuration -/

/-- Priority-1 point of the regression configuration: `(0, 1, 1)`. -/
def counterexampleFirst : CartesianPoint3 := ⟨0, 1, 1⟩

/-- Priority-2 point of the regression configuration: `(1, -1, 1)`. -/
def counterexampleSecond : CartesianPoint3 := ⟨1, -1, 1⟩

/-- Priority-3 point of the regression configuration: `(-1, -1, 1)`. -/
def counterexampleThird : CartesianPoint3 := ⟨-1, -1, 1⟩

/-- Priority-4 (lowest) point of the regression configuration: `(0, 0, -1)`, behind the
screen plane `z = 1`. -/
def counterexampleFourth : CartesianPoint3 := ⟨0, 0, -1⟩

theorem counterexample_orientedVolume :
    CartesianPoint3.orientedVolume counterexampleFirst counterexampleSecond
      counterexampleThird counterexampleFourth = -8 := by
  norm_num [CartesianPoint3.orientedVolume, counterexampleFirst, counterexampleSecond,
    counterexampleThird, counterexampleFourth]

theorem counterexample_twiceSignedArea2D :
    twiceSignedArea2D counterexampleFirst counterexampleSecond counterexampleThird = -4 := by
  norm_num [twiceSignedArea2D, counterexampleFirst, counterexampleSecond, counterexampleThird]

theorem counterexample_clockwise : ClockwiseOnScreen
    counterexampleFirst counterexampleSecond counterexampleThird := by
  unfold ClockwiseOnScreen
  rw [counterexample_twiceSignedArea2D]
  norm_num

theorem counterexample_screenTurn :
    screenTurn counterexampleFirst counterexampleSecond counterexampleThird =
      ScreenTurn.clockwise := by
  rw [screenTurn_eq_clockwise_iff]
  exact counterexample_clockwise

/-- The corrected executable producer maps the regression volume `-8` to `R`. -/
theorem counterexample_descriptorOfOrientedVolume :
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume counterexampleFirst counterexampleSecond
          counterexampleThird counterexampleFourth) = some RS.R := by
  rw [counterexample_orientedVolume]
  exact (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_R_iff (-8)).mpr
    (by norm_num)

/-- The corrected declarative rational relation certifies `R` for the regression
configuration. -/
theorem counterexample_rationalDescriptor_R :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.R := by
  rw [rationalTetrahedralDescriptor_cons_iff]
  change CartesianPoint3.orientedVolume counterexampleFirst counterexampleSecond
      counterexampleThird counterexampleFourth < 0
  rw [counterexample_orientedVolume]
  norm_num

/-- The corrected declarative rational relation does not certify `S` for the regression
configuration. -/
theorem counterexample_rationalDescriptor_not_S :
    ¬ CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.S := by
  intro rational
  rw [rationalTetrahedralDescriptor_cons_iff] at rational
  change 0 < CartesianPoint3.orientedVolume counterexampleFirst counterexampleSecond
      counterexampleThird counterexampleFourth at rational
  rw [counterexample_orientedVolume] at rational
  norm_num at rational

/-- The list-facing executable pipeline reads the regression configuration as `R`. -/
theorem counterexample_priorityOrderedDescriptor_R :
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] = some RS.R := by
  have pointReading :
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
          [counterexampleFirst, counterexampleSecond, counterexampleThird,
            counterexampleFourth] =
        CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
          (CartesianPoint3.orientedVolume counterexampleFirst counterexampleSecond
            counterexampleThird counterexampleFourth) := rfl
  rw [pointReading]
  exact counterexample_descriptorOfOrientedVolume

/-- The source calibration reads the regression configuration as `R`. -/
theorem counterexample_sourceCalibrated_R :
    SourceCalibratedDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.R := by
  refine ⟨counterexampleFirst, counterexampleSecond, counterexampleThird,
    counterexampleFourth, rfl, ?_, ?_, ?_, ?_⟩
  · norm_num [counterexampleFirst, counterexampleSecond]
  · norm_num [counterexampleSecond, counterexampleThird]
  · norm_num [counterexampleFourth, counterexampleFirst]
  · exact Or.inl ⟨rfl, counterexample_screenTurn⟩

/-- The viewing-normalized volume-sign relation reads the regression configuration as `R`. -/
theorem counterexample_corrected_R :
    CorrectedTetrahedralDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.R := by
  refine ⟨counterexampleFirst, counterexampleSecond, counterexampleThird,
    counterexampleFourth, 1, -1, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [counterexampleFirst]
  · norm_num [counterexampleSecond]
  · norm_num [counterexampleThird]
  · norm_num [counterexampleFourth]
  · norm_num
  · exact Or.inl ⟨rfl, by rw [counterexample_orientedVolume]; norm_num⟩

/-- The general source-conformance theorem instantiates on the regression configuration. -/
theorem counterexample_generalSourceAgreement :
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume counterexampleFirst counterexampleSecond
          counterexampleThird counterexampleFourth) = some RS.R ↔
      SourceCalibratedDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.R :=
  descriptorOfOrientedVolume?_eq_some_iff_source counterexampleFirst counterexampleSecond
    counterexampleThird counterexampleFourth 1 (-1)
    (by norm_num [counterexampleFirst]) (by norm_num [counterexampleSecond])
    (by norm_num [counterexampleThird]) (by norm_num [counterexampleFourth])
    (by norm_num) RS.R

/-- **Post-repair regression.**  For the standard screen coordinates with descending priority
points `(0,1,1)`, `(1,-1,1)`, `(-1,-1,1)`, `(0,0,-1)`, the corrected executable producer
returns `R`, the corrected list-facing pipeline returns `R`, the corrected declarative
relation certifies `R` and not `S`, and the source-calibrated reading is `R`.  All components
are kernel-checked computations on exact rational coordinates. -/
theorem counterexample_regression :
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume counterexampleFirst counterexampleSecond
          counterexampleThird counterexampleFourth) = some RS.R ∧
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] = some RS.R ∧
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.R ∧
      ¬ CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.S ∧
      SourceCalibratedDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.R ∧
      CorrectedTetrahedralDescriptor
        [counterexampleFirst, counterexampleSecond, counterexampleThird,
          counterexampleFourth] RS.R :=
  ⟨counterexample_descriptorOfOrientedVolume, counterexample_priorityOrderedDescriptor_R,
    counterexample_rationalDescriptor_R, counterexample_rationalDescriptor_not_S,
    counterexample_sourceCalibrated_R, counterexample_corrected_R⟩

end CIPTetrahedralViewingCalibration
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

Each main general calibration and source-agreement theorem is checked to depend only on
kernel-authority axioms (`propext`, `Classical.choice`, `Quot.sound`); in particular no
`native_decide`/compiler trust, `sorryAx`, or project axiom may enter these proof terms. -/

assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.orientedVolume_eq_screenSeparation_mul_twiceSignedArea2D
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.orientedVolume_neg_iff_clockwise
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.sourceCalibratedDescriptor_cons_iff_of_viewing
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.sourceCalibrated_iff_corrected
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.rationalTetrahedralDescriptor_cons_iff
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.rationalTetrahedralDescriptor_iff_descriptorOfOrientedVolume
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.rationalTetrahedralDescriptor_iff_corrected_under_viewing
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.sourceCalibrated_iff_rationalDescriptor_under_viewing
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.descriptorOfOrientedVolume?_eq_some_iff_source
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.descriptorOfPriorityOrderedPoints?_eq_some_iff_source
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.descriptorOfOrientedVolume?_eq_none_iff_sourceDegenerate
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralViewingCalibration.sourceCalibrated_conforms_real_handedness
