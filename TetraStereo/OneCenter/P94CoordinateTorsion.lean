import TetraStereo.OneCenter.CIPP94ConformationCompletePipeline
import TetraStereo.OneCenter.LocalizedRule3Spatial
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

/-!
# Exact coordinate-derived P-94 torsion angles

P-94.2.1 defines the principal torsion of `X-A-B-Y` by viewing from `A` toward `B` and
projecting the two terminal arms normal to that axis.  This module performs that construction on
the exact rational coordinates already used by the molecular spatial ingress.  The resulting
angle is an exact real number: rational coordinates do not imply a rational angle.

For the directed axis `A -> B`, the scalar triple product
`(B-A) · ((X-A) x (Y-B))` is positive exactly when the front arm must make the positive
right-handed rotation to reach the rear arm.  Because the viewer looks *along* the directed axis,
that right-handed rotation appears clockwise, agreeing with P-94's positive-clockwise convention.
The source excludes terminal arms collinear with the axis; the evaluator refuses exactly those
cases rather than assigning the default argument of the zero complex number.
-/

namespace BlueBookP94.CoordinateTorsion

/-- The four exact spatial points in the source order `X-A-B-Y`. -/
structure PointFrame where
  front : CartesianPoint3
  axisFront : CartesianPoint3
  axisRear : CartesianPoint3
  rear : CartesianPoint3
  deriving DecidableEq, Repr

namespace PointFrame

def axis (frame : PointFrame) : RationalVector3 :=
  CartesianPoint3.displacement frame.axisFront frame.axisRear

def frontArm (frame : PointFrame) : RationalVector3 :=
  CartesianPoint3.displacement frame.axisFront frame.front

def rearArm (frame : PointFrame) : RationalVector3 :=
  CartesianPoint3.displacement frame.axisRear frame.rear

def frontNormal (frame : PointFrame) : RationalVector3 :=
  RationalVector3.cross frame.axis frame.frontArm

def rearNormal (frame : PointFrame) : RationalVector3 :=
  RationalVector3.cross frame.axis frame.rearArm

def axisSquared (frame : PointFrame) : ℚ :=
  RationalVector3.dot frame.axis frame.axis

def frontNormalSquared (frame : PointFrame) : ℚ :=
  RationalVector3.dot frame.frontNormal frame.frontNormal

def rearNormalSquared (frame : PointFrame) : ℚ :=
  RationalVector3.dot frame.rearNormal frame.rearNormal

/-- Cosine numerator of the projected front-to-rear turn. -/
def cosineNumerator (frame : PointFrame) : ℚ :=
  RationalVector3.dot frame.frontNormal frame.rearNormal

/-- Oriented sine numerator.  Positive is clockwise to a viewer looking `A -> B`. -/
def sineNumerator (frame : PointFrame) : ℚ :=
  RationalVector3.dot frame.axis
    (RationalVector3.cross frame.frontArm frame.rearArm)

/-- Exact P-94 applicability for a coordinate frame: the axis has direction and neither terminal
arm is collinear with it.  Strict squared-norm positivity is convenient over rational points and
is mathematically equivalent to the three corresponding vectors being nonzero. -/
def Noncollinear (frame : PointFrame) : Prop :=
  0 < frame.axisSquared ∧
    0 < frame.frontNormalSquared ∧
    0 < frame.rearNormalSquared

/-- The unnormalized complex direction of the projected turn.  Multiplying the triple product by
the exact axis length puts its magnitude on the same scale as the cosine numerator. -/
noncomputable def angleComplex (frame : PointFrame) : ℂ :=
  { re := (frame.cosineNumerator : ℝ)
    im := Real.sqrt (frame.axisSquared : ℝ) * (frame.sineNumerator : ℝ) }

/-- Principal signed P-94 angle in degrees, before packaging its proved range. -/
noncomputable def principalDegrees (frame : PointFrame) : ℝ :=
  Complex.arg frame.angleComplex * 180 / Real.pi

end PointFrame

/-- The three-dimensional Gram identity behind the coordinate construction.  In particular, two
nonzero projected arms cannot simultaneously have zero cosine and sine numerators. -/
theorem torsionNumerator_norm_identity (frame : PointFrame) :
    frame.cosineNumerator ^ 2 + frame.axisSquared * frame.sineNumerator ^ 2 =
      frame.frontNormalSquared * frame.rearNormalSquared := by
  simp [PointFrame.cosineNumerator, PointFrame.axisSquared,
    PointFrame.sineNumerator, PointFrame.frontNormalSquared,
    PointFrame.rearNormalSquared, PointFrame.frontNormal, PointFrame.rearNormal,
    PointFrame.axis, PointFrame.frontArm, PointFrame.rearArm,
    CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross]
  ring

/-- P-94 noncollinearity makes the complex projected direction nonzero. -/
theorem noncollinear_angleComplex_ne_zero (frame : PointFrame)
    (noncollinear : frame.Noncollinear) :
    frame.angleComplex ≠ 0 := by
  intro zero
  have realZero : (frame.cosineNumerator : ℝ) = 0 := by
    simpa [PointFrame.angleComplex] using congrArg Complex.re zero
  have imaginaryZero :
      Real.sqrt (frame.axisSquared : ℝ) * (frame.sineNumerator : ℝ) = 0 := by
    simpa [PointFrame.angleComplex] using congrArg Complex.im zero
  have axisPositive : (0 : ℝ) < (frame.axisSquared : ℝ) := by
    exact_mod_cast noncollinear.1
  have sqrtPositive : 0 < Real.sqrt (frame.axisSquared : ℝ) :=
    Real.sqrt_pos.2 axisPositive
  have sineCastZero : (frame.sineNumerator : ℝ) = 0 :=
    (mul_eq_zero.mp imaginaryZero).resolve_left sqrtPositive.ne'
  have cosineZero : frame.cosineNumerator = 0 := by
    exact_mod_cast realZero
  have sineZero : frame.sineNumerator = 0 := by
    exact_mod_cast sineCastZero
  have identity := torsionNumerator_norm_identity frame
  rw [cosineZero, sineZero] at identity
  norm_num at identity
  rcases identity with frontZero | rearZero
  · exact (ne_of_gt noncollinear.2.1) frontZero
  · exact (ne_of_gt noncollinear.2.2) rearZero

theorem principalDegrees_lowerBound (frame : PointFrame) :
    (-180 : ℝ) ≤ frame.principalDegrees := by
  rw [PointFrame.principalDegrees, le_div_iff₀ Real.pi_pos]
  have argumentLower := (Complex.neg_pi_lt_arg frame.angleComplex).le
  nlinarith [Real.pi_pos]

theorem principalDegrees_upperBound (frame : PointFrame) :
    frame.principalDegrees ≤ (180 : ℝ) := by
  rw [PointFrame.principalDegrees, div_le_iff₀ Real.pi_pos]
  have argumentUpper := Complex.arg_le_pi frame.angleComplex
  nlinarith [Real.pi_pos]

/-- The exact bounded torsion value associated with a point frame.  It is exposed only after the
P-94 noncollinearity gate below. -/
noncomputable def principalAngle (frame : PointFrame) : TorsionAngle :=
  TorsionAngle.ofReal frame.principalDegrees
    (principalDegrees_lowerBound frame) (principalDegrees_upperBound frame)

@[simp] theorem principalAngle_degrees (frame : PointFrame) :
    (principalAngle frame).degrees = frame.principalDegrees :=
  rfl

/-- Independent coordinate meaning of one exact torsion angle. -/
def ExactTorsionAngle (frame : PointFrame) (angle : TorsionAngle) : Prop :=
  frame.Noncollinear ∧ angle.degrees = frame.principalDegrees

/-- Exact coordinate evaluator.  Its noncomputability is honest: comparison and argument of exact
real numbers are specification-level operations, not floating-point approximations. -/
noncomputable def torsionAngleOfPoints? (frame : PointFrame) : Option TorsionAngle :=
  by
    classical
    exact if noncollinear : frame.Noncollinear then some (principalAngle frame) else none

theorem torsionAngleOfPoints?_eq_some_iff (frame : PointFrame) (angle : TorsionAngle) :
    torsionAngleOfPoints? frame = some angle ↔ ExactTorsionAngle frame angle := by
  classical
  by_cases noncollinear : frame.Noncollinear
  · constructor
    · intro computed
      have equal : principalAngle frame = angle := by
        simpa [torsionAngleOfPoints?, noncollinear] using computed
      subst angle
      exact ⟨noncollinear, rfl⟩
    · rintro ⟨_, degrees⟩
      have equal : principalAngle frame = angle := by
        apply TorsionAngle.ext
        simpa using degrees.symm
      simp [torsionAngleOfPoints?, noncollinear, equal]
  · simp [torsionAngleOfPoints?, ExactTorsionAngle, noncollinear]

theorem torsionAngleOfPoints?_eq_none_iff (frame : PointFrame) :
    torsionAngleOfPoints? frame = none ↔ ¬frame.Noncollinear := by
  classical
  by_cases noncollinear : frame.Noncollinear <;>
    simp [torsionAngleOfPoints?, noncollinear]

/-! ## Literal sign-convention witnesses -/

def positiveQuarterTurnFrame : PointFrame :=
  { front := { x := 0, y := 1, z := 0 }
    axisFront := { x := 0, y := 0, z := 0 }
    axisRear := { x := 1, y := 0, z := 0 }
    rear := { x := 1, y := 0, z := 1 } }

def negativeQuarterTurnFrame : PointFrame :=
  { front := { x := 0, y := 1, z := 0 }
    axisFront := { x := 0, y := 0, z := 0 }
    axisRear := { x := 1, y := 0, z := 0 }
    rear := { x := 1, y := 0, z := -1 } }

private theorem positiveQuarterTurn_noncollinear :
    positiveQuarterTurnFrame.Noncollinear := by
  norm_num [PointFrame.Noncollinear, PointFrame.axisSquared,
    PointFrame.frontNormalSquared, PointFrame.rearNormalSquared,
    PointFrame.frontNormal, PointFrame.rearNormal, PointFrame.axis,
    PointFrame.frontArm, PointFrame.rearArm, CartesianPoint3.displacement,
    RationalVector3.dot, RationalVector3.cross, positiveQuarterTurnFrame]

private theorem negativeQuarterTurn_noncollinear :
    negativeQuarterTurnFrame.Noncollinear := by
  norm_num [PointFrame.Noncollinear, PointFrame.axisSquared,
    PointFrame.frontNormalSquared, PointFrame.rearNormalSquared,
    PointFrame.frontNormal, PointFrame.rearNormal, PointFrame.axis,
    PointFrame.frontArm, PointFrame.rearArm, CartesianPoint3.displacement,
    RationalVector3.dot, RationalVector3.cross, negativeQuarterTurnFrame]

private theorem positiveQuarterTurn_principalDegrees :
    positiveQuarterTurnFrame.principalDegrees = 90 := by
  have complexValue : positiveQuarterTurnFrame.angleComplex = Complex.I := by
    apply Complex.ext <;>
      norm_num [PointFrame.angleComplex, PointFrame.cosineNumerator,
        PointFrame.sineNumerator, PointFrame.axisSquared, PointFrame.frontNormal,
        PointFrame.rearNormal, PointFrame.axis, PointFrame.frontArm,
        PointFrame.rearArm, CartesianPoint3.displacement, RationalVector3.dot,
        RationalVector3.cross, positiveQuarterTurnFrame]
  rw [PointFrame.principalDegrees]
  rw [complexValue]
  rw [Complex.arg_I]
  field_simp [Real.pi_ne_zero]
  ring

private theorem negativeQuarterTurn_principalDegrees :
    negativeQuarterTurnFrame.principalDegrees = -90 := by
  have complexValue : negativeQuarterTurnFrame.angleComplex = -Complex.I := by
    apply Complex.ext <;>
      norm_num [PointFrame.angleComplex, PointFrame.cosineNumerator,
        PointFrame.sineNumerator, PointFrame.axisSquared, PointFrame.frontNormal,
        PointFrame.rearNormal, PointFrame.axis, PointFrame.frontArm,
        PointFrame.rearArm, CartesianPoint3.displacement, RationalVector3.dot,
        RationalVector3.cross, negativeQuarterTurnFrame]
  rw [PointFrame.principalDegrees]
  rw [complexValue]
  rw [Complex.arg_neg_I]
  field_simp [Real.pi_ne_zero]
  ring

/-- A positive right-handed quarter turn is literally the P-94 positive-clockwise `+90°`. -/
theorem positiveQuarterTurn_degrees :
    ∃ angle,
      torsionAngleOfPoints? positiveQuarterTurnFrame = some angle ∧
      angle.degrees = 90 ∧ SignAgreesWithRotation angle .clockwise := by
  classical
  refine ⟨principalAngle positiveQuarterTurnFrame, ?_, ?_, ?_⟩
  · simp [torsionAngleOfPoints?, positiveQuarterTurn_noncollinear]
  · exact positiveQuarterTurn_principalDegrees
  · simp [SignAgreesWithRotation, positiveQuarterTurn_principalDegrees]

/-- The mirror quarter turn is literally the P-94 negative-anticlockwise `-90°`. -/
theorem negativeQuarterTurn_degrees :
    ∃ angle,
      torsionAngleOfPoints? negativeQuarterTurnFrame = some angle ∧
      angle.degrees = -90 ∧ SignAgreesWithRotation angle .anticlockwise := by
  classical
  refine ⟨principalAngle negativeQuarterTurnFrame, ?_, ?_, ?_⟩
  · simp [torsionAngleOfPoints?, negativeQuarterTurn_noncollinear]
  · exact negativeQuarterTurn_principalDegrees
  · simp [SignAgreesWithRotation, negativeQuarterTurn_principalDegrees]

/-! ## Exact spatial-configuration ingress -/

/-- Independent molecule-indexed coordinate meaning of a physical `X-A-B-Y` torsion. -/
def SpatialTorsionAngleJudgment (spatial : SpatialConfiguration)
    (front axisFront axisRear rear : ℕ) (angle : TorsionAngle) : Prop :=
  ∃ frontPoint axisFrontPoint axisRearPoint rearPoint,
    spatial.positions[front]? = some frontPoint ∧
    spatial.positions[axisFront]? = some axisFrontPoint ∧
    spatial.positions[axisRear]? = some axisRearPoint ∧
    spatial.positions[rear]? = some rearPoint ∧
    ExactTorsionAngle
      { front := frontPoint
        axisFront := axisFrontPoint
        axisRear := axisRearPoint
        rear := rearPoint }
      angle

/-- Look up the four physical atoms and derive their exact P-94 torsion. -/
noncomputable def spatialTorsionAngle? (spatial : SpatialConfiguration)
    (front axisFront axisRear rear : ℕ) : Option TorsionAngle := do
  let frontPoint ← spatial.positions[front]?
  let axisFrontPoint ← spatial.positions[axisFront]?
  let axisRearPoint ← spatial.positions[axisRear]?
  let rearPoint ← spatial.positions[rear]?
  torsionAngleOfPoints?
    { front := frontPoint
      axisFront := axisFrontPoint
      axisRear := axisRearPoint
      rear := rearPoint }

theorem spatialTorsionAngle?_eq_some_iff (spatial : SpatialConfiguration)
    (front axisFront axisRear rear : ℕ) (angle : TorsionAngle) :
    spatialTorsionAngle? spatial front axisFront axisRear rear = some angle ↔
      SpatialTorsionAngleJudgment spatial front axisFront axisRear rear angle := by
  constructor
  · intro computed
    cases frontPointEq : spatial.positions[front]? with
    | none => simp [spatialTorsionAngle?, frontPointEq] at computed
    | some frontPoint =>
        cases axisFrontPointEq : spatial.positions[axisFront]? with
        | none => simp [spatialTorsionAngle?, frontPointEq, axisFrontPointEq] at computed
        | some axisFrontPoint =>
            cases axisRearPointEq : spatial.positions[axisRear]? with
            | none =>
                simp [spatialTorsionAngle?, frontPointEq, axisFrontPointEq,
                  axisRearPointEq] at computed
            | some axisRearPoint =>
                cases rearPointEq : spatial.positions[rear]? with
                | none =>
                    simp [spatialTorsionAngle?, frontPointEq, axisFrontPointEq,
                      axisRearPointEq, rearPointEq] at computed
                | some rearPoint =>
                    refine ⟨frontPoint, axisFrontPoint, axisRearPoint, rearPoint,
                      frontPointEq, axisFrontPointEq, axisRearPointEq, rearPointEq, ?_⟩
                    exact (torsionAngleOfPoints?_eq_some_iff _ _).mp (by
                      simpa [spatialTorsionAngle?, frontPointEq, axisFrontPointEq,
                        axisRearPointEq, rearPointEq] using computed)
  · rintro ⟨frontPoint, axisFrontPoint, axisRearPoint, rearPoint,
      frontPointEq, axisFrontPointEq, axisRearPointEq, rearPointEq, judgment⟩
    unfold spatialTorsionAngle?
    rw [frontPointEq, axisFrontPointEq, axisRearPointEq, rearPointEq]
    exact (torsionAngleOfPoints?_eq_some_iff _ _).mpr judgment

/-- Exhaustive coordinate-ingress refusal: failure means exactly that no independently justified
angle exists, covering every missing coordinate and either P-94 collinearity failure. -/
theorem spatialTorsionAngle?_eq_none_iff (spatial : SpatialConfiguration)
    (front axisFront axisRear rear : ℕ) :
    spatialTorsionAngle? spatial front axisFront axisRear rear = none ↔
      ¬∃ angle, SpatialTorsionAngleJudgment spatial front axisFront axisRear rear angle := by
  constructor
  · intro computed ⟨angle, judgment⟩
    have some := (spatialTorsionAngle?_eq_some_iff
      spatial front axisFront axisRear rear angle).mpr judgment
    rw [computed] at some
    simp at some
  · intro absent
    cases computed : spatialTorsionAngle? spatial front axisFront axisRear rear with
    | none => rfl
    | some angle =>
        exfalso
        exact absent ⟨angle,
          (spatialTorsionAngle?_eq_some_iff
            spatial front axisFront axisRear rear angle).mp computed⟩

end BlueBookP94.CoordinateTorsion

end TetraStereo.OneCenter
