import TetraStereo.OneCenter.CIPObservedDerivedHelicalSpatialCompleteness
import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialDescriptor
import TetraStereo.OneCenter.P94CoordinateTorsion
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Source viewing calibration for exact helical `P/M`

This module fixes and audits the sign convention used by the coordinate-derived helical route.
It is a calibration/verification module only: the production evaluator is
`helicalDescriptorOfSpatialReferences?` in `CIPObservedHelicalSpatialConformance`, and the
public producer is `ChemistryNormalizationResult.coordinateDerivedHelicalAssignment?` in
`CIPObservedDerivedHelicalSpatialCompleteness`.

## The calibrated statement

P-92.1.2.2.1 says: looking along the chirality axis, proceeding from the nearer priority ligand
to the farther priority ligand, the helix is `M` when the turn is anticlockwise and `P` when it is
clockwise.  For an identified helix with an ordered path and one senior terminal reference at each
end, take the directed axis from the near path endpoint to the far path endpoint.  The scalar
triple product

`axis · (frontArm × backArm)`

is positive exactly for the clockwise near-to-far turn and negative exactly for the anticlockwise
turn.  Therefore:

* positive measure  => source clockwise  => `P`;
* negative measure  => source anticlockwise => `M`;
* zero measure is refused because it supplies no handed turn.

The canonical check is axis `+z`, near reference `+x`, far reference `+y`: the triple product is
`+1`, and the turn viewed from the near toward the far endpoint is clockwise, hence source `P`.
This module proves that witness below.

## Consistency with existing primitives

* `CartesianPoint3.helicalReferenceMeasure` is literally the P-94 `sineNumerator` of the frame
  `front := nearReference`, `axisFront := nearEndpoint`, `axisRear := farEndpoint`,
  `rear := farReference`, and is literally the existing axial `axialChiralityMeasure`.
* The existing axial primitive is not edited.  Its sign convention remains negative => `Ra`,
  positive => `Sa`.  Under aligned references, the source-facing bridge is `Sa` => `P` and
  `Ra` => `M`, uniformly recovering `positive => Sa => P`.
* Consequently a positive helical measure has a positive P-94 `principalDegrees` under the
  P-94 noncollinearity hypotheses.

## Applicability boundary

The calibrated judgment is a **terminal-reference** judgment.  It depends only on the two path
endpoints, the two terminal references, and their exact coordinates; this is proved as
`rationalHelicalObservationJudgment_of_endpoints_eq`.  The endpoint turn alone is *not* universal
whole-path handedness.  Whole-path winding enters only through the separate
`P93AuthorityCoherentHelicalWinding` hypothesis carried by
`P93AuthorityHelixFrame.ValidFor`, which additionally requires an identified helix of at least
four atoms.  The calibration theorem extracts that hypothesis rather than deriving it from the
terminal turn.
-/

/-! ## Identity with the P-94 and axial numerators -/

/-- The helical terminal-reference measure is exactly the P-94 oriented sine numerator of the
induced torsion frame.  This is a definitional identity, not a new sign convention. -/
theorem CartesianPoint3.helicalReferenceMeasure_eq_p94SineNumerator
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    CartesianPoint3.helicalReferenceMeasure nearEndpoint farEndpoint nearReference farReference =
      BlueBookP94.CoordinateTorsion.PointFrame.sineNumerator
        { front := nearReference
          axisFront := nearEndpoint
          axisRear := farEndpoint
          rear := farReference } := rfl

/-- The helical terminal-reference measure is exactly the existing axial chirality numerator.
The axial module keeps its own calibration; this is only an arithmetic identification. -/
theorem CartesianPoint3.helicalReferenceMeasure_eq_axialChiralityMeasure
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    CartesianPoint3.helicalReferenceMeasure nearEndpoint farEndpoint nearReference farReference =
      CartesianPoint3.axialChiralityMeasure nearEndpoint farEndpoint nearReference farReference := rfl

/-- The P-94 torsion frame induced by a near-to-far helix endpoint and terminal-reference
quadruple. -/
def terminalReferencePointFrame
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    BlueBookP94.CoordinateTorsion.PointFrame :=
  { front := nearReference
    axisFront := nearEndpoint
    axisRear := farEndpoint
    rear := farReference }

@[simp] theorem terminalReferencePointFrame_sineNumerator
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    (terminalReferencePointFrame nearEndpoint farEndpoint nearReference farReference).sineNumerator =
      CartesianPoint3.helicalReferenceMeasure
        nearEndpoint farEndpoint nearReference farReference := rfl

/-! ## P-94 principal-angle sign transfer -/

namespace BlueBookP94.CoordinateTorsion

namespace PointFrame

/-- A positive P-94 sine numerator, under P-94 noncollinearity, gives a positive principal
torsion angle.  The proof only uses that `principalDegrees` is the principal argument scaled by
the positive factor `180 / π`. -/
theorem principalDegrees_pos_of_sineNumerator_pos
    (frame : PointFrame) (noncollinear : frame.Noncollinear)
    (positive : 0 < frame.sineNumerator) :
    0 < frame.principalDegrees := by
  have axisPositive : (0 : ℝ) < (frame.axisSquared : ℝ) := by
    exact_mod_cast noncollinear.1
  have sqrtPositive : 0 < Real.sqrt (frame.axisSquared : ℝ) :=
    Real.sqrt_pos.2 axisPositive
  have sinePositive : (0 : ℝ) < (frame.sineNumerator : ℝ) := by
    exact_mod_cast positive
  have imaginaryPositive : 0 < frame.angleComplex.im := by
    show 0 < Real.sqrt (frame.axisSquared : ℝ) * (frame.sineNumerator : ℝ)
    exact mul_pos sqrtPositive sinePositive
  have argumentNonnegative : 0 ≤ frame.angleComplex.arg :=
    Complex.arg_nonneg_iff.mpr imaginaryPositive.le
  have argumentNeZero : frame.angleComplex.arg ≠ 0 := by
    intro zero
    have imaginaryZero : frame.angleComplex.im = 0 :=
      (Complex.arg_eq_zero_iff.mp zero).2
    linarith
  have argumentPositive : 0 < frame.angleComplex.arg :=
    lt_of_le_of_ne argumentNonnegative (Ne.symm argumentNeZero)
  have degreeScale : (0 : ℝ) < 180 / Real.pi :=
    div_pos (by norm_num) Real.pi_pos
  have principalEq : frame.principalDegrees =
      frame.angleComplex.arg * (180 / Real.pi) := by
    unfold principalDegrees
    rw [mul_div_assoc]
  rw [principalEq]
  exact mul_pos argumentPositive degreeScale

/-- A negative P-94 sine numerator gives a negative principal torsion angle. -/
theorem principalDegrees_neg_of_sineNumerator_neg
    (frame : PointFrame) (noncollinear : frame.Noncollinear)
    (negative : frame.sineNumerator < 0) :
    frame.principalDegrees < 0 := by
  have axisPositive : (0 : ℝ) < (frame.axisSquared : ℝ) := by
    exact_mod_cast noncollinear.1
  have sqrtPositive : 0 < Real.sqrt (frame.axisSquared : ℝ) :=
    Real.sqrt_pos.2 axisPositive
  have sineNegative : (frame.sineNumerator : ℝ) < 0 := by
    exact_mod_cast negative
  have imaginaryNegative : frame.angleComplex.im < 0 := by
    show Real.sqrt (frame.axisSquared : ℝ) * (frame.sineNumerator : ℝ) < 0
    exact mul_neg_of_pos_of_neg sqrtPositive sineNegative
  have argumentNegative : frame.angleComplex.arg < 0 :=
    Complex.arg_neg_iff.mpr imaginaryNegative
  have degreeScale : (0 : ℝ) < 180 / Real.pi :=
    div_pos (by norm_num) Real.pi_pos
  have principalEq : frame.principalDegrees =
      frame.angleComplex.arg * (180 / Real.pi) := by
    unfold principalDegrees
    rw [mul_div_assoc]
  rw [principalEq]
  exact mul_neg_of_neg_of_pos argumentNegative degreeScale

end PointFrame

end BlueBookP94.CoordinateTorsion

/-- Positive helical terminal-reference measure transfers to the positive P-94 principal
angle. -/
theorem terminalReferencePointFrame_principalDegrees_pos_of_helicalMeasure_pos
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3)
    (noncollinear :
      (terminalReferencePointFrame nearEndpoint farEndpoint nearReference farReference).Noncollinear)
    (positive : 0 < CartesianPoint3.helicalReferenceMeasure
      nearEndpoint farEndpoint nearReference farReference) :
    0 < (terminalReferencePointFrame nearEndpoint farEndpoint nearReference farReference).principalDegrees := by
  apply BlueBookP94.CoordinateTorsion.PointFrame.principalDegrees_pos_of_sineNumerator_pos
  · exact noncollinear
  · exact positive

/-- Negative helical terminal-reference measure transfers to the negative P-94 principal
angle. -/
theorem terminalReferencePointFrame_principalDegrees_neg_of_helicalMeasure_neg
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3)
    (noncollinear :
      (terminalReferencePointFrame nearEndpoint farEndpoint nearReference farReference).Noncollinear)
    (negative : CartesianPoint3.helicalReferenceMeasure
      nearEndpoint farEndpoint nearReference farReference < 0) :
    (terminalReferencePointFrame nearEndpoint farEndpoint nearReference farReference).principalDegrees < 0 := by
  apply BlueBookP94.CoordinateTorsion.PointFrame.principalDegrees_neg_of_sineNumerator_neg
  · exact noncollinear
  · exact negative

/-- The P-94 sign transfer, stated directly for the calibrated `P/M` descriptor. -/
theorem terminalReferencePointFrame_principalDegrees_sign_of_helicalDescriptor
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3)
    (noncollinear :
      (terminalReferencePointFrame nearEndpoint farEndpoint nearReference farReference).Noncollinear)
    (descriptor : HelicalDescriptor)
    (judged : BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor
      nearEndpoint farEndpoint nearReference farReference descriptor) :
    (descriptor = .P →
        0 < (terminalReferencePointFrame
          nearEndpoint farEndpoint nearReference farReference).principalDegrees) ∧
      (descriptor = .M →
        (terminalReferencePointFrame
          nearEndpoint farEndpoint nearReference farReference).principalDegrees < 0) := by
  constructor
  · intro isP
    rw [isP] at judged
    exact terminalReferencePointFrame_principalDegrees_pos_of_helicalMeasure_pos
      nearEndpoint farEndpoint nearReference farReference noncollinear
      (by simpa [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor] using judged)
  · intro isM
    rw [isM] at judged
    exact terminalReferencePointFrame_principalDegrees_neg_of_helicalMeasure_neg
      nearEndpoint farEndpoint nearReference farReference noncollinear
      (by simpa [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor] using judged)

/-! ## Source screw handedness -/

/-- The P-92.1.2.2.1 source turn sense when looking from the nearer priority reference toward
the farther priority reference. -/
inductive SourceScrewSense where
  | clockwise
  | anticlockwise
  deriving DecidableEq, Repr

namespace SourceScrewSense

/-- `P` is the plus / clockwise sense; `M` is the minus / anticlockwise sense. -/
def toHelicalDescriptor : SourceScrewSense → HelicalDescriptor
  | .clockwise => .P
  | .anticlockwise => .M

def ofHelicalDescriptor : HelicalDescriptor → SourceScrewSense
  | .P => .clockwise
  | .M => .anticlockwise

@[simp] theorem toHelicalDescriptor_clockwise :
    toHelicalDescriptor .clockwise = .P := rfl

@[simp] theorem toHelicalDescriptor_anticlockwise :
    toHelicalDescriptor .anticlockwise = .M := rfl

@[simp] theorem ofHelicalDescriptor_P : ofHelicalDescriptor .P = .clockwise := rfl

@[simp] theorem ofHelicalDescriptor_M : ofHelicalDescriptor .M = .anticlockwise := rfl

theorem ofHelicalDescriptor_toHelicalDescriptor (sense : SourceScrewSense) :
    ofHelicalDescriptor (toHelicalDescriptor sense) = sense := by
  cases sense <;> rfl

theorem toHelicalDescriptor_ofHelicalDescriptor (descriptor : HelicalDescriptor) :
    toHelicalDescriptor (ofHelicalDescriptor descriptor) = descriptor := by
  cases descriptor <;> rfl

end SourceScrewSense

namespace CartesianPoint3

/-- Exact source turn sense for a near-to-far endpoint/reference quadruple.  A positive
near-to-far triple product is clockwise; a negative one is anticlockwise; zero is refused. -/
def sourceScrewSense?
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    Option SourceScrewSense :=
  let measure := helicalReferenceMeasure nearEndpoint farEndpoint nearReference farReference
  if 0 < measure then some .clockwise
  else if measure < 0 then some .anticlockwise
  else none

theorem sourceScrewSense?_eq_some_clockwise_iff
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    sourceScrewSense? nearEndpoint farEndpoint nearReference farReference = some .clockwise ↔
      0 < helicalReferenceMeasure nearEndpoint farEndpoint nearReference farReference := by
  unfold sourceScrewSense?
  by_cases positive : 0 < CartesianPoint3.helicalReferenceMeasure
      nearEndpoint farEndpoint nearReference farReference
  · simp [positive]
  · by_cases negative : CartesianPoint3.helicalReferenceMeasure
        nearEndpoint farEndpoint nearReference farReference < 0
    · simp [positive, negative]
    · simp [positive, negative]

theorem sourceScrewSense?_eq_some_anticlockwise_iff
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    sourceScrewSense? nearEndpoint farEndpoint nearReference farReference = some .anticlockwise ↔
      helicalReferenceMeasure nearEndpoint farEndpoint nearReference farReference < 0 := by
  unfold sourceScrewSense?
  by_cases positive : 0 < CartesianPoint3.helicalReferenceMeasure
      nearEndpoint farEndpoint nearReference farReference
  · have notNegative : ¬ CartesianPoint3.helicalReferenceMeasure
        nearEndpoint farEndpoint nearReference farReference < 0 :=
      not_lt_of_ge positive.le
    simp [positive, notNegative]
  · by_cases negative : CartesianPoint3.helicalReferenceMeasure
        nearEndpoint farEndpoint nearReference farReference < 0
    · simp [positive, negative]
    · simp [positive, negative]

/-- The source screw sense is exactly the helical `P/M` descriptor under the calibrated map. -/
theorem sourceScrewSense?_eq_some_iff
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3)
    (sense : SourceScrewSense) :
    sourceScrewSense? nearEndpoint farEndpoint nearReference farReference = some sense ↔
      helicalDescriptorOfSpatialReferences? nearEndpoint farEndpoint nearReference farReference =
        some sense.toHelicalDescriptor := by
  cases sense with
  | clockwise =>
      rw [show SourceScrewSense.toHelicalDescriptor .clockwise = .P from rfl]
      exact ⟨fun computed =>
          (helicalDescriptorOfSpatialReferences?_eq_some_P_iff
            nearEndpoint farEndpoint nearReference farReference).mpr
            ((sourceScrewSense?_eq_some_clockwise_iff
              nearEndpoint farEndpoint nearReference farReference).mp computed),
        fun computed =>
          (sourceScrewSense?_eq_some_clockwise_iff
            nearEndpoint farEndpoint nearReference farReference).mpr
            ((helicalDescriptorOfSpatialReferences?_eq_some_P_iff
              nearEndpoint farEndpoint nearReference farReference).mp computed)⟩
  | anticlockwise =>
      rw [show SourceScrewSense.toHelicalDescriptor .anticlockwise = .M from rfl]
      exact ⟨fun computed =>
          (helicalDescriptorOfSpatialReferences?_eq_some_M_iff
            nearEndpoint farEndpoint nearReference farReference).mpr
            ((sourceScrewSense?_eq_some_anticlockwise_iff
              nearEndpoint farEndpoint nearReference farReference).mp computed),
        fun computed =>
          (sourceScrewSense?_eq_some_anticlockwise_iff
            nearEndpoint farEndpoint nearReference farReference).mpr
            ((helicalDescriptorOfSpatialReferences?_eq_some_M_iff
              nearEndpoint farEndpoint nearReference farReference).mp computed)⟩

/-- The corrected helical evaluator is exactly the source screw sense mapped into `P/M`. -/
theorem helicalDescriptorOfSpatialReferences?_eq_sourceScrewSense_map
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences? nearEndpoint farEndpoint nearReference farReference =
      (sourceScrewSense? nearEndpoint farEndpoint nearReference farReference).map
        SourceScrewSense.toHelicalDescriptor := by
  apply Option.ext
  intro descriptor
  rw [helicalDescriptorOfSpatialReferences?_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · intro judged
    cases descriptor with
    | P =>
        refine ⟨.clockwise,
          (sourceScrewSense?_eq_some_clockwise_iff
            nearEndpoint farEndpoint nearReference farReference).mpr ?_, rfl⟩
        simpa [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor] using judged
    | M =>
        refine ⟨.anticlockwise,
          (sourceScrewSense?_eq_some_anticlockwise_iff
            nearEndpoint farEndpoint nearReference farReference).mpr ?_, rfl⟩
        simpa [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor] using judged
  · rintro ⟨sense, senseSome, mapped⟩
    cases sense with
    | clockwise =>
        have descriptorEq : descriptor = .P := by
          simpa [SourceScrewSense.toHelicalDescriptor] using mapped.symm
        rw [descriptorEq]
        simpa [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor] using
          (sourceScrewSense?_eq_some_clockwise_iff
            nearEndpoint farEndpoint nearReference farReference).mp senseSome
    | anticlockwise =>
        have descriptorEq : descriptor = .M := by
          simpa [SourceScrewSense.toHelicalDescriptor] using mapped.symm
        rw [descriptorEq]
        simpa [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor] using
          (sourceScrewSense?_eq_some_anticlockwise_iff
            nearEndpoint farEndpoint nearReference farReference).mp senseSome

/-! ## Canonical near-to-far right-handed witness -/

/-- Axis `+z`, near reference `+x`, far reference `+y`: the canonical source `P` turn. -/
def canonicalNearEndpoint : CartesianPoint3 := { x := 0, y := 0, z := 0 }
def canonicalFarEndpoint : CartesianPoint3 := { x := 0, y := 0, z := 1 }
def canonicalNearReference : CartesianPoint3 := { x := 1, y := 0, z := 0 }
def canonicalFarReference : CartesianPoint3 := { x := 0, y := 1, z := 1 }

theorem canonicalRightHandedHelix_measure :
    helicalReferenceMeasure canonicalNearEndpoint canonicalFarEndpoint
      canonicalNearReference canonicalFarReference = 1 := by
  norm_num [canonicalNearEndpoint, canonicalFarEndpoint, canonicalNearReference,
    canonicalFarReference, helicalReferenceMeasure, displacement,
    RationalVector3.dot, RationalVector3.cross]

theorem canonicalRightHandedHelix_sourceScrewSense :
    sourceScrewSense? canonicalNearEndpoint canonicalFarEndpoint
      canonicalNearReference canonicalFarReference = some .clockwise := by
  rw [sourceScrewSense?_eq_some_clockwise_iff, canonicalRightHandedHelix_measure]
  norm_num

theorem canonicalRightHandedHelix_descriptor :
    helicalDescriptorOfSpatialReferences? canonicalNearEndpoint canonicalFarEndpoint
      canonicalNearReference canonicalFarReference = some .P := by
  rw [helicalDescriptorOfSpatialReferences?_eq_some_P_iff,
    canonicalRightHandedHelix_measure]
  norm_num

/-- The canonical positive-measure witness is source-clockwise and helically `P`, confirming
that the corrected mapping is positive (not negative) => `P`. -/
theorem canonicalRightHandedHelix_source_screw_P :
    helicalReferenceMeasure canonicalNearEndpoint canonicalFarEndpoint
        canonicalNearReference canonicalFarReference = 1 ∧
      sourceScrewSense? canonicalNearEndpoint canonicalFarEndpoint
          canonicalNearReference canonicalFarReference = some .clockwise ∧
      helicalDescriptorOfSpatialReferences? canonicalNearEndpoint canonicalFarEndpoint
          canonicalNearReference canonicalFarReference = some .P :=
  ⟨canonicalRightHandedHelix_measure, canonicalRightHandedHelix_sourceScrewSense,
    canonicalRightHandedHelix_descriptor⟩

end CartesianPoint3

/-! ## Bridge to the existing axial primitive -/

namespace AxialDescriptor

/-- Source-facing map from the existing axial `Rₐ/Sₐ` primitive to helical `M/P`.  Aligned
references give axial `Sₐ` (positive measure) => helical `P`, and axial `Rₐ` (negative measure)
=> helical `M`.  The axial module itself is unchanged. -/
def toHelicalDescriptor : AxialDescriptor → HelicalDescriptor
  | .Ra => .M
  | .Sa => .P

@[simp] theorem toHelicalDescriptor_Ra : toHelicalDescriptor .Ra = .M := rfl

@[simp] theorem toHelicalDescriptor_Sa : toHelicalDescriptor .Sa = .P := rfl

end AxialDescriptor

/-- Pointwise axial bridge for `P`: the corrected helical evaluator returns `P` exactly when the
existing axial primitive returns `Sₐ` on the same aligned references. -/
theorem helicalDescriptorOfSpatialReferences?_eq_some_P_iff_axialDescriptor_Sa
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences? nearEndpoint farEndpoint nearReference farReference =
        some .P ↔
      axialDescriptorOfSpatialReferences? nearEndpoint farEndpoint nearReference farReference =
        some .Sa := by
  rw [helicalDescriptorOfSpatialReferences?_eq_some_P_iff,
    axialDescriptorOfSpatialReferences?_eq_some_iff]
  simp [RationalAxialSpatialDescriptor,
    CartesianPoint3.helicalReferenceMeasure_eq_axialChiralityMeasure]

/-- Pointwise axial bridge for `M`: the corrected helical evaluator returns `M` exactly when the
existing axial primitive returns `Rₐ` on the same aligned references. -/
theorem helicalDescriptorOfSpatialReferences?_eq_some_M_iff_axialDescriptor_Ra
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences? nearEndpoint farEndpoint nearReference farReference =
        some .M ↔
      axialDescriptorOfSpatialReferences? nearEndpoint farEndpoint nearReference farReference =
        some .Ra := by
  rw [helicalDescriptorOfSpatialReferences?_eq_some_M_iff,
    axialDescriptorOfSpatialReferences?_eq_some_iff]
  simp [RationalAxialSpatialDescriptor,
    CartesianPoint3.helicalReferenceMeasure_eq_axialChiralityMeasure]

/-- Whole-option form of the axial bridge: the corrected helical evaluator is the existing axial
evaluator composed with `Rₐ ↦ M`, `Sₐ ↦ P`. -/
theorem helicalDescriptorOfSpatialReferences?_eq_axialDescriptor_map
    (nearEndpoint farEndpoint nearReference farReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences? nearEndpoint farEndpoint nearReference farReference =
      (axialDescriptorOfSpatialReferences? nearEndpoint farEndpoint nearReference farReference).map
        AxialDescriptor.toHelicalDescriptor := by
  apply Option.ext
  intro descriptor
  rw [helicalDescriptorOfSpatialReferences?_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · intro judged
    cases descriptor with
    | P =>
        have helicalSome :
            helicalDescriptorOfSpatialReferences?
              nearEndpoint farEndpoint nearReference farReference = some .P :=
          (helicalDescriptorOfSpatialReferences?_eq_some_iff
            nearEndpoint farEndpoint nearReference farReference .P).mpr judged
        exact ⟨.Sa,
          (helicalDescriptorOfSpatialReferences?_eq_some_P_iff_axialDescriptor_Sa
            nearEndpoint farEndpoint nearReference farReference).mp helicalSome,
          rfl⟩
    | M =>
        have helicalSome :
            helicalDescriptorOfSpatialReferences?
              nearEndpoint farEndpoint nearReference farReference = some .M :=
          (helicalDescriptorOfSpatialReferences?_eq_some_iff
            nearEndpoint farEndpoint nearReference farReference .M).mpr judged
        exact ⟨.Ra,
          (helicalDescriptorOfSpatialReferences?_eq_some_M_iff_axialDescriptor_Ra
            nearEndpoint farEndpoint nearReference farReference).mp helicalSome,
          rfl⟩
  · rintro ⟨axial, axialSome, mapped⟩
    cases axial with
    | Ra =>
        have descriptorEq : descriptor = .M := by
          simpa [AxialDescriptor.toHelicalDescriptor] using mapped.symm
        rw [descriptorEq]
        have helicalSome :
            helicalDescriptorOfSpatialReferences?
              nearEndpoint farEndpoint nearReference farReference = some .M :=
          (helicalDescriptorOfSpatialReferences?_eq_some_M_iff_axialDescriptor_Ra
            nearEndpoint farEndpoint nearReference farReference).mpr axialSome
        exact (helicalDescriptorOfSpatialReferences?_eq_some_iff
          nearEndpoint farEndpoint nearReference farReference .M).mp helicalSome
    | Sa =>
        have descriptorEq : descriptor = .P := by
          simpa [AxialDescriptor.toHelicalDescriptor] using mapped.symm
        rw [descriptorEq]
        have helicalSome :
            helicalDescriptorOfSpatialReferences?
              nearEndpoint farEndpoint nearReference farReference = some .P :=
          (helicalDescriptorOfSpatialReferences?_eq_some_P_iff_axialDescriptor_Sa
            nearEndpoint farEndpoint nearReference farReference).mpr axialSome
        exact (helicalDescriptorOfSpatialReferences?_eq_some_iff
          nearEndpoint farEndpoint nearReference farReference .P).mp helicalSome

/-! ## Endpoint locality: the terminal turn is not whole-path handedness -/

/-- The exact helical descriptor depends only on the two path endpoints and the two terminal
references.  Interior path atoms and their local turns cannot change it. -/
theorem IndexedHelicalGeometryObservation.spatialDescriptor?_eq_of_endpoints_eq
    (first second : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration)
    (frontReferenceEq : second.frontReference = first.frontReference)
    (backReferenceEq : second.backReference = first.backReference)
    (endpointsEq : helicalPathEndpoints? second.helixPath =
      helicalPathEndpoints? first.helixPath) :
    second.spatialDescriptor? spatial = first.spatialDescriptor? spatial := by
  unfold IndexedHelicalGeometryObservation.spatialDescriptor?
  simp only [endpointsEq, frontReferenceEq, backReferenceEq]

/-- The calibrated terminal-reference judgment transfers between records with the same path
endpoints and terminal references.  It makes no assertion about the interior of the path. -/
theorem BlueBookP93.GeometryIngress.rationalHelicalObservationJudgment_of_endpoints_eq
    (spatial : SpatialConfiguration)
    (first second : IndexedHelicalGeometryObservation) (descriptor : HelicalDescriptor)
    (frontReferenceEq : second.frontReference = first.frontReference)
    (backReferenceEq : second.backReference = first.backReference)
    (endpointsEq : helicalPathEndpoints? second.helixPath =
      helicalPathEndpoints? first.helixPath)
    (judged : BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment
      spatial first descriptor) :
    BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment
      spatial second descriptor := by
  have firstDescriptor :=
    (first.spatialDescriptor?_eq_some_iff spatial descriptor).mpr judged
  have secondDescriptor : second.spatialDescriptor? spatial = some descriptor := by
    rw [IndexedHelicalGeometryObservation.spatialDescriptor?_eq_of_endpoints_eq
      first second spatial frontReferenceEq backReferenceEq endpointsEq]
    exact firstDescriptor
  exact (second.spatialDescriptor?_eq_some_iff spatial descriptor).mp secondDescriptor

/-! ## Applicability extraction from identified P-93 helix frames -/

theorem P93AuthorityHelixFrame.validFor_length
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path) :
    4 ≤ path.length :=
  valid.2.2.1

theorem P93AuthorityHelixFrame.validFor_pathEndpoints
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path) :
    ∃ front back spatial,
      BlueBookP93.GeometryIngress.HelicalPathEndpoints path front back ∧
      source.spatial? = some spatial := by
  rcases valid.2.2.2.2.2.2 with
    ⟨front, back, spatial, _windingSense, endpoints, _bondFront, _bondBack, spatialEq,
      _judged, _senseEq, _coherent⟩
  exact ⟨front, back, spatial, endpoints, spatialEq⟩

/-- The identified-helix applicability evidence carries whole-path coherent winding.  This is
the hypothesis that the terminal-reference turn alone does not supply. -/
theorem P93AuthorityHelixFrame.validFor_coherentWinding
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path) :
    ∃ front back spatial,
      BlueBookP93.GeometryIngress.HelicalPathEndpoints path front back ∧
      source.spatial? = some spatial ∧
      P93AuthorityCoherentHelicalWinding spatial path frame.record.sense := by
  rcases valid.2.2.2.2.2.2 with
    ⟨front, back, spatial, windingSense, endpoints, _bondFront, _bondBack, spatialEq,
      _judged, senseEq, coherent⟩
  rw [senseEq] at coherent
  exact ⟨front, back, spatial, endpoints, spatialEq, coherent⟩

/-- Every valid identified-helix frame carries the exact rational terminal-reference judgment
for its own descriptor. -/
theorem P93AuthorityHelixFrame.validFor_rationalHelicalJudgment
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path) :
    ∃ front back spatial,
      BlueBookP93.GeometryIngress.HelicalPathEndpoints path front back ∧
      source.spatial? = some spatial ∧
      BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment
        spatial frame.record frame.descriptor := by
  rcases valid.2.2.2.2.2.2 with
    ⟨front, back, spatial, _windingSense, endpoints, _bondFront, _bondBack, spatialEq,
      judged, _senseEq, _coherent⟩
  exact ⟨front, back, spatial, endpoints, spatialEq, judged⟩

/-- The valid frame's descriptor is exactly the value the public producer reads from the
coordinates of the source spatial configuration. -/
theorem P93AuthorityHelixFrame.validFor_spatialDescriptor?
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path) :
    ∃ spatial,
      source.spatial? = some spatial ∧
      frame.record.spatialDescriptor? spatial = some frame.descriptor := by
  rcases valid.2.2.2.2.2.2 with
    ⟨front, back, spatial, _windingSense, _endpoints, _bondFront, _bondBack, spatialEq,
      judged, _senseEq, _coherent⟩
  exact ⟨spatial, spatialEq,
    (frame.record.spatialDescriptor?_eq_some_iff spatial frame.descriptor).mpr judged⟩

/-- A valid identified-helix frame whose record passes the finite molecule-backed test produces
exactly the public coordinate-derived helical assignment for its descriptor. -/
theorem P93AuthorityHelixFrame.validFor_coordinateDerivedHelicalAssignment?
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path)
    {result : ChemistryNormalizationResult}
    (frameOK : result.moleculeBackedHelicalFrameOK? frame.record = true) :
    ∃ spatial,
      source.spatial? = some spatial ∧
      result.coordinateDerivedHelicalAssignment? spatial frame.record =
        some
          { unit := StereoUnit.helix frame.record.helixPath
            outcome := StereoOutcome.helical frame.descriptor } := by
  rcases P93AuthorityHelixFrame.validFor_spatialDescriptor? valid with
    ⟨spatial, spatialEq, descriptorEq⟩
  refine ⟨spatial, spatialEq, ?_⟩
  simp [ChemistryNormalizationResult.coordinateDerivedHelicalAssignment?,
    frameOK, descriptorEq]

/-- The frame descriptor is `P` exactly when the supplied raw sense is positive. -/
theorem P93AuthorityHelixFrame.validFor_descriptor_P_iff
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path) :
    frame.descriptor = .P ↔ frame.record.sense = .positive := by
  rw [valid.2.1]
  cases frame.record.sense <;> simp [HelicalDescriptor.ofSense]

/-- The frame descriptor is `M` exactly when the supplied raw sense is negative. -/
theorem P93AuthorityHelixFrame.validFor_descriptor_M_iff
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path) :
    frame.descriptor = .M ↔ frame.record.sense = .negative := by
  rw [valid.2.1]
  cases frame.record.sense <;> simp [HelicalDescriptor.ofSense]

/-- A valid `P` frame has a positive exact near-to-far terminal-reference measure at the source
coordinates, with the path endpoints and both terminal references located in that source spatial
configuration. -/
theorem P93AuthorityHelixFrame.validFor_descriptor_P_implies_positive_measure
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path)
    (isP : frame.descriptor = .P) :
    ∃ spatial frontAtom backAtom nearPoint farPoint nearReferencePoint farReferencePoint,
      source.spatial? = some spatial ∧
      BlueBookP93.GeometryIngress.HelicalPathEndpoints
        frame.record.helixPath frontAtom backAtom ∧
      BlueBookP93.GeometryIngress.SpatialPointAt spatial frontAtom nearPoint ∧
      BlueBookP93.GeometryIngress.SpatialPointAt spatial backAtom farPoint ∧
      BlueBookP93.GeometryIngress.SpatialPointAt spatial
        frame.record.frontReference nearReferencePoint ∧
      BlueBookP93.GeometryIngress.SpatialPointAt spatial
        frame.record.backReference farReferencePoint ∧
      BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor
        nearPoint farPoint nearReferencePoint farReferencePoint .P := by
  rcases valid.2.2.2.2.2.2 with
    ⟨front, back, spatial, _windingSense, _endpoints, _bondFront, _bondBack, spatialEq,
      judged, _senseEq, _coherent⟩
  rw [isP] at judged
  unfold BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment at judged
  rcases judged with
    ⟨frontAtom, backAtom, nearPoint, farPoint, nearReferencePoint, farReferencePoint,
      endpointJudgment, nearPointAt, farPointAt, nearReferenceAt, farReferenceAt,
      rational⟩
  exact ⟨spatial, frontAtom, backAtom, nearPoint, farPoint, nearReferencePoint,
    farReferencePoint, spatialEq, endpointJudgment, nearPointAt, farPointAt,
    nearReferenceAt, farReferenceAt, rational⟩

/-- A valid `M` frame has a negative exact near-to-far terminal-reference measure at the source
coordinates, with the path endpoints and both terminal references located in that source spatial
configuration. -/
theorem P93AuthorityHelixFrame.validFor_descriptor_M_implies_negative_measure
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path)
    (isM : frame.descriptor = .M) :
    ∃ spatial frontAtom backAtom nearPoint farPoint nearReferencePoint farReferencePoint,
      source.spatial? = some spatial ∧
      BlueBookP93.GeometryIngress.HelicalPathEndpoints
        frame.record.helixPath frontAtom backAtom ∧
      BlueBookP93.GeometryIngress.SpatialPointAt spatial frontAtom nearPoint ∧
      BlueBookP93.GeometryIngress.SpatialPointAt spatial backAtom farPoint ∧
      BlueBookP93.GeometryIngress.SpatialPointAt spatial
        frame.record.frontReference nearReferencePoint ∧
      BlueBookP93.GeometryIngress.SpatialPointAt spatial
        frame.record.backReference farReferencePoint ∧
      BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor
        nearPoint farPoint nearReferencePoint farReferencePoint .M := by
  rcases valid.2.2.2.2.2.2 with
    ⟨front, back, spatial, _windingSense, _endpoints, _bondFront, _bondBack, spatialEq,
      judged, _senseEq, _coherent⟩
  rw [isM] at judged
  unfold BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment at judged
  rcases judged with
    ⟨frontAtom, backAtom, nearPoint, farPoint, nearReferencePoint, farReferencePoint,
      endpointJudgment, nearPointAt, farPointAt, nearReferenceAt, farReferenceAt,
      rational⟩
  exact ⟨spatial, frontAtom, backAtom, nearPoint, farPoint, nearReferencePoint,
    farReferencePoint, spatialEq, endpointJudgment, nearPointAt, farPointAt,
    nearReferenceAt, farReferenceAt, rational⟩

/-- A valid `P` frame realizes the source clockwise screw sense on its terminal references. -/
theorem P93AuthorityHelixFrame.validFor_descriptor_P_sourceScrewSense
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path)
    (isP : frame.descriptor = .P) :
    ∃ spatial nearPoint farPoint nearReferencePoint farReferencePoint,
      source.spatial? = some spatial ∧
      CartesianPoint3.sourceScrewSense?
        nearPoint farPoint nearReferencePoint farReferencePoint = some .clockwise := by
  rcases P93AuthorityHelixFrame.validFor_descriptor_P_implies_positive_measure
    valid isP with
    ⟨spatial, _frontAtom, _backAtom, nearPoint, farPoint, nearReferencePoint,
      farReferencePoint, spatialEq, _endpoints, _nearPointAt, _farPointAt,
      _nearReferenceAt, _farReferenceAt, judged⟩
  exact ⟨spatial, nearPoint, farPoint, nearReferencePoint, farReferencePoint, spatialEq,
    (CartesianPoint3.sourceScrewSense?_eq_some_clockwise_iff
      nearPoint farPoint nearReferencePoint farReferencePoint).mpr
      (by simpa [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor] using judged)⟩

/-- A valid `M` frame realizes the source anticlockwise screw sense on its terminal
references. -/
theorem P93AuthorityHelixFrame.validFor_descriptor_M_sourceScrewSense
    {source : AuthoritativeChemicalInput} {path : List Nat}
    {frame : P93AuthorityHelixFrame} (valid : frame.ValidFor source path)
    (isM : frame.descriptor = .M) :
    ∃ spatial nearPoint farPoint nearReferencePoint farReferencePoint,
      source.spatial? = some spatial ∧
      CartesianPoint3.sourceScrewSense?
        nearPoint farPoint nearReferencePoint farReferencePoint = some .anticlockwise := by
  rcases P93AuthorityHelixFrame.validFor_descriptor_M_implies_negative_measure
    valid isM with
    ⟨spatial, _frontAtom, _backAtom, nearPoint, farPoint, nearReferencePoint,
      farReferencePoint, spatialEq, _endpoints, _nearPointAt, _farPointAt,
      _nearReferenceAt, _farReferenceAt, judged⟩
  exact ⟨spatial, nearPoint, farPoint, nearReferencePoint, farReferencePoint, spatialEq,
    (CartesianPoint3.sourceScrewSense?_eq_some_anticlockwise_iff
      nearPoint farPoint nearReferencePoint farReferencePoint).mpr
      (by simpa [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor] using judged)⟩

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.helicalReferenceMeasure_eq_p94SineNumerator
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.helicalReferenceMeasure_eq_axialChiralityMeasure
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.CoordinateTorsion.PointFrame.principalDegrees_pos_of_sineNumerator_pos
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.CoordinateTorsion.PointFrame.principalDegrees_neg_of_sineNumerator_neg
assert_kernel_only TetraStereo.OneCenter.terminalReferencePointFrame_principalDegrees_pos_of_helicalMeasure_pos
assert_kernel_only TetraStereo.OneCenter.terminalReferencePointFrame_principalDegrees_neg_of_helicalMeasure_neg
assert_kernel_only TetraStereo.OneCenter.terminalReferencePointFrame_principalDegrees_sign_of_helicalDescriptor
assert_kernel_only TetraStereo.OneCenter.SourceScrewSense.ofHelicalDescriptor_toHelicalDescriptor
assert_kernel_only TetraStereo.OneCenter.SourceScrewSense.toHelicalDescriptor_ofHelicalDescriptor
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.sourceScrewSense?_eq_some_clockwise_iff
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.sourceScrewSense?_eq_some_anticlockwise_iff
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.sourceScrewSense?_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.helicalDescriptorOfSpatialReferences?_eq_sourceScrewSense_map
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.canonicalRightHandedHelix_measure
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.canonicalRightHandedHelix_sourceScrewSense
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.canonicalRightHandedHelix_descriptor
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.canonicalRightHandedHelix_source_screw_P
assert_kernel_only TetraStereo.OneCenter.helicalDescriptorOfSpatialReferences?_eq_some_P_iff_axialDescriptor_Sa
assert_kernel_only TetraStereo.OneCenter.helicalDescriptorOfSpatialReferences?_eq_some_M_iff_axialDescriptor_Ra
assert_kernel_only TetraStereo.OneCenter.helicalDescriptorOfSpatialReferences?_eq_axialDescriptor_map
assert_kernel_only TetraStereo.OneCenter.IndexedHelicalGeometryObservation.spatialDescriptor?_eq_of_endpoints_eq
assert_kernel_only TetraStereo.OneCenter.BlueBookP93.GeometryIngress.rationalHelicalObservationJudgment_of_endpoints_eq
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_length
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_pathEndpoints
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_coherentWinding
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_rationalHelicalJudgment
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_spatialDescriptor?
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_coordinateDerivedHelicalAssignment?
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_descriptor_P_iff
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_descriptor_M_iff
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_descriptor_P_implies_positive_measure
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_descriptor_M_implies_negative_measure
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_descriptor_P_sourceScrewSense
assert_kernel_only TetraStereo.OneCenter.P93AuthorityHelixFrame.validFor_descriptor_M_sourceScrewSense

end TetraStereo.OneCenter
