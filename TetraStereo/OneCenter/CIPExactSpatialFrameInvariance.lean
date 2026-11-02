import TetraStereo.OneCenter.CIPObservedPlanarSpatialConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Coordinate-frame invariance of exact spatial descriptors

Exact rational coordinates should not make a stereochemical answer depend on the arbitrary
origin or positive unit scale selected by an importer.  This file proves that boundary directly
for the spatial primitives used by planar, axial, helical, and Rule-3 double-bond classifiers.
-/

namespace CartesianPoint3

/-- Translate a rational point by an arbitrary rational offset. -/
def translated (point offset : CartesianPoint3) : CartesianPoint3 :=
  { x := point.x + offset.x
    y := point.y + offset.y
    z := point.z + offset.z }

/-- Uniform rational scaling about the coordinate origin.  Descriptor invariance below requires
the factor to be positive, as is appropriate for a change of length unit. -/
def uniformlyScaled (factor : ℚ) (point : CartesianPoint3) : CartesianPoint3 :=
  { x := factor * point.x
    y := factor * point.y
    z := factor * point.z }

@[simp] theorem displacement_translated
    (source target offset : CartesianPoint3) :
    displacement (source.translated offset) (target.translated offset) =
      displacement source target := by
  cases source
  cases target
  cases offset
  simp [translated, displacement]

/-- An affine determinant is independent of the coordinate origin. -/
theorem orientedVolume_translated
    (first second third fourth offset : CartesianPoint3) :
    orientedVolume (first.translated offset) (second.translated offset)
        (third.translated offset) (fourth.translated offset) =
      orientedVolume first second third fourth := by
  simp [translated, orientedVolume]

/-- A uniform scale multiplies a three-dimensional affine determinant by the cube of its factor. -/
theorem orientedVolume_uniformlyScaled
    (factor : ℚ) (first second third fourth : CartesianPoint3) :
    orientedVolume (first.uniformlyScaled factor) (second.uniformlyScaled factor)
        (third.uniformlyScaled factor) (fourth.uniformlyScaled factor) =
      factor ^ 3 * orientedVolume first second third fourth := by
  simp [uniformlyScaled, orientedVolume]
  ring

/-- Axial chirality is independent of the coordinate origin. -/
theorem axialChiralityMeasure_translated
    (axisStart axisEnd startHigh endHigh offset : CartesianPoint3) :
    axialChiralityMeasure (axisStart.translated offset) (axisEnd.translated offset)
        (startHigh.translated offset) (endHigh.translated offset) =
      axialChiralityMeasure axisStart axisEnd startHigh endHigh := by
  simp [axialChiralityMeasure, displacement_translated]

/-- A uniform scale multiplies the axial scalar triple product by the cube of its factor. -/
theorem axialChiralityMeasure_uniformlyScaled
    (factor : ℚ) (axisStart axisEnd startHigh endHigh : CartesianPoint3) :
    axialChiralityMeasure (axisStart.uniformlyScaled factor)
        (axisEnd.uniformlyScaled factor) (startHigh.uniformlyScaled factor)
        (endHigh.uniformlyScaled factor) =
      factor ^ 3 * axialChiralityMeasure axisStart axisEnd startHigh endHigh := by
  simp [axialChiralityMeasure, uniformlyScaled, displacement,
    RationalVector3.dot, RationalVector3.cross]
  ring

/-- Terminal-reference helicity is independent of the coordinate origin. -/
theorem helicalReferenceMeasure_translated
    (frontEndpoint backEndpoint frontReference backReference offset : CartesianPoint3) :
    helicalReferenceMeasure (frontEndpoint.translated offset) (backEndpoint.translated offset)
        (frontReference.translated offset) (backReference.translated offset) =
      helicalReferenceMeasure frontEndpoint backEndpoint frontReference backReference := by
  simp [helicalReferenceMeasure, displacement_translated]

/-- A uniform scale multiplies the helical scalar triple product by the cube of its factor. -/
theorem helicalReferenceMeasure_uniformlyScaled
    (factor : ℚ) (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    helicalReferenceMeasure (frontEndpoint.uniformlyScaled factor)
        (backEndpoint.uniformlyScaled factor) (frontReference.uniformlyScaled factor)
        (backReference.uniformlyScaled factor) =
      factor ^ 3 * helicalReferenceMeasure
        frontEndpoint backEndpoint frontReference backReference := by
  simp [helicalReferenceMeasure, uniformlyScaled, displacement,
    RationalVector3.dot, RationalVector3.cross]
  ring

/-- Rule-3 coplanarity is independent of the coordinate origin. -/
theorem rule3Coplanarity_translated
    (leftEndpoint rightEndpoint leftReference rightReference offset : CartesianPoint3) :
    rule3Coplanarity (leftEndpoint.translated offset) (rightEndpoint.translated offset)
        (leftReference.translated offset) (rightReference.translated offset) =
      rule3Coplanarity leftEndpoint rightEndpoint leftReference rightReference := by
  simp [rule3Coplanarity, displacement_translated]

theorem rule3Coplanarity_uniformlyScaled
    (factor : ℚ) (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    rule3Coplanarity (leftEndpoint.uniformlyScaled factor)
        (rightEndpoint.uniformlyScaled factor) (leftReference.uniformlyScaled factor)
        (rightReference.uniformlyScaled factor) =
      factor ^ 3 * rule3Coplanarity
        leftEndpoint rightEndpoint leftReference rightReference := by
  simp [rule3Coplanarity, uniformlyScaled, displacement,
    RationalVector3.dot, RationalVector3.cross]
  ring

/-- Rule-3 same-side/opposite-side geometry is independent of the coordinate origin. -/
theorem rule3SideProduct_translated
    (leftEndpoint rightEndpoint leftReference rightReference offset : CartesianPoint3) :
    rule3SideProduct (leftEndpoint.translated offset) (rightEndpoint.translated offset)
        (leftReference.translated offset) (rightReference.translated offset) =
      rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference := by
  simp [rule3SideProduct, displacement_translated]

/-- The Rule-3 side-normal dot product is homogeneous of degree four. -/
theorem rule3SideProduct_uniformlyScaled
    (factor : ℚ) (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    rule3SideProduct (leftEndpoint.uniformlyScaled factor)
        (rightEndpoint.uniformlyScaled factor) (leftReference.uniformlyScaled factor)
        (rightReference.uniformlyScaled factor) =
      factor ^ 4 * rule3SideProduct
        leftEndpoint rightEndpoint leftReference rightReference := by
  simp [rule3SideProduct, uniformlyScaled, displacement,
    RationalVector3.dot, RationalVector3.cross]
  ring

end CartesianPoint3

namespace SpatialConfiguration

/-- Apply a coordinate-frame map to every atom position without changing molecular indices. -/
def mapPoints (spatial : SpatialConfiguration)
    (mapPoint : CartesianPoint3 → CartesianPoint3) : SpatialConfiguration :=
  { positions := spatial.positions.map mapPoint }

@[simp] theorem mapPoints_position
    (spatial : SpatialConfiguration) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (atom : ℕ) :
    (spatial.mapPoints mapPoint).positions[atom]? =
      spatial.positions[atom]?.map mapPoint := by
  simp [mapPoints, List.getElem?_map]

/-- Mapping all stored points commutes with finite exact coordinate collection. -/
theorem mapM_positions_mapPoints
    (spatial : SpatialConfiguration) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (atoms : List ℕ) :
    atoms.mapM (fun atom => (spatial.mapPoints mapPoint).positions[atom]?) =
      (atoms.mapM (fun atom => spatial.positions[atom]?)).map (List.map mapPoint) := by
  induction atoms with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mapM_cons, mapPoints_position]
      cases headEq : spatial.positions[head]? with
      | none => simp
      | some headPoint =>
          have ih' :
              tail.mapM (fun atom => spatial.positions[atom]?.map mapPoint) =
                (tail.mapM (fun atom => spatial.positions[atom]?)).map
                  (List.map mapPoint) := by
            simpa only [mapPoints_position] using ih
          rw [ih']
          cases tailEq : tail.mapM (fun atom => spatial.positions[atom]?) with
          | none => simp
          | some tailPoints => simp

end SpatialConfiguration

/-- An exact rational affine change of three-dimensional coordinates. -/
structure RationalAffineFrameTransform where
  m00 : ℚ
  m01 : ℚ
  m02 : ℚ
  m10 : ℚ
  m11 : ℚ
  m12 : ℚ
  m20 : ℚ
  m21 : ℚ
  m22 : ℚ
  offset : CartesianPoint3
  deriving DecidableEq, Repr

namespace RationalAffineFrameTransform

/-- Exact determinant of the linear part. -/
def determinant (transform : RationalAffineFrameTransform) : ℚ :=
  transform.m00 * (transform.m11 * transform.m22 - transform.m12 * transform.m21) -
    transform.m01 * (transform.m10 * transform.m22 - transform.m12 * transform.m20) +
    transform.m02 * (transform.m10 * transform.m21 - transform.m11 * transform.m20)

/-- Apply the affine frame change to one point. -/
def applyPoint (transform : RationalAffineFrameTransform)
    (point : CartesianPoint3) : CartesianPoint3 :=
  { x := transform.m00 * point.x + transform.m01 * point.y +
      transform.m02 * point.z + transform.offset.x
    y := transform.m10 * point.x + transform.m11 * point.y +
      transform.m12 * point.z + transform.offset.y
    z := transform.m20 * point.x + transform.m21 * point.y +
      transform.m22 * point.z + transform.offset.z }

/-- The affine determinant transforms by the determinant of the coordinate-frame linear part. -/
theorem orientedVolume_applyPoint
    (transform : RationalAffineFrameTransform)
    (first second third fourth : CartesianPoint3) :
    CartesianPoint3.orientedVolume (transform.applyPoint first) (transform.applyPoint second)
        (transform.applyPoint third) (transform.applyPoint fourth) =
      transform.determinant * CartesianPoint3.orientedVolume first second third fourth := by
  simp [applyPoint, determinant, CartesianPoint3.orientedVolume]
  ring

/-- Axial scalar-triple-product handedness has the same determinant transformation law. -/
theorem axialChiralityMeasure_applyPoint
    (transform : RationalAffineFrameTransform)
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) :
    CartesianPoint3.axialChiralityMeasure (transform.applyPoint axisStart)
        (transform.applyPoint axisEnd) (transform.applyPoint startHigh)
        (transform.applyPoint endHigh) =
      transform.determinant *
        CartesianPoint3.axialChiralityMeasure axisStart axisEnd startHigh endHigh := by
  simp [applyPoint, determinant, CartesianPoint3.axialChiralityMeasure,
    CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross]
  ring

/-- Terminal-reference helical handedness has the same determinant transformation law. -/
theorem helicalReferenceMeasure_applyPoint
    (transform : RationalAffineFrameTransform)
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    CartesianPoint3.helicalReferenceMeasure (transform.applyPoint frontEndpoint)
        (transform.applyPoint backEndpoint) (transform.applyPoint frontReference)
        (transform.applyPoint backReference) =
      transform.determinant * CartesianPoint3.helicalReferenceMeasure
        frontEndpoint backEndpoint frontReference backReference := by
  simp [applyPoint, determinant, CartesianPoint3.helicalReferenceMeasure,
    CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross]
  ring

end RationalAffineFrameTransform

private theorem positive_mul_sign_iff (factor value : ℚ) (positive : 0 < factor) :
    (0 < factor * value ↔ 0 < value) ∧
      (factor * value < 0 ↔ value < 0) ∧
      (factor * value = 0 ↔ value = 0) := by
  constructor
  · constructor <;> intro hypothesis <;> nlinarith
  constructor
  · constructor <;> intro hypothesis <;> nlinarith
  · constructor <;> intro hypothesis <;> nlinarith

private theorem negative_mul_sign_iff (factor value : ℚ) (negative : factor < 0) :
    (0 < factor * value ↔ value < 0) ∧
      (factor * value < 0 ↔ 0 < value) ∧
      (factor * value = 0 ↔ value = 0) := by
  constructor
  · constructor <;> intro hypothesis <;> nlinarith
  constructor
  · constructor <;> intro hypothesis <;> nlinarith
  · constructor <;> intro hypothesis <;> nlinarith

/-- The exact planar descriptor is independent of coordinate origin. -/
theorem planarDescriptorOfDerivedTetrahedron?_translated
    (a b y z offset : CartesianPoint3) :
    planarDescriptorOfDerivedTetrahedron? (a.translated offset) (b.translated offset)
        (y.translated offset) (z.translated offset) =
      planarDescriptorOfDerivedTetrahedron? a b y z := by
  apply Option.ext
  intro descriptor
  rw [planarDescriptorOfDerivedTetrahedron?_eq_some_iff,
    planarDescriptorOfDerivedTetrahedron?_eq_some_iff]
  cases descriptor <;>
    simp [BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor,
      CartesianPoint3.orientedVolume_translated]

/-- Positive changes of coordinate unit preserve `Rₚ/Sₚ`. -/
theorem planarDescriptorOfDerivedTetrahedron?_uniformlyScaled
    (factor : ℚ) (positive : 0 < factor) (a b y z : CartesianPoint3) :
    planarDescriptorOfDerivedTetrahedron? (a.uniformlyScaled factor)
        (b.uniformlyScaled factor) (y.uniformlyScaled factor) (z.uniformlyScaled factor) =
      planarDescriptorOfDerivedTetrahedron? a b y z := by
  have cubePositive : 0 < factor ^ 3 := pow_pos positive 3
  have signs := positive_mul_sign_iff (factor ^ 3)
    (CartesianPoint3.orientedVolume a b y z) cubePositive
  apply Option.ext
  intro descriptor
  rw [planarDescriptorOfDerivedTetrahedron?_eq_some_iff,
    planarDescriptorOfDerivedTetrahedron?_eq_some_iff]
  cases descriptor <;>
    simp [BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor,
      CartesianPoint3.orientedVolume_uniformlyScaled, signs.1, signs.2.1]

/-- Every exact rational affine coordinate change with positive determinant preserves
`Rₚ/Sₚ`; its translation, rotation, shear, and positive scale components cannot alter the result. -/
theorem planarDescriptorOfDerivedTetrahedron?_orientationPreservingAffine
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant)
    (a b y z : CartesianPoint3) :
    planarDescriptorOfDerivedTetrahedron? (transform.applyPoint a) (transform.applyPoint b)
        (transform.applyPoint y) (transform.applyPoint z) =
      planarDescriptorOfDerivedTetrahedron? a b y z := by
  have signs := positive_mul_sign_iff transform.determinant
    (CartesianPoint3.orientedVolume a b y z) orientationPreserving
  apply Option.ext
  intro descriptor
  rw [planarDescriptorOfDerivedTetrahedron?_eq_some_iff,
    planarDescriptorOfDerivedTetrahedron?_eq_some_iff]
  cases descriptor <;>
    simp [BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor,
      RationalAffineFrameTransform.orientedVolume_applyPoint, signs.1, signs.2.1]

/-- A negative-determinant rational affine frame change mirrors `Rₚ/Sₚ` and preserves
degenerate refusal. -/
theorem planarDescriptorOfDerivedTetrahedron?_orientationReversingAffine
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0)
    (a b y z : CartesianPoint3) :
    planarDescriptorOfDerivedTetrahedron? (transform.applyPoint a) (transform.applyPoint b)
        (transform.applyPoint y) (transform.applyPoint z) =
      (planarDescriptorOfDerivedTetrahedron? a b y z).map PlanarDescriptor.mirror := by
  let volume := CartesianPoint3.orientedVolume a b y z
  have signs := negative_mul_sign_iff transform.determinant volume orientationReversing
  unfold planarDescriptorOfDerivedTetrahedron?
  rw [RationalAffineFrameTransform.orientedVolume_applyPoint]
  by_cases positive : 0 < volume
  · have transformedNegative : transform.determinant * volume < 0 := signs.2.1.mpr positive
    have notTransformedPositive : ¬ 0 < transform.determinant * volume :=
      not_lt_of_ge transformedNegative.le
    simp [volume, positive, transformedNegative, notTransformedPositive,
      PlanarDescriptor.mirror]
  · by_cases negative : volume < 0
    · have transformedPositive : 0 < transform.determinant * volume := signs.1.mpr negative
      simp [volume, positive, negative, transformedPositive, PlanarDescriptor.mirror]
    · have zero : volume = 0 := le_antisymm (not_lt.mp positive) (not_lt.mp negative)
      simp [volume, zero]

/-- The exact axial descriptor is independent of coordinate origin. -/
theorem axialDescriptorOfSpatialReferences?_translated
    (axisStart axisEnd startHigh endHigh offset : CartesianPoint3) :
    axialDescriptorOfSpatialReferences? (axisStart.translated offset)
        (axisEnd.translated offset) (startHigh.translated offset) (endHigh.translated offset) =
      axialDescriptorOfSpatialReferences? axisStart axisEnd startHigh endHigh := by
  apply Option.ext
  intro descriptor
  rw [axialDescriptorOfSpatialReferences?_eq_some_iff,
    axialDescriptorOfSpatialReferences?_eq_some_iff]
  cases descriptor <;>
    simp [RationalAxialSpatialDescriptor, CartesianPoint3.axialChiralityMeasure_translated]

/-- Positive changes of coordinate unit preserve `Rₐ/Sₐ`. -/
theorem axialDescriptorOfSpatialReferences?_uniformlyScaled
    (factor : ℚ) (positive : 0 < factor)
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) :
    axialDescriptorOfSpatialReferences? (axisStart.uniformlyScaled factor)
        (axisEnd.uniformlyScaled factor) (startHigh.uniformlyScaled factor)
        (endHigh.uniformlyScaled factor) =
      axialDescriptorOfSpatialReferences? axisStart axisEnd startHigh endHigh := by
  have cubePositive : 0 < factor ^ 3 := pow_pos positive 3
  have signs := positive_mul_sign_iff (factor ^ 3)
    (CartesianPoint3.axialChiralityMeasure axisStart axisEnd startHigh endHigh) cubePositive
  apply Option.ext
  intro descriptor
  rw [axialDescriptorOfSpatialReferences?_eq_some_iff,
    axialDescriptorOfSpatialReferences?_eq_some_iff]
  cases descriptor <;>
    simp [RationalAxialSpatialDescriptor,
      CartesianPoint3.axialChiralityMeasure_uniformlyScaled, signs.1, signs.2.1]

/-- Every exact rational affine coordinate change with positive determinant preserves
coordinate-derived axial chirality. -/
theorem axialDescriptorOfSpatialReferences?_orientationPreservingAffine
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant)
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) :
    axialDescriptorOfSpatialReferences? (transform.applyPoint axisStart)
        (transform.applyPoint axisEnd) (transform.applyPoint startHigh)
        (transform.applyPoint endHigh) =
      axialDescriptorOfSpatialReferences? axisStart axisEnd startHigh endHigh := by
  have signs := positive_mul_sign_iff transform.determinant
    (CartesianPoint3.axialChiralityMeasure axisStart axisEnd startHigh endHigh)
    orientationPreserving
  apply Option.ext
  intro descriptor
  rw [axialDescriptorOfSpatialReferences?_eq_some_iff,
    axialDescriptorOfSpatialReferences?_eq_some_iff]
  cases descriptor <;>
    simp [RationalAxialSpatialDescriptor,
      RationalAffineFrameTransform.axialChiralityMeasure_applyPoint,
      signs.1, signs.2.1]

/-- A negative-determinant rational affine frame change mirrors `Rₐ/Sₐ` and preserves
degenerate refusal. -/
theorem axialDescriptorOfSpatialReferences?_orientationReversingAffine
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0)
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) :
    axialDescriptorOfSpatialReferences? (transform.applyPoint axisStart)
        (transform.applyPoint axisEnd) (transform.applyPoint startHigh)
        (transform.applyPoint endHigh) =
      (axialDescriptorOfSpatialReferences? axisStart axisEnd startHigh endHigh).map
        AxialDescriptor.mirror := by
  let measure := CartesianPoint3.axialChiralityMeasure axisStart axisEnd startHigh endHigh
  have signs := negative_mul_sign_iff transform.determinant measure orientationReversing
  unfold axialDescriptorOfSpatialReferences?
  rw [RationalAffineFrameTransform.axialChiralityMeasure_applyPoint]
  by_cases negative : measure < 0
  · have transformedPositive : 0 < transform.determinant * measure := signs.1.mpr negative
    have notTransformedNegative : ¬ transform.determinant * measure < 0 :=
      not_lt_of_ge transformedPositive.le
    simp [measure, negative, transformedPositive, notTransformedNegative,
      AxialDescriptor.mirror]
  · by_cases positive : 0 < measure
    · have transformedNegative : transform.determinant * measure < 0 := signs.2.1.mpr positive
      simp [measure, negative, positive, transformedNegative, AxialDescriptor.mirror]
    · have zero : measure = 0 := le_antisymm (not_lt.mp positive) (not_lt.mp negative)
      simp [measure, zero]

/-- The exact terminal-reference helical descriptor is independent of coordinate origin. -/
theorem helicalDescriptorOfSpatialReferences?_translated
    (frontEndpoint backEndpoint frontReference backReference offset : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences? (frontEndpoint.translated offset)
        (backEndpoint.translated offset) (frontReference.translated offset)
        (backReference.translated offset) =
      helicalDescriptorOfSpatialReferences?
        frontEndpoint backEndpoint frontReference backReference := by
  apply Option.ext
  intro descriptor
  rw [helicalDescriptorOfSpatialReferences?_eq_some_iff,
    helicalDescriptorOfSpatialReferences?_eq_some_iff]
  cases descriptor <;>
    simp [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor,
      CartesianPoint3.helicalReferenceMeasure_translated]

/-- Positive changes of coordinate unit preserve terminal-reference `P/M`. -/
theorem helicalDescriptorOfSpatialReferences?_uniformlyScaled
    (factor : ℚ) (positive : 0 < factor)
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences? (frontEndpoint.uniformlyScaled factor)
        (backEndpoint.uniformlyScaled factor) (frontReference.uniformlyScaled factor)
        (backReference.uniformlyScaled factor) =
      helicalDescriptorOfSpatialReferences?
        frontEndpoint backEndpoint frontReference backReference := by
  have cubePositive : 0 < factor ^ 3 := pow_pos positive 3
  have signs := positive_mul_sign_iff (factor ^ 3)
    (CartesianPoint3.helicalReferenceMeasure
      frontEndpoint backEndpoint frontReference backReference) cubePositive
  apply Option.ext
  intro descriptor
  rw [helicalDescriptorOfSpatialReferences?_eq_some_iff,
    helicalDescriptorOfSpatialReferences?_eq_some_iff]
  cases descriptor <;>
    simp [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor,
      CartesianPoint3.helicalReferenceMeasure_uniformlyScaled, signs.1, signs.2.1]

/-- Every exact rational affine coordinate change with positive determinant preserves the
represented terminal-reference helical handedness. -/
theorem helicalDescriptorOfSpatialReferences?_orientationPreservingAffine
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant)
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences? (transform.applyPoint frontEndpoint)
        (transform.applyPoint backEndpoint) (transform.applyPoint frontReference)
        (transform.applyPoint backReference) =
      helicalDescriptorOfSpatialReferences?
        frontEndpoint backEndpoint frontReference backReference := by
  have signs := positive_mul_sign_iff transform.determinant
    (CartesianPoint3.helicalReferenceMeasure
      frontEndpoint backEndpoint frontReference backReference) orientationPreserving
  apply Option.ext
  intro descriptor
  rw [helicalDescriptorOfSpatialReferences?_eq_some_iff,
    helicalDescriptorOfSpatialReferences?_eq_some_iff]
  cases descriptor <;>
    simp [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor,
      RationalAffineFrameTransform.helicalReferenceMeasure_applyPoint,
      signs.1, signs.2.1]

/-- A negative-determinant rational affine frame change mirrors terminal-reference `P/M` and
preserves degenerate refusal. -/
theorem helicalDescriptorOfSpatialReferences?_orientationReversingAffine
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0)
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences? (transform.applyPoint frontEndpoint)
        (transform.applyPoint backEndpoint) (transform.applyPoint frontReference)
        (transform.applyPoint backReference) =
      (helicalDescriptorOfSpatialReferences?
        frontEndpoint backEndpoint frontReference backReference).map HelicalDescriptor.mirror := by
  let measure := CartesianPoint3.helicalReferenceMeasure
    frontEndpoint backEndpoint frontReference backReference
  have signs := negative_mul_sign_iff transform.determinant measure orientationReversing
  unfold helicalDescriptorOfSpatialReferences?
  rw [RationalAffineFrameTransform.helicalReferenceMeasure_applyPoint]
  by_cases negative : measure < 0
  · have transformedPositive : 0 < transform.determinant * measure := signs.1.mpr negative
    have notTransformedNegative : ¬ transform.determinant * measure < 0 :=
      not_lt_of_ge transformedPositive.le
    simp [measure, negative, transformedPositive, notTransformedNegative,
      HelicalDescriptor.mirror]
  · by_cases positive : 0 < measure
    · have transformedNegative : transform.determinant * measure < 0 := signs.2.1.mpr positive
      simp [measure, negative, positive, transformedNegative, HelicalDescriptor.mirror]
    · have zero : measure = 0 := le_antisymm (not_lt.mp positive) (not_lt.mp negative)
      simp [measure, zero]

/-- Exact Rule-3 double-bond geometry is independent of coordinate origin. -/
theorem rule3GeometryOfSpatialReferences?_translated
    (leftEndpoint rightEndpoint leftReference rightReference offset : CartesianPoint3) :
    rule3GeometryOfSpatialReferences? (leftEndpoint.translated offset)
        (rightEndpoint.translated offset) (leftReference.translated offset)
        (rightReference.translated offset) =
      rule3GeometryOfSpatialReferences?
        leftEndpoint rightEndpoint leftReference rightReference := by
  apply Option.ext
  intro geometry
  rw [rule3GeometryOfSpatialReferences?_eq_some_iff,
    rule3GeometryOfSpatialReferences?_eq_some_iff]
  cases geometry <;>
    simp [RationalRule3SpatialGeometry, CartesianPoint3.rule3Coplanarity_translated,
      CartesianPoint3.rule3SideProduct_translated]

/-- Positive changes of coordinate unit preserve `seqCis/seqTrans` and all refusals. -/
theorem rule3GeometryOfSpatialReferences?_uniformlyScaled
    (factor : ℚ) (positive : 0 < factor)
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    rule3GeometryOfSpatialReferences? (leftEndpoint.uniformlyScaled factor)
        (rightEndpoint.uniformlyScaled factor) (leftReference.uniformlyScaled factor)
        (rightReference.uniformlyScaled factor) =
      rule3GeometryOfSpatialReferences?
        leftEndpoint rightEndpoint leftReference rightReference := by
  have cubePositive : 0 < factor ^ 3 := pow_pos positive 3
  have fourthPositive : 0 < factor ^ 4 := pow_pos positive 4
  have coplanarSigns := positive_mul_sign_iff (factor ^ 3)
    (CartesianPoint3.rule3Coplanarity
      leftEndpoint rightEndpoint leftReference rightReference) cubePositive
  have sideSigns := positive_mul_sign_iff (factor ^ 4)
    (CartesianPoint3.rule3SideProduct
      leftEndpoint rightEndpoint leftReference rightReference) fourthPositive
  apply Option.ext
  intro geometry
  rw [rule3GeometryOfSpatialReferences?_eq_some_iff,
    rule3GeometryOfSpatialReferences?_eq_some_iff]
  cases geometry <;>
    simp [RationalRule3SpatialGeometry, CartesianPoint3.rule3Coplanarity_uniformlyScaled,
      CartesianPoint3.rule3SideProduct_uniformlyScaled,
      coplanarSigns.2.2, sideSigns.1, sideSigns.2.1]

/-- The complete molecule-prioritized axial coordinate evaluator is invariant under every
orientation-preserving rational affine change of frame, including all refusal branches. -/
theorem ChemistryNormalizationResult.axialObservationSpatialDescriptor?_orientationPreservingAffine
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    result.axialObservationSpatialDescriptor?
        (spatial.mapPoints transform.applyPoint) record =
      result.axialObservationSpatialDescriptor? spatial record := by
  unfold ChemistryNormalizationResult.axialObservationSpatialDescriptor?
  generalize startEq : seniorReferenceOfDecision?
    (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
      result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
      record.axisStart record.startFirst record.startSecond)
    record.startFirst record.startSecond = startHigh
  cases startHigh with
  | none => simp [startEq]
  | some startHigh =>
      generalize endEq : seniorReferenceOfDecision?
        (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
          result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
          record.axisEnd record.endFirst record.endSecond)
        record.endFirst record.endSecond = endHigh
      cases endHigh with
      | none => simp [startEq, endEq]
      | some endHigh =>
          cases axisStartEq : spatial.positions[record.axisStart]? with
          | none => simp [startEq, endEq, SpatialConfiguration.pointAt?, axisStartEq]
          | some axisStartPoint =>
              cases axisEndEq : spatial.positions[record.axisEnd]? with
              | none =>
                  simp [startEq, endEq, SpatialConfiguration.pointAt?,
                    axisStartEq, axisEndEq]
              | some axisEndPoint =>
                  cases startHighEq : spatial.positions[startHigh]? with
                  | none =>
                      simp [startEq, endEq, SpatialConfiguration.pointAt?,
                        axisStartEq, axisEndEq, startHighEq]
                  | some startHighPoint =>
                      cases endHighEq : spatial.positions[endHigh]? with
                      | none =>
                          simp [startEq, endEq, SpatialConfiguration.pointAt?,
                            axisStartEq, axisEndEq, endHighEq]
                      | some endHighPoint =>
                          simp [startEq, endEq, SpatialConfiguration.pointAt?,
                            axisStartEq, axisEndEq, startHighEq, endHighEq,
                            axialDescriptorOfSpatialReferences?_orientationPreservingAffine,
                            orientationPreserving]

/-- A coordinate reflection mirrors the result of the complete molecule-prioritized axial
evaluator and preserves every refusal branch. -/
theorem ChemistryNormalizationResult.axialObservationSpatialDescriptor?_orientationReversingAffine
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation)
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0) :
    result.axialObservationSpatialDescriptor?
        (spatial.mapPoints transform.applyPoint) record =
      (result.axialObservationSpatialDescriptor? spatial record).map
        AxialDescriptor.mirror := by
  unfold ChemistryNormalizationResult.axialObservationSpatialDescriptor?
  generalize startEq : seniorReferenceOfDecision?
    (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
      result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
      record.axisStart record.startFirst record.startSecond)
    record.startFirst record.startSecond = startHigh
  cases startHigh with
  | none => simp [startEq]
  | some startHigh =>
      generalize endEq : seniorReferenceOfDecision?
        (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
          result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
          record.axisEnd record.endFirst record.endSecond)
        record.endFirst record.endSecond = endHigh
      cases endHigh with
      | none => simp [startEq, endEq]
      | some endHigh =>
          cases axisStartEq : spatial.positions[record.axisStart]? with
          | none => simp [startEq, endEq, SpatialConfiguration.pointAt?, axisStartEq]
          | some axisStartPoint =>
              cases axisEndEq : spatial.positions[record.axisEnd]? with
              | none =>
                  simp [startEq, endEq, SpatialConfiguration.pointAt?,
                    axisStartEq, axisEndEq]
              | some axisEndPoint =>
                  cases startHighEq : spatial.positions[startHigh]? with
                  | none =>
                      simp [startEq, endEq, SpatialConfiguration.pointAt?,
                        axisStartEq, axisEndEq, startHighEq]
                  | some startHighPoint =>
                      cases endHighEq : spatial.positions[endHigh]? with
                      | none =>
                          simp [startEq, endEq, SpatialConfiguration.pointAt?,
                            axisStartEq, axisEndEq, endHighEq]
                      | some endHighPoint =>
                          simp [startEq, endEq, SpatialConfiguration.pointAt?,
                            axisStartEq, axisEndEq, startHighEq, endHighEq,
                            axialDescriptorOfSpatialReferences?_orientationReversingAffine,
                            orientationReversing]

/-- Reflect the externally supplied handedness bit of an axial observation without changing its
molecular roles. -/
def IndexedAxialGeometryObservation.mirrorSense
    (record : IndexedAxialGeometryObservation) : IndexedAxialGeometryObservation :=
  { record with sense := record.sense.mirror }

@[simp] theorem IndexedAxialGeometryObservation.mirrorSense_sense
    (record : IndexedAxialGeometryObservation) :
    record.mirrorSense.sense = record.sense.mirror := rfl

@[simp] theorem ChemistryNormalizationResult.axialObservationSpatialDescriptor?_mirrorSense
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation) :
    result.axialObservationSpatialDescriptor? spatial record.mirrorSense =
      result.axialObservationSpatialDescriptor? spatial record := by
  rfl

/-- Agreement between a supplied axial sense and the independently recomputed coordinate
descriptor is itself invariant under an orientation-preserving affine frame change. -/
theorem ChemistryNormalizationResult.axialObservationSpatiallyValid?_orientationPreservingAffine
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    result.axialObservationSpatiallyValid?
        (spatial.mapPoints transform.applyPoint) record =
      result.axialObservationSpatiallyValid? spatial record := by
  simp [ChemistryNormalizationResult.axialObservationSpatiallyValid?,
    result.axialObservationSpatialDescriptor?_orientationPreservingAffine
      spatial record transform orientationPreserving]

/-- Reflecting both the coordinates and the supplied axial handedness preserves exact validation.
Reflecting only one of them would correctly reverse the descriptor and need not validate. -/
theorem ChemistryNormalizationResult.axialObservationSpatiallyValid?_orientationReversingAffine_mirrorSense
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation)
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0) :
    result.axialObservationSpatiallyValid?
        (spatial.mapPoints transform.applyPoint) record.mirrorSense =
      result.axialObservationSpatiallyValid? spatial record := by
  unfold ChemistryNormalizationResult.axialObservationSpatiallyValid?
  rw [result.axialObservationSpatialDescriptor?_orientationReversingAffine
    spatial record.mirrorSense transform orientationReversing]
  simp only [result.axialObservationSpatialDescriptor?_mirrorSense spatial record,
    IndexedAxialGeometryObservation.mirrorSense_sense,
    AxialDescriptor.ofSense_mirror]
  generalize computedEq : result.axialObservationSpatialDescriptor? spatial record = computed
  cases computed with
  | none => rfl
  | some descriptor => cases descriptor <;> cases record.sense <;> rfl

/-- The complete ordered-path terminal-reference helical evaluator is invariant under every
orientation-preserving rational affine change of frame, including missing and zero-turn refusal. -/
theorem IndexedHelicalGeometryObservation.spatialDescriptor?_orientationPreservingAffine
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    record.spatialDescriptor? (spatial.mapPoints transform.applyPoint) =
      record.spatialDescriptor? spatial := by
  unfold IndexedHelicalGeometryObservation.spatialDescriptor?
  cases endpointsEq : helicalPathEndpoints? record.helixPath with
  | none => simp
  | some endpoints =>
      cases frontEq : spatial.positions[endpoints.1]? with
      | none => simp [SpatialConfiguration.pointAt?, frontEq]
      | some frontPoint =>
          cases backEq : spatial.positions[endpoints.2]? with
          | none =>
              simp [SpatialConfiguration.pointAt?, frontEq, backEq]
          | some backPoint =>
              cases frontReferenceEq : spatial.positions[record.frontReference]? with
              | none =>
                  simp [SpatialConfiguration.pointAt?, frontReferenceEq]
              | some frontReferencePoint =>
                  cases backReferenceEq : spatial.positions[record.backReference]? with
                  | none =>
                      simp [SpatialConfiguration.pointAt?, frontReferenceEq, backReferenceEq]
                  | some backReferencePoint =>
                      simp [SpatialConfiguration.pointAt?, frontEq, backEq,
                        frontReferenceEq, backReferenceEq,
                        helicalDescriptorOfSpatialReferences?_orientationPreservingAffine,
                        orientationPreserving]

/-- A coordinate reflection mirrors the result of the complete ordered-path helical evaluator and
preserves missing-coordinate and zero-turn refusal. -/
theorem IndexedHelicalGeometryObservation.spatialDescriptor?_orientationReversingAffine
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration)
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0) :
    record.spatialDescriptor? (spatial.mapPoints transform.applyPoint) =
      (record.spatialDescriptor? spatial).map HelicalDescriptor.mirror := by
  unfold IndexedHelicalGeometryObservation.spatialDescriptor?
  cases endpointsEq : helicalPathEndpoints? record.helixPath with
  | none => simp
  | some endpoints =>
      cases frontEq : spatial.positions[endpoints.1]? with
      | none => simp [SpatialConfiguration.pointAt?, frontEq]
      | some frontPoint =>
          cases backEq : spatial.positions[endpoints.2]? with
          | none =>
              simp [SpatialConfiguration.pointAt?, frontEq, backEq]
          | some backPoint =>
              cases frontReferenceEq : spatial.positions[record.frontReference]? with
              | none =>
                  simp [SpatialConfiguration.pointAt?, frontReferenceEq]
              | some frontReferencePoint =>
                  cases backReferenceEq : spatial.positions[record.backReference]? with
                  | none =>
                      simp [SpatialConfiguration.pointAt?, frontReferenceEq, backReferenceEq]
                  | some backReferencePoint =>
                      simp [SpatialConfiguration.pointAt?, frontEq, backEq,
                        frontReferenceEq, backReferenceEq,
                        helicalDescriptorOfSpatialReferences?_orientationReversingAffine,
                        orientationReversing]

/-- Reflect the externally supplied handedness bit of a helical observation without changing its
ordered molecular path or terminal references. -/
def IndexedHelicalGeometryObservation.mirrorSense
    (record : IndexedHelicalGeometryObservation) : IndexedHelicalGeometryObservation :=
  { record with sense := record.sense.mirror }

@[simp] theorem IndexedHelicalGeometryObservation.mirrorSense_sense
    (record : IndexedHelicalGeometryObservation) :
    record.mirrorSense.sense = record.sense.mirror := rfl

@[simp] theorem IndexedHelicalGeometryObservation.spatialDescriptor?_mirrorSense
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration) :
    record.mirrorSense.spatialDescriptor? spatial = record.spatialDescriptor? spatial := by
  rfl

/-- Agreement between a supplied helical sense and its terminal-reference coordinate descriptor
is invariant under an orientation-preserving affine frame change. -/
theorem IndexedHelicalGeometryObservation.spatiallyValid?_orientationPreservingAffine
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    record.spatiallyValid? (spatial.mapPoints transform.applyPoint) =
      record.spatiallyValid? spatial := by
  simp [IndexedHelicalGeometryObservation.spatiallyValid?,
    record.spatialDescriptor?_orientationPreservingAffine
      spatial transform orientationPreserving]

/-- Reflecting both coordinates and the supplied helical handedness preserves exact validation. -/
theorem IndexedHelicalGeometryObservation.spatiallyValid?_orientationReversingAffine_mirrorSense
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration)
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0) :
    record.mirrorSense.spatiallyValid? (spatial.mapPoints transform.applyPoint) =
      record.spatiallyValid? spatial := by
  unfold IndexedHelicalGeometryObservation.spatiallyValid?
  rw [record.mirrorSense.spatialDescriptor?_orientationReversingAffine
    spatial transform orientationReversing]
  simp only [record.spatialDescriptor?_mirrorSense spatial,
    IndexedHelicalGeometryObservation.mirrorSense_sense,
    HelicalDescriptor.ofSense_mirror]
  generalize computedEq : record.spatialDescriptor? spatial = computed
  cases computed with
  | none => rfl
  | some descriptor => cases descriptor <;> cases record.sense <;> rfl

/-- The complete source-shaped planar assignment—not only its determinant helper—is invariant
under every rational affine coordinate-frame change with positive determinant.  Molecular frame
validation and CIP priority are untouched; all point collection, coplanarity, descriptor, and
refusal branches agree. -/
theorem ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?_orientationPreservingAffine
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    result.planarDerivedTetrahedronAssignment?
        (spatial.mapPoints transform.applyPoint) record =
      result.planarDerivedTetrahedronAssignment? spatial record := by
  unfold ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?
  by_cases frameAccepted : result.planarDerivedMolecularFrameOK? record = true
  · rw [if_pos frameAccepted, if_pos frameAccepted]
    generalize referencesEq : strictReferencePairOfDecision?
      (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
        result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
        record.pilotAtom record.firstReference record.secondReference)
      record.firstReference record.secondReference = references
    cases references with
    | none => simp [referencesEq]
    | some references =>
        cases highEq : spatial.positions[references.1]? with
        | none => simp [referencesEq, highEq]
        | some highPoint =>
            cases lowEq : spatial.positions[references.2]? with
            | none => simp [referencesEq, highEq, lowEq]
            | some lowPoint =>
                cases yEq : spatial.positions[record.inPlaneBondAtom]? with
                | none => simp [referencesEq, yEq]
                | some yPoint =>
                    cases zEq : spatial.positions[record.outOfPlaneAtom]? with
                    | none => simp [referencesEq, yEq, zEq]
                    | some zPoint =>
                        cases planeEq : record.planeAtoms.mapM
                            (fun atom => spatial.positions[atom]?) with
                        | none =>
                            have mappedPlaneEq :
                                record.planeAtoms.mapM (fun atom =>
                                    (spatial.mapPoints
                                      transform.applyPoint).positions[atom]?) = none := by
                              rw [SpatialConfiguration.mapM_positions_mapPoints, planeEq]
                              rfl
                            have optionMappedPlaneEq :
                                record.planeAtoms.mapM (fun atom =>
                                    spatial.positions[atom]?.map transform.applyPoint) = none := by
                              simpa only [SpatialConfiguration.mapPoints_position] using
                                mappedPlaneEq
                            simp [referencesEq, yEq, zEq, optionMappedPlaneEq]
                        | some planePoints =>
                            have mappedPlaneEq :
                                record.planeAtoms.mapM (fun atom =>
                                    (spatial.mapPoints
                                      transform.applyPoint).positions[atom]?) =
                                  some (planePoints.map transform.applyPoint) := by
                              rw [SpatialConfiguration.mapM_positions_mapPoints, planeEq]
                              rfl
                            have optionMappedPlaneEq :
                                record.planeAtoms.mapM (fun atom =>
                                    spatial.positions[atom]?.map transform.applyPoint) =
                                  some (planePoints.map transform.applyPoint) := by
                              simpa only [SpatialConfiguration.mapPoints_position] using
                                mappedPlaneEq
                            have transformedCoplanarityPoint
                                (point : CartesianPoint3) :
                                CartesianPoint3.orientedVolume
                                    (transform.applyPoint highPoint)
                                    (transform.applyPoint lowPoint)
                                    (transform.applyPoint yPoint)
                                    (transform.applyPoint point) = 0 ↔
                                  CartesianPoint3.orientedVolume
                                    highPoint lowPoint yPoint point = 0 := by
                              rw [
                                RationalAffineFrameTransform.orientedVolume_applyPoint]
                              constructor
                              · intro zero
                                exact (mul_eq_zero.mp zero).resolve_left
                                  (ne_of_gt orientationPreserving)
                              · intro zero
                                simp [zero]
                            simp [referencesEq, highEq, lowEq, yEq, zEq,
                              optionMappedPlaneEq,
                              transformedCoplanarityPoint,
                              planarDescriptorOfDerivedTetrahedron?_orientationPreservingAffine,
                              orientationPreserving]
  · rw [if_neg frameAccepted, if_neg frameAccepted]

/-- Mirror only a planar outcome while retaining the stereogenic-unit identity.  The fallback
cases make this a total typed map; the source-shaped planar evaluator below can produce only the
planar case. -/
def StereoAssignment.mirrorPlanarDescriptor (assignment : StereoAssignment) : StereoAssignment :=
  match assignment.outcome with
  | .planar descriptor =>
      { assignment with outcome := .planar descriptor.mirror }
  | _ => assignment

@[simp] theorem StereoAssignment.mirrorPlanarDescriptor_planar
    (unit : StereoUnit) (descriptor : PlanarDescriptor) :
    ({ unit := unit, outcome := StereoOutcome.planar descriptor } : StereoAssignment).mirrorPlanarDescriptor =
      { unit := unit, outcome := StereoOutcome.planar descriptor.mirror } := rfl

/-- A negative-determinant rational affine transform mirrors the complete source-shaped planar
assignment. Molecular validation, priority, missing-coordinate refusal, and coplanarity refusal
are preserved; every successful `Rₚ/Sₚ` result is exchanged. -/
theorem ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?_orientationReversingAffine
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0) :
    result.planarDerivedTetrahedronAssignment?
        (spatial.mapPoints transform.applyPoint) record =
      (result.planarDerivedTetrahedronAssignment? spatial record).map
        StereoAssignment.mirrorPlanarDescriptor := by
  unfold ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?
  by_cases frameAccepted : result.planarDerivedMolecularFrameOK? record = true
  · rw [if_pos frameAccepted, if_pos frameAccepted]
    generalize referencesEq : strictReferencePairOfDecision?
      (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
        result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
        record.pilotAtom record.firstReference record.secondReference)
      record.firstReference record.secondReference = references
    cases references with
    | none => simp [referencesEq]
    | some references =>
        cases highEq : spatial.positions[references.1]? with
        | none => simp [referencesEq, highEq]
        | some highPoint =>
            cases lowEq : spatial.positions[references.2]? with
            | none => simp [referencesEq, highEq, lowEq]
            | some lowPoint =>
                cases yEq : spatial.positions[record.inPlaneBondAtom]? with
                | none => simp [referencesEq, yEq]
                | some yPoint =>
                    cases zEq : spatial.positions[record.outOfPlaneAtom]? with
                    | none => simp [referencesEq, yEq, zEq]
                    | some zPoint =>
                        cases planeEq : record.planeAtoms.mapM
                            (fun atom => spatial.positions[atom]?) with
                        | none =>
                            have mappedPlaneEq :
                                record.planeAtoms.mapM (fun atom =>
                                    (spatial.mapPoints
                                      transform.applyPoint).positions[atom]?) = none := by
                              rw [SpatialConfiguration.mapM_positions_mapPoints, planeEq]
                              rfl
                            have optionMappedPlaneEq :
                                record.planeAtoms.mapM (fun atom =>
                                    spatial.positions[atom]?.map transform.applyPoint) = none := by
                              simpa only [SpatialConfiguration.mapPoints_position] using
                                mappedPlaneEq
                            simp [referencesEq, yEq, zEq, optionMappedPlaneEq]
                        | some planePoints =>
                            have mappedPlaneEq :
                                record.planeAtoms.mapM (fun atom =>
                                    (spatial.mapPoints
                                      transform.applyPoint).positions[atom]?) =
                                  some (planePoints.map transform.applyPoint) := by
                              rw [SpatialConfiguration.mapM_positions_mapPoints, planeEq]
                              rfl
                            have optionMappedPlaneEq :
                                record.planeAtoms.mapM (fun atom =>
                                    spatial.positions[atom]?.map transform.applyPoint) =
                                  some (planePoints.map transform.applyPoint) := by
                              simpa only [SpatialConfiguration.mapPoints_position] using
                                mappedPlaneEq
                            have transformedCoplanarityPoint
                                (point : CartesianPoint3) :
                                CartesianPoint3.orientedVolume
                                    (transform.applyPoint highPoint)
                                    (transform.applyPoint lowPoint)
                                    (transform.applyPoint yPoint)
                                    (transform.applyPoint point) = 0 ↔
                                  CartesianPoint3.orientedVolume
                                    highPoint lowPoint yPoint point = 0 := by
                              rw [
                                RationalAffineFrameTransform.orientedVolume_applyPoint]
                              constructor
                              · intro zero
                                exact (mul_eq_zero.mp zero).resolve_left
                                  (ne_of_lt orientationReversing)
                              · intro zero
                                simp [zero]
                            have descriptorAssignmentMap :
                                ((planarDescriptorOfDerivedTetrahedron?
                                    highPoint lowPoint yPoint zPoint).map
                                  PlanarDescriptor.mirror).bind (fun descriptor =>
                                    some { unit := StereoUnit.plane record.planeAtoms
                                           outcome := StereoOutcome.planar descriptor }) =
                                  ((planarDescriptorOfDerivedTetrahedron?
                                    highPoint lowPoint yPoint zPoint).bind (fun descriptor =>
                                      some { unit := StereoUnit.plane record.planeAtoms
                                             outcome := StereoOutcome.planar descriptor })).map
                                    StereoAssignment.mirrorPlanarDescriptor := by
                              cases descriptorEq : planarDescriptorOfDerivedTetrahedron?
                                  highPoint lowPoint yPoint zPoint <;>
                                simp [StereoAssignment.mirrorPlanarDescriptor]
                            simp [referencesEq, highEq, lowEq, yEq, zEq,
                              optionMappedPlaneEq,
                              transformedCoplanarityPoint,
                              planarDescriptorOfDerivedTetrahedron?_orientationReversingAffine,
                              orientationReversing, descriptorAssignmentMap,
                              StereoAssignment.mirrorPlanarDescriptor]
                            by_cases coplanar : ∀ point ∈ planePoints,
                              CartesianPoint3.orientedVolume
                                highPoint lowPoint yPoint point = 0
                            · simp only [if_pos coplanar]
                              cases descriptorEq : planarDescriptorOfDerivedTetrahedron?
                                  highPoint lowPoint yPoint zPoint <;>
                                simp [StereoAssignment.mirrorPlanarDescriptor]
                            · simp [coplanar]
  · simp [if_neg frameAccepted]

/-- P-93.5.5.1 preferred cyclophane-plane naming inherits the complete affine-frame
invariance of its source-shaped planar assignment.  In particular, a change of origin,
orientation-preserving shear, rotation, or positive change of coordinate units cannot change
either refusal or the preferred `P/M` result. -/
theorem ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor?_orientationPreservingAffine
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedCyclophanePlanarNamingObservation)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    result.preferredCyclophanePlanarDescriptor?
        (spatial.mapPoints transform.applyPoint) record =
      result.preferredCyclophanePlanarDescriptor? spatial record := by
  unfold ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor?
  rw [result.planarDerivedTetrahedronAssignment?_orientationPreservingAffine
    spatial record.planar transform orientationPreserving]

/-- Coordinate reflection mirrors the preferred P-93.5.5.1 cyclophane-plane name, while all
applicability and refusal branches remain refusal. -/
theorem ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor?_orientationReversingAffine
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedCyclophanePlanarNamingObservation)
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0) :
    result.preferredCyclophanePlanarDescriptor?
        (spatial.mapPoints transform.applyPoint) record =
      (result.preferredCyclophanePlanarDescriptor? spatial record).map
        BlueBookP93.Cyclic.CyclophanePlaneDescriptor.mirror := by
  unfold ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor?
  rw [result.planarDerivedTetrahedronAssignment?_orientationReversingAffine
    spatial record.planar transform orientationReversing]
  by_cases locantAccepted : record.locantIsCompositeRingLocantViewedFromPilotAtom
  · simp only [if_pos locantAccepted]
    generalize assignmentEq : result.planarDerivedTetrahedronAssignment?
      spatial record.planar = assignment
    cases assignment with
    | none => rfl
    | some assignment =>
        cases outcomeEq : assignment.outcome <;>
          simp [StereoAssignment.mirrorPlanarDescriptor, outcomeEq,
            BlueBookP93.Cyclic.preferredOfGeneralPlanar_mirror]
  · simp [locantAccepted]

/-- The axial observation filter retains exactly the same records in every
orientation-preserving rational affine coordinate frame. -/
theorem IndexedCIPGeometryObservations.withSpatiallyValidatedAxes_orientationPreservingAffine
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    observations.withSpatiallyValidatedAxes result
        (spatial.mapPoints transform.applyPoint) =
      observations.withSpatiallyValidatedAxes result spatial := by
  simp [IndexedCIPGeometryObservations.withSpatiallyValidatedAxes,
    result.axialObservationSpatiallyValid?_orientationPreservingAffine
      spatial _ transform orientationPreserving]

/-- Simultaneous axial/helical validation retains exactly the same observation structure in every
orientation-preserving rational affine coordinate frame. -/
theorem IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices_orientationPreservingAffine
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    observations.withSpatiallyValidatedAxesAndHelices result
        (spatial.mapPoints transform.applyPoint) =
      observations.withSpatiallyValidatedAxesAndHelices result spatial := by
  simp [IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices,
    IndexedCIPGeometryObservations.withSpatiallyValidatedAxes,
    result.axialObservationSpatiallyValid?_orientationPreservingAffine
      spatial _ transform orientationPreserving,
    IndexedHelicalGeometryObservation.spatiallyValid?_orientationPreservingAffine
      _ spatial transform orientationPreserving]

/-- Removing legacy raw planar senses after coordinate validation is frame-independent. -/
theorem IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation_orientationPreservingAffine
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    observations.withoutRawPlanesAfterSpatialValidation result
        (spatial.mapPoints transform.applyPoint) =
      observations.withoutRawPlanesAfterSpatialValidation result spatial := by
  rw [IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation,
    IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation,
    observations.withSpatiallyValidatedAxesAndHelices_orientationPreservingAffine
      result spatial transform orientationPreserving]

/-- End-to-end equality for the public joined exact-spatial analyzer: a positive-determinant
rational affine change of coordinates changes neither the output list nor its order, conflict
resolution, refusals, or any emitted descriptor. -/
theorem analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_orientationPreservingAffine
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry certified
        (spatial.mapPoints transform.applyPoint) observations derivedPlanes =
      analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry certified
        spatial observations derivedPlanes := by
  have candidatesEq :
      derivedPlanes.filterMap
          (certified.result.planarDerivedTetrahedronAssignment?
            (spatial.mapPoints transform.applyPoint)) =
        derivedPlanes.filterMap
          (certified.result.planarDerivedTetrahedronAssignment? spatial) := by
    induction derivedPlanes with
    | nil => rfl
    | cons record tail ih =>
        simp only [List.filterMap_cons]
        rw [certified.result.planarDerivedTetrahedronAssignment?_orientationPreservingAffine
          spatial record transform orientationPreserving, ih]
  have baseEq :
      derivedPlanarSpatialBaseAssignments certified
          (spatial.mapPoints transform.applyPoint) observations =
        derivedPlanarSpatialBaseAssignments certified spatial observations := by
    unfold derivedPlanarSpatialBaseAssignments
    rw [observations.withoutRawPlanesAfterSpatialValidation_orientationPreservingAffine
      certified.result spatial transform orientationPreserving]
  have derivedEq :
      certified.result.derivedPlanarSpatialAssignments
          (spatial.mapPoints transform.applyPoint) derivedPlanes =
        certified.result.derivedPlanarSpatialAssignments spatial derivedPlanes := by
    unfold ChemistryNormalizationResult.derivedPlanarSpatialAssignments
    rw [candidatesEq]
  unfold analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
  rw [baseEq, derivedEq]

end TetraStereo.OneCenter
