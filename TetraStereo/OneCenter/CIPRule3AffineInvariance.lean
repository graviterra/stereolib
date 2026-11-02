import TetraStereo.OneCenter.CIPExactSpatialFrameInvariance

set_option autoImplicit false

/-!
# Invertible-affine invariance of exact Rule-3 side geometry

Although a dot product of cross products is not invariant under a general affine map off the
accepted domain, the Rule-3 evaluator first requires exact coplanarity. On that domain the right
reference arm is a linear combination of the bond axis and the left reference arm, so the side
product is the linear-combination coefficient times a strictly positive squared-normal factor.
Every invertible affine map preserves that coefficient and keeps the new squared-normal factor
strictly positive. Hence `seqCis`, `seqTrans`, and every refusal branch are preserved by arbitrary
invertible rational affine maps, including shears and reflections.
-/

namespace TetraStereo.OneCenter

namespace AuthoritativeChemicalInput

/-- Change only the exact spatial coordinate frame of an authoritative input. Constitution and
diagram evidence are retained verbatim. -/
def mapSpatialPoints (input : AuthoritativeChemicalInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) : AuthoritativeChemicalInput :=
  { input with spatial? := input.spatial?.map fun spatial => spatial.mapPoints mapPoint }

/-- Mapping points preserves the format-neutral structural admission certificate because it does
not change the molecule, diagram indices, or the number of stored spatial positions. -/
theorem mapSpatialPoints_structurallyWellFormed
    (input : AuthoritativeChemicalInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (wellFormed : input.StructurallyWellFormed) :
    (input.mapSpatialPoints mapPoint).StructurallyWellFormed := by
  rcases wellFormed with ⟨moleculeWellFormed, spatialWellFormed, diagramWellFormed⟩
  refine ⟨moleculeWellFormed, ?_, diagramWellFormed⟩
  cases spatialEq : input.spatial? with
  | none => simp [mapSpatialPoints, SpatialIndicesWellFormed, spatialEq]
  | some spatial =>
      have lengthEq : spatial.positions.length = input.molecule.atomCount := by
        simpa [SpatialIndicesWellFormed, spatialEq] using spatialWellFormed
      simpa [mapSpatialPoints, SpatialIndicesWellFormed, spatialEq,
        SpatialConfiguration.mapPoints] using lengthEq

end AuthoritativeChemicalInput

namespace CertifiedAuthoritativeChemicalInput

/-- Transport a certified authoritative input across a point map without re-running admission. -/
def mapSpatialPoints (certified : CertifiedAuthoritativeChemicalInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) : CertifiedAuthoritativeChemicalInput :=
  { input := certified.input.mapSpatialPoints mapPoint
    structurallyWellFormed := certified.input.mapSpatialPoints_structurallyWellFormed
      mapPoint certified.structurallyWellFormed }

end CertifiedAuthoritativeChemicalInput

namespace CertifiedLocalizedCIPInput

/-- Transport a localized CIP input across a coordinate-frame map. Its molecular graph and graph
admission proof are definitionally unchanged. -/
def mapSpatialPoints (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) : CertifiedLocalizedCIPInput :=
  { certified := input.certified.mapSpatialPoints mapPoint
    graphReady := input.graphReady }

@[simp] theorem spatialPointAt?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (atom : input.Atom) :
    (input.mapSpatialPoints mapPoint).spatialPointAt? atom =
      (input.spatialPointAt? atom).map mapPoint := by
  unfold CertifiedLocalizedCIPInput.mapSpatialPoints
    CertifiedAuthoritativeChemicalInput.mapSpatialPoints
    AuthoritativeChemicalInput.mapSpatialPoints spatialPointAt?
  change (input.certified.input.spatial?.map
      (fun spatial => spatial.mapPoints mapPoint) >>= fun spatial =>
        spatial.positions[atom.val]?) =
    (input.certified.input.spatial? >>= fun spatial =>
      spatial.positions[atom.val]?).map mapPoint
  cases input.certified.input.spatial? <;>
    simp [SpatialConfiguration.mapPoints_position]

@[simp] theorem moleculeGraph_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).moleculeGraph = input.moleculeGraph := by
  rfl

@[simp] theorem atomCount_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).certified.input.molecule.atomCount =
      input.certified.input.molecule.atomCount := by
  rfl

@[simp] theorem localizedRule3ExplicitSubstituents_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (endpoint partner : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedRule3ExplicitSubstituents endpoint partner =
      input.localizedRule3ExplicitSubstituents endpoint partner := by
  rfl

@[simp] theorem executableOfficialNeighborCopies_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (atom : input.Atom) :
    (input.mapSpatialPoints mapPoint).executableOfficialNeighborCopies atom =
      input.executableOfficialNeighborCopies atom := by
  unfold executableOfficialNeighborCopies
  rw [moleculeGraph_mapSpatialPoints]
  rfl

@[simp] theorem executableOfficialChildCopies_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (node : OfficialCIPNode input.Atom) :
    (input.mapSpatialPoints mapPoint).executableOfficialChildCopies node =
      input.executableOfficialChildCopies node := by
  unfold executableOfficialChildCopies
  cases node.current? with
  | none => rfl
  | some current =>
      cases node.parent? with
      | none => simp only [executableOfficialNeighborCopies_mapSpatialPoints]
      | some parent =>
          simp only [executableOfficialNeighborCopies_mapSpatialPoints]
          rfl

@[simp] theorem executableOfficialCIPChildren_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (node : OfficialCIPNode input.Atom) :
    (input.mapSpatialPoints mapPoint).executableOfficialCIPChildren node =
      input.executableOfficialCIPChildren node := by
  unfold executableOfficialCIPChildren
  rw [executableOfficialChildCopies_mapSpatialPoints]
  rfl

@[simp] theorem buildExecutableOfficialRuleMajorKey_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (fuel : ℕ) (node : OfficialCIPNode input.Atom) :
    (input.mapSpatialPoints mapPoint).buildExecutableOfficialRuleMajorKey fuel node =
      input.buildExecutableOfficialRuleMajorKey fuel node := by
  unfold buildExecutableOfficialRuleMajorKey
  rw [moleculeGraph_mapSpatialPoints]
  have childrenEq :
      (input.mapSpatialPoints mapPoint).executableOfficialCIPChildren =
        input.executableOfficialCIPChildren := by
    funext current
    exact executableOfficialCIPChildren_mapSpatialPoints input mapPoint current
  rw [childrenEq]

@[simp] theorem localizedRule3BranchKey?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (endpoint reference : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedRule3BranchKey? endpoint reference =
      input.localizedRule3BranchKey? endpoint reference := by
  unfold localizedRule3BranchKey?
  simp only [atomCount_mapSpatialPoints,
    buildExecutableOfficialRuleMajorKey_mapSpatialPoints]

@[simp] theorem localizedRule3ConstitutionalSeniorReference?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (endpoint partner : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedRule3ConstitutionalSeniorReference?
        endpoint partner =
      input.localizedRule3ConstitutionalSeniorReference? endpoint partner := by
  unfold localizedRule3ConstitutionalSeniorReference?
  rw [localizedRule3ExplicitSubstituents_mapSpatialPoints]
  generalize candidatesEq :
      input.localizedRule3ExplicitSubstituents endpoint partner = candidates
  cases candidates with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second tail =>
          cases tail with
          | cons third tail => simp
          | nil =>
              simp only [localizedRule3BranchKey?_mapSpatialPoints]
              cases input.localizedRule3BranchKey? endpoint first with
              | none => rfl
              | some firstKey =>
                  cases input.localizedRule3BranchKey? endpoint second with
                  | none => rfl
                  | some secondKey =>
                      cases firstKey.compare? secondKey with
                      | none => rfl
                      | some comparison => cases comparison <;> rfl

end CertifiedLocalizedCIPInput

namespace RationalVector3

def IsLinearCombination (right axis left : RationalVector3) (alpha beta : ℚ) : Prop :=
  right.x = alpha * axis.x + beta * left.x ∧
  right.y = alpha * axis.y + beta * left.y ∧
  right.z = alpha * axis.z + beta * left.z

def CrossNonzero (axis left : RationalVector3) : Prop :=
  (cross axis left).x ≠ 0 ∨ (cross axis left).y ≠ 0 ∨ (cross axis left).z ≠ 0

theorem dot_cross_self_pos (axis left : RationalVector3)
    (nonzero : CrossNonzero axis left) :
    0 < dot (cross axis left) (cross axis left) := by
  unfold CrossNonzero at nonzero
  unfold cross at nonzero
  unfold cross dot
  dsimp at nonzero ⊢
  rcases nonzero with xNonzero | yNonzero | zNonzero
  · nlinarith [mul_self_pos.mpr xNonzero,
      sq_nonneg (axis.z * left.x - axis.x * left.z),
      sq_nonneg (axis.x * left.y - axis.y * left.x)]
  · nlinarith [sq_nonneg (axis.y * left.z - axis.z * left.y),
      mul_self_pos.mpr yNonzero,
      sq_nonneg (axis.x * left.y - axis.y * left.x)]
  · nlinarith [sq_nonneg (axis.y * left.z - axis.z * left.y),
      sq_nonneg (axis.z * left.x - axis.x * left.z),
      mul_self_pos.mpr zNonzero]

theorem dot_cross_right_of_linearCombination
    (axis left right : RationalVector3) (alpha beta : ℚ)
    (combination : IsLinearCombination right axis left alpha beta) :
    dot (cross axis left) (cross axis right) =
      beta * dot (cross axis left) (cross axis left) := by
  rcases combination with ⟨rightX, rightY, rightZ⟩
  unfold cross dot
  dsimp
  rw [rightX, rightY, rightZ]
  ring

theorem exists_linearCombination_of_coplanar_of_crossNonzero
    (axis left right : RationalVector3)
    (coplanar : dot axis (cross left right) = 0)
    (nonzero : CrossNonzero axis left) :
    ∃ alpha beta, IsLinearCombination right axis left alpha beta := by
  rcases nonzero with xNonzero | yNonzero | zNonzero
  · have denominatorNonzero : left.z * axis.y - left.y * axis.z ≠ 0 := by
      simpa only [cross, mul_comm] using xNonzero
    refine ⟨(right.y * left.z - right.z * left.y) /
        (left.z * axis.y - left.y * axis.z),
      (axis.y * right.z - axis.z * right.y) /
        (left.z * axis.y - left.y * axis.z), ?_⟩
    unfold IsLinearCombination
    constructor
    · dsimp
      field_simp [denominatorNonzero]
      unfold dot cross at coplanar
      dsimp at coplanar
      nlinarith
    · constructor <;> dsimp <;>
        field_simp [denominatorNonzero] <;> ring
  · have denominatorNonzero : left.x * axis.z - left.z * axis.x ≠ 0 := by
      simpa only [cross, mul_comm] using yNonzero
    refine ⟨(right.z * left.x - right.x * left.z) /
        (left.x * axis.z - left.z * axis.x),
      (axis.z * right.x - axis.x * right.z) /
        (left.x * axis.z - left.z * axis.x), ?_⟩
    unfold IsLinearCombination
    constructor
    · dsimp
      field_simp [denominatorNonzero]
      ring
    · constructor
      · dsimp
        field_simp [denominatorNonzero]
        unfold dot cross at coplanar
        dsimp at coplanar
        nlinarith
      · dsimp
        field_simp [denominatorNonzero]
        ring
  · have denominatorNonzero : left.y * axis.x - left.x * axis.y ≠ 0 := by
      simpa only [cross, mul_comm] using zNonzero
    refine ⟨(right.x * left.y - right.y * left.x) /
        (left.y * axis.x - left.x * axis.y),
      (axis.x * right.y - axis.y * right.x) /
        (left.y * axis.x - left.x * axis.y), ?_⟩
    unfold IsLinearCombination
    constructor
    · dsimp
      field_simp [denominatorNonzero]
      ring
    · constructor
      · dsimp
        field_simp [denominatorNonzero]
        ring
      · dsimp
        field_simp [denominatorNonzero]
        unfold dot cross at coplanar
        dsimp at coplanar
        nlinarith

end RationalVector3

namespace RationalAffineFrameTransform

def applyVector (transform : RationalAffineFrameTransform)
    (vector : RationalVector3) : RationalVector3 :=
  { x := transform.m00 * vector.x + transform.m01 * vector.y +
      transform.m02 * vector.z
    y := transform.m10 * vector.x + transform.m11 * vector.y +
      transform.m12 * vector.z
    z := transform.m20 * vector.x + transform.m21 * vector.y +
      transform.m22 * vector.z }

theorem applyVector_preserves_linearCombination
    (transform : RationalAffineFrameTransform)
    (right axis left : RationalVector3) (alpha beta : ℚ)
    (combination : RationalVector3.IsLinearCombination right axis left alpha beta) :
    RationalVector3.IsLinearCombination (transform.applyVector right)
      (transform.applyVector axis) (transform.applyVector left) alpha beta := by
  rcases combination with ⟨rightX, rightY, rightZ⟩
  unfold RationalVector3.IsLinearCombination applyVector
  dsimp
  rw [rightX, rightY, rightZ]
  constructor
  · ring
  constructor <;> ring

theorem cross_applyVector_components
    (transform : RationalAffineFrameTransform) (axis left : RationalVector3) :
    let original := RationalVector3.cross axis left
    let transformed := RationalVector3.cross
      (transform.applyVector axis) (transform.applyVector left)
    transformed.x =
        (transform.m11 * transform.m22 - transform.m12 * transform.m21) * original.x +
        (transform.m12 * transform.m20 - transform.m10 * transform.m22) * original.y +
        (transform.m10 * transform.m21 - transform.m11 * transform.m20) * original.z ∧
      transformed.y =
        (transform.m02 * transform.m21 - transform.m01 * transform.m22) * original.x +
        (transform.m00 * transform.m22 - transform.m02 * transform.m20) * original.y +
        (transform.m01 * transform.m20 - transform.m00 * transform.m21) * original.z ∧
      transformed.z =
        (transform.m01 * transform.m12 - transform.m02 * transform.m11) * original.x +
        (transform.m02 * transform.m10 - transform.m00 * transform.m12) * original.y +
        (transform.m00 * transform.m11 - transform.m01 * transform.m10) * original.z := by
  simp [applyVector, RationalVector3.cross]
  constructor
  · ring
  constructor <;> ring

theorem determinant_mul_cross_components
    (transform : RationalAffineFrameTransform) (axis left : RationalVector3) :
    let transformed := RationalVector3.cross
      (transform.applyVector axis) (transform.applyVector left)
    transform.determinant * (RationalVector3.cross axis left).x =
        transform.m00 * transformed.x + transform.m10 * transformed.y +
          transform.m20 * transformed.z ∧
      transform.determinant * (RationalVector3.cross axis left).y =
        transform.m01 * transformed.x + transform.m11 * transformed.y +
          transform.m21 * transformed.z ∧
      transform.determinant * (RationalVector3.cross axis left).z =
        transform.m02 * transformed.x + transform.m12 * transformed.y +
          transform.m22 * transformed.z := by
  simp [applyVector, determinant, RationalVector3.cross]
  constructor
  · ring
  constructor <;> ring

theorem crossNonzero_applyVector
    (transform : RationalAffineFrameTransform) (axis left : RationalVector3)
    (determinantNonzero : transform.determinant ≠ 0)
    (nonzero : RationalVector3.CrossNonzero axis left) :
    RationalVector3.CrossNonzero (transform.applyVector axis)
      (transform.applyVector left) := by
  by_contra transformedZero
  unfold RationalVector3.CrossNonzero at transformedZero
  simp only [not_or, not_ne_iff] at transformedZero
  rcases transformedZero with ⟨transformedX, transformedY, transformedZ⟩
  have identities := transform.determinant_mul_cross_components axis left
  rcases identities with ⟨identityX, identityY, identityZ⟩
  rw [transformedX, transformedY, transformedZ] at identityX identityY identityZ
  have originalX : (RationalVector3.cross axis left).x = 0 :=
    (mul_eq_zero.mp (by simpa using identityX)).resolve_left determinantNonzero
  have originalY : (RationalVector3.cross axis left).y = 0 :=
    (mul_eq_zero.mp (by simpa using identityY)).resolve_left determinantNonzero
  have originalZ : (RationalVector3.cross axis left).z = 0 :=
    (mul_eq_zero.mp (by simpa using identityZ)).resolve_left determinantNonzero
  rcases nonzero with xNonzero | yNonzero | zNonzero
  · exact xNonzero originalX
  · exact yNonzero originalY
  · exact zNonzero originalZ

theorem not_crossNonzero_applyVector
    (transform : RationalAffineFrameTransform) (axis left : RationalVector3)
    (zero : ¬ RationalVector3.CrossNonzero axis left) :
    ¬ RationalVector3.CrossNonzero (transform.applyVector axis)
      (transform.applyVector left) := by
  unfold RationalVector3.CrossNonzero at zero ⊢
  simp only [not_or, not_ne_iff] at zero ⊢
  rcases zero with ⟨originalX, originalY, originalZ⟩
  rcases transform.cross_applyVector_components axis left with
    ⟨transformedX, transformedY, transformedZ⟩
  simp [originalX, originalY, originalZ] at transformedX transformedY transformedZ
  exact ⟨transformedX, transformedY, transformedZ⟩

end RationalAffineFrameTransform

namespace CartesianPoint3

theorem displacement_applyPoint
    (transform : RationalAffineFrameTransform) (source target : CartesianPoint3) :
    displacement (transform.applyPoint source) (transform.applyPoint target) =
      transform.applyVector (displacement source target) := by
  cases source
  cases target
  simp [RationalAffineFrameTransform.applyPoint,
    RationalAffineFrameTransform.applyVector, displacement]
  constructor
  · ring
  constructor <;> ring

theorem rule3Coplanarity_applyPoint
    (transform : RationalAffineFrameTransform)
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    rule3Coplanarity (transform.applyPoint leftEndpoint)
        (transform.applyPoint rightEndpoint) (transform.applyPoint leftReference)
        (transform.applyPoint rightReference) =
      transform.determinant *
        rule3Coplanarity leftEndpoint rightEndpoint leftReference rightReference := by
  simp [RationalAffineFrameTransform.applyPoint,
    RationalAffineFrameTransform.determinant, rule3Coplanarity,
    displacement, RationalVector3.dot, RationalVector3.cross]
  ring

theorem rule3SideProduct_signs_applyPoint
    (transform : RationalAffineFrameTransform)
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3)
    (determinantNonzero : transform.determinant ≠ 0)
    (coplanar : rule3Coplanarity leftEndpoint rightEndpoint
      leftReference rightReference = 0) :
    (0 < rule3SideProduct (transform.applyPoint leftEndpoint)
        (transform.applyPoint rightEndpoint) (transform.applyPoint leftReference)
        (transform.applyPoint rightReference) ↔
      0 < rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference) ∧
    (rule3SideProduct (transform.applyPoint leftEndpoint)
        (transform.applyPoint rightEndpoint) (transform.applyPoint leftReference)
        (transform.applyPoint rightReference) < 0 ↔
      rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference < 0) := by
  let axis := displacement leftEndpoint rightEndpoint
  let leftArm := displacement leftEndpoint leftReference
  let rightArm := displacement rightEndpoint rightReference
  have coplanarVectors : RationalVector3.dot axis
      (RationalVector3.cross leftArm rightArm) = 0 := by
    simpa [rule3Coplanarity, axis, leftArm, rightArm] using coplanar
  have transformedAxis :
      displacement (transform.applyPoint leftEndpoint)
          (transform.applyPoint rightEndpoint) = transform.applyVector axis := by
    simpa [axis] using displacement_applyPoint transform leftEndpoint rightEndpoint
  have transformedLeftArm :
      displacement (transform.applyPoint leftEndpoint)
          (transform.applyPoint leftReference) = transform.applyVector leftArm := by
    simpa [leftArm] using displacement_applyPoint transform leftEndpoint leftReference
  have transformedRightArm :
      displacement (transform.applyPoint rightEndpoint)
          (transform.applyPoint rightReference) = transform.applyVector rightArm := by
    simpa [rightArm] using displacement_applyPoint transform rightEndpoint rightReference
  by_cases crossNonzero : RationalVector3.CrossNonzero axis leftArm
  · obtain ⟨alpha, beta, combination⟩ :=
      RationalVector3.exists_linearCombination_of_coplanar_of_crossNonzero
        axis leftArm rightArm coplanarVectors crossNonzero
    have transformedCombination :=
      transform.applyVector_preserves_linearCombination
        rightArm axis leftArm alpha beta combination
    have originalSideEq :
        rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference =
          beta * RationalVector3.dot (RationalVector3.cross axis leftArm)
            (RationalVector3.cross axis leftArm) := by
      simpa [rule3SideProduct, axis, leftArm, rightArm] using
        RationalVector3.dot_cross_right_of_linearCombination
          axis leftArm rightArm alpha beta combination
    have transformedSideEq :
        rule3SideProduct (transform.applyPoint leftEndpoint)
            (transform.applyPoint rightEndpoint) (transform.applyPoint leftReference)
            (transform.applyPoint rightReference) =
          beta * RationalVector3.dot
            (RationalVector3.cross (transform.applyVector axis)
              (transform.applyVector leftArm))
            (RationalVector3.cross (transform.applyVector axis)
              (transform.applyVector leftArm)) := by
      rw [rule3SideProduct, transformedAxis, transformedLeftArm, transformedRightArm]
      exact RationalVector3.dot_cross_right_of_linearCombination
        (transform.applyVector axis) (transform.applyVector leftArm)
        (transform.applyVector rightArm) alpha beta transformedCombination
    have originalNormPositive :=
      RationalVector3.dot_cross_self_pos axis leftArm crossNonzero
    have transformedCrossNonzero := transform.crossNonzero_applyVector
      axis leftArm determinantNonzero crossNonzero
    have transformedNormPositive :=
      RationalVector3.dot_cross_self_pos (transform.applyVector axis)
        (transform.applyVector leftArm) transformedCrossNonzero
    rw [originalSideEq, transformedSideEq]
    constructor
    · rw [mul_pos_iff_of_pos_right transformedNormPositive,
        mul_pos_iff_of_pos_right originalNormPositive]
    · simp [mul_neg_iff, transformedNormPositive, originalNormPositive,
        not_lt_of_ge transformedNormPositive.le,
        not_lt_of_ge originalNormPositive.le]
  · have transformedCrossZero :=
      transform.not_crossNonzero_applyVector axis leftArm crossNonzero
    unfold RationalVector3.CrossNonzero at crossNonzero transformedCrossZero
    simp only [not_or, not_ne_iff] at crossNonzero transformedCrossZero
    rcases crossNonzero with ⟨originalX, originalY, originalZ⟩
    rcases transformedCrossZero with ⟨transformedX, transformedY, transformedZ⟩
    have originalSideZero :
        rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference = 0 := by
      unfold rule3SideProduct
      rw [show displacement leftEndpoint rightEndpoint = axis from rfl,
        show displacement leftEndpoint leftReference = leftArm from rfl]
      simp [RationalVector3.dot, originalX, originalY, originalZ]
    have transformedSideZero :
        rule3SideProduct (transform.applyPoint leftEndpoint)
            (transform.applyPoint rightEndpoint) (transform.applyPoint leftReference)
            (transform.applyPoint rightReference) = 0 := by
      unfold rule3SideProduct
      rw [transformedAxis, transformedLeftArm]
      simp [RationalVector3.dot, transformedX, transformedY, transformedZ]
    simp [originalSideZero, transformedSideZero]

end CartesianPoint3

/-- Unlike chiral triple-product descriptors, coplanar Rule-3 side geometry is invariant under
every invertible rational affine transform, including shears and spatial reflections. -/
theorem rule3GeometryOfSpatialReferences?_affine
    (transform : RationalAffineFrameTransform)
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3)
    (determinantNonzero : transform.determinant ≠ 0) :
    rule3GeometryOfSpatialReferences? (transform.applyPoint leftEndpoint)
        (transform.applyPoint rightEndpoint) (transform.applyPoint leftReference)
        (transform.applyPoint rightReference) =
      rule3GeometryOfSpatialReferences?
        leftEndpoint rightEndpoint leftReference rightReference := by
  apply Option.ext
  intro geometry
  rw [rule3GeometryOfSpatialReferences?_eq_some_iff,
    rule3GeometryOfSpatialReferences?_eq_some_iff]
  have coplanarityIff :
      CartesianPoint3.rule3Coplanarity (transform.applyPoint leftEndpoint)
          (transform.applyPoint rightEndpoint) (transform.applyPoint leftReference)
          (transform.applyPoint rightReference) = 0 ↔
        CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint
          leftReference rightReference = 0 := by
    rw [CartesianPoint3.rule3Coplanarity_applyPoint]
    exact mul_eq_zero.trans (or_iff_right determinantNonzero)
  cases geometry with
  | nonstereogenic => simp [RationalRule3SpatialGeometry, coplanarityIff]
  | seqcis =>
      simp only [RationalRule3SpatialGeometry]
      constructor
      · rintro ⟨transformedCoplanar, transformedPositive⟩
        have originalCoplanar := coplanarityIff.mp transformedCoplanar
        have signs := CartesianPoint3.rule3SideProduct_signs_applyPoint transform
          leftEndpoint rightEndpoint leftReference rightReference
          determinantNonzero originalCoplanar
        exact ⟨originalCoplanar, signs.1.mp transformedPositive⟩
      · rintro ⟨originalCoplanar, originalPositive⟩
        have signs := CartesianPoint3.rule3SideProduct_signs_applyPoint transform
          leftEndpoint rightEndpoint leftReference rightReference
          determinantNonzero originalCoplanar
        exact ⟨coplanarityIff.mpr originalCoplanar, signs.1.mpr originalPositive⟩
  | seqtrans =>
      simp only [RationalRule3SpatialGeometry]
      constructor
      · rintro ⟨transformedCoplanar, transformedNegative⟩
        have originalCoplanar := coplanarityIff.mp transformedCoplanar
        have signs := CartesianPoint3.rule3SideProduct_signs_applyPoint transform
          leftEndpoint rightEndpoint leftReference rightReference
          determinantNonzero originalCoplanar
        exact ⟨originalCoplanar, signs.2.mp transformedNegative⟩
      · rintro ⟨originalCoplanar, originalNegative⟩
        have signs := CartesianPoint3.rule3SideProduct_signs_applyPoint transform
          leftEndpoint rightEndpoint leftReference rightReference
          determinantNonzero originalCoplanar
        exact ⟨coplanarityIff.mpr originalCoplanar, signs.2.mpr originalNegative⟩

namespace CertifiedLocalizedCIPInput

/-- Retype a molecule-backed Rule-3 result after changing only its input coordinate frame. -/
def LocalizedRule3SpatialUnitResult.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (result : input.LocalizedRule3SpatialUnitResult)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3SpatialUnitResult :=
  { leftReference := result.leftReference
    rightReference := result.rightReference
    geometry := result.geometry }

/-- Retype a descriptor-bearing endpoint decision after changing only the coordinate frame. -/
def LocalizedRule3EndpointPriority.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (priority : input.LocalizedRule3EndpointPriority)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3EndpointPriority :=
  match priority with
  | .senior reference => .senior reference
  | .nonstereogenic => .nonstereogenic

/-- Retype a descriptor-bearing Rule-3 result after changing only its input coordinate frame. -/
def LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (result : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3DescriptorBearingSpatialUnitResult :=
  { leftPriority := result.leftPriority.mapSpatialPoints mapPoint
    rightPriority := result.rightPriority.mapSpatialPoints mapPoint
    geometry := result.geometry }

/-- The complete molecule-backed constitutional Rule-3 subpipeline is invariant under every
invertible rational affine frame change. This includes candidate enumeration, complete branch-key
construction, strict senior-reference selection, exact coordinate lookup, spatial classification,
and every refusal branch. -/
theorem localizedRule3SpatialUnit?_affine
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3SpatialUnit? left right =
      (input.localizedRule3SpatialUnit? left right).map
        (fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedRule3SpatialUnit?
  rw [moleculeGraph_mapSpatialPoints]
  by_cases doubleBond : input.moleculeGraph.bond left right = 2
  · simp only [if_pos doubleBond]
    cases leftReferenceEq : input.localizedRule3ConstitutionalSeniorReference? left right with
    | none =>
        have mappedLeftReferenceEq :
            (input.mapSpatialPoints transform.applyPoint).localizedRule3ConstitutionalSeniorReference?
              left right = none := by
          rw [localizedRule3ConstitutionalSeniorReference?_mapSpatialPoints,
            leftReferenceEq]
        simp [mappedLeftReferenceEq]
    | some leftReference =>
        have mappedLeftReferenceEq :
            (input.mapSpatialPoints transform.applyPoint).localizedRule3ConstitutionalSeniorReference?
              left right =
              some leftReference := by
          rw [localizedRule3ConstitutionalSeniorReference?_mapSpatialPoints,
            leftReferenceEq]
        cases rightReferenceEq : input.localizedRule3ConstitutionalSeniorReference? right left with
        | none =>
            have mappedRightReferenceEq :
                (input.mapSpatialPoints transform.applyPoint).localizedRule3ConstitutionalSeniorReference?
                  right left = none := by
              rw [localizedRule3ConstitutionalSeniorReference?_mapSpatialPoints,
                rightReferenceEq]
            simp [mappedLeftReferenceEq, mappedRightReferenceEq]
        | some rightReference =>
            have mappedRightReferenceEq :
                (input.mapSpatialPoints transform.applyPoint).localizedRule3ConstitutionalSeniorReference?
                  right left =
                  some rightReference := by
              rw [localizedRule3ConstitutionalSeniorReference?_mapSpatialPoints,
                rightReferenceEq]
            cases leftPointEq : input.spatialPointAt? left with
            | none =>
                have mappedLeftPointEq :
                    (input.mapSpatialPoints transform.applyPoint).spatialPointAt? left = none := by
                  rw [spatialPointAt?_mapSpatialPoints, leftPointEq]
                  rfl
                simp [mappedLeftReferenceEq, mappedRightReferenceEq,
                  mappedLeftPointEq]
            | some leftPoint =>
                have mappedLeftPointEq :
                    (input.mapSpatialPoints transform.applyPoint).spatialPointAt? left =
                      some (transform.applyPoint leftPoint) := by
                  rw [spatialPointAt?_mapSpatialPoints, leftPointEq]
                  rfl
                cases rightPointEq : input.spatialPointAt? right with
                | none =>
                    have mappedRightPointEq :
                        (input.mapSpatialPoints transform.applyPoint).spatialPointAt? right =
                          none := by
                      rw [spatialPointAt?_mapSpatialPoints, rightPointEq]
                      rfl
                    simp [mappedLeftReferenceEq, mappedRightReferenceEq,
                      mappedLeftPointEq, mappedRightPointEq]
                | some rightPoint =>
                    have mappedRightPointEq :
                        (input.mapSpatialPoints transform.applyPoint).spatialPointAt? right =
                          some (transform.applyPoint rightPoint) := by
                      rw [spatialPointAt?_mapSpatialPoints, rightPointEq]
                      rfl
                    cases leftReferencePointEq : input.spatialPointAt? leftReference with
                    | none =>
                        have mappedLeftReferencePointEq :
                            (input.mapSpatialPoints transform.applyPoint).spatialPointAt?
                                leftReference = none := by
                          rw [spatialPointAt?_mapSpatialPoints, leftReferencePointEq]
                          rfl
                        simp [mappedLeftReferenceEq, mappedRightReferenceEq,
                          mappedLeftPointEq, mappedRightPointEq,
                          leftReferencePointEq]
                    | some leftReferencePoint =>
                        have mappedLeftReferencePointEq :
                            (input.mapSpatialPoints transform.applyPoint).spatialPointAt?
                                leftReference = some (transform.applyPoint leftReferencePoint) := by
                          rw [spatialPointAt?_mapSpatialPoints, leftReferencePointEq]
                          rfl
                        cases rightReferencePointEq : input.spatialPointAt? rightReference with
                        | none =>
                            have mappedRightReferencePointEq :
                                (input.mapSpatialPoints transform.applyPoint).spatialPointAt?
                                    rightReference = none := by
                              rw [spatialPointAt?_mapSpatialPoints, rightReferencePointEq]
                              rfl
                            simp [mappedLeftReferenceEq, mappedRightReferenceEq,
                              mappedLeftPointEq, mappedRightPointEq,
                              rightReferencePointEq]
                        | some rightReferencePoint =>
                            have mappedRightReferencePointEq :
                                (input.mapSpatialPoints transform.applyPoint).spatialPointAt?
                                    rightReference =
                                  some (transform.applyPoint rightReferencePoint) := by
                              rw [spatialPointAt?_mapSpatialPoints, rightReferencePointEq]
                              rfl
                            simp only [mappedLeftReferenceEq, mappedRightReferenceEq,
                              mappedLeftPointEq, mappedRightPointEq]
                            simp [leftReferencePointEq, rightReferencePointEq,
                              rule3GeometryOfSpatialReferences?_affine transform
                                leftPoint rightPoint leftReferencePoint rightReferencePoint
                                determinantNonzero,
                              LocalizedRule3SpatialUnitResult.mapSpatialPoints]
  · rw [if_neg doubleBond]
    simp [doubleBond]

/-- The descriptor-bearing Rule-3 spatial evaluator is affine-natural whenever the transported
occurrence keys yield the corresponding endpoint priorities. This theorem covers both Rules-4/5
resolved senior references and proved nonstereogenic endpoint ties. The remaining independent
transport obligation is exactly the naturality of the occurrence-key compiler itself. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_affine_of_priorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (transform : RationalAffineFrameTransform)
    (mappedLeftFrame mappedRightFrame :
      (input.mapSpatialPoints transform.applyPoint).LocalizedRule3EndpointKeyFrame)
    (leftPriorityInvariant :
      (input.mapSpatialPoints transform.applyPoint).localizedRule3EndpointPriority
          mappedLeftFrame =
        (input.localizedRule3EndpointPriority leftFrame).mapSpatialPoints
          transform.applyPoint)
    (rightPriorityInvariant :
      (input.mapSpatialPoints transform.applyPoint).localizedRule3EndpointPriority
          mappedRightFrame =
        (input.localizedRule3EndpointPriority rightFrame).mapSpatialPoints
          transform.applyPoint)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3DescriptorBearingSpatialUnit?
        left right mappedLeftFrame mappedRightFrame =
      (input.localizedRule3DescriptorBearingSpatialUnit?
          left right leftFrame rightFrame).map
        (fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedRule3DescriptorBearingSpatialUnit?
  rw [moleculeGraph_mapSpatialPoints]
  by_cases doubleBond : input.moleculeGraph.bond left right = 2
  · simp only [if_pos doubleBond]
    generalize leftPriorityEq : input.localizedRule3EndpointPriority leftFrame = leftPriority
    generalize rightPriorityEq : input.localizedRule3EndpointPriority rightFrame = rightPriority
    have mappedLeftPriorityEq :
        (input.mapSpatialPoints transform.applyPoint).localizedRule3EndpointPriority
            mappedLeftFrame = leftPriority.mapSpatialPoints transform.applyPoint := by
      rw [leftPriorityInvariant, leftPriorityEq]
    have mappedRightPriorityEq :
        (input.mapSpatialPoints transform.applyPoint).localizedRule3EndpointPriority
            mappedRightFrame = rightPriority.mapSpatialPoints transform.applyPoint := by
      rw [rightPriorityInvariant, rightPriorityEq]
    rw [mappedLeftPriorityEq, mappedRightPriorityEq]
    cases leftPriority with
    | nonstereogenic =>
        simp [LocalizedRule3EndpointPriority.mapSpatialPoints,
          LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints]
    | senior leftReference =>
        cases rightPriority with
        | nonstereogenic =>
            simp [LocalizedRule3EndpointPriority.mapSpatialPoints,
              LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints]
        | senior rightReference =>
            simp only [LocalizedRule3EndpointPriority.mapSpatialPoints]
            cases leftPointEq : input.spatialPointAt? left with
            | none => simp [spatialPointAt?_mapSpatialPoints, leftPointEq]
            | some leftPoint =>
                cases rightPointEq : input.spatialPointAt? right with
                | none =>
                    simp [spatialPointAt?_mapSpatialPoints, leftPointEq, rightPointEq]
                | some rightPoint =>
                    cases leftReferencePointEq : input.spatialPointAt? leftReference with
                    | none =>
                        simp [spatialPointAt?_mapSpatialPoints, leftPointEq, rightPointEq,
                          leftReferencePointEq]
                    | some leftReferencePoint =>
                        cases rightReferencePointEq : input.spatialPointAt? rightReference with
                        | none =>
                            simp [spatialPointAt?_mapSpatialPoints, leftPointEq, rightPointEq,
                              leftReferencePointEq, rightReferencePointEq]
                        | some rightReferencePoint =>
                            simp [spatialPointAt?_mapSpatialPoints, leftPointEq, rightPointEq,
                              leftReferencePointEq, rightReferencePointEq,
                              rule3GeometryOfSpatialReferences?_affine transform
                                leftPoint rightPoint leftReferencePoint rightReferencePoint
                                determinantNonzero,
                              LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints,
                              LocalizedRule3EndpointPriority.mapSpatialPoints]
  · simp [doubleBond]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
