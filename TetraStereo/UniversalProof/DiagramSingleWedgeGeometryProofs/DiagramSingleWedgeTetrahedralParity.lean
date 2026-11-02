import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6Analysis
import TetraStereo.OneCenter.AuthoritativeSemanticParserDiagramRule3Through6Analysis

set_option autoImplicit false

namespace TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs

































































open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.Rule6HandednessSemantics

/-! ## Drawing-plane points and the plain-triangle area -/

/-- The plain drawing-plane point lifted to drawing depth `0`. -/
def planePoint (point : CartesianPoint2) : CartesianPoint3 :=
  { x := point.x, y := point.y, z := 0 }

/-- The wedge endpoint lifted to the signed drawing depth `height` (positive for solid, negative
for hashed).  The `z` component is a *convention representative* of the wedge glyph, deliberately
not a measured physical depth; only its sign is consumed downstream. -/
def liftedTip (point : CartesianPoint2) (height : ℚ) : CartesianPoint3 :=
  { x := point.x, y := point.y, z := height }

@[simp] theorem planePoint_z (point : CartesianPoint2) : (planePoint point).z = 0 := rfl

@[simp] theorem liftedTip_z (point : CartesianPoint2) (height : ℚ) :
    (liftedTip point height).z = height := rfl

/-- Doubled signed area of the planar triangle through three drawing points, using only their
`x`/`y` components. -/
def plainTriangleArea (first second third : CartesianPoint3) : ℚ :=
  first.x * (second.y - third.y) + second.x * (third.y - first.y) +
    third.x * (first.y - second.y)

/-- Signed cross product of two planar vectors. -/
def planarCross (left right : CartesianPoint2) : ℚ :=
  left.x * right.y - left.y * right.x

/-- The planar edge from `center` to `point`. -/
def planarEdge (center point : CartesianPoint2) : CartesianPoint2 :=
  { x := point.x - center.x, y := point.y - center.y }

theorem planarCross_skew (left right : CartesianPoint2) :
    planarCross left right = -planarCross right left := by
  simp only [planarCross]
  ring

/-- Swapping the first two plain endpoints negates the doubled area. -/
theorem plainTriangleArea_swap (first second third : CartesianPoint3) :
    plainTriangleArea second first third = -plainTriangleArea first second third := by
  simp only [plainTriangleArea]
  ring

/-- Cyclic rotation of the three plain endpoints preserves the doubled area. -/
theorem plainTriangleArea_cycle (first second third : CartesianPoint3) :
    plainTriangleArea second third first = plainTriangleArea first second third := by
  simp only [plainTriangleArea]
  ring

/-- The plain-triangle area expands as the sum of the three consecutive edge cross products around
*any* planar anchor.  This is the exact identity behind the "surround" condition. -/
theorem plainTriangleArea_eq_cross_sum (center first second third : CartesianPoint2) :
    plainTriangleArea (planePoint first) (planePoint second) (planePoint third) =
      planarCross (planarEdge center first) (planarEdge center second) +
      planarCross (planarEdge center second) (planarEdge center third) +
      planarCross (planarEdge center third) (planarEdge center first) := by
  simp only [plainTriangleArea, planarCross, planarEdge, planePoint]
  ring

/-! ## The exact signed factorization -/

/-- **Exact signed factorization of the affine oriented volume of a one-wedge depiction.**  When
the three plain endpoints lie in the drawing plane `z = 0`, the oriented volume anchored at the
wedge tip factors as minus the tip height times the doubled signed plain-triangle area.  The sign
is fixed by the actual argument order `first second third tip`. -/
theorem orientedVolume_plain_wedge_factor
    (first second third tip : CartesianPoint3)
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0) :
    CartesianPoint3.orientedVolume first second third tip =
      -(tip.z * plainTriangleArea first second third) := by
  simp only [CartesianPoint3.orientedVolume]
  rw [firstPlane, secondPlane, thirdPlane]
  simp only [plainTriangleArea]
  ring

/-! ## Surrounding plain rays -/

/-- Three plain rays surround the centre in one fixed cyclic sense: the three consecutive signed
cross products all have the same strictly positive sign.  This is the orientation-preserving half of
`PlainRaysSurround`. -/
def CyclicSurround (center first second third : CartesianPoint2) : Prop :=
  0 < planarCross (planarEdge center first) (planarEdge center second) ∧
  0 < planarCross (planarEdge center second) (planarEdge center third) ∧
  0 < planarCross (planarEdge center third) (planarEdge center first)

/-- The three plain drawing rays surround the centre in either cyclic sense.  This is the drawing
admission for the three-plain subset; it excludes collinear placements (vanishing area) and
reflex / large-gap orderings (the centre falling outside the plain triangle). -/
def PlainRaysSurround (center first second third : CartesianPoint2) : Prop :=
  CyclicSurround center first second third ∨ CyclicSurround center first third second

/-- A positively surrounding plain triple spans a strictly positive doubled area. -/
theorem cyclicSurround_area_positive (center first second third : CartesianPoint2)
    (surround : CyclicSurround center first second third) :
    0 < plainTriangleArea (planePoint first) (planePoint second) (planePoint third) := by
  rw [plainTriangleArea_eq_cross_sum]
  rcases surround with ⟨h12, h23, h31⟩
  linarith

/-- The opposite cyclic sense spans a strictly negative doubled area. -/
theorem reverseCyclicSurround_area_negative (center first second third : CartesianPoint2)
    (surround : CyclicSurround center first third second) :
    plainTriangleArea (planePoint first) (planePoint second) (planePoint third) < 0 := by
  rw [plainTriangleArea_eq_cross_sum]
  rcases surround with ⟨h13, h32, h21⟩
  have h12 : planarCross (planarEdge center first) (planarEdge center second) < 0 := by
    rw [planarCross_skew]
    linarith
  have h23 : planarCross (planarEdge center second) (planarEdge center third) < 0 := by
    rw [planarCross_skew]
    linarith
  have h31 : planarCross (planarEdge center third) (planarEdge center first) < 0 := by
    rw [planarCross_skew]
    linarith
  linarith

/-- A surrounding plain triple is non-collinear. -/
theorem plainRaysSurround_area_ne_zero (center first second third : CartesianPoint2)
    (surround : PlainRaysSurround center first second third) :
    plainTriangleArea (planePoint first) (planePoint second) (planePoint third) ≠ 0 := by
  rcases surround with h | h
  · exact ne_of_gt (cyclicSurround_area_positive center first second third h)
  · exact ne_of_lt (reverseCyclicSurround_area_negative center first second third h)

/-! ## Exact volume-sign wrappers around the existing parity relation

The calibrated source producer assigns `.clockwise` to a negative written-order affine
determinant and `.anticlockwise` to a positive one.  The two accurately named wrappers below state
that assignment.  The two historical-named wrappers are kept because a kernel certificate pins the
old identifiers; their statements are the corrected ones, and the docstrings mark the name as a
stable API key rather than a description of the conclusion. -/

/-- **Accurate name.**  A negative written-order volume is the `.clockwise` carrier. -/
theorem tetrahedralInputParityOfPoints?_eq_some_clockwise_of_volume_negative
    (first second third fourth : CartesianPoint3)
    (negative : CartesianPoint3.orientedVolume first second third fourth < 0) :
    tetrahedralInputParityOfPoints? [first, second, third, fourth] = some .clockwise :=
  (tetrahedralInputParityOfPoints?_eq_some_iff _ _).mpr
    ⟨first, second, third, fourth, rfl, negative⟩

/-- **Accurate name.**  A positive written-order volume is the `.anticlockwise` carrier. -/
theorem tetrahedralInputParityOfPoints?_eq_some_anticlockwise_of_volume_positive
    (first second third fourth : CartesianPoint3)
    (positive : 0 < CartesianPoint3.orientedVolume first second third fourth) :
    tetrahedralInputParityOfPoints? [first, second, third, fourth] = some .anticlockwise :=
  (tetrahedralInputParityOfPoints?_eq_some_iff _ _).mpr
    ⟨first, second, third, fourth, rfl, positive⟩

/-- **Historical API key.**  The suffix predates the handedness calibration repair and describes
the old, incorrect carrier assignment.  The statement is the corrected one: a positive volume is
`.anticlockwise`.  Use `tetrahedralInputParityOfPoints?_eq_some_anticlockwise_of_volume_positive`
for new code. -/
theorem tetrahedralInputParityOfPoints?_eq_some_clockwise_of_volume_positive
    (first second third fourth : CartesianPoint3)
    (positive : 0 < CartesianPoint3.orientedVolume first second third fourth) :
    tetrahedralInputParityOfPoints? [first, second, third, fourth] = some .anticlockwise :=
  tetrahedralInputParityOfPoints?_eq_some_anticlockwise_of_volume_positive
    first second third fourth positive

/-- **Historical API key.**  The suffix predates the handedness calibration repair and describes
the old, incorrect carrier assignment.  The statement is the corrected one: a negative volume is
`.clockwise`.  Use `tetrahedralInputParityOfPoints?_eq_some_clockwise_of_volume_negative` for new
code. -/
theorem tetrahedralInputParityOfPoints?_eq_some_anticlockwise_of_volume_negative
    (first second third fourth : CartesianPoint3)
    (negative : CartesianPoint3.orientedVolume first second third fourth < 0) :
    tetrahedralInputParityOfPoints? [first, second, third, fourth] = some .clockwise :=
  tetrahedralInputParityOfPoints?_eq_some_clockwise_of_volume_negative
    first second third fourth negative

theorem tetrahedralInputParityOfPoints?_eq_none_of_volume_zero
    (first second third fourth : CartesianPoint3)
    (zero : CartesianPoint3.orientedVolume first second third fourth = 0) :
    tetrahedralInputParityOfPoints? [first, second, third, fourth] = none := by
  simp [AuthoritativeChemicalInput.tetrahedralInputParityOfPoints?, zero]

/-! ## Signed parity of a plain-wedge frame -/

/-- A positive plain-height product (negative volume) selects `.clockwise`. -/
theorem plainWedge_parity_of_product_positive
    (first second third tip : CartesianPoint3)
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0)
    (positive : 0 < tip.z * plainTriangleArea first second third) :
    tetrahedralInputParityOfPoints? [first, second, third, tip] = some .clockwise := by
  apply tetrahedralInputParityOfPoints?_eq_some_clockwise_of_volume_negative
  rw [orientedVolume_plain_wedge_factor first second third tip firstPlane secondPlane thirdPlane]
  linarith

/-- A negative plain-height product (positive volume) selects `.anticlockwise`. -/
theorem plainWedge_parity_of_product_negative
    (first second third tip : CartesianPoint3)
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0)
    (negative : tip.z * plainTriangleArea first second third < 0) :
    tetrahedralInputParityOfPoints? [first, second, third, tip] = some .anticlockwise := by
  apply tetrahedralInputParityOfPoints?_eq_some_anticlockwise_of_volume_positive
  rw [orientedVolume_plain_wedge_factor first second third tip firstPlane secondPlane thirdPlane]
  linarith

/-- Accurate semantic alias: a positive plain-height product is `.clockwise`. -/
theorem plainWedge_parity_clockwise_of_product_positive
    (first second third tip : CartesianPoint3)
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0)
    (positive : 0 < tip.z * plainTriangleArea first second third) :
    tetrahedralInputParityOfPoints? [first, second, third, tip] = some .clockwise :=
  plainWedge_parity_of_product_positive
    first second third tip firstPlane secondPlane thirdPlane positive

/-- Accurate semantic alias: a negative plain-height product is `.anticlockwise`. -/
theorem plainWedge_parity_anticlockwise_of_product_negative
    (first second third tip : CartesianPoint3)
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0)
    (negative : tip.z * plainTriangleArea first second third < 0) :
    tetrahedralInputParityOfPoints? [first, second, third, tip] = some .anticlockwise :=
  plainWedge_parity_of_product_negative
    first second third tip firstPlane secondPlane thirdPlane negative

/-- A **solid** wedge (`+h`, toward the viewer) on a positively surrounding plain triple gives
`.clockwise` under the calibrated right-handed carrier assignment. -/
theorem plainWedge_solid_parity
    (center first second third wedge : CartesianPoint2) {height : ℚ} (hpos : 0 < height)
    (surround : CyclicSurround center first second third) :
    tetrahedralInputParityOfPoints?
        [planePoint first, planePoint second, planePoint third, liftedTip wedge height] =
      some .clockwise := by
  apply plainWedge_parity_of_product_positive _ _ _ _ rfl rfl rfl
  simpa using mul_pos hpos (cyclicSurround_area_positive center first second third surround)

/-- A **hashed** wedge (`-h`, away from the viewer) on a positively surrounding plain triple gives
`.anticlockwise` under the calibrated right-handed carrier assignment. -/
theorem plainWedge_hashed_parity
    (center first second third wedge : CartesianPoint2) {height : ℚ} (hneg : height < 0)
    (surround : CyclicSurround center first second third) :
    tetrahedralInputParityOfPoints?
        [planePoint first, planePoint second, planePoint third, liftedTip wedge height] =
      some .anticlockwise := by
  apply plainWedge_parity_of_product_negative _ _ _ _ rfl rfl rfl
  simpa using
    mul_neg_of_neg_of_pos hneg (cyclicSurround_area_positive center first second third surround)

/-- Accurate semantic alias for the solid-wedge carrier. -/
theorem plainWedge_solid_parity_clockwise
    (center first second third wedge : CartesianPoint2) {height : ℚ} (hpos : 0 < height)
    (surround : CyclicSurround center first second third) :
    tetrahedralInputParityOfPoints?
        [planePoint first, planePoint second, planePoint third, liftedTip wedge height] =
      some .clockwise :=
  plainWedge_solid_parity center first second third wedge hpos surround

/-- Accurate semantic alias for the hashed-wedge carrier. -/
theorem plainWedge_hashed_parity_anticlockwise
    (center first second third wedge : CartesianPoint2) {height : ℚ} (hneg : height < 0)
    (surround : CyclicSurround center first second third) :
    tetrahedralInputParityOfPoints?
        [planePoint first, planePoint second, planePoint third, liftedTip wedge height] =
      some .anticlockwise :=
  plainWedge_hashed_parity center first second third wedge hneg surround

/-! ## Invariance laws -/

/-- **Negating the wedge height reverses the parity.**  Exact for every plain triple in the drawing
plane, independently of the plain area. -/
theorem plainWedge_parity_negate_height
    (first second third : CartesianPoint3) (wedge : CartesianPoint2) (height : ℚ)
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0) :
    Option.map reverseTetrahedralInputParity
        (tetrahedralInputParityOfPoints?
          [first, second, third, liftedTip wedge height]) =
      tetrahedralInputParityOfPoints?
        [first, second, third, liftedTip wedge (-height)] := by
  rcases lt_trichotomy (height * plainTriangleArea first second third) 0 with h | h | h
  · have forward :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge height] =
          some .anticlockwise :=
      plainWedge_parity_of_product_negative _ _ _ _ firstPlane secondPlane thirdPlane
        (by simpa only [liftedTip_z] using h)
    have negated :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge (-height)] =
          some .clockwise := by
      apply plainWedge_parity_of_product_positive _ _ _ _ firstPlane secondPlane thirdPlane
      have : (liftedTip wedge (-height)).z * plainTriangleArea first second third =
          -(height * plainTriangleArea first second third) := by
        simp only [liftedTip_z]
        ring
      rw [this]
      linarith
    rw [forward, negated]
    simp [reverseTetrahedralInputParity]
  · have zero :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge height] = none := by
      apply tetrahedralInputParityOfPoints?_eq_none_of_volume_zero
      rw [orientedVolume_plain_wedge_factor _ _ _ _ firstPlane secondPlane thirdPlane,
        liftedTip_z, h]
      simp
    have zeroNeg :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge (-height)] = none := by
      apply tetrahedralInputParityOfPoints?_eq_none_of_volume_zero
      rw [orientedVolume_plain_wedge_factor _ _ _ _ firstPlane secondPlane thirdPlane]
      simp only [liftedTip_z]
      rw [show (-height) * plainTriangleArea first second third =
            -(height * plainTriangleArea first second third) by ring, h]
      simp
    rw [zero, zeroNeg]
    simp
  · have forward :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge height] =
          some .clockwise :=
      plainWedge_parity_of_product_positive _ _ _ _ firstPlane secondPlane thirdPlane
        (by simpa only [liftedTip_z] using h)
    have negated :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge (-height)] =
          some .anticlockwise := by
      apply plainWedge_parity_of_product_negative _ _ _ _ firstPlane secondPlane thirdPlane
      have : (liftedTip wedge (-height)).z * plainTriangleArea first second third =
          -(height * plainTriangleArea first second third) := by
        simp only [liftedTip_z]
        ring
      rw [this]
      linarith
    rw [forward, negated]
    simp [reverseTetrahedralInputParity]

/-- **Magnitude invariance.**  For a fixed drawing position the parity depends only on the *sign*
of the wedge height, not its magnitude. -/
theorem plainWedge_parity_height_magnitude_invariant
    (first second third : CartesianPoint3) (wedge : CartesianPoint2) {h₁ h₂ : ℚ}
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0)
    (h₁pos : 0 < h₁) (h₂pos : 0 < h₂) :
    tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge h₁] =
      tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge h₂] := by
  rcases lt_trichotomy (plainTriangleArea first second third) 0 with hA | hA | hA
  · have p₁ : (liftedTip wedge h₁).z * plainTriangleArea first second third < 0 := by
      simpa only [liftedTip_z] using mul_neg_of_pos_of_neg h₁pos hA
    have p₂ : (liftedTip wedge h₂).z * plainTriangleArea first second third < 0 := by
      simpa only [liftedTip_z] using mul_neg_of_pos_of_neg h₂pos hA
    rw [plainWedge_parity_of_product_negative _ _ _ _ firstPlane secondPlane thirdPlane p₁,
      plainWedge_parity_of_product_negative _ _ _ _ firstPlane secondPlane thirdPlane p₂]
  · have zero₁ : CartesianPoint3.orientedVolume first second third (liftedTip wedge h₁) = 0 := by
      rw [orientedVolume_plain_wedge_factor _ _ _ _ firstPlane secondPlane thirdPlane]
      simp [hA]
    have zero₂ : CartesianPoint3.orientedVolume first second third (liftedTip wedge h₂) = 0 := by
      rw [orientedVolume_plain_wedge_factor _ _ _ _ firstPlane secondPlane thirdPlane]
      simp [hA]
    rw [tetrahedralInputParityOfPoints?_eq_none_of_volume_zero _ _ _ _ zero₁,
      tetrahedralInputParityOfPoints?_eq_none_of_volume_zero _ _ _ _ zero₂]
  · have p₁ : 0 < (liftedTip wedge h₁).z * plainTriangleArea first second third := by
      simpa only [liftedTip_z] using mul_pos h₁pos hA
    have p₂ : 0 < (liftedTip wedge h₂).z * plainTriangleArea first second third := by
      simpa only [liftedTip_z] using mul_pos h₂pos hA
    rw [plainWedge_parity_of_product_positive _ _ _ _ firstPlane secondPlane thirdPlane p₁,
      plainWedge_parity_of_product_positive _ _ _ _ firstPlane secondPlane thirdPlane p₂]

/-- **Collinear plain endpoints refuse a parity** entirely, for any wedge height. -/
theorem plainWedge_parity_collinear_refused
    (first second third : CartesianPoint3) (wedge : CartesianPoint2) (height : ℚ)
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0)
    (collinear : plainTriangleArea first second third = 0) :
    tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge height] = none := by
  apply tetrahedralInputParityOfPoints?_eq_none_of_volume_zero
  rw [orientedVolume_plain_wedge_factor _ _ _ _ firstPlane secondPlane thirdPlane]
  simp [collinear]

/-- **Swapping the first two plain endpoints reverses the parity.**  This is a concrete, proved
instance of the explicit permutation transport: the parity computed in the written order is
reindexed, not assumed to already be in the canonical order. -/
theorem plainWedge_parity_swap_plain
    (first second third : CartesianPoint3) (wedge : CartesianPoint2) (height : ℚ)
    (firstPlane : first.z = 0) (secondPlane : second.z = 0) (thirdPlane : third.z = 0) :
    Option.map reverseTetrahedralInputParity
        (tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge height]) =
      tetrahedralInputParityOfPoints? [second, first, third, liftedTip wedge height] := by
  have hprod : (liftedTip wedge height).z * plainTriangleArea second first third =
      -((liftedTip wedge height).z * plainTriangleArea first second third) := by
    rw [plainTriangleArea_swap first second third]
    ring
  rcases lt_trichotomy
      ((liftedTip wedge height).z * plainTriangleArea first second third) 0 with hp | hp | hp
  · have forward :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge height] =
          some .anticlockwise :=
      plainWedge_parity_of_product_negative _ _ _ _ firstPlane secondPlane thirdPlane hp
    have swapped :
        tetrahedralInputParityOfPoints? [second, first, third, liftedTip wedge height] =
          some .clockwise := by
      apply plainWedge_parity_of_product_positive _ _ _ _ secondPlane firstPlane thirdPlane
      rw [hprod]
      linarith
    rw [forward, swapped]
    simp [reverseTetrahedralInputParity]
  · have forward :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge height] = none := by
      apply tetrahedralInputParityOfPoints?_eq_none_of_volume_zero
      rw [orientedVolume_plain_wedge_factor _ _ _ _ firstPlane secondPlane thirdPlane, hp]
      simp
    have swapped :
        tetrahedralInputParityOfPoints? [second, first, third, liftedTip wedge height] = none := by
      apply tetrahedralInputParityOfPoints?_eq_none_of_volume_zero
      rw [orientedVolume_plain_wedge_factor _ _ _ _ secondPlane firstPlane thirdPlane, hprod, hp]
      simp
    rw [forward, swapped]
    simp
  · have forward :
        tetrahedralInputParityOfPoints? [first, second, third, liftedTip wedge height] =
          some .clockwise :=
      plainWedge_parity_of_product_positive _ _ _ _ firstPlane secondPlane thirdPlane hp
    have swapped :
        tetrahedralInputParityOfPoints? [second, first, third, liftedTip wedge height] =
          some .anticlockwise := by
      apply plainWedge_parity_of_product_negative _ _ _ _ secondPlane firstPlane thirdPlane
      rw [hprod]
      linarith
    rw [forward, swapped]
    simp [reverseTetrahedralInputParity]

/-! ## Explicit permutation transport at the descriptor level -/

/-- Reindexing by an even permutation leaves the parity unchanged. -/
theorem reindexTetrahedralInputParity_of_even
    (parity : TetrahedralInputParity) (sigma : Equiv.Perm (Fin 4))
    (even : RawMolecule.permutationIsEven (finFourPermutationList sigma) = true) :
    reindexTetrahedralInputParity parity sigma = parity := by
  simp [reindexTetrahedralInputParity, even]

/-- Reindexing by an odd permutation reverses the parity. -/
theorem reindexTetrahedralInputParity_of_odd
    (parity : TetrahedralInputParity) (sigma : Equiv.Perm (Fin 4))
    (odd : RawMolecule.permutationIsEven (finFourPermutationList sigma) = false) :
    reindexTetrahedralInputParity parity sigma = reverseTetrahedralInputParity parity := by
  simp [reindexTetrahedralInputParity, odd]

/-- Reversing an input parity twice is the identity. -/
theorem reverseTetrahedralInputParity_involutive (parity : TetrahedralInputParity) :
    reverseTetrahedralInputParity (reverseTetrahedralInputParity parity) = parity := by
  cases parity <;> rfl

/-- The identity frame transports no parity.  This is the base case of the explicit
written-to-canonical transport used by the adapter. -/
theorem reindexTetrahedralInputParity_one (parity : TetrahedralInputParity) :
    reindexTetrahedralInputParity parity (1 : Equiv.Perm (Fin 4)) = parity := by
  have identityEven :
      RawMolecule.permutationIsEven
        (finFourPermutationList (1 : Equiv.Perm (Fin 4))) = true := by decide
  simp [reindexTetrahedralInputParity, identityEven]

/-- Reindexing commutes with parity reversal: transporting a reversed written-order parity equals
reversing the transported parity.  This is the frame-transport law that lets the adapter argue about
solid/hashed glyphs independently of the written-to-canonical permutation. -/
theorem reindexTetrahedralInputParity_reverse (parity : TetrahedralInputParity)
    (frame : Equiv.Perm (Fin 4)) :
    reindexTetrahedralInputParity (reverseTetrahedralInputParity parity) frame =
      reverseTetrahedralInputParity (reindexTetrahedralInputParity parity frame) := by
  by_cases even : RawMolecule.permutationIsEven (finFourPermutationList frame) = true
  · rw [reindexTetrahedralInputParity_of_even _ _ even,
      reindexTetrahedralInputParity_of_even _ _ even]
  · have odd : RawMolecule.permutationIsEven (finFourPermutationList frame) = false :=
      Bool.eq_false_of_not_eq_true even
    rw [reindexTetrahedralInputParity_of_odd _ _ odd,
      reindexTetrahedralInputParity_of_odd _ _ odd,
      reverseTetrahedralInputParity_involutive]

/-- Reversing the input parity swaps the `R/S` descriptor of every fixed ordering.  Consequently a
solid and a hashed wedge on the same plain triple yield *opposite* descriptors once the remaining
Rule-3--6 machinery is fixed. -/
theorem descriptorOfFinFourOrdering_reverse
    (parity : TetrahedralInputParity) (ordering : Equiv.Perm (Fin 4)) :
    descriptorOfFinFourOrdering (reverseTetrahedralInputParity parity) ordering =
      RS.swap (descriptorOfFinFourOrdering parity ordering) := by
  cases parity <;>
    cases even : RawMolecule.permutationIsEven (finFourPermutationList ordering) <;>
      simp [descriptorOfFinFourOrdering, RawMolecule.descriptorOfParity,
        reverseTetrahedralInputParity, RS.swap, even]

end TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs
