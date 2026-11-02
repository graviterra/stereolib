import TetraStereo.OneCenter.IR9CubeSpatialPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.CubeSpatialOrbitCompleteness

open FiniteSymmetry
open CubeSourceIndexCompleteness
open CubeSpatialPerception

/-!
# Exact spatial-orbit completeness for ideal CU-8

The exact metric recognized by `CubeSpatialPerception` is rigid enough to determine the cube's
typed vertices up to precisely the 48 signed-axis symmetries already used by the complete
mathematical CU-8 priority index.  Consequently, retaining every accepted coordinate placement
does not create descriptor ambiguity: all accepted placements produce the same complete index.

This closes the coordinate-to-relative-index seam for the strict ideal rational-coordinate model.
It does not introduce a tolerance, a source-unpublished short index, or a cube-specific `A`/`C`
orientation convention.
-/

abbrev Position := CubeSourceIndexCompleteness.Position

/-- The vertex whose only positive binary coordinate is `axis`. -/
def basis (axis : Fin 3) : Position :=
  fun coordinate => decide (coordinate = axis)

theorem basis_injective : Function.Injective basis := by
  decide

@[simp] theorem pairSignature_origin_basis (axis : Fin 3) :
    pairSignature origin (basis axis) = 1 := by
  revert axis
  decide

theorem pairSignature_eq_zero_iff (left right : Position) :
    pairSignature left right = 0 ↔ left = right := by
  revert left right
  decide

theorem pairSignature_pos_of_ne
    {left right : Position} (different : left ≠ right) :
    0 < pairSignature left right :=
  Nat.pos_of_ne_zero (fun zero =>
    different ((pairSignature_eq_zero_iff left right).mp zero))

/-- The three vertices at Hamming distance one from the typed origin are exactly the basis
vertices, with a unique axis for each. -/
theorem pairSignature_origin_eq_one_iff_existsUnique_basis (position : Position) :
    pairSignature origin position = 1 ↔
      ∃! axis : Fin 3, position = basis axis := by
  constructor
  · intro one
    change (Finset.univ.filter fun coordinate : Fin 3 =>
      origin coordinate ≠ position coordinate).card = 1 at one
    rcases Finset.card_eq_one.mp one with ⟨axis, supportEq⟩
    have positionEq : position = basis axis := by
      funext coordinate
      by_cases same : coordinate = axis
      · subst coordinate
        have axisMem : axis ∈ Finset.univ.filter fun coordinate : Fin 3 =>
            origin coordinate ≠ position coordinate := by
          rw [supportEq]
          simp
        have axisDiff : origin axis ≠ position axis :=
          (Finset.mem_filter.mp axisMem).2
        have positionTrue : position axis = true := by
          simpa [origin] using axisDiff
        simp [basis, positionTrue]
      · have coordinateNotMem : coordinate ∉
            Finset.univ.filter fun coordinate : Fin 3 =>
              origin coordinate ≠ position coordinate := by
          rw [supportEq]
          simpa using same
        have coordinateSame : origin coordinate = position coordinate := by
          exact not_ne_iff.mp (by simpa using coordinateNotMem)
        have positionFalse : position coordinate = false := by
          simpa [origin] using coordinateSame.symm
        simp [basis, same, positionFalse]
    refine ⟨axis, positionEq, ?_⟩
    intro other otherEq
    apply basis_injective
    exact otherEq.symm.trans positionEq
  · rintro ⟨axis, positionEq, _unique⟩
    rw [positionEq]
    exact pairSignature_origin_basis axis

/-- Distances from the origin and the three basis vertices distinguish every cube vertex. -/
theorem position_eq_of_distance_fingerprint
    (left right : Position)
    (originDistance :
      pairSignature origin left = pairSignature origin right)
    (basisDistances :
      ∀ axis : Fin 3,
        pairSignature (basis axis) left = pairSignature (basis axis) right) :
    left = right := by
  revert left right
  decide

theorem flipPermutation_preserves_pairSignature
    (flip : Position) (left right : Position) :
    pairSignature (flipPermutation flip left) (flipPermutation flip right) =
      pairSignature left right := by
  revert flip left right
  decide

theorem axisPermutation_preserves_pairSignature
    (axis : Equiv.Perm (Fin 3)) (left right : Position) :
    pairSignature (axisPermutation axis left) (axisPermutation axis right) =
      pairSignature left right := by
  revert axis left right
  decide

@[simp] theorem axisPermutation_basis
    (axis : Equiv.Perm (Fin 3)) (coordinate : Fin 3) :
    axisPermutation axis (basis coordinate) = basis (axis coordinate) := by
  revert axis coordinate
  decide

/-- Translate an arbitrary cube permutation so that it fixes the typed origin. -/
def normalizedPermutation (symmetry : Equiv.Perm Position) : Equiv.Perm Position :=
  symmetry.trans (flipPermutation (symmetry origin))

@[simp] theorem normalizedPermutation_origin (symmetry : Equiv.Perm Position) :
    normalizedPermutation symmetry origin = origin := by
  funext coordinate
  simp [normalizedPermutation, flipPermutation, origin]

theorem normalizedPermutation_preserves_pairSignature
    (symmetry : Equiv.Perm Position)
    (preserves : ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right)
    (left right : Position) :
    pairSignature (normalizedPermutation symmetry left)
        (normalizedPermutation symmetry right) =
      pairSignature left right := by
  calc
    pairSignature (normalizedPermutation symmetry left)
        (normalizedPermutation symmetry right) =
      pairSignature (symmetry left) (symmetry right) := by
        exact flipPermutation_preserves_pairSignature
          (symmetry origin) (symmetry left) (symmetry right)
    _ = pairSignature left right := preserves left right

/-- Converse to signed-axis invariance: every permutation preserving all cube pair signatures is
one of the 48 structurally admitted signed-axis frames. -/
theorem pairSignature_preserving_mem_fullSymmetryGroup
    (symmetry : Equiv.Perm Position)
    (preserves : ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right) :
    symmetry ∈ fullSymmetryGroup := by
  classical
  let normalized := normalizedPermutation symmetry
  have normalizedOrigin : normalized origin = origin := by
    exact normalizedPermutation_origin symmetry
  have normalizedPreserves : ∀ left right,
      pairSignature (normalized left) (normalized right) = pairSignature left right := by
    exact normalizedPermutation_preserves_pairSignature symmetry preserves
  have eachBasis (coordinate : Fin 3) :
      pairSignature origin (normalized (basis coordinate)) = 1 := by
    calc
      pairSignature origin (normalized (basis coordinate)) =
          pairSignature (normalized origin) (normalized (basis coordinate)) := by
            rw [normalizedOrigin]
      _ = pairSignature origin (basis coordinate) :=
        normalizedPreserves origin (basis coordinate)
      _ = 1 := pairSignature_origin_basis coordinate
  have basisImage (coordinate : Fin 3) :
      ∃! target : Fin 3, normalized (basis coordinate) = basis target :=
    (pairSignature_origin_eq_one_iff_existsUnique_basis
      (normalized (basis coordinate))).mp (eachBasis coordinate)
  let axis : Fin 3 → Fin 3 :=
    fun coordinate => Classical.choose (basisImage coordinate).exists
  have axisSpec (coordinate : Fin 3) :
      normalized (basis coordinate) = basis (axis coordinate) :=
    Classical.choose_spec (basisImage coordinate).exists
  have axisInjective : Function.Injective axis := by
    intro left right same
    apply basis_injective
    apply normalized.injective
    rw [axisSpec left, axisSpec right, same]
  have axisBijective : Function.Bijective axis :=
    (Fintype.bijective_iff_injective_and_card axis).mpr
      ⟨axisInjective, rfl⟩
  let axisEquiv : Equiv.Perm (Fin 3) := Equiv.ofBijective axis axisBijective
  have axisEquivSpec (coordinate : Fin 3) :
      normalized (basis coordinate) = basis (axisEquiv coordinate) := by
    exact axisSpec coordinate
  have normalizedEq : normalized = axisPermutation axisEquiv := by
    apply Equiv.ext
    intro position
    apply position_eq_of_distance_fingerprint
    · calc
        pairSignature origin (normalized position) =
            pairSignature (normalized origin) (normalized position) := by
              rw [normalizedOrigin]
        _ = pairSignature origin position := normalizedPreserves origin position
        _ = pairSignature origin (axisPermutation axisEquiv position) := by
          symm
          exact axisPermutation_preserves_pairSignature axisEquiv origin position
    · intro target
      let source : Fin 3 := axisEquiv.symm target
      have normalizedBasis : normalized (basis source) = basis target := by
        calc
          normalized (basis source) = basis (axisEquiv source) := axisEquivSpec source
          _ = basis target := by simp [source]
      calc
        pairSignature (basis target) (normalized position) =
            pairSignature (normalized (basis source)) (normalized position) := by
              rw [normalizedBasis]
        _ = pairSignature (basis source) position :=
          normalizedPreserves (basis source) position
        _ = pairSignature (basis target) (axisPermutation axisEquiv position) := by
          symm
          simpa [source] using
            (axisPermutation_preserves_pairSignature axisEquiv (basis source) position)
  have symmetryEq : symmetry = coordinatePermutation (symmetry origin) axisEquiv := by
    apply Equiv.ext
    intro position
    have normalizedPoint :
        normalized position = axisPermutation axisEquiv position := by
      rw [normalizedEq]
    have recovered := congrArg (flipPermutation (symmetry origin)) normalizedPoint
    simpa [normalized, normalizedPermutation, coordinatePermutation,
      flipPermutation] using recovered
  exact ⟨symmetry origin, axisEquiv, symmetryEq⟩

@[simp] theorem pairSignature_origin_firstNeighbor :
    pairSignature origin firstNeighbor = 1 := by
  decide

theorem origin_ne_firstNeighbor : origin ≠ firstNeighbor := by
  decide

/-- If one bijection makes all Hamming distances proportional to another, with both reference
scales positive, surjectivity forces the scale factor to be one and the bijection preserves every
pair signature exactly. -/
theorem proportional_pairSignature_preserving
    (symmetry : Equiv.Perm Position)
    (leftScale rightScale : ℚ)
    (leftPositive : 0 < leftScale)
    (_rightPositive : 0 < rightScale)
    (proportional : ∀ left right,
      (pairSignature (symmetry left) (symmetry right) : ℚ) * leftScale =
        (pairSignature left right : ℚ) * rightScale) :
    ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right := by
  let k := pairSignature (symmetry origin) (symmetry firstNeighbor)
  let preOrigin := symmetry.symm origin
  let preNeighbor := symmetry.symm firstNeighbor
  let m := pairSignature preOrigin preNeighbor
  have kPositive : 0 < k := by
    apply pairSignature_pos_of_ne
    exact fun same => origin_ne_firstNeighbor (symmetry.injective same)
  have mPositive : 0 < m := by
    apply pairSignature_pos_of_ne
    exact fun same => origin_ne_firstNeighbor (symmetry.symm.injective same)
  have edgeEquation : (k : ℚ) * leftScale = rightScale := by
    simpa [k] using proportional origin firstNeighbor
  have inverseEquation : leftScale = (m : ℚ) * rightScale := by
    simpa [preOrigin, preNeighbor, m] using proportional preOrigin preNeighbor
  have productScale : ((m : ℚ) * (k : ℚ)) * leftScale = leftScale := by
    calc
      ((m : ℚ) * (k : ℚ)) * leftScale =
          (m : ℚ) * ((k : ℚ) * leftScale) := by ring
      _ = (m : ℚ) * rightScale := by rw [edgeEquation]
      _ = leftScale := inverseEquation.symm
  have productCast : (m : ℚ) * (k : ℚ) = 1 := by
    apply mul_right_cancel₀ (ne_of_gt leftPositive)
    simpa using productScale
  have productNat : m * k = 1 := by
    exact_mod_cast productCast
  have kEq : k = 1 := by
    apply Nat.eq_one_of_dvd_one
    exact ⟨m, by simpa [Nat.mul_comm] using productNat.symm⟩
  have scales : leftScale = rightScale := by
    simpa [kEq] using edgeEquation
  intro left right
  have castSame :
      (pairSignature (symmetry left) (symmetry right) : ℚ) =
        (pairSignature left right : ℚ) := by
    apply mul_right_cancel₀ (ne_of_gt leftPositive)
    simpa [scales] using proportional left right
  exact_mod_cast castSame

/-- The role transition that follows a donor from the right placement back to its role in the
left placement. -/
def placementTransition
    (left right : CubeSpatialPerception.Placement) : Equiv.Perm Position :=
  right.trans left.symm

@[simp] theorem placementTransition_apply_index
    (left right : CubeSpatialPerception.Placement) (position : Position) :
    left (placementTransition left right position) = right position := by
  simp [placementTransition]

theorem placementTransition_pointAt
    (frame : CubeSpatialPerception.Frame)
    (left right : CubeSpatialPerception.Placement) (position : Position) :
    frame.pointAt left (placementTransition left right position) =
      frame.pointAt right position := by
  simp [CubeSpatialPerception.Frame.pointAt, placementTransition]

/-- Any two exact placements recognized from the same coordinates differ by a member of the full
48-element ideal-cube symmetry group. -/
theorem recognizedPlacements_transition_mem_fullSymmetryGroup
    (frame : CubeSpatialPerception.Frame)
    (left right : CubeSpatialPerception.Placement)
    (leftRecognized : left ∈ recognizedPlacements frame)
    (rightRecognized : right ∈ recognizedPlacements frame) :
    placementTransition left right ∈ fullSymmetryGroup := by
  apply pairSignature_preserving_mem_fullSymmetryGroup
  apply proportional_pairSignature_preserving
    (placementTransition left right)
    (edgeSquared frame left) (edgeSquared frame right)
    (recognizedPlacement_edgeSquared_positive frame left leftRecognized)
    (recognizedPlacement_edgeSquared_positive frame right rightRecognized)
  intro first second
  calc
    (pairSignature (placementTransition left right first)
          (placementTransition left right second) : ℚ) * edgeSquared frame left =
        squaredDistance
          (frame.pointAt left (placementTransition left right first))
          (frame.pointAt left (placementTransition left right second)) := by
            symm
            exact recognizedPlacement_exact_metric frame left leftRecognized _ _
    _ = squaredDistance (frame.pointAt right first) (frame.pointAt right second) := by
      rw [placementTransition_pointAt, placementTransition_pointAt]
    _ = (pairSignature first second : ℚ) * edgeSquared frame right :=
      recognizedPlacement_exact_metric frame right rightRecognized first second

/-- Every exact placement recognized from one physical CU-8 frame produces the same complete
mathematical priority index, for arbitrary (including repeated and primed) production priorities. -/
theorem recognizedPlacements_priorityIndex_eq
    (frame : CubeSpatialPerception.Frame)
    (priorityByDonor : Fin 8 → PolyhedralPriorityNumber)
    (left right : CubeSpatialPerception.Placement)
    (leftRecognized : left ∈ recognizedPlacements frame)
    (rightRecognized : right ∈ recognizedPlacements frame) :
    cubeCompleteConfigurationIndex
        (fun position => priorityByDonor (left position)) =
      cubeCompleteConfigurationIndex
        (fun position => priorityByDonor (right position)) := by
  apply (productionCompleteIndex_eq_iff_symmetryEquivalent _ _).mpr
  let transition : fullSymmetryGroup :=
    ⟨placementTransition left right,
      recognizedPlacements_transition_mem_fullSymmetryGroup
        frame left right leftRecognized rightRecognized⟩
  refine ⟨transition, ?_⟩
  funext position
  simp [relabel, transition, placementTransition]

end TetraStereo.OneCenter.RedBookIR9.CubeSpatialOrbitCompleteness
