import TetraStereo.OneCenter.IR9BipyramidalSourceIndexCompleteness
import Mathlib.GroupTheory.SpecificGroups.Dihedral

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.BipyramidalAbsoluteSymmetry

open FiniteSymmetry

/-!
# Proper rotations and absolute classes of ideal bipyramids

An ideal `n`-gonal bipyramid has two axial vertices and an equatorial regular `n`-gon.  Its full
vertex group is the product of the axial interchange group with the polygon's dihedral group.
Spatial orientation is preserved exactly when axial and polygon orientation signs agree: either
both are preserved, or the axial vertices are exchanged while the equatorial traversal is
reflected.

The generic development below derives the full and proper subgroups from those coordinate frames,
proves their proper/mirror coset decomposition, and instantiates the generic exact-two-absolute-
indices theorem.  Concrete kernel-checked instances are supplied for every represented family:
TBPY-5, PBPY-7, HBPY-8, and HBPY-9.
-/

/-- Two axial positions plus an equatorial `n`-gon. -/
abbrev Position (n : Nat) := Fin 2 ⊕ ZMod n

/-- One complete ideal-bipyramid coordinate frame. -/
abbrev CoordinateFrame (n : Nat) := Equiv.Perm (Fin 2) × DihedralGroup n

/-- Faithful geometric action of a dihedral frame on equatorial coordinates.  The sign convention
is chosen so that the action respects Mathlib's multiplication convention for `DihedralGroup`. -/
def polygonPermutation {n : Nat} : DihedralGroup n → Equiv.Perm (ZMod n)
  | .r offset =>
      { toFun := fun position => position - offset
        invFun := fun position => position + offset
        left_inv := by intro position; simp
        right_inv := by intro position; simp }
  | .sr offset =>
      { toFun := fun position => offset - position
        invFun := fun position => offset - position
        left_inv := by intro position; simp
        right_inv := by intro position; simp }

@[simp] theorem polygonPermutation_r_apply {n : Nat}
    (offset position : ZMod n) :
    polygonPermutation (.r offset) position = position - offset := rfl

@[simp] theorem polygonPermutation_sr_apply {n : Nat}
    (offset position : ZMod n) :
    polygonPermutation (.sr offset) position = offset - position := rfl

@[simp] theorem polygonPermutation_one {n : Nat} :
    polygonPermutation (1 : DihedralGroup n) = 1 := by
  rw [DihedralGroup.one_def]
  apply Equiv.ext
  intro position
  simp [polygonPermutation]

theorem polygonPermutation_mul {n : Nat}
    (first second : DihedralGroup n) :
    polygonPermutation first * polygonPermutation second =
      polygonPermutation (first * second) := by
  apply Equiv.ext
  intro position
  cases first <;> cases second <;> simp [Equiv.Perm.coe_mul] <;> ring

theorem polygonPermutation_inv {n : Nat} (frame : DihedralGroup n) :
    (polygonPermutation frame)⁻¹ = polygonPermutation frame⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [polygonPermutation_mul]
  simp

/-- Apply independent axial and dihedral equatorial frame changes. -/
def coordinatePermutation {n : Nat}
    (axis : Equiv.Perm (Fin 2)) (polygon : DihedralGroup n) :
    Equiv.Perm (Position n) :=
  Equiv.sumCongr axis (polygonPermutation polygon)

@[simp] theorem coordinatePermutation_inl {n : Nat}
    (axis : Equiv.Perm (Fin 2)) (polygon : DihedralGroup n) (position : Fin 2) :
    coordinatePermutation axis polygon (Sum.inl position) = Sum.inl (axis position) := rfl

@[simp] theorem coordinatePermutation_inr {n : Nat}
    (axis : Equiv.Perm (Fin 2)) (polygon : DihedralGroup n) (position : ZMod n) :
    coordinatePermutation axis polygon (Sum.inr position) =
      Sum.inr (polygonPermutation polygon position) := rfl

theorem coordinatePermutation_mul {n : Nat}
    (firstAxis secondAxis : Equiv.Perm (Fin 2))
    (firstPolygon secondPolygon : DihedralGroup n) :
    coordinatePermutation firstAxis firstPolygon *
        coordinatePermutation secondAxis secondPolygon =
      coordinatePermutation (firstAxis * secondAxis) (firstPolygon * secondPolygon) := by
  apply Equiv.ext
  intro position
  cases position with
  | inl axial => simp [Equiv.Perm.coe_mul]
  | inr equatorial =>
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, coordinatePermutation_inr]
      congr 1
      simpa only [Equiv.Perm.coe_mul, Function.comp_apply] using
        congrArg (fun permutation : Equiv.Perm (ZMod n) => permutation equatorial)
          (polygonPermutation_mul firstPolygon secondPolygon)

theorem coordinatePermutation_inv {n : Nat}
    (axis : Equiv.Perm (Fin 2)) (polygon : DihedralGroup n) :
    (coordinatePermutation axis polygon)⁻¹ =
      coordinatePermutation axis⁻¹ polygon⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [coordinatePermutation_mul]
  apply Equiv.ext
  intro position
  cases position <;> simp [coordinatePermutation]

/-- All admitted vertex symmetries of the ideal bipyramid. -/
def fullSymmetryGroup (n : Nat) : SymmetryGroup (Position n) where
  carrier := { symmetry |
    ∃ axis : Equiv.Perm (Fin 2), ∃ polygon : DihedralGroup n,
      symmetry = coordinatePermutation axis polygon }
  one_mem' := ⟨1, 1, by
    apply Equiv.ext
    intro position
    cases position with
    | inl axial => rfl
    | inr equatorial =>
        change Sum.inr equatorial = Sum.inr ((polygonPermutation 1) equatorial)
        rw [polygonPermutation_one]
        rfl⟩
  mul_mem' := by
    rintro first second ⟨firstAxis, firstPolygon, rfl⟩
      ⟨secondAxis, secondPolygon, rfl⟩
    exact ⟨firstAxis * secondAxis, firstPolygon * secondPolygon,
      coordinatePermutation_mul _ _ _ _⟩
  inv_mem' := by
    rintro symmetry ⟨axis, polygon, rfl⟩
    exact ⟨axis⁻¹, polygon⁻¹, coordinatePermutation_inv axis polygon⟩

/-- Orientation of a polygon frame: rotations preserve traversal and reflections reverse it. -/
def polygonOrientationSign {n : Nat} : DihedralGroup n → ℤˣ
  | .r _ => 1
  | .sr _ => -1

@[simp] theorem polygonOrientationSign_one {n : Nat} :
    polygonOrientationSign (1 : DihedralGroup n) = 1 := by
  rw [DihedralGroup.one_def]
  rfl

theorem polygonOrientationSign_mul {n : Nat} (first second : DihedralGroup n) :
    polygonOrientationSign (first * second) =
      polygonOrientationSign first * polygonOrientationSign second := by
  cases first <;> cases second <;> simp [polygonOrientationSign]

theorem polygonOrientationSign_inv {n : Nat} (frame : DihedralGroup n) :
    polygonOrientationSign frame⁻¹ = polygonOrientationSign frame := by
  cases frame <;> simp [polygonOrientationSign]

/-- Spatial orientation character of a complete bipyramid frame. -/
def frameOrientationSign {n : Nat}
    (axis : Equiv.Perm (Fin 2)) (polygon : DihedralGroup n) : ℤˣ :=
  Equiv.Perm.sign axis * polygonOrientationSign polygon

/-- Orientation-preserving bipyramid vertex symmetries. -/
def properSymmetryGroup (n : Nat) : SymmetryGroup (Position n) where
  carrier := { symmetry |
    ∃ axis : Equiv.Perm (Fin 2), ∃ polygon : DihedralGroup n,
      symmetry = coordinatePermutation axis polygon ∧
        frameOrientationSign axis polygon = 1 }
  one_mem' :=
    ⟨1, 1, by
      apply Equiv.ext
      intro position
      cases position with
      | inl axial => rfl
      | inr equatorial =>
          change Sum.inr equatorial = Sum.inr ((polygonPermutation 1) equatorial)
          rw [polygonPermutation_one]
          rfl,
      by simp [frameOrientationSign]⟩
  mul_mem' := by
    rintro first second ⟨firstAxis, firstPolygon, rfl, firstProper⟩
      ⟨secondAxis, secondPolygon, rfl, secondProper⟩
    refine ⟨firstAxis * secondAxis, firstPolygon * secondPolygon,
      coordinatePermutation_mul _ _ _ _, ?_⟩
    unfold frameOrientationSign at firstProper secondProper ⊢
    rw [Equiv.Perm.sign_mul, polygonOrientationSign_mul]
    calc
      (Equiv.Perm.sign firstAxis * Equiv.Perm.sign secondAxis) *
          (polygonOrientationSign firstPolygon * polygonOrientationSign secondPolygon) =
        (Equiv.Perm.sign firstAxis * polygonOrientationSign firstPolygon) *
          (Equiv.Perm.sign secondAxis * polygonOrientationSign secondPolygon) := by ac_rfl
      _ = 1 := by rw [firstProper, secondProper, one_mul]
  inv_mem' := by
    rintro symmetry ⟨axis, polygon, rfl, proper⟩
    refine ⟨axis⁻¹, polygon⁻¹, coordinatePermutation_inv axis polygon, ?_⟩
    simpa [frameOrientationSign, Equiv.Perm.sign_inv, polygonOrientationSign_inv]
      using proper

/-- A fixed improper mirror: preserve the axial names and reflect the equatorial polygon. -/
def mirror (n : Nat) : Equiv.Perm (Position n) :=
  coordinatePermutation 1 (.sr 0)

theorem mirror_mem_fullSymmetryGroup (n : Nat) :
    mirror n ∈ fullSymmetryGroup n := ⟨1, .sr 0, rfl⟩

/-- Every full bipyramid frame is proper or belongs to the fixed mirror coset. -/
theorem fullSymmetryGroup_proper_or_mirror_coset (n : Nat) :
    ∀ symmetry : fullSymmetryGroup n,
      symmetry.1 ∈ properSymmetryGroup n ∨
        ∃ rotation : properSymmetryGroup n,
          symmetry.1 = mirror n * rotation.1 := by
  intro symmetry
  rcases symmetry.2 with ⟨axis, polygon, same⟩
  rw [same]
  by_cases proper : frameOrientationSign axis polygon = 1
  · exact Or.inl ⟨axis, polygon, rfl, proper⟩
  · right
    have improper : frameOrientationSign axis polygon = -1 :=
      (Int.units_eq_one_or (frameOrientationSign axis polygon)).resolve_left proper
    let reflectedPolygon : DihedralGroup n := .sr 0 * polygon
    have rotationProper : frameOrientationSign axis reflectedPolygon = 1 := by
      unfold reflectedPolygon frameOrientationSign at improper ⊢
      rw [polygonOrientationSign_mul]
      simp only [polygonOrientationSign]
      calc
        Equiv.Perm.sign axis * (-1 * polygonOrientationSign polygon) =
            (-1) * (Equiv.Perm.sign axis * polygonOrientationSign polygon) := by ac_rfl
        _ = (-1) * (-1) := by rw [improper]
        _ = 1 := by decide
    let rotation : properSymmetryGroup n :=
      ⟨coordinatePermutation axis reflectedPolygon,
        ⟨axis, reflectedPolygon, rfl, rotationProper⟩⟩
    refine ⟨rotation, ?_⟩
    change coordinatePermutation axis polygon =
      coordinatePermutation 1 (.sr 0) *
        coordinatePermutation axis reflectedPolygon
    rw [coordinatePermutation_mul]
    have cancelReflection :
        (.sr 0 : DihedralGroup n) * reflectedPolygon = polygon := by
      simp [reflectedPolygon, ← mul_assoc]
    simp [cancelReflection]

/-- The coordinate description is faithful when distinct axial/dihedral frames induce distinct
vertex permutations.  The represented bipyramids all satisfy this condition; keeping it explicit
also records why the degenerate `n = 0, 1, 2` polygons are not chemical instances of this model. -/
def CoordinateFaithful (n : Nat) : Prop :=
  Function.Injective (fun frame : CoordinateFrame n =>
    coordinatePermutation frame.1 frame.2)

/-- The dihedral action on a nondegenerate polygon is faithful.  The hypothesis excludes exactly
the small moduli in which a rotation and a reflection can act identically on all vertices. -/
theorem polygonPermutation_injective {n : Nat}
    (two_ne_zero : (2 : ZMod n) ≠ 0) :
    Function.Injective (@polygonPermutation n) := by
  intro first second same
  cases first with
  | r firstOffset =>
      cases second with
      | r secondOffset =>
          have atZero := congrArg
            (fun permutation : Equiv.Perm (ZMod n) => permutation 0) same
          simp only [polygonPermutation_r_apply] at atZero
          have offsetsEqual : firstOffset = secondOffset := by
            simpa using congrArg Neg.neg atZero
          exact congrArg DihedralGroup.r offsetsEqual
      | sr secondOffset =>
          exfalso
          apply two_ne_zero
          have atZero := congrArg
            (fun permutation : Equiv.Perm (ZMod n) => permutation 0) same
          have atOne := congrArg
            (fun permutation : Equiv.Perm (ZMod n) => permutation 1) same
          simp only [polygonPermutation_r_apply, polygonPermutation_sr_apply] at atZero atOne
          linear_combination atOne - atZero
  | sr firstOffset =>
      cases second with
      | r secondOffset =>
          exfalso
          apply two_ne_zero
          have atZero := congrArg
            (fun permutation : Equiv.Perm (ZMod n) => permutation 0) same
          have atOne := congrArg
            (fun permutation : Equiv.Perm (ZMod n) => permutation 1) same
          simp only [polygonPermutation_r_apply, polygonPermutation_sr_apply] at atZero atOne
          linear_combination atZero - atOne
      | sr secondOffset =>
          have atZero := congrArg
            (fun permutation : Equiv.Perm (ZMod n) => permutation 0) same
          simp only [polygonPermutation_sr_apply] at atZero
          have offsetsEqual : firstOffset = secondOffset := by
            simpa using atZero
          exact congrArg DihedralGroup.sr offsetsEqual

/-- Coordinate faithfulness follows structurally from faithfulness of the equatorial polygon. -/
theorem coordinateFaithful_of_two_ne_zero {n : Nat}
    (two_ne_zero : (2 : ZMod n) ≠ 0) : CoordinateFaithful n := by
  intro first second same
  apply Prod.ext
  · apply Equiv.ext
    intro axial
    have atAxial := congrArg
      (fun permutation : Equiv.Perm (Position n) => permutation (Sum.inl axial)) same
    exact Sum.inl.inj atAxial
  · apply polygonPermutation_injective two_ne_zero
    apply Equiv.ext
    intro equatorial
    have atEquatorial := congrArg
      (fun permutation : Equiv.Perm (Position n) => permutation (Sum.inr equatorial)) same
    exact Sum.inr.inj atEquatorial

/-- Recover one coordinate frame from membership in the full derived symmetry group. -/
noncomputable def fullFrameOfSymmetry {n : Nat}
    (symmetry : fullSymmetryGroup n) : CoordinateFrame n :=
  (Classical.choose symmetry.2, Classical.choose (Classical.choose_spec symmetry.2))

theorem coordinatePermutation_fullFrameOfSymmetry {n : Nat}
    (symmetry : fullSymmetryGroup n) :
    coordinatePermutation (fullFrameOfSymmetry symmetry).1
        (fullFrameOfSymmetry symmetry).2 = symmetry.1 := by
  unfold fullFrameOfSymmetry
  exact (Classical.choose_spec (Classical.choose_spec symmetry.2)).symm

/-- Faithfulness turns the coordinate presentation of the full group into an exact bijection. -/
noncomputable def fullCoordinateFrameEquiv {n : Nat}
    (faithful : CoordinateFaithful n) :
    CoordinateFrame n ≃ fullSymmetryGroup n where
  toFun frame :=
    ⟨coordinatePermutation frame.1 frame.2, ⟨frame.1, frame.2, rfl⟩⟩
  invFun := fullFrameOfSymmetry
  left_inv := by
    intro frame
    apply faithful
    exact coordinatePermutation_fullFrameOfSymmetry _
  right_inv := by
    intro symmetry
    apply Subtype.ext
    exact coordinatePermutation_fullFrameOfSymmetry symmetry

/-- Coordinate frames satisfying the spatial-orientation criterion. -/
abbrev ProperCoordinateFrame (n : Nat) :=
  { frame : CoordinateFrame n // frameOrientationSign frame.1 frame.2 = 1 }

/-- Recover one proper coordinate frame from proper-subgroup membership. -/
noncomputable def properFrameOfSymmetry {n : Nat}
    (symmetry : properSymmetryGroup n) : ProperCoordinateFrame n := by
  let axis := Classical.choose symmetry.2
  let axisCertificate := Classical.choose_spec symmetry.2
  let polygon := Classical.choose axisCertificate
  let certificate := Classical.choose_spec axisCertificate
  exact ⟨(axis, polygon), certificate.2⟩

theorem coordinatePermutation_properFrameOfSymmetry {n : Nat}
    (symmetry : properSymmetryGroup n) :
    coordinatePermutation (properFrameOfSymmetry symmetry).1.1
        (properFrameOfSymmetry symmetry).1.2 = symmetry.1 := by
  unfold properFrameOfSymmetry
  exact (Classical.choose_spec (Classical.choose_spec symmetry.2)).1.symm

/-- Faithfulness likewise identifies proper frames exactly with proper vertex symmetries. -/
noncomputable def properCoordinateFrameEquiv {n : Nat}
    (faithful : CoordinateFaithful n) :
    ProperCoordinateFrame n ≃ properSymmetryGroup n where
  toFun frame :=
    ⟨coordinatePermutation frame.1.1 frame.1.2,
      ⟨frame.1.1, frame.1.2, rfl, frame.2⟩⟩
  invFun := properFrameOfSymmetry
  left_inv := by
    intro frame
    apply Subtype.ext
    apply faithful
    exact coordinatePermutation_properFrameOfSymmetry _
  right_inv := by
    intro symmetry
    apply Subtype.ext
    exact coordinatePermutation_properFrameOfSymmetry symmetry

/-- The chosen equatorial reflection is not a proper rotation whenever the coordinate action is
faithful. -/
theorem mirror_not_mem_properSymmetryGroup {n : Nat}
    (faithful : CoordinateFaithful n) :
    mirror n ∉ properSymmetryGroup n := by
  rintro ⟨axis, polygon, same, proper⟩
  have sameFrame : (axis, polygon) = (1, .sr 0) := by
    apply faithful
    simpa [mirror] using same.symm
  cases sameFrame
  simp [frameOrientationSign, polygonOrientationSign] at proper

/-- An injective priority placement cannot be superimposed on its mirror by a proper rotation. -/
theorem injectivePlacement_not_properEquivalent_to_mirror {n : Nat}
    (faithful : CoordinateFaithful n) {Label : Type*}
    (placement : Position n → Label)
    (injective : Function.Injective placement) :
    ¬SymmetryEquivalent (properSymmetryGroup n) placement
      (relabel (mirror n) placement) := by
  rintro ⟨rotation, samePlacement⟩
  have samePermutation : mirror n = rotation.1 := by
    apply Equiv.ext
    intro position
    apply injective
    exact congrFun samePlacement position
  exact mirror_not_mem_properSymmetryGroup faithful
    (samePermutation ▸ rotation.2)

/-- **Exact absolute ideal-bipyramid theorem.**

For any faithful ideal bipyramid, every full relative orbit of an injectively priority-labelled
placement contains exactly two proper-rotation canonical indices: the placement class and its
mirror class. -/
theorem injectivePlacement_has_exactlyTwoAbsoluteIndices {n : Nat} [NeZero n]
    (faithful : CoordinateFaithful n)
    (placement : Position n → BlueBookP93.PriorityNumber)
    (injective : Function.Injective placement) :
    ExactTwoAbsoluteIndices (fullSymmetryGroup n) (properSymmetryGroup n) (mirror n)
      (fun position => priorityDigit (placement position)) := by
  let encodedPlacement := fun position => priorityDigit (placement position)
  have encodedInjective : Function.Injective encodedPlacement :=
    priorityDigit_injective.comp injective
  exact chiralRelativeOrbit_has_exactlyTwoAbsoluteIndices
    (fullSymmetryGroup n) (properSymmetryGroup n) (mirror n)
    (mirror_mem_fullSymmetryGroup n)
    (fullSymmetryGroup_proper_or_mirror_coset n) encodedPlacement
    (injectivePlacement_not_properEquivalent_to_mirror faithful encodedPlacement
      encodedInjective)

/-! The following four computations use ordinary kernel `decide`: their proof terms are reduced
and checked by Lean's kernel. -/

theorem coordinateFaithful_three : CoordinateFaithful 3 := by
  apply coordinateFaithful_of_two_ne_zero
  decide

theorem coordinateFaithful_five : CoordinateFaithful 5 := by
  apply coordinateFaithful_of_two_ne_zero
  decide

theorem coordinateFaithful_six : CoordinateFaithful 6 := by
  apply coordinateFaithful_of_two_ne_zero
  decide

theorem coordinateFaithful_seven : CoordinateFaithful 7 := by
  apply coordinateFaithful_of_two_ne_zero
  decide

noncomputable instance fullSymmetryGroupThreeFintype : Fintype (fullSymmetryGroup 3) :=
  Fintype.ofEquiv (CoordinateFrame 3)
    (fullCoordinateFrameEquiv coordinateFaithful_three)

noncomputable instance fullSymmetryGroupFiveFintype : Fintype (fullSymmetryGroup 5) :=
  Fintype.ofEquiv (CoordinateFrame 5)
    (fullCoordinateFrameEquiv coordinateFaithful_five)

noncomputable instance fullSymmetryGroupSixFintype : Fintype (fullSymmetryGroup 6) :=
  Fintype.ofEquiv (CoordinateFrame 6)
    (fullCoordinateFrameEquiv coordinateFaithful_six)

noncomputable instance fullSymmetryGroupSevenFintype : Fintype (fullSymmetryGroup 7) :=
  Fintype.ofEquiv (CoordinateFrame 7)
    (fullCoordinateFrameEquiv coordinateFaithful_seven)

noncomputable instance properSymmetryGroupThreeFintype : Fintype (properSymmetryGroup 3) :=
  Fintype.ofEquiv (ProperCoordinateFrame 3)
    (properCoordinateFrameEquiv coordinateFaithful_three)

noncomputable instance properSymmetryGroupFiveFintype : Fintype (properSymmetryGroup 5) :=
  Fintype.ofEquiv (ProperCoordinateFrame 5)
    (properCoordinateFrameEquiv coordinateFaithful_five)

noncomputable instance properSymmetryGroupSixFintype : Fintype (properSymmetryGroup 6) :=
  Fintype.ofEquiv (ProperCoordinateFrame 6)
    (properCoordinateFrameEquiv coordinateFaithful_six)

noncomputable instance properSymmetryGroupSevenFintype : Fintype (properSymmetryGroup 7) :=
  Fintype.ofEquiv (ProperCoordinateFrame 7)
    (properCoordinateFrameEquiv coordinateFaithful_seven)

/-- The represented full ideal-bipyramid groups have orders `4n`. -/
theorem card_fullSymmetryGroup_three : Fintype.card (fullSymmetryGroup 3) = 12 := by
  rw [← Fintype.card_congr (fullCoordinateFrameEquiv coordinateFaithful_three)]
  decide

theorem card_fullSymmetryGroup_five : Fintype.card (fullSymmetryGroup 5) = 20 := by
  rw [← Fintype.card_congr (fullCoordinateFrameEquiv coordinateFaithful_five)]
  decide

theorem card_fullSymmetryGroup_six : Fintype.card (fullSymmetryGroup 6) = 24 := by
  rw [← Fintype.card_congr (fullCoordinateFrameEquiv coordinateFaithful_six)]
  decide

theorem card_fullSymmetryGroup_seven : Fintype.card (fullSymmetryGroup 7) = 28 := by
  rw [← Fintype.card_congr (fullCoordinateFrameEquiv coordinateFaithful_seven)]
  decide

/-- Exactly half of each represented full group preserves spatial orientation. -/
theorem card_properSymmetryGroup_three : Fintype.card (properSymmetryGroup 3) = 6 := by
  rw [← Fintype.card_congr (properCoordinateFrameEquiv coordinateFaithful_three)]
  decide

theorem card_properSymmetryGroup_five : Fintype.card (properSymmetryGroup 5) = 10 := by
  rw [← Fintype.card_congr (properCoordinateFrameEquiv coordinateFaithful_five)]
  decide

theorem card_properSymmetryGroup_six : Fintype.card (properSymmetryGroup 6) = 12 := by
  rw [← Fintype.card_congr (properCoordinateFrameEquiv coordinateFaithful_six)]
  decide

theorem card_properSymmetryGroup_seven : Fintype.card (properSymmetryGroup 7) = 14 := by
  rw [← Fintype.card_congr (properCoordinateFrameEquiv coordinateFaithful_seven)]
  decide

/-- TBPY-5 has exactly two absolute classes for an injective five-priority placement. -/
theorem trigonalBipyramid_injectivePlacement_has_exactlyTwoAbsoluteIndices
    (placement : Position 3 → BlueBookP93.PriorityNumber)
    (injective : Function.Injective placement) :
    ExactTwoAbsoluteIndices (fullSymmetryGroup 3) (properSymmetryGroup 3) (mirror 3)
      (fun position => priorityDigit (placement position)) :=
  injectivePlacement_has_exactlyTwoAbsoluteIndices coordinateFaithful_three placement injective

/-- PBPY-7 has exactly two absolute classes for an injective seven-priority placement. -/
theorem pentagonalBipyramid_injectivePlacement_has_exactlyTwoAbsoluteIndices
    (placement : Position 5 → BlueBookP93.PriorityNumber)
    (injective : Function.Injective placement) :
    ExactTwoAbsoluteIndices (fullSymmetryGroup 5) (properSymmetryGroup 5) (mirror 5)
      (fun position => priorityDigit (placement position)) :=
  injectivePlacement_has_exactlyTwoAbsoluteIndices coordinateFaithful_five placement injective

/-- HBPY-8 has exactly two absolute classes for an injective eight-priority placement. -/
theorem hexagonalBipyramid_injectivePlacement_has_exactlyTwoAbsoluteIndices
    (placement : Position 6 → BlueBookP93.PriorityNumber)
    (injective : Function.Injective placement) :
    ExactTwoAbsoluteIndices (fullSymmetryGroup 6) (properSymmetryGroup 6) (mirror 6)
      (fun position => priorityDigit (placement position)) :=
  injectivePlacement_has_exactlyTwoAbsoluteIndices coordinateFaithful_six placement injective

/-- HBPY-9 has exactly two absolute classes for an injective nine-priority placement. -/
theorem heptagonalBipyramid_injectivePlacement_has_exactlyTwoAbsoluteIndices
    (placement : Position 7 → BlueBookP93.PriorityNumber)
    (injective : Function.Injective placement) :
    ExactTwoAbsoluteIndices (fullSymmetryGroup 7) (properSymmetryGroup 7) (mirror 7)
      (fun position => priorityDigit (placement position)) :=
  injectivePlacement_has_exactlyTwoAbsoluteIndices coordinateFaithful_seven placement injective

/-- Reversing the observed equatorial progression reverses the independent IR-9 `A/C` symbol. -/
def oppositeRotationSense : BlueBookP93.RotationSense → BlueBookP93.RotationSense
  | .clockwise => .counterclockwise
  | .counterclockwise => .clockwise

theorem chiralitySymbol_oppositeRotationSense
    (sense : BlueBookP93.RotationSense) :
    BlueBookP93.chiralitySymbol (oppositeRotationSense sense) =
      match BlueBookP93.chiralitySymbol sense with
      | .A => .C
      | .C => .A := by
  cases sense <;> rfl

end TetraStereo.OneCenter.RedBookIR9.BipyramidalAbsoluteSymmetry
