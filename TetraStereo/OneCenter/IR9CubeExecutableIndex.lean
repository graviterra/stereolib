import TetraStereo.OneCenter.IR9CubeSourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.CubeSourceIndexCompleteness

open FiniteSymmetry

/-!
# Executable CU-8 complete mathematical index

The source-completeness module proves that the 48 signed-coordinate frames exhaust the full
ideal-cube symmetry group.  This refinement enumerates those frames directly and chooses the least
complete eight-position priority word.  The output is the mathematical completion of the general
IR-9.3.3.2 distinguishing requirement, not an unpublished short CU-8 recipe, and introduces no
absolute `A`/`C` convention.
-/

/-- Explicit binary-coordinate order used by the executable word: `000`, `001`, ..., `111`. -/
def executableTypedPositionOrder : List Position :=
  [ ![false, false, false], ![false, false, true],
    ![false, true, false],  ![false, true, true],
    ![true, false, false],  ![true, false, true],
    ![true, true, false],   ![true, true, true] ]

theorem executableTypedPositionOrder_nodup : executableTypedPositionOrder.Nodup := by
  decide

theorem mem_executableTypedPositionOrder (position : Position) :
    position ∈ executableTypedPositionOrder := by
  fin_cases position <;> decide

/-- Assign values to the eight typed binary-coordinate roles in `000`, ..., `111` order. -/
def placementOfEntries {α : Type}
    (v000 v001 v010 v011 v100 v101 v110 v111 : α) : Position → α :=
  fun position =>
    if position 0 then
      if position 1 then
        if position 2 then v111 else v110
      else if position 2 then v101 else v100
    else if position 1 then
      if position 2 then v011 else v010
    else if position 2 then v001 else v000

/-- One complete cube word in a selected signed-coordinate frame. -/
def coordinateOrbitCode (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) : List PriorityDigit :=
  executableTypedPositionOrder.map fun position =>
    priorityDigit (placement (coordinatePermutation frame.1 frame.2 position))

/-- All 48 explicitly enumerable ideal-cube frame words. -/
def coordinateOrbitCodes (placement : Position → PriorityNumber) :
    Finset (List PriorityDigit) :=
  Finset.univ.image (coordinateOrbitCode placement)

theorem coordinateOrbitCodes_nonempty (placement : Position → PriorityNumber) :
    (coordinateOrbitCodes placement).Nonempty := by
  exact ⟨coordinateOrbitCode placement (origin, 1), by simp [coordinateOrbitCodes]⟩

/-- Computable CU-8 mathematical completion: the least complete word among all 48 frames. -/
def executableSourceIndex (placement : Position → PriorityNumber) : List PriorityDigit :=
  (coordinateOrbitCodes placement).min' (coordinateOrbitCodes_nonempty placement)

/-- Composition on the directly enumerable coordinate-frame carrier. -/
def composeFrame (first second : CoordinateFrame) : CoordinateFrame :=
  (composeFlip first.1 first.2 second.1, first.2 * second.2)

/-- Inverse on the directly enumerable coordinate-frame carrier. -/
def inverseFrame (frame : CoordinateFrame) : CoordinateFrame :=
  (inverseFlip frame.1 frame.2, frame.2⁻¹)

theorem coordinatePermutation_compose (first second : CoordinateFrame) :
    coordinatePermutation first.1 first.2 * coordinatePermutation second.1 second.2 =
      coordinatePermutation (composeFrame first second).1
        (composeFrame first second).2 := by
  exact coordinatePermutation_mul first.1 first.2 second.1 second.2

theorem coordinatePermutation_inverseFrame (frame : CoordinateFrame) :
    (coordinatePermutation frame.1 frame.2)⁻¹ =
      coordinatePermutation (inverseFrame frame).1 (inverseFrame frame).2 := by
  exact coordinatePermutation_inverse frame.1 frame.2

theorem composeFrame_inverse_right (frame candidate : CoordinateFrame) :
    composeFrame frame (composeFrame (inverseFrame frame) candidate) = candidate := by
  apply coordinateSymmetry_injective
  apply Subtype.ext
  change coordinatePermutation
      (composeFrame frame (composeFrame (inverseFrame frame) candidate)).1
        (composeFrame frame (composeFrame (inverseFrame frame) candidate)).2 =
    coordinatePermutation candidate.1 candidate.2
  rw [← coordinatePermutation_compose, ← coordinatePermutation_compose,
    ← coordinatePermutation_inverseFrame]
  simp

theorem coordinateOrbitCode_relabel (placement : Position → PriorityNumber)
    (relabelFrame frame : CoordinateFrame) :
    coordinateOrbitCode
        (relabel (coordinatePermutation relabelFrame.1 relabelFrame.2) placement) frame =
      coordinateOrbitCode placement (composeFrame relabelFrame frame) := by
  unfold coordinateOrbitCode
  apply List.map_congr_left
  intro position _member
  apply congrArg priorityDigit
  apply congrArg placement
  exact DFunLike.congr_fun (coordinatePermutation_compose relabelFrame frame) position

theorem coordinateOrbitCodes_relabel (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) :
    coordinateOrbitCodes
        (relabel (coordinatePermutation frame.1 frame.2) placement) =
      coordinateOrbitCodes placement := by
  ext code
  simp only [coordinateOrbitCodes, Finset.mem_image, Finset.mem_univ, true_and,
    coordinateOrbitCode_relabel]
  constructor
  · rintro ⟨candidate, rfl⟩
    exact ⟨composeFrame frame candidate, rfl⟩
  · rintro ⟨candidate, rfl⟩
    refine ⟨composeFrame (inverseFrame frame) candidate, ?_⟩
    rw [composeFrame_inverse_right]

theorem executableSourceIndex_relabel (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) :
    executableSourceIndex
        (relabel (coordinatePermutation frame.1 frame.2) placement) =
      executableSourceIndex placement := by
  simp only [executableSourceIndex, coordinateOrbitCodes_relabel]

private theorem eq_on_of_map_eq_map {α β : Type*} {entries : List α}
    {left right : α → β} (same : entries.map left = entries.map right)
    {entry : α} (member : entry ∈ entries) : left entry = right entry := by
  induction entries with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.cons.injEq] at same
      rcases same with ⟨sameHead, sameTail⟩
      rcases List.mem_cons.mp member with sameEntry | memberTail
      · subst entry
        exact sameHead
      · exact inductionHypothesis sameTail memberTail

/-- Exact executable CU-8 completeness: equality is precisely full ideal-cube symmetry. -/
theorem executableSourceIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber) :
    executableSourceIndex left = executableSourceIndex right ↔ Equivalent left right := by
  constructor
  · intro sameIndex
    have leftMember := Finset.min'_mem
      (coordinateOrbitCodes left) (coordinateOrbitCodes_nonempty left)
    have rightMember := Finset.min'_mem
      (coordinateOrbitCodes right) (coordinateOrbitCodes_nonempty right)
    rcases Finset.mem_image.mp leftMember with ⟨leftFrame, _, leftCode⟩
    rcases Finset.mem_image.mp rightMember with ⟨rightFrame, _, rightCode⟩
    have codesEqual : coordinateOrbitCode left leftFrame =
        coordinateOrbitCode right rightFrame := by
      exact leftCode.trans (sameIndex.trans rightCode.symm)
    have pointwise : ∀ position,
        left (coordinatePermutation leftFrame.1 leftFrame.2 position) =
          right (coordinatePermutation rightFrame.1 rightFrame.2 position) := by
      intro position
      apply priorityDigit_injective
      exact eq_on_of_map_eq_map codesEqual (mem_executableTypedPositionOrder position)
    let transported := composeFrame leftFrame (inverseFrame rightFrame)
    refine ⟨coordinateSymmetry transported, ?_⟩
    funext position
    change right position =
      left (coordinatePermutation transported.1 transported.2 position)
    have canceled : coordinatePermutation rightFrame.1 rightFrame.2
        (coordinatePermutation (inverseFrame rightFrame).1
          (inverseFrame rightFrame).2 position) = position := by
      have canceledBase :=
        (coordinatePermutation rightFrame.1 rightFrame.2).apply_symm_apply position
      rw [← coordinatePermutation_inverseFrame] at *
      exact canceledBase
    calc
      right position = right (coordinatePermutation rightFrame.1 rightFrame.2
          (coordinatePermutation (inverseFrame rightFrame).1
            (inverseFrame rightFrame).2 position)) := congrArg right canceled.symm
      _ = left (coordinatePermutation leftFrame.1 leftFrame.2
          (coordinatePermutation (inverseFrame rightFrame).1
            (inverseFrame rightFrame).2 position)) :=
        (pointwise (coordinatePermutation (inverseFrame rightFrame).1
          (inverseFrame rightFrame).2 position)).symm
      _ = left (coordinatePermutation transported.1 transported.2 position) := by
        exact congrArg left (DFunLike.congr_fun
          (coordinatePermutation_compose leftFrame (inverseFrame rightFrame)) position)
  · rintro ⟨symmetry, rfl⟩
    obtain ⟨frame, rfl⟩ := coordinateSymmetry_surjective symmetry
    exact (executableSourceIndex_relabel left frame).symm

/-- Executable and existing mathematical CU-8 words induce exactly the same classification. -/
theorem executableSourceIndex_sameClassification_as_source
    (left right : Position → PriorityNumber) :
    executableSourceIndex left = executableSourceIndex right ↔
      sourceIndex left = sourceIndex right := by
  rw [executableSourceIndex_eq_iff_symmetryEquivalent,
    sourceIndex_eq_iff_symmetryEquivalent]

/-- Executable production-facing complete CU-8 mathematical word. -/
def executableCubeConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  executableSourceIndex
    (fun position => BlueBookP93.priorityOfProduction (placement position))

/-- Executable and mathematical production entries have the same exact collision boundary. -/
theorem executableCubeConfigurationIndex_sameClassification_as_mathematical
    (left right : Position → PolyhedralPriorityNumber) :
    executableCubeConfigurationIndex left = executableCubeConfigurationIndex right ↔
      cubeCompleteConfigurationIndex left = cubeCompleteConfigurationIndex right := by
  exact executableSourceIndex_sameClassification_as_source
    (fun position => BlueBookP93.priorityOfProduction (left position))
    (fun position => BlueBookP93.priorityOfProduction (right position))

end TetraStereo.OneCenter.RedBookIR9.CubeSourceIndexCompleteness
