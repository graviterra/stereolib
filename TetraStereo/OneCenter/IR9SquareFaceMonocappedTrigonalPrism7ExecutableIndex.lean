import TetraStereo.OneCenter.IR9SquareFaceMonocappedTrigonalPrism7SourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquareFaceMonocappedTrigonalPrism7SourceIndexCompleteness

open FiniteSymmetry
open SquareFaceMonocappedTrigonalPrism7FiniteSymmetry

/-!
# Executable TPRS-7 complete mathematical index

The independent TPRS-7 development proves that exchanging the triangular faces and optionally
reflecting the capped-square corners exhausts the four-element full symmetry group.  This module
enumerates those four coordinate frames directly and proves that its computable minimum has
exactly the same collision classes as the mathematical `sourceGeneralIndex`.

This remains a complete relative symmetry word.  It is not an unpublished short Red Book digit
recipe and it supplies no unsupported absolute `A`/`C` convention.
-/

/-- One complete encoded TPRS-7 word in a selected coordinate frame. -/
def coordinateOrbitCode (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) : List PriorityDigit :=
  typedPositionOrder.map fun position =>
    priorityDigit (placement (coordinatePermutation frame.1 frame.2 position))

/-- The four directly enumerable TPRS-7 coordinate-frame words. -/
def coordinateOrbitCodes (placement : Position → PriorityNumber) :
    Finset (List PriorityDigit) :=
  Finset.univ.image (coordinateOrbitCode placement)

theorem coordinateOrbitCodes_nonempty (placement : Position → PriorityNumber) :
    (coordinateOrbitCodes placement).Nonempty := by
  exact ⟨coordinateOrbitCode placement (1, false), by simp [coordinateOrbitCodes]⟩

/-- Computable TPRS-7 mathematical completion: the least complete priority word among the four
explicit idealized coordinate frames. -/
def executableSourceIndex (placement : Position → PriorityNumber) : List PriorityDigit :=
  (coordinateOrbitCodes placement).min' (coordinateOrbitCodes_nonempty placement)

/-- Composition of the face exchange and capped-square reflection coordinates. -/
def composeFrame (first second : CoordinateFrame) : CoordinateFrame :=
  (first.1 * second.1, first.2 != second.2)

/-- Inversion of a TPRS-7 coordinate frame.  The corner reflection is self-inverse. -/
def inverseFrame (frame : CoordinateFrame) : CoordinateFrame :=
  (frame.1⁻¹, frame.2)

theorem coordinatePermutation_compose (first second : CoordinateFrame) :
    coordinatePermutation first.1 first.2 * coordinatePermutation second.1 second.2 =
      coordinatePermutation (composeFrame first second).1 (composeFrame first second).2 := by
  rcases first with ⟨firstFace, firstReflect⟩
  rcases second with ⟨secondFace, secondReflect⟩
  apply Equiv.ext
  intro position
  cases firstReflect <;> cases secondReflect <;> cases position with
  | cap => rfl
  | prismVertex face corner =>
      fin_cases corner <;>
        simp [composeFrame, coordinatePermutation, cornerPermutation,
          cappedSquareReflection]

theorem coordinatePermutation_inverse (frame : CoordinateFrame) :
    (coordinatePermutation frame.1 frame.2)⁻¹ =
      coordinatePermutation (inverseFrame frame).1 (inverseFrame frame).2 := by
  rcases frame with ⟨face, reflect⟩
  apply Equiv.ext
  intro position
  cases reflect <;> cases position with
  | cap => rfl
  | prismVertex side corner =>
      fin_cases corner <;>
        simp [inverseFrame, coordinatePermutation, cornerPermutation,
          cappedSquareReflection]

theorem composeFrame_inverse_left (frame candidate : CoordinateFrame) :
    composeFrame (inverseFrame frame) (composeFrame frame candidate) = candidate := by
  rcases frame with ⟨face, reflect⟩
  rcases candidate with ⟨candidateFace, candidateReflect⟩
  cases reflect <;> cases candidateReflect <;>
    simp [composeFrame, inverseFrame]

theorem composeFrame_inverse_right (frame candidate : CoordinateFrame) :
    composeFrame frame (composeFrame (inverseFrame frame) candidate) = candidate := by
  rcases frame with ⟨face, reflect⟩
  rcases candidate with ⟨candidateFace, candidateReflect⟩
  cases reflect <;> cases candidateReflect <;>
    simp [composeFrame, inverseFrame]

theorem coordinatePermutation_identity :
    coordinatePermutation (1 : Equiv.Perm (Fin 2)) false = 1 := by
  apply Equiv.ext
  intro position
  cases position with
  | cap => rfl
  | prismVertex side corner => simp [coordinatePermutation, cornerPermutation]

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

/-- Exact executable TPRS-7 completeness: two words collide precisely when a full idealized
TPRS-7 symmetry transports one complete priority placement to the other. -/
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
      exact eq_on_of_map_eq_map codesEqual (mem_typedPositionOrder position)
    let transported := composeFrame leftFrame (inverseFrame rightFrame)
    refine ⟨coordinateSymmetry transported, ?_⟩
    funext position
    change right position =
      left (coordinatePermutation transported.1 transported.2 position)
    have canceled : coordinatePermutation rightFrame.1 rightFrame.2
        (coordinatePermutation (inverseFrame rightFrame).1
          (inverseFrame rightFrame).2 position) = position := by
      have composed := DFunLike.congr_fun
        (coordinatePermutation_compose rightFrame (inverseFrame rightFrame)) position
      simpa [composeFrame, inverseFrame, coordinatePermutation_identity] using composed
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

/-- The executable and mathematical indices may select different reference words, but identify
exactly the same relative configurations. -/
theorem executableSourceIndex_sameClassification_as_source
    (left right : Position → PriorityNumber) :
    executableSourceIndex left = executableSourceIndex right ↔
      sourceGeneralIndex left = sourceGeneralIndex right := by
  rw [executableSourceIndex_eq_iff_symmetryEquivalent,
    sourceGeneralIndex_eq_iff_symmetryEquivalent]

/-- Executable production-facing TPRS-7 complete mathematical word. -/
def executableSquareFaceMonocappedTrigonalPrismConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  executableSourceIndex
    (fun position => BlueBookP93.priorityOfProduction (placement position))

/-- The executable and mathematical production entries have the same exact collision boundary. -/
theorem executableSquareFaceMonocappedTrigonalPrismConfigurationIndex_sameClassification_as_mathematical
    (left right : Position → PolyhedralPriorityNumber) :
    executableSquareFaceMonocappedTrigonalPrismConfigurationIndex left =
        executableSquareFaceMonocappedTrigonalPrismConfigurationIndex right ↔
      squareFaceMonocappedTrigonalPrismConfigurationIndex left =
        squareFaceMonocappedTrigonalPrismConfigurationIndex right := by
  exact executableSourceIndex_sameClassification_as_source
    (fun position => BlueBookP93.priorityOfProduction (left position))
    (fun position => BlueBookP93.priorityOfProduction (right position))

end TetraStereo.OneCenter.RedBookIR9.SquareFaceMonocappedTrigonalPrism7SourceIndexCompleteness
