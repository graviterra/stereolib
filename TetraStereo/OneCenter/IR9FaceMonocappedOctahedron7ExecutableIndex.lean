import TetraStereo.OneCenter.IR9FaceMonocappedOctahedron7SourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness

open FiniteSymmetry

/-!
# Executable OCF-7 complete mathematical index

The independent OCF-7 module proves that simultaneous permutations of the three capped-face
corners exhaust the six-element full symmetry group.  This downstream refinement enumerates those
six frames directly and proves that its computable minimum induces exactly the same symmetry
classification as the existing mathematical `sourceIndex`.

The result remains a complete relative symmetry word.  It is not presented as an unpublished
Red Book short digit recipe and does not introduce an unsupported absolute `A`/`C` convention.
-/

/-- One complete encoded OCF-7 word in the frame selected by a permutation of the three capped
face corners. -/
def coordinateOrbitCode (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) : List PriorityDigit :=
  typedPositionOrder.map fun position =>
    priorityDigit (placement (coordinatePermutation frame position))

/-- The six explicitly enumerable OCF-7 frame words.  Unlike enumeration of the subtype-valued
signature group, this definition is directly executable. -/
def coordinateOrbitCodes (placement : Position → PriorityNumber) :
    Finset (List PriorityDigit) :=
  Finset.univ.image (coordinateOrbitCode placement)

theorem coordinateOrbitCodes_nonempty (placement : Position → PriorityNumber) :
    (coordinateOrbitCodes placement).Nonempty := by
  exact ⟨coordinateOrbitCode placement 1, by simp [coordinateOrbitCodes]⟩

/-- Computable OCF-7 mathematical completion: choose the least complete priority word among the
six explicit simultaneous corner frames. -/
def executableSourceIndex (placement : Position → PriorityNumber) : List PriorityDigit :=
  (coordinateOrbitCodes placement).min' (coordinateOrbitCodes_nonempty placement)

theorem coordinatePermutation_mul (first second : CoordinateFrame) :
    coordinatePermutation first * coordinatePermutation second =
      coordinatePermutation (first * second) := by
  apply Equiv.ext
  intro position
  cases position <;> simp [coordinatePermutation]

theorem coordinatePermutation_inv (frame : CoordinateFrame) :
    (coordinatePermutation frame)⁻¹ = coordinatePermutation frame⁻¹ := by
  apply Equiv.ext
  intro position
  cases position <;> simp [coordinatePermutation]

theorem coordinatePermutation_one :
    coordinatePermutation (1 : CoordinateFrame) = 1 := by
  apply Equiv.ext
  intro position
  cases position <;> simp [coordinatePermutation]

theorem coordinateOrbitCode_relabel (placement : Position → PriorityNumber)
    (relabelFrame frame : CoordinateFrame) :
    coordinateOrbitCode (relabel (coordinatePermutation relabelFrame) placement) frame =
      coordinateOrbitCode placement (relabelFrame * frame) := by
  unfold coordinateOrbitCode
  apply List.map_congr_left
  intro position _member
  apply congrArg priorityDigit
  apply congrArg placement
  exact DFunLike.congr_fun (coordinatePermutation_mul relabelFrame frame) position

theorem coordinateOrbitCodes_relabel (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) :
    coordinateOrbitCodes (relabel (coordinatePermutation frame) placement) =
      coordinateOrbitCodes placement := by
  ext code
  simp only [coordinateOrbitCodes, Finset.mem_image, Finset.mem_univ, true_and,
    coordinateOrbitCode_relabel]
  constructor
  · rintro ⟨candidate, rfl⟩
    exact ⟨frame * candidate, rfl⟩
  · rintro ⟨candidate, rfl⟩
    refine ⟨frame⁻¹ * candidate, ?_⟩
    simp

theorem executableSourceIndex_relabel (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) :
    executableSourceIndex (relabel (coordinatePermutation frame) placement) =
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

/-- Exact executable OCF-7 completeness: two words collide precisely when a full idealized OCF-7
symmetry transports one complete priority placement to the other. -/
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
        left (coordinatePermutation leftFrame position) =
          right (coordinatePermutation rightFrame position) := by
      intro position
      apply priorityDigit_injective
      exact eq_on_of_map_eq_map codesEqual (mem_typedPositionOrder position)
    refine ⟨coordinateSymmetry (leftFrame * rightFrame⁻¹), ?_⟩
    funext position
    change right position =
      left (coordinatePermutation (leftFrame * rightFrame⁻¹) position)
    have canceled : coordinatePermutation rightFrame
        (coordinatePermutation rightFrame⁻¹ position) = position := by
      have composed := DFunLike.congr_fun
        (coordinatePermutation_mul rightFrame rightFrame⁻¹) position
      simpa [coordinatePermutation_one] using composed
    calc
      right position = right (coordinatePermutation rightFrame
          (coordinatePermutation rightFrame⁻¹ position)) :=
        congrArg right canceled.symm
      _ = left (coordinatePermutation leftFrame
          (coordinatePermutation rightFrame⁻¹ position)) :=
        (pointwise (coordinatePermutation rightFrame⁻¹ position)).symm
      _ = left (coordinatePermutation (leftFrame * rightFrame⁻¹) position) := by
        exact congrArg left (DFunLike.congr_fun
          (coordinatePermutation_mul leftFrame rightFrame⁻¹) position)
  · rintro ⟨symmetry, rfl⟩
    obtain ⟨frame, rfl⟩ := coordinateSymmetry_surjective symmetry
    exact (executableSourceIndex_relabel left frame).symm

/-- The executable and pre-existing noncomputable words use potentially different complete
position enumerations, but they identify exactly the same relative configurations. -/
theorem executableSourceIndex_sameClassification_as_source
    (left right : Position → PriorityNumber) :
    executableSourceIndex left = executableSourceIndex right ↔
      sourceIndex left = sourceIndex right := by
  rw [executableSourceIndex_eq_iff_symmetryEquivalent,
    sourceIndex_eq_iff_symmetryEquivalent]

/-- Executable production-facing OCF-7 complete mathematical index.  Its result is still the
seven-entry symmetry word, not an unpublished geometry-specific short syntax. -/
def executableFaceMonocappedOctahedronConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  executableSourceIndex
    (fun position => BlueBookP93.priorityOfProduction (placement position))

/-- Executable and existing mathematical production words have exactly the same collision
boundary, even though their internal complete position enumerations need not be identical. -/
theorem executableFaceMonocappedOctahedronConfigurationIndex_sameClassification_as_mathematical
    (left right : Position → PolyhedralPriorityNumber) :
    executableFaceMonocappedOctahedronConfigurationIndex left =
        executableFaceMonocappedOctahedronConfigurationIndex right ↔
      faceMonocappedOctahedronConfigurationIndex left =
        faceMonocappedOctahedronConfigurationIndex right := by
  exact executableSourceIndex_sameClassification_as_source
    (fun position => BlueBookP93.priorityOfProduction (left position))
    (fun position => BlueBookP93.priorityOfProduction (right position))

end TetraStereo.OneCenter.RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness
