import TetraStereo.OneCenter.IR9SquareAntiprism8SourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquareAntiprism8SourceIndexCompleteness

open FiniteSymmetry

/-!
# Executable SAPR-8 complete mathematical index

The source-completeness module proves that the sixteen alternating-rim dihedral frames exhaust the
full ideal square-antiprism symmetry group.  This refinement enumerates those frames directly and
chooses the least complete eight-position priority word.  The output is the mathematical
completion of IR-9.3.3.2, not an unpublished SAPR-8 short recipe, and it introduces no absolute
`A`/`C` convention.
-/

/-- Explicit alternating-rim order used by the executable word. -/
def executableTypedPositionOrder : List Position := [0, 1, 2, 3, 4, 5, 6, 7]

theorem executableTypedPositionOrder_nodup : executableTypedPositionOrder.Nodup := by
  decide

theorem mem_executableTypedPositionOrder (position : Position) :
    position ∈ executableTypedPositionOrder := by
  fin_cases position <;> decide

/-- Assign values to the eight alternating-rim roles in cyclic order. -/
def placementOfEntries {alpha : Type}
    (v0 v1 v2 v3 v4 v5 v6 v7 : alpha) : Position → alpha :=
  fun position => ![v0, v1, v2, v3, v4, v5, v6, v7] position

/-- One complete SAPR-8 word in a selected dihedral frame. -/
def coordinateOrbitCode (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) : List PriorityDigit :=
  executableTypedPositionOrder.map fun position =>
    priorityDigit (placement (coordinatePermutation frame position))

/-- All sixteen explicitly enumerable ideal square-antiprism frame words. -/
def coordinateOrbitCodes (placement : Position → PriorityNumber) :
    Finset (List PriorityDigit) :=
  Finset.univ.image (coordinateOrbitCode placement)

theorem coordinateOrbitCodes_nonempty (placement : Position → PriorityNumber) :
    (coordinateOrbitCodes placement).Nonempty := by
  exact ⟨coordinateOrbitCode placement 1, by simp [coordinateOrbitCodes]⟩

/-- Computable SAPR-8 mathematical completion: the least complete word among all sixteen
frames. -/
def executableSourceIndex (placement : Position → PriorityNumber) : List PriorityDigit :=
  (coordinateOrbitCodes placement).min' (coordinateOrbitCodes_nonempty placement)

theorem coordinateOrbitCode_relabel (placement : Position → PriorityNumber)
    (relabelFrame frame : CoordinateFrame) :
    coordinateOrbitCode
        (relabel (coordinatePermutation relabelFrame) placement) frame =
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

private theorem eq_on_of_map_eq_map {alpha beta : Type} {entries : List alpha}
    {left right : alpha → beta} (same : entries.map left = entries.map right)
    {entry : alpha} (member : entry ∈ entries) : left entry = right entry := by
  induction entries with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.cons.injEq] at same
      rcases same with ⟨sameHead, sameTail⟩
      rcases List.mem_cons.mp member with sameEntry | memberTail
      · subst entry
        exact sameHead
      · exact inductionHypothesis sameTail memberTail

/-- Exact executable SAPR-8 completeness: equality is precisely full idealized symmetry. -/
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
        coordinateOrbitCode right rightFrame :=
      leftCode.trans (sameIndex.trans rightCode.symm)
    have pointwise : ∀ position,
        left (coordinatePermutation leftFrame position) =
          right (coordinatePermutation rightFrame position) := by
      intro position
      apply priorityDigit_injective
      exact eq_on_of_map_eq_map codesEqual
        (mem_executableTypedPositionOrder position)
    let transported := leftFrame * rightFrame⁻¹
    refine ⟨coordinateSymmetry transported, ?_⟩
    funext position
    change right position = left (coordinatePermutation transported position)
    have canceled : coordinatePermutation rightFrame
        (coordinatePermutation rightFrame⁻¹ position) = position := by
      rw [← coordinatePermutation_inv]
      exact (coordinatePermutation rightFrame).apply_symm_apply position
    calc
      right position = right (coordinatePermutation rightFrame
          (coordinatePermutation rightFrame⁻¹ position)) := congrArg right canceled.symm
      _ = left (coordinatePermutation leftFrame
          (coordinatePermutation rightFrame⁻¹ position)) :=
        (pointwise (coordinatePermutation rightFrame⁻¹ position)).symm
      _ = left (coordinatePermutation transported position) := by
        exact congrArg left (DFunLike.congr_fun
          (coordinatePermutation_mul leftFrame rightFrame⁻¹) position)
  · rintro ⟨symmetry, rfl⟩
    obtain ⟨frame, rfl⟩ := coordinateSymmetry_surjective symmetry
    exact (executableSourceIndex_relabel left frame).symm

/-- Executable and existing mathematical SAPR-8 words induce exactly the same classification. -/
theorem executableSourceIndex_sameClassification_as_source
    (left right : Position → PriorityNumber) :
    executableSourceIndex left = executableSourceIndex right ↔
      sourceIndex left = sourceIndex right := by
  rw [executableSourceIndex_eq_iff_symmetryEquivalent,
    sourceIndex_eq_iff_symmetryEquivalent]

/-- Executable production-facing complete SAPR-8 mathematical word. -/
def executableSquareAntiprismConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  executableSourceIndex
    (fun position => BlueBookP93.priorityOfProduction (placement position))

/-- Executable and mathematical production entries have the same exact collision boundary. -/
theorem executableSquareAntiprismConfigurationIndex_sameClassification_as_mathematical
    (left right : Position → PolyhedralPriorityNumber) :
    executableSquareAntiprismConfigurationIndex left =
        executableSquareAntiprismConfigurationIndex right ↔
      squareAntiprismCompleteConfigurationIndex left =
        squareAntiprismCompleteConfigurationIndex right := by
  exact executableSourceIndex_sameClassification_as_source
    (fun position => BlueBookP93.priorityOfProduction (left position))
    (fun position => BlueBookP93.priorityOfProduction (right position))

end TetraStereo.OneCenter.RedBookIR9.SquareAntiprism8SourceIndexCompleteness
