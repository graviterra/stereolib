import TetraStereo.OneCenter.IR9TransBicappedOctahedron8SourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness

open FiniteSymmetry

/-!
# Executable OCT-8 complete mathematical index

The source-completeness module proves that the twelve face-exchange/pair-permutation frames exhaust
the full ideal trans-bicapped-octahedron symmetry group.  This refinement enumerates those frames
directly and chooses the least complete eight-position priority word.  The output is the
mathematical completion of IR-9.3.3.2, not an unpublished OCT-8 short recipe, and it introduces no
absolute `A`/`C` convention.
-/

/-- Explicit typed order: the two opposite caps followed by the three base vertices incident to
side zero and then the three incident to side one. -/
def executableTypedPositionOrder : List Position :=
  [.cap 0, .cap 1,
    .baseVertex 0 0, .baseVertex 0 1, .baseVertex 0 2,
    .baseVertex 1 0, .baseVertex 1 1, .baseVertex 1 2]

theorem executableTypedPositionOrder_nodup : executableTypedPositionOrder.Nodup := by
  decide

theorem mem_executableTypedPositionOrder (position : Position) :
    position ∈ executableTypedPositionOrder := by
  cases position with
  | cap side => fin_cases side <;> decide
  | baseVertex side pair => fin_cases side <;> fin_cases pair <;> decide

/-- Assign values to the typed cap and base-incidence roles. -/
def placementOfEntries {alpha : Type}
    (cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2 : alpha) : Position → alpha
  | .cap side => ![cap0, cap1] side
  | .baseVertex side pair =>
      ![![s0p0, s0p1, s0p2], ![s1p0, s1p1, s1p2]] side pair

/-- One complete OCT-8 word in a selected structural frame. -/
def coordinateOrbitCode (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) : List PriorityDigit :=
  executableTypedPositionOrder.map fun position =>
    priorityDigit (placement (coordinatePermutation frame.1 frame.2 position))

/-- All twelve explicitly enumerable ideal trans-bicapped-octahedron frame words. -/
def coordinateOrbitCodes (placement : Position → PriorityNumber) :
    Finset (List PriorityDigit) :=
  Finset.univ.image (coordinateOrbitCode placement)

theorem coordinateOrbitCodes_nonempty (placement : Position → PriorityNumber) :
    (coordinateOrbitCodes placement).Nonempty := by
  exact ⟨coordinateOrbitCode placement 1, by simp [coordinateOrbitCodes]⟩

/-- Computable OCT-8 mathematical completion: the least complete word among all twelve
frames. -/
def executableSourceIndex (placement : Position → PriorityNumber) : List PriorityDigit :=
  (coordinateOrbitCodes placement).min' (coordinateOrbitCodes_nonempty placement)

theorem coordinateOrbitCode_relabel (placement : Position → PriorityNumber)
    (relabelFrame frame : CoordinateFrame) :
    coordinateOrbitCode
        (relabel (coordinatePermutation relabelFrame.1 relabelFrame.2) placement) frame =
      coordinateOrbitCode placement (relabelFrame * frame) := by
  unfold coordinateOrbitCode
  apply List.map_congr_left
  intro position _member
  apply congrArg priorityDigit
  apply congrArg placement
  exact DFunLike.congr_fun
    (coordinatePermutation_mul relabelFrame.1 frame.1 relabelFrame.2 frame.2) position

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
    exact ⟨frame * candidate, rfl⟩
  · rintro ⟨candidate, rfl⟩
    refine ⟨frame⁻¹ * candidate, ?_⟩
    simp

theorem executableSourceIndex_relabel (placement : Position → PriorityNumber)
    (frame : CoordinateFrame) :
    executableSourceIndex
        (relabel (coordinatePermutation frame.1 frame.2) placement) =
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

/-- Exact executable OCT-8 completeness: equality is precisely full idealized symmetry. -/
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
        left (coordinatePermutation leftFrame.1 leftFrame.2 position) =
          right (coordinatePermutation rightFrame.1 rightFrame.2 position) := by
      intro position
      apply priorityDigit_injective
      exact eq_on_of_map_eq_map codesEqual
        (mem_executableTypedPositionOrder position)
    let transported := leftFrame * rightFrame⁻¹
    refine ⟨coordinateSymmetry transported, ?_⟩
    funext position
    change right position =
      left (coordinatePermutation transported.1 transported.2 position)
    have canceled : coordinatePermutation rightFrame.1 rightFrame.2
        (coordinatePermutation rightFrame⁻¹.1 rightFrame⁻¹.2 position) = position := by
      have inverseFramePermutation :
          coordinatePermutation rightFrame⁻¹.1 rightFrame⁻¹.2 =
            (coordinatePermutation rightFrame.1 rightFrame.2)⁻¹ := by
        simpa using (coordinatePermutation_inv rightFrame.1 rightFrame.2).symm
      rw [inverseFramePermutation]
      exact (coordinatePermutation rightFrame.1 rightFrame.2).apply_symm_apply position
    calc
      right position = right (coordinatePermutation rightFrame.1 rightFrame.2
          (coordinatePermutation rightFrame⁻¹.1 rightFrame⁻¹.2 position)) :=
        congrArg right canceled.symm
      _ = left (coordinatePermutation leftFrame.1 leftFrame.2
          (coordinatePermutation rightFrame⁻¹.1 rightFrame⁻¹.2 position)) :=
        (pointwise (coordinatePermutation rightFrame⁻¹.1 rightFrame⁻¹.2 position)).symm
      _ = left (coordinatePermutation transported.1 transported.2 position) := by
        exact congrArg left (DFunLike.congr_fun
          (coordinatePermutation_mul leftFrame.1 rightFrame⁻¹.1
            leftFrame.2 rightFrame⁻¹.2) position)
  · rintro ⟨symmetry, rfl⟩
    obtain ⟨frame, rfl⟩ := coordinateSymmetry_surjective symmetry
    exact (executableSourceIndex_relabel left frame).symm

/-- Executable and existing mathematical OCT-8 words induce exactly the same classification. -/
theorem executableSourceIndex_sameClassification_as_source
    (left right : Position → PriorityNumber) :
    executableSourceIndex left = executableSourceIndex right ↔
      sourceIndex left = sourceIndex right := by
  rw [executableSourceIndex_eq_iff_symmetryEquivalent,
    sourceIndex_eq_iff_symmetryEquivalent]

/-- Executable production-facing complete OCT-8 mathematical word. -/
def executableTransBicappedOctahedronConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  executableSourceIndex
    (fun position => BlueBookP93.priorityOfProduction (placement position))

/-- Executable and mathematical production entries have the same exact collision boundary. -/
theorem executableTransBicappedOctahedronConfigurationIndex_sameClassification_as_mathematical
    (left right : Position → PolyhedralPriorityNumber) :
    executableTransBicappedOctahedronConfigurationIndex left =
        executableTransBicappedOctahedronConfigurationIndex right ↔
      transBicappedOctahedronCompleteConfigurationIndex left =
        transBicappedOctahedronCompleteConfigurationIndex right := by
  exact executableSourceIndex_sameClassification_as_source
    (fun position => BlueBookP93.priorityOfProduction (left position))
    (fun position => BlueBookP93.priorityOfProduction (right position))

end TetraStereo.OneCenter.RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness
