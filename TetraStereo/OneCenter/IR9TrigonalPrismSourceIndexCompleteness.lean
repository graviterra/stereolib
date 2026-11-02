import TetraStereo.OneCenter.IR9TrigonalPrismFiniteSymmetry
import Mathlib.Data.List.Sort

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalPrismSourceIndexCompleteness

open FiniteSymmetry
open TrigonalPrismFiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

private local instance priorityDigitWordDecidableLT : DecidableLT (List PriorityDigit) :=
  LinearOrder.toDecidableLT

/-- The three positions on one triangular face, in corresponding-corner order. -/
def faceWord (placement : Position → PriorityNumber) (face : Fin 2) :
    List PriorityNumber :=
  List.ofFn fun corner : Fin 3 => placement (coordinates.symm (face, corner))

/-- The six-entry placement word in the fixed face/corner coordinate frame. -/
def placementWord (placement : Position → PriorityNumber) : List PriorityNumber :=
  faceWord placement 0 ++ faceWord placement 1

/-- The twelve source-prescribed aligned TPR-6 frame words. -/
def sourceFrameCandidates (placement : Position → PriorityNumber) :
    List (List PriorityNumber) :=
  BlueBookP93.trigonalPrismFrameCandidates (faceWord placement 0) (faceWord placement 1)

/-- The complete six-entry canonical word selected internally by the source algorithm. -/
def sourceFullWord (placement : Position → PriorityNumber) : List PriorityNumber :=
  BlueBookP93.mostSeniorPrioritySequence (sourceFrameCandidates placement)

/-- The published three-entry TPR-6 configuration index. -/
def sourceIndex (placement : Position → PriorityNumber) : List PriorityNumber :=
  BlueBookP93.trigonalPrismIndex (faceWord placement 0) (faceWord placement 1)

theorem sourceIndex_eq_drop_sourceFullWord (placement : Position → PriorityNumber) :
    sourceIndex placement = (sourceFullWord placement).drop 3 := by
  rfl

def encodeWord (word : List PriorityNumber) : List PriorityDigit :=
  word.map priorityDigit

theorem priorityDigit_senior_iff (left right : PriorityNumber) :
    left.seniorTo right = true ↔ priorityDigit left < priorityDigit right := by
  rcases left with ⟨leftNumber, leftPrimes⟩
  rcases right with ⟨rightNumber, rightPrimes⟩
  simp [BlueBookP93.PriorityNumber.seniorTo, priorityDigit, Prod.Lex.lt_iff]

theorem priorityDecision_eq_gt_iff (left right : PriorityNumber) :
    BlueBookP93.priorityDecision left right = .gt ↔
      priorityDigit left < priorityDigit right := by
  unfold BlueBookP93.priorityDecision
  by_cases leftSenior : left.seniorTo right = true
  · simp [leftSenior, (priorityDigit_senior_iff left right).mp leftSenior]
  · have notLeftDigit : ¬priorityDigit left < priorityDigit right := by
      exact fun less => leftSenior ((priorityDigit_senior_iff left right).mpr less)
    simp only [leftSenior, Bool.false_eq_true, ↓reduceIte]
    by_cases rightSenior : right.seniorTo left = true
    · simp [rightSenior, notLeftDigit]
    · simp [rightSenior, notLeftDigit]

theorem priorityDecision_eq_eq_iff (left right : PriorityNumber) :
    BlueBookP93.priorityDecision left right = .eq ↔ left = right := by
  unfold BlueBookP93.priorityDecision
  by_cases leftSenior : left.seniorTo right = true
  · constructor
    · simp [leftSenior]
    · intro same
      subst right
      simp [BlueBookP93.PriorityNumber.seniorTo] at leftSenior
  · have notLeftDigit : ¬priorityDigit left < priorityDigit right := by
      exact fun less => leftSenior ((priorityDigit_senior_iff left right).mpr less)
    simp only [leftSenior, Bool.false_eq_true, ↓reduceIte]
    by_cases rightSenior : right.seniorTo left = true
    · constructor
      · simp [rightSenior]
      · intro same
        subst right
        simp [BlueBookP93.PriorityNumber.seniorTo] at rightSenior
    · have notRightDigit : ¬priorityDigit right < priorityDigit left := by
        exact fun less => rightSenior ((priorityDigit_senior_iff right left).mpr less)
      have digitSame : priorityDigit left = priorityDigit right :=
        le_antisymm (le_of_not_gt notRightDigit) (le_of_not_gt notLeftDigit)
      have same := priorityDigit_injective digitSame
      subst right
      simp [BlueBookP93.PriorityNumber.seniorTo]

theorem comparePrioritySequence_eq_gt_iff (left right : List PriorityNumber) :
    left.length = right.length →
    (BlueBookP93.comparePrioritySequence left right = .gt ↔
      encodeWord left < encodeWord right) := by
  induction left generalizing right with
  | nil =>
      intro sameLength
      cases right with
      | nil => simp [BlueBookP93.comparePrioritySequence, encodeWord]
      | cons head tail => simp at sameLength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp
      | cons rightHead rightTail =>
          intro sameLength
          have tailLength : leftTail.length = rightTail.length := by simpa using sameLength
          simp only [BlueBookP93.comparePrioritySequence, encodeWord, List.map_cons]
          cases decisionEq : BlueBookP93.priorityDecision leftHead rightHead with
          | gt =>
              have less := (priorityDecision_eq_gt_iff leftHead rightHead).mp decisionEq
              constructor
              · intro _
                exact List.Lex.rel less
              · intro _
                rfl
          | eq =>
              have same := (priorityDecision_eq_eq_iff leftHead rightHead).mp decisionEq
              subst rightHead
              simpa using inductionHypothesis rightTail tailLength
          | lt =>
              have notLess : ¬priorityDigit leftHead < priorityDigit rightHead := by
                intro less
                have := (priorityDecision_eq_gt_iff leftHead rightHead).mpr less
                simp_all
              have notSame : priorityDigit leftHead ≠ priorityDigit rightHead := by
                intro same
                have originalSame := priorityDigit_injective same
                have := (priorityDecision_eq_eq_iff leftHead rightHead).mpr originalSame
                simp_all
              have greater : priorityDigit rightHead < priorityDigit leftHead :=
                lt_of_le_of_ne (le_of_not_gt notLess) notSame.symm
              have greaterWords :
                  priorityDigit rightHead :: List.map priorityDigit rightTail <
                    priorityDigit leftHead :: List.map priorityDigit leftTail :=
                List.Lex.rel greater
              constructor
              · intro impossible
                cases impossible
              · intro wordLess
                exact (not_lt_of_ge (le_of_lt greaterWords) wordLess).elim

@[simp] theorem length_faceWord (placement : Position → PriorityNumber) (face : Fin 2) :
    (faceWord placement face).length = 3 := by
  simp [faceWord]

theorem sourceFrameCandidates_nonempty (placement : Position → PriorityNumber) :
    sourceFrameCandidates placement ≠ [] := by
  simp [sourceFrameCandidates, BlueBookP93.trigonalPrismFrameCandidates]

theorem length_of_mem_sourceFrameCandidates
    (placement : Position → PriorityNumber) {candidate : List PriorityNumber}
    (member : candidate ∈ sourceFrameCandidates placement) : candidate.length = 6 := by
  simp [sourceFrameCandidates, BlueBookP93.trigonalPrismFrameCandidates,
    BlueBookP93.trigonalPrismFrame] at member
  rcases member with ⟨offset, offsetLt, rfl⟩ | ⟨offset, offsetLt, rfl⟩ |
      ⟨offset, offsetLt, rfl⟩ | ⟨offset, offsetLt, rfl⟩ <;>
    simp [length_faceWord] <;> omega

def seniorChoice (current candidate : List PriorityNumber) : List PriorityNumber :=
  if BlueBookP93.comparePrioritySequence candidate current == .gt then candidate else current

theorem encodeWord_seniorChoice {current candidate : List PriorityNumber}
    (sameLength : candidate.length = current.length) :
    encodeWord (seniorChoice current candidate) =
      min (encodeWord current) (encodeWord candidate) := by
  unfold seniorChoice
  by_cases chosen : BlueBookP93.comparePrioritySequence candidate current = .gt
  · simp only [chosen, beq_self_eq_true, ↓reduceIte]
    have less := (comparePrioritySequence_eq_gt_iff candidate current sameLength).mp chosen
    exact (min_eq_right less.le).symm
  · have notLess : ¬encodeWord candidate < encodeWord current := by
      intro less
      exact chosen ((comparePrioritySequence_eq_gt_iff candidate current sameLength).mpr less)
    have comparisonNotTrue :
        (BlueBookP93.comparePrioritySequence candidate current == .gt) = false := by
      simpa using chosen
    simp only [comparisonNotTrue, Bool.false_eq_true, ↓reduceIte]
    exact (min_eq_left (le_of_not_gt notLess)).symm

theorem length_seniorChoice {current candidate : List PriorityNumber} {length : Nat}
    (currentLength : current.length = length) (candidateLength : candidate.length = length) :
    (seniorChoice current candidate).length = length := by
  unfold seniorChoice
  split <;> assumption

theorem encodeWord_foldl_seniorChoice
    (candidates : List (List PriorityNumber)) (current : List PriorityNumber) (length : Nat)
    (currentLength : current.length = length)
    (candidateLengths : ∀ candidate ∈ candidates, candidate.length = length) :
    encodeWord (candidates.foldl seniorChoice current) =
      (candidates.map encodeWord).foldl min (encodeWord current) := by
  induction candidates generalizing current with
  | nil => rfl
  | cons candidate candidates inductionHypothesis =>
      simp only [List.foldl_cons, List.map_cons]
      have candidateLength : candidate.length = length :=
        candidateLengths candidate (by simp)
      rw [inductionHypothesis (seniorChoice current candidate)
        (length_seniorChoice currentLength candidateLength)]
      · rw [encodeWord_seniorChoice (candidateLength.trans currentLength.symm)]
      · intro later laterMember
        exact candidateLengths later (by simp [laterMember])

theorem foldl_min_mem {α : Type*} [LinearOrder α]
    (entries : List α) (current : α) : entries.foldl min current ∈ current :: entries := by
  induction entries generalizing current with
  | nil => simp
  | cons entry entries inductionHypothesis =>
      simp only [List.foldl_cons]
      have member := inductionHypothesis (min current entry)
      rcases List.mem_cons.mp member with same | later
      · rw [same]
        rcases min_choice current entry with minimumIsCurrent | minimumIsEntry
        · exact List.mem_cons.mpr (Or.inl minimumIsCurrent)
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl minimumIsEntry)))
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr later)))

theorem foldl_min_le_of_mem {α : Type*} [LinearOrder α]
    (entries : List α) (current entry : α) (member : entry ∈ current :: entries) :
    entries.foldl min current ≤ entry := by
  induction entries generalizing current entry with
  | nil =>
      have same : entry = current := by simpa using member
      subst entry
      exact le_rfl
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with same | member
      · subst entry
        exact (inductionHypothesis (min current head) (min current head)
          (List.mem_cons_self)).trans (min_le_left current head)
      · rcases List.mem_cons.mp member with same | memberTail
        · subst entry
          exact (inductionHypothesis (min current head) (min current head)
            (List.mem_cons_self)).trans (min_le_right current head)
        · exact inductionHypothesis (min current head) entry
            (List.mem_cons.mpr (Or.inr memberTail))

theorem foldl_min_eq_minimum_of_cons {α : Type*} [LinearOrder α]
    (first : α) (rest : List α) :
    rest.foldl min first =
      (first :: rest).minimum_of_length_pos (by simp) := by
  apply le_antisymm
  · apply foldl_min_le_of_mem
    exact (first :: rest).minimum_of_length_pos_mem (by simp)
  · apply (first :: rest).minimum_of_length_pos_le_of_mem
    exact foldl_min_mem rest first

/-- The complete source word, after the injective priority encoding, is the least of the twelve
source frame words in ordinary lexicographic order. -/
theorem encodeWord_sourceFullWord_eq_minimum (placement : Position → PriorityNumber) :
    (encodeWord (sourceFullWord placement) : WithTop (List PriorityDigit)) =
      ((sourceFrameCandidates placement).map encodeWord).minimum := by
  unfold sourceFullWord BlueBookP93.mostSeniorPrioritySequence
  cases candidatesEq : sourceFrameCandidates placement with
  | nil => exact (sourceFrameCandidates_nonempty placement candidatesEq).elim
  | cons first rest =>
      change (encodeWord (rest.foldl seniorChoice first) : WithTop (List PriorityDigit)) =
        (encodeWord first :: rest.map encodeWord).minimum
      rw [encodeWord_foldl_seniorChoice rest first 6]
      · rw [foldl_min_eq_minimum_of_cons (encodeWord first) (rest.map encodeWord)]
        simp only [List.coe_minimum_of_length_pos]
      · exact length_of_mem_sourceFrameCandidates placement (candidatesEq ▸ List.mem_cons_self)
      · intro candidate member
        exact length_of_mem_sourceFrameCandidates placement
          (candidatesEq ▸ List.mem_cons.mpr (Or.inr member))

/-! ## Exact identification of the twelve source frames -/

def cornerRotation : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 1) * (Equiv.swap 1 2)

def sourceCornerFrames : List (Equiv.Perm (Fin 3)) :=
  [1, cornerRotation, cornerRotation ^ 2, Equiv.swap 0 2, Equiv.swap 0 1, Equiv.swap 1 2]

def sourceFaceFrames : List (Equiv.Perm (Fin 2)) :=
  [1, Equiv.swap 0 1]

@[simp] theorem cornerRotation_apply (corner : Fin 3) :
    cornerRotation corner = ![1, 2, 0] corner := by
  fin_cases corner <;> decide

@[simp] theorem cornerRotation_sq_apply (corner : Fin 3) :
    (cornerRotation ^ 2) corner = ![2, 0, 1] corner := by
  fin_cases corner <;> decide

@[simp] theorem swap_zero_two_apply (corner : Fin 3) :
    Equiv.swap (0 : Fin 3) 2 corner = ![2, 1, 0] corner := by
  fin_cases corner <;> decide

@[simp] theorem swap_zero_one_apply_fin3 (corner : Fin 3) :
    Equiv.swap (0 : Fin 3) 1 corner = ![1, 0, 2] corner := by
  fin_cases corner <;> decide

@[simp] theorem swap_one_two_apply_fin3 (corner : Fin 3) :
    Equiv.swap (1 : Fin 3) 2 corner = ![0, 2, 1] corner := by
  fin_cases corner <;> decide

@[simp] theorem swap_zero_one_apply_fin2 (face : Fin 2) :
    Equiv.swap (0 : Fin 2) 1 face = ![1, 0] face := by
  fin_cases face <;> decide

theorem sourceCornerFrames_nodup : sourceCornerFrames.Nodup := by
  decide

theorem sourceFaceFrames_nodup : sourceFaceFrames.Nodup := by
  decide

theorem mem_sourceCornerFrames (corner : Equiv.Perm (Fin 3)) :
    corner ∈ sourceCornerFrames := by
  have exhaustive : sourceCornerFrames.toFinset = Finset.univ := by decide
  have member : corner ∈ sourceCornerFrames.toFinset := by
    rw [exhaustive]
    simp
  simpa using member

theorem mem_sourceFaceFrames (face : Equiv.Perm (Fin 2)) :
    face ∈ sourceFaceFrames := by
  have exhaustive : sourceFaceFrames.toFinset = Finset.univ := by decide
  have member : face ∈ sourceFaceFrames.toFinset := by
    rw [exhaustive]
    simp
  simpa using member

/-- The complete six-entry word seen in one face/corner frame. -/
def coordinateFrameWord (placement : Position → PriorityNumber)
    (face : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3)) :
    List PriorityNumber :=
  placementWord (relabel (coordinatePermutation face corner) placement)

def enumeratedCoordinateFrameWords (placement : Position → PriorityNumber) :
    List (List PriorityNumber) :=
  sourceFaceFrames.flatMap fun face =>
    sourceCornerFrames.map fun corner => coordinateFrameWord placement face corner

theorem sourceFrameCandidates_eq_enumeratedCoordinateFrameWords
    (placement : Position → PriorityNumber) :
    sourceFrameCandidates placement = enumeratedCoordinateFrameWords placement := by
  have rangeThree : List.range 3 = [0, 1, 2] := by decide
  rw [show sourceFrameCandidates placement =
      BlueBookP93.trigonalPrismFrameCandidates (faceWord placement 0)
        (faceWord placement 1) by rfl]
  simp [BlueBookP93.trigonalPrismFrameCandidates, rangeThree,
    BlueBookP93.trigonalPrismFrame, enumeratedCoordinateFrameWords,
    sourceFaceFrames, sourceCornerFrames, coordinateFrameWord, placementWord, faceWord,
    relabel, coordinatePermutation, coordinates]

theorem mem_sourceFrameCandidates_iff
    (placement : Position → PriorityNumber) (word : List PriorityNumber) :
    word ∈ sourceFrameCandidates placement ↔
      ∃ face : Equiv.Perm (Fin 2), ∃ corner : Equiv.Perm (Fin 3),
        word = coordinateFrameWord placement face corner := by
  rw [sourceFrameCandidates_eq_enumeratedCoordinateFrameWords]
  simp only [enumeratedCoordinateFrameWords, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨face, faceMember, corner, cornerMember, rfl⟩
    exact ⟨face, corner, rfl⟩
  · rintro ⟨face, corner, rfl⟩
    exact ⟨face, mem_sourceFaceFrames face, corner, mem_sourceCornerFrames corner, rfl⟩

theorem mem_sourceFrameCandidates_iff_exists_symmetry
    (placement : Position → PriorityNumber) (word : List PriorityNumber) :
    word ∈ sourceFrameCandidates placement ↔
      ∃ symmetry : fullSymmetryGroup,
        word = placementWord (relabel symmetry.1 placement) := by
  rw [mem_sourceFrameCandidates_iff]
  constructor
  · rintro ⟨face, corner, rfl⟩
    exact ⟨coordinateSymmetry (face, corner), rfl⟩
  · rintro ⟨symmetry, rfl⟩
    rcases coordinateSymmetry_surjective symmetry with ⟨⟨face, corner⟩, same⟩
    refine ⟨face, corner, ?_⟩
    simp only [coordinateFrameWord]
    exact congrArg (fun admitted : fullSymmetryGroup =>
      placementWord (relabel admitted.1 placement)) same.symm

theorem relabel_relabel (placement : Position → PriorityNumber)
    (first second : Equiv.Perm Position) :
    relabel second (relabel first placement) = relabel (first * second) placement := by
  rfl

theorem sourceFrameCandidates_relabel_membership
    (placement : Position → PriorityNumber) (symmetry : fullSymmetryGroup)
    (word : List PriorityNumber) :
    word ∈ sourceFrameCandidates (relabel symmetry.1 placement) ↔
      word ∈ sourceFrameCandidates placement := by
  simp only [mem_sourceFrameCandidates_iff_exists_symmetry]
  constructor
  · rintro ⟨frame, rfl⟩
    refine ⟨symmetry * frame, ?_⟩
    exact congrArg placementWord (relabel_relabel placement symmetry.1 frame.1)
  · rintro ⟨frame, rfl⟩
    refine ⟨symmetry⁻¹ * frame, ?_⟩
    rw [relabel_relabel]
    simp

theorem encodedSourceFrameCandidates_relabel_membership
    (placement : Position → PriorityNumber) (symmetry : fullSymmetryGroup)
    (digits : List PriorityDigit) :
    digits ∈ (sourceFrameCandidates (relabel symmetry.1 placement)).map encodeWord ↔
      digits ∈ (sourceFrameCandidates placement).map encodeWord := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨word, member, rfl⟩
    exact ⟨word, (sourceFrameCandidates_relabel_membership placement symmetry word).mp member,
      rfl⟩
  · rintro ⟨word, member, rfl⟩
    exact ⟨word, (sourceFrameCandidates_relabel_membership placement symmetry word).mpr member,
      rfl⟩

/-- The complete source word is invariant under every signature-derived full prism symmetry. -/
theorem sourceFullWord_invariant
    (placement : Position → PriorityNumber) (symmetry : fullSymmetryGroup) :
    sourceFullWord (relabel symmetry.1 placement) = sourceFullWord placement := by
  apply (List.map_injective_iff.mpr priorityDigit_injective)
  apply WithTop.coe_injective
  change (encodeWord (sourceFullWord (relabel symmetry.1 placement)) :
      WithTop (List PriorityDigit)) =
    (encodeWord (sourceFullWord placement) : WithTop (List PriorityDigit))
  rw [encodeWord_sourceFullWord_eq_minimum, encodeWord_sourceFullWord_eq_minimum]
  apply le_antisymm
  · have subset :
        (sourceFrameCandidates placement).map encodeWord ⊆
          (sourceFrameCandidates (relabel symmetry.1 placement)).map encodeWord := by
      intro digits member
      exact (encodedSourceFrameCandidates_relabel_membership placement symmetry digits).mpr member
    exact List.minimum_anti subset
  · have subset :
        (sourceFrameCandidates (relabel symmetry.1 placement)).map encodeWord ⊆
          (sourceFrameCandidates placement).map encodeWord := by
      intro digits member
      exact (encodedSourceFrameCandidates_relabel_membership placement symmetry digits).mp member
    exact List.minimum_anti subset

/-- Therefore the published three-entry index itself is frame invariant. -/
theorem sourceIndex_invariant
    (placement : Position → PriorityNumber) (symmetry : fullSymmetryGroup) :
    sourceIndex (relabel symmetry.1 placement) = sourceIndex placement := by
  simp only [sourceIndex_eq_drop_sourceFullWord, sourceFullWord_invariant placement symmetry]

theorem foldl_seniorChoice_mem
    (entries : List (List PriorityNumber)) (current : List PriorityNumber) :
    entries.foldl seniorChoice current ∈ current :: entries := by
  induction entries generalizing current with
  | nil => simp
  | cons entry entries inductionHypothesis =>
      simp only [List.foldl_cons]
      have member := inductionHypothesis (seniorChoice current entry)
      rcases List.mem_cons.mp member with same | later
      · rw [same]
        unfold seniorChoice
        split
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr later)))

theorem mostSeniorPrioritySequence_mem
    (candidates : List (List PriorityNumber)) (nonempty : candidates ≠ []) :
    BlueBookP93.mostSeniorPrioritySequence candidates ∈ candidates := by
  unfold BlueBookP93.mostSeniorPrioritySequence
  cases candidates with
  | nil => contradiction
  | cons first rest => exact foldl_seniorChoice_mem rest first

theorem sourceFullWord_mem_sourceFrameCandidates (placement : Position → PriorityNumber) :
    sourceFullWord placement ∈ sourceFrameCandidates placement := by
  exact mostSeniorPrioritySequence_mem (sourceFrameCandidates placement)
    (sourceFrameCandidates_nonempty placement)

theorem placementWord_eq_ofFn (placement : Position → PriorityNumber) :
    placementWord placement = List.ofFn placement := by
  unfold placementWord faceWord
  symm
  rw [List.ofFn_mul (m := 2) (n := 3) placement]
  simp [coordinates]
  norm_num [finProdFinEquiv]
  constructor
  · exact congrArg placement (Fin.ext rfl)
  constructor
  · exact congrArg placement (Fin.ext rfl)
  constructor
  · exact congrArg placement (Fin.ext rfl)
  · exact congrArg placement (Fin.ext rfl)

theorem placementWord_injective : Function.Injective placementWord := by
  intro left right same
  rw [placementWord_eq_ofFn, placementWord_eq_ofFn] at same
  exact List.ofFn_injective same

/-- Equality of the complete six-entry source words is exactly full prism symmetry equivalence. -/
theorem sourceFullWord_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber) :
    sourceFullWord left = sourceFullWord right ↔
      SymmetryEquivalent fullSymmetryGroup left right := by
  constructor
  · intro sameWord
    have leftMember := sourceFullWord_mem_sourceFrameCandidates left
    have rightMember := sourceFullWord_mem_sourceFrameCandidates right
    rcases (mem_sourceFrameCandidates_iff_exists_symmetry left (sourceFullWord left)).mp
        leftMember with ⟨leftFrame, leftWord⟩
    rcases (mem_sourceFrameCandidates_iff_exists_symmetry right (sourceFullWord right)).mp
        rightMember with ⟨rightFrame, rightWord⟩
    have framedSame : relabel leftFrame.1 left = relabel rightFrame.1 right := by
      apply placementWord_injective
      calc
        placementWord (relabel leftFrame.1 left) = sourceFullWord left := leftWord.symm
        _ = sourceFullWord right := sameWord
        _ = placementWord (relabel rightFrame.1 right) := rightWord
    refine ⟨leftFrame * rightFrame⁻¹, ?_⟩
    funext position
    simpa [relabel] using (congrFun framedSame (rightFrame.1.symm position)).symm
  · rintro ⟨symmetry, rfl⟩
    exact (sourceFullWord_invariant left symmetry).symm

theorem sourceFullWord_length (placement : Position → PriorityNumber) :
    (sourceFullWord placement).length = 6 :=
  length_of_mem_sourceFrameCandidates placement
    (sourceFullWord_mem_sourceFrameCandidates placement)

theorem sourceFullWord_perm_placementWord (placement : Position → PriorityNumber) :
    List.Perm (sourceFullWord placement) (placementWord placement) := by
  rcases (mem_sourceFrameCandidates_iff_exists_symmetry placement
      (sourceFullWord placement)).mp (sourceFullWord_mem_sourceFrameCandidates placement) with
    ⟨symmetry, wordEq⟩
  rw [wordEq, placementWord_eq_ofFn, placementWord_eq_ofFn]
  simpa [relabel, Function.comp_def] using symmetry.1.ofFn_comp_perm placement

theorem encodeWord_sourceFullWord_le_of_mem
    (placement : Position → PriorityNumber) {candidate : List PriorityNumber}
    (member : candidate ∈ sourceFrameCandidates placement) :
    encodeWord (sourceFullWord placement) ≤ encodeWord candidate := by
  have encodedMember : encodeWord candidate ∈
      (sourceFrameCandidates placement).map encodeWord := by
    exact List.mem_map.mpr ⟨candidate, member, rfl⟩
  have bound := List.minimum_le_of_mem' encodedMember
  rw [← encodeWord_sourceFullWord_eq_minimum] at bound
  exact WithTop.coe_le_coe.mp bound

/-- The omitted first triangular-face word is canonically sorted from senior to junior.  This is
the reconstruction fact needed to justify omitting it from the published three-entry index. -/
theorem encodeWord_take_three_sourceFullWord_pairwise
    (placement : Position → PriorityNumber) :
    (encodeWord ((sourceFullWord placement).take 3)).Pairwise (· ≤ ·) := by
  rcases (mem_sourceFrameCandidates_iff_exists_symmetry placement
      (sourceFullWord placement)).mp (sourceFullWord_mem_sourceFrameCandidates placement) with
    ⟨frame, wordEq⟩
  let framed : Position → PriorityNumber := relabel frame.1 placement
  have wordEq' : sourceFullWord placement = placementWord framed := wordEq
  let swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let swap02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let swap12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have candidateMember (corner : Equiv.Perm (Fin 3)) :
      coordinateFrameWord framed 1 corner ∈ sourceFrameCandidates placement := by
    have framedMember : coordinateFrameWord framed 1 corner ∈
        sourceFrameCandidates framed :=
      (mem_sourceFrameCandidates_iff framed _).mpr ⟨1, corner, rfl⟩
    exact (sourceFrameCandidates_relabel_membership placement frame _).mp framedMember
  have minimum01 := encodeWord_sourceFullWord_le_of_mem placement
    (candidateMember swap01)
  have minimum02 := encodeWord_sourceFullWord_le_of_mem placement
    (candidateMember swap02)
  have minimum12 := encodeWord_sourceFullWord_le_of_mem placement
    (candidateMember swap12)
  have firstLeSecond :
      priorityDigit (framed (coordinates.symm (0, 0))) ≤
        priorityDigit (framed (coordinates.symm (0, 1))) := by
    by_contra notLe
    have reversed : priorityDigit (framed (coordinates.symm (0, 1))) <
        priorityDigit (framed (coordinates.symm (0, 0))) := lt_of_not_ge notLe
    have swappedLess : encodeWord (coordinateFrameWord framed 1 swap01) <
        encodeWord (sourceFullWord placement) := by
      rw [wordEq']
      simpa [swap01, coordinateFrameWord, placementWord, faceWord, encodeWord,
        relabel, coordinatePermutation, coordinates] using (List.Lex.rel reversed)
    exact (not_lt_of_ge minimum01 swappedLess)
  have firstLeThird :
      priorityDigit (framed (coordinates.symm (0, 0))) ≤
        priorityDigit (framed (coordinates.symm (0, 2))) := by
    by_contra notLe
    have reversed : priorityDigit (framed (coordinates.symm (0, 2))) <
        priorityDigit (framed (coordinates.symm (0, 0))) := lt_of_not_ge notLe
    have swappedLess : encodeWord (coordinateFrameWord framed 1 swap02) <
        encodeWord (sourceFullWord placement) := by
      rw [wordEq']
      simpa [swap02, coordinateFrameWord, placementWord, faceWord, encodeWord,
        relabel, coordinatePermutation, coordinates] using (List.Lex.rel reversed)
    exact (not_lt_of_ge minimum02 swappedLess)
  have secondLeThird :
      priorityDigit (framed (coordinates.symm (0, 1))) ≤
        priorityDigit (framed (coordinates.symm (0, 2))) := by
    by_contra notLe
    have reversed : priorityDigit (framed (coordinates.symm (0, 2))) <
        priorityDigit (framed (coordinates.symm (0, 1))) := lt_of_not_ge notLe
    have swappedLess : encodeWord (coordinateFrameWord framed 1 swap12) <
        encodeWord (sourceFullWord placement) := by
      rw [wordEq']
      simpa [swap12, coordinateFrameWord, placementWord, faceWord, encodeWord,
        relabel, coordinatePermutation, coordinates] using
          (List.Lex.cons (a := priorityDigit (framed (coordinates.symm (0, 0))))
            (List.Lex.rel reversed))
    exact (not_lt_of_ge minimum12 swappedLess)
  rw [wordEq']
  simpa [placementWord, faceWord, encodeWord] using
    And.intro (And.intro firstLeSecond firstLeThird) secondLeThird

/-! ## Completeness of the published three-entry index -/

/-- Equality of the complete six-entry priority multisets.  This is the comparison context in
which IUPAC's omission of the canonically determined first-face prefix is information preserving. -/
def SamePriorityMultiset
    (left right : Position → PriorityNumber) : Prop :=
  List.Perm (placementWord left) (placementWord right)

/-- Under equality of the complete ligand-priority multiset, equality of the published
three-entry TPR-6 index is exactly equivalence under the full ideal-prism symmetry group. -/
theorem sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
    (sameMultiset : SamePriorityMultiset left right) :
    sourceIndex left = sourceIndex right ↔
      SymmetryEquivalent fullSymmetryGroup left right := by
  constructor
  · intro sameIndex
    have sameSuffix : (sourceFullWord left).drop 3 = (sourceFullWord right).drop 3 := by
      simpa only [sourceIndex_eq_drop_sourceFullWord] using sameIndex
    have fullPerm : List.Perm (sourceFullWord left) (sourceFullWord right) :=
      (sourceFullWord_perm_placementWord left).trans
        (sameMultiset.trans (sourceFullWord_perm_placementWord right).symm)
    have appendedPerm : List.Perm
        ((sourceFullWord left).take 3 ++ (sourceFullWord left).drop 3)
        ((sourceFullWord right).take 3 ++ (sourceFullWord left).drop 3) := by
      rw [List.take_append_drop, sameSuffix, List.take_append_drop]
      exact fullPerm
    have prefixPerm : List.Perm ((sourceFullWord left).take 3)
        ((sourceFullWord right).take 3) := by
      exact (List.perm_append_right_iff ((sourceFullWord left).drop 3)).mp appendedPerm
    have encodedPrefixPerm : List.Perm
        (encodeWord ((sourceFullWord left).take 3))
        (encodeWord ((sourceFullWord right).take 3)) :=
      prefixPerm.map priorityDigit
    have encodedPrefixSame :
        encodeWord ((sourceFullWord left).take 3) =
          encodeWord ((sourceFullWord right).take 3) :=
      encodedPrefixPerm.eq_of_pairwise'
        (encodeWord_take_three_sourceFullWord_pairwise left)
        (encodeWord_take_three_sourceFullWord_pairwise right)
    have prefixSame : (sourceFullWord left).take 3 =
        (sourceFullWord right).take 3 :=
      (List.map_injective_iff.mpr priorityDigit_injective) encodedPrefixSame
    have fullSame : sourceFullWord left = sourceFullWord right := by
      calc
        sourceFullWord left = (sourceFullWord left).take 3 ++
            (sourceFullWord left).drop 3 := (List.take_append_drop 3 _).symm
        _ = (sourceFullWord right).take 3 ++
            (sourceFullWord right).drop 3 := by rw [prefixSame, sameSuffix]
        _ = sourceFullWord right := List.take_append_drop 3 _
    exact (sourceFullWord_eq_iff_symmetryEquivalent left right).mp fullSame
  · intro equivalent
    rcases equivalent with ⟨symmetry, rfl⟩
    exact (sourceIndex_invariant left symmetry).symm

/-- Source-spelled form: this theorem applies directly to
`BlueBookP93.trigonalPrismIndex`, not merely to an alternative canonical index. -/
theorem blueBook_trigonalPrismIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber)
    (sameMultiset : SamePriorityMultiset left right) :
    BlueBookP93.trigonalPrismIndex (faceWord left 0) (faceWord left 1) =
        BlueBookP93.trigonalPrismIndex (faceWord right 0) (faceWord right 1) ↔
      SymmetryEquivalent fullSymmetryGroup left right :=
  sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset left right sameMultiset

end TetraStereo.OneCenter.RedBookIR9.TrigonalPrismSourceIndexCompleteness
