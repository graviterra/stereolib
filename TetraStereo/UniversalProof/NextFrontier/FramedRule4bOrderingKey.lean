import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorProjectedOrderingKey

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TetraStereo.OneCenter.FramedRule4bOrderingKey

open RawMolecule FrameRuntime FramedDescriptorOrderingKey FramedDescriptorProjectedOrderingKey

/-! Dynamic references are collected and ranked independently for each ligand. Failed unary
queries are totalized only in the key; a successful production run supplies the exact read/rank
values. Authoritative mixed-empty ordering and fast refusal retain their actual runtime policy. -/

/-- Unary Rule-4b key.  Reference-count priority is compared before the ranked descriptor
readings, as required by IUPAC P-92.5.2.1 criterion (c)(i). -/
structure DenseRule4bProjectedKey where
  referenceCountPriority : Nat
  readings : List (List Key)

/-- One selected reference precedes two.  Zero and unsupported counts are retained below both
supported nonzero counts; the authoritative mode compares those mixed cases while the fast mode refuses them. -/
def denseRule4bReferenceCountPriority : Nat → Nat
  | 1 => 2
  | 2 => 1
  | _ => 0

def totalRankedOccurrenceRule4bReferences (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ) (root : Cursor)
    (references : List RS) : List RS :=
  (FrameRuntime.rankRule4bReferences? mol profile authoritative state fuel root references).getD references

def buildDenseRule4bProjectedKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool) (state : OccurrenceAuxState)
    (fuel : ℕ) (root : Cursor) : DenseRule4bProjectedKey :=
  let references := (rule4bReferences? mol profile state fuel [root]).getD []
  let ranked := totalRankedOccurrenceRule4bReferences mol profile authoritative state fuel root references
  { referenceCountPriority := denseRule4bReferenceCountPriority references.length
    readings := ranked.map fun reference =>
      buildDenseTiedRootDescriptorKey mol profile authoritative state fuel (.rule4b reference reference) true root }

def compareDenseRule4bProjectedKeys :
    DenseRule4bProjectedKey → DenseRule4bProjectedKey → Ordering :=
  compareLex
    (Ordering.byKey DenseRule4bProjectedKey.referenceCountPriority compare)
    (Ordering.byKey DenseRule4bProjectedKey.readings
      (List.compareLex compareDenseTiedRootDescriptorKeys))

theorem compareDenseRule4bProjectedKeys_transCmp :
    Std.TransCmp compareDenseRule4bProjectedKeys := by
  unfold compareDenseRule4bProjectedKeys
  letI := compareDenseTiedRootDescriptorKeys_transCmp
  infer_instance

@[simp] theorem compareDenseRule4bProjectedKeys_same_count
    (priority : Nat) (leftReadings rightReadings : List (List Key)) :
    compareDenseRule4bProjectedKeys
        { referenceCountPriority := priority, readings := leftReadings }
        { referenceCountPriority := priority, readings := rightReadings } =
      List.compareLex compareDenseTiedRootDescriptorKeys leftReadings rightReadings := by
  simp [compareDenseRule4bProjectedKeys, compareLex, Ordering.byKey]

@[simp] theorem compareDenseRule4bProjectedKeys_one_over_two
    (leftReadings rightReadings : List (List Key)) :
    compareDenseRule4bProjectedKeys
        { referenceCountPriority := 2, readings := leftReadings }
        { referenceCountPriority := 1, readings := rightReadings } = Ordering.gt := by
  rfl

@[simp] theorem compareDenseRule4bProjectedKeys_two_below_one
    (leftReadings rightReadings : List (List Key)) :
    compareDenseRule4bProjectedKeys
        { referenceCountPriority := 1, readings := leftReadings }
        { referenceCountPriority := 2, readings := rightReadings } = Ordering.lt := by
  rfl

theorem rankOccurrenceRule4bReferences_length_of_success (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ) (root : Cursor) :
    ∀ references ranked,
    FrameRuntime.rankRule4bReferences? mol profile authoritative state fuel root references = some ranked →
      ranked.length = references.length
  | [], ranked, computed => by simp [FrameRuntime.rankRule4bReferences?] at computed; subst ranked; rfl
  | [first], ranked, computed => by
      simp [FrameRuntime.rankRule4bReferences?] at computed
      subst ranked
      rfl
  | [first, second], ranked, computed => by
      simp only [FrameRuntime.rankRule4bReferences?] at computed
      cases decisionEq : compareDescriptorAtTiedRoot? mol profile authoritative state fuel
          (.rule4b first second) root root with
      | none => simp [decisionEq] at computed
      | some decision =>
          cases decision <;> simp [decisionEq] at computed <;> subst ranked <;> rfl
  | first :: second :: third :: rest, ranked, computed => by
      simp [FrameRuntime.rankRule4bReferences?] at computed
      subst ranked
      rfl

theorem list_eq_getD_two {alpha : Type*} (values : List alpha)
    (fallback0 fallback1 : alpha) (lengthEq : values.length = 2) :
    values = [values.getD 0 fallback0, values.getD 1 fallback1] := by
  cases values with
  | nil => simp at lengthEq
  | cons first tail =>
      cases tail with
      | nil => simp at lengthEq
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest => simp at lengthEq

theorem exists_pair_of_length_eq_two {alpha : Type*} (values : List alpha)
    (lengthEq : values.length = 2) : ∃ first second, values = [first, second] := by
  cases values with
  | nil => simp at lengthEq
  | cons first tail =>
      cases tail with
      | nil => simp at lengthEq
      | cons second rest =>
          cases rest with
          | nil => exact ⟨first, second, rfl⟩
          | cons third rest => simp at lengthEq

theorem compareRule4b_success_factors (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : Cursor) (decision : Ordering)
    (computed : compareRule4b? mol profile authoritative state fuel left right = some decision) :
    compareDenseRule4bProjectedKeys
      (buildDenseRule4bProjectedKey mol profile authoritative state fuel left)
      (buildDenseRule4bProjectedKey mol profile authoritative state fuel right) = decision := by
  cases leftRead : rule4bReferences? mol profile state fuel [left] with
  | none => simp [compareRule4b?, leftRead] at computed
  | some leftReferences =>
      cases rightRead : rule4bReferences? mol profile state fuel [right] with
      | none => simp [compareRule4b?, leftRead, rightRead] at computed
      | some rightReferences =>
          cases authoritative with
          | false =>
              cases leftRefsEq : leftReferences with
              | nil =>
                  cases rightRefsEq : rightReferences with
                  | nil =>
                      simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                      subst decision
                      simp [leftRead, rightRead, buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                        leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                        FrameRuntime.rankRule4bReferences?, List.compareLex, compareLex, Ordering.byKey]
                  | cons rightFirst rightTail =>
                      cases rightTail with
                      | nil =>
                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                      | cons rightSecond rightRest =>
                          cases rightRest <;>
                            simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
              | cons leftFirst leftTail =>
                  cases leftTail with
                  | nil =>
                      cases rightRefsEq : rightReferences with
                      | nil => simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                      | cons rightFirst rightTail =>
                          cases rightTail with
                          | nil =>
                              cases selectedEq : compareDescriptorAtTiedRoot? mol profile false state fuel
                                  (.rule4b leftFirst rightFirst) left right with
                              | none =>
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq, selectedEq]
                                    at computed
                              | some selected =>
                                  have selectedFactor :=
                                    compareOccurrenceDescriptorAtTiedRoot_success_factors mol profile false state fuel
                                      (.rule4b leftFirst rightFirst) left right selected selectedEq
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq, selectedEq]
                                    at computed
                                  subst decision
                                  rw [buildDenseTiedRoot_rule4b_left_local mol profile false state fuel leftFirst
                                    rightFirst left] at selectedFactor
                                  rw [buildDenseTiedRoot_rule4b_right_local mol profile false state fuel leftFirst
                                    rightFirst right] at selectedFactor
                                  rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent mol profile false state fuel
                                    rightFirst right] at selectedFactor
                                  simp [leftRead, rightRead, buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                                    leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                                    FrameRuntime.rankRule4bReferences?, List.compareLex, selectedFactor]
                                  cases selected <;> rfl
                          | cons rightSecond rightRest =>
                              cases rightRest with
                              | nil =>
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                                  subst decision
                                  simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                    denseRule4bReferenceCountPriority, leftRefsEq, rightRefsEq,
                                    totalRankedOccurrenceRule4bReferences,
                                    FrameRuntime.rankRule4bReferences?, compareLex, Ordering.byKey]
                              | cons rightThird rightMore =>
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                  | cons leftSecond leftRest =>
                      cases leftRest with
                      | cons leftThird leftMore =>
                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq] at computed
                      | nil =>
                          cases rightRefsEq : rightReferences with
                          | nil => simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                          | cons rightFirst rightTail =>
                              cases rightTail with
                              | nil =>
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                                  subst decision
                                  simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                    denseRule4bReferenceCountPriority, leftRefsEq, rightRefsEq,
                                    totalRankedOccurrenceRule4bReferences,
                                    FrameRuntime.rankRule4bReferences?, compareLex, Ordering.byKey]
                              | cons rightSecond rightRest =>
                                  cases rightRest with
                                  | cons rightThird rightMore =>
                                      simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                                  | nil =>
                                      cases rankLeftEq : FrameRuntime.rankRule4bReferences? mol profile false state fuel left
                                          [leftFirst, leftSecond] with
                                      | none =>
                                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq, rankLeftEq]
                                            at computed
                                      | some rankedLeft =>
                                          cases rankRightEq : FrameRuntime.rankRule4bReferences? mol profile false state fuel right
                                              [rightFirst, rightSecond] with
                                          | none =>
                                              simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq,
                                                rankLeftEq, rankRightEq] at computed
                                          | some rankedRight =>
                                              have rankedLeftLength :=
                                                rankOccurrenceRule4bReferences_length_of_success mol profile false state fuel
                                                  left [leftFirst, leftSecond] rankedLeft rankLeftEq
                                              have rankedRightLength :=
                                                rankOccurrenceRule4bReferences_length_of_success mol profile false state fuel
                                                  right [rightFirst, rightSecond] rankedRight rankRightEq
                                              rcases exists_pair_of_length_eq_two rankedLeft rankedLeftLength with
                                                ⟨rankedLeftFirst, rankedLeftSecond, rfl⟩
                                              rcases exists_pair_of_length_eq_two rankedRight rankedRightLength with
                                                ⟨rankedRightFirst, rankedRightSecond, rfl⟩
                                              simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq,
                                                rankLeftEq, rankRightEq] at computed
                                              cases firstEq : compareDescriptorAtTiedRoot? mol profile false state fuel
                                                  (.rule4b rankedLeftFirst rankedRightFirst) left right with
                                              | none =>
                                                  rw [firstEq] at computed
                                                  simp at computed
                                              | some first =>
                                                  have firstFactor :=
                                                    compareOccurrenceDescriptorAtTiedRoot_success_factors mol profile false state fuel (.rule4b rankedLeftFirst rankedRightFirst)
                                                        left right first firstEq
                                                  rw [buildDenseTiedRoot_rule4b_left_local mol profile false state fuel
                                                    rankedLeftFirst rankedRightFirst left]
                                                    at firstFactor
                                                  rw [buildDenseTiedRoot_rule4b_right_local mol profile false state fuel
                                                    rankedLeftFirst rankedRightFirst right]
                                                    at firstFactor
                                                  rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent mol profile false state fuel rankedRightFirst right] at firstFactor
                                                  cases first with
                                                  | lt =>
                                                      simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq,
                                                        rankLeftEq, rankRightEq, firstEq] at computed
                                                      subst decision
                                                      simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                                        denseRule4bReferenceCountPriority,
                                                        leftRefsEq, rightRefsEq,
                                                        totalRankedOccurrenceRule4bReferences, rankLeftEq,
                                                        rankRightEq, List.compareLex,
                                                        firstFactor]
                                                  | gt =>
                                                      simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq,
                                                        rankLeftEq, rankRightEq, firstEq] at computed
                                                      subst decision
                                                      simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                                        denseRule4bReferenceCountPriority,
                                                        leftRefsEq, rightRefsEq,
                                                        totalRankedOccurrenceRule4bReferences, rankLeftEq,
                                                        rankRightEq, List.compareLex,
                                                        firstFactor]
                                                  | eq =>
                                                      cases secondEq : compareDescriptorAtTiedRoot? mol profile false state fuel
                                                          (.rule4b rankedLeftSecond rankedRightSecond) left right with
                                                      | none =>
                                                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq,
                                                            rightRefsEq, rankLeftEq, rankRightEq, firstEq,
                                                            secondEq] at computed
                                                      | some second =>
                                                          have secondFactor :=
                                                            compareOccurrenceDescriptorAtTiedRoot_success_factors mol profile false state fuel
                                                              (.rule4b rankedLeftSecond rankedRightSecond)
                                                                left right second
                                                              secondEq
                                                          rw [buildDenseTiedRoot_rule4b_left_local mol profile false state fuel
                                                            rankedLeftSecond rankedRightSecond left]
                                                            at secondFactor
                                                          rw [buildDenseTiedRoot_rule4b_right_local mol profile false state fuel
                                                            rankedLeftSecond rankedRightSecond right]
                                                            at secondFactor
                                                          rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent mol profile false state fuel rankedRightSecond right]
                                                            at secondFactor
                                                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq,
                                                            rightRefsEq, rankLeftEq, rankRightEq, firstEq,
                                                            secondEq] at computed
                                                          subst decision
                                                          simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                                            denseRule4bReferenceCountPriority, leftRefsEq,
                                                            rightRefsEq, totalRankedOccurrenceRule4bReferences,
                                                            rankLeftEq, rankRightEq, List.compareLex, firstFactor,
                                                            secondFactor]
                                                          cases second <;> rfl

          | true =>
              cases leftRefsEq : leftReferences with
              | nil =>
                  cases rightRefsEq : rightReferences with
                  | nil =>
                      simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                      subst decision
                      simp [leftRead, rightRead, buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                        leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                        FrameRuntime.rankRule4bReferences?, List.compareLex, compareLex, Ordering.byKey]
                  | cons rightFirst rightTail =>
                      cases rightTail with
                      | nil =>
                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq]
                            at computed
                          subst decision
                          simp [leftRead, rightRead, buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                            leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                            FrameRuntime.rankRule4bReferences?, compareLex, Ordering.byKey]
                          rfl
                      | cons rightSecond rightRest =>
                          cases rightRest with
                          | nil =>
                              simp [leftRead, rightRead, compareRule4b?, leftRefsEq,
                                rightRefsEq] at computed
                              subst decision
                              simp [leftRead, rightRead, buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                                leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                                FrameRuntime.rankRule4bReferences?, compareLex, Ordering.byKey]
                              rfl
                          | cons rightThird rightMore =>
                              simp [leftRead, rightRead, compareRule4b?, leftRefsEq,
                                rightRefsEq] at computed
              | cons leftFirst leftTail =>
                  cases leftTail with
                  | nil =>
                      cases rightRefsEq : rightReferences with
                      | nil =>
                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq]
                            at computed
                          subst decision
                          simp [leftRead, rightRead, buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                            leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                            FrameRuntime.rankRule4bReferences?, compareLex, Ordering.byKey]
                          rfl
                      | cons rightFirst rightTail =>
                          cases rightTail with
                          | nil =>
                              cases selectedEq : compareDescriptorAtTiedRoot? mol profile true state fuel
                                  (.rule4b leftFirst rightFirst) left right with
                              | none =>
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq, selectedEq]
                                    at computed
                              | some selected =>
                                  have selectedFactor :=
                                    compareOccurrenceDescriptorAtTiedRoot_success_factors mol profile true state fuel
                                      (.rule4b leftFirst rightFirst) left right selected selectedEq
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq, selectedEq]
                                    at computed
                                  subst decision
                                  rw [buildDenseTiedRoot_rule4b_left_local mol profile true state fuel leftFirst
                                    rightFirst left] at selectedFactor
                                  rw [buildDenseTiedRoot_rule4b_right_local mol profile true state fuel leftFirst
                                    rightFirst right] at selectedFactor
                                  rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent mol profile true state fuel
                                    rightFirst right] at selectedFactor
                                  simp [leftRead, rightRead, buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                                    leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                                    FrameRuntime.rankRule4bReferences?, List.compareLex, selectedFactor]
                                  cases selected <;> rfl
                          | cons rightSecond rightRest =>
                              cases rightRest with
                              | nil =>
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                                  subst decision
                                  simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                    denseRule4bReferenceCountPriority, leftRefsEq, rightRefsEq,
                                    totalRankedOccurrenceRule4bReferences,
                                    FrameRuntime.rankRule4bReferences?, compareLex, Ordering.byKey]
                              | cons rightThird rightMore =>
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                  | cons leftSecond leftRest =>
                      cases leftRest with
                      | cons leftThird leftMore =>
                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq] at computed
                      | nil =>
                          cases rightRefsEq : rightReferences with
                          | nil =>
                              simp [leftRead, rightRead, compareRule4b?, leftRefsEq,
                                rightRefsEq] at computed
                              subst decision
                              simp [leftRead, rightRead, buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                                leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                                FrameRuntime.rankRule4bReferences?, compareLex, Ordering.byKey]
                              rfl
                          | cons rightFirst rightTail =>
                              cases rightTail with
                              | nil =>
                                  simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                                  subst decision
                                  simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                    denseRule4bReferenceCountPriority, leftRefsEq, rightRefsEq,
                                    totalRankedOccurrenceRule4bReferences,
                                    FrameRuntime.rankRule4bReferences?, compareLex, Ordering.byKey]
                              | cons rightSecond rightRest =>
                                  cases rightRest with
                                  | cons rightThird rightMore =>
                                      simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq] at computed
                                  | nil =>
                                      cases rankLeftEq : FrameRuntime.rankRule4bReferences? mol profile true state fuel left
                                          [leftFirst, leftSecond] with
                                      | none =>
                                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq, rankLeftEq]
                                            at computed
                                      | some rankedLeft =>
                                          cases rankRightEq : FrameRuntime.rankRule4bReferences? mol profile true state fuel right
                                              [rightFirst, rightSecond] with
                                          | none =>
                                              simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq,
                                                rankLeftEq, rankRightEq] at computed
                                          | some rankedRight =>
                                              have rankedLeftLength :=
                                                rankOccurrenceRule4bReferences_length_of_success mol profile true state fuel
                                                  left [leftFirst, leftSecond] rankedLeft rankLeftEq
                                              have rankedRightLength :=
                                                rankOccurrenceRule4bReferences_length_of_success mol profile true state fuel
                                                  right [rightFirst, rightSecond] rankedRight rankRightEq
                                              rcases exists_pair_of_length_eq_two rankedLeft rankedLeftLength with
                                                ⟨rankedLeftFirst, rankedLeftSecond, rfl⟩
                                              rcases exists_pair_of_length_eq_two rankedRight rankedRightLength with
                                                ⟨rankedRightFirst, rankedRightSecond, rfl⟩
                                              simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq,
                                                rankLeftEq, rankRightEq] at computed
                                              cases firstEq : compareDescriptorAtTiedRoot? mol profile true state fuel
                                                  (.rule4b rankedLeftFirst rankedRightFirst) left right with
                                              | none =>
                                                  rw [firstEq] at computed
                                                  simp at computed
                                              | some first =>
                                                  have firstFactor :=
                                                    compareOccurrenceDescriptorAtTiedRoot_success_factors mol profile true state fuel (.rule4b rankedLeftFirst rankedRightFirst)
                                                        left right first firstEq
                                                  rw [buildDenseTiedRoot_rule4b_left_local mol profile true state fuel
                                                    rankedLeftFirst rankedRightFirst left]
                                                    at firstFactor
                                                  rw [buildDenseTiedRoot_rule4b_right_local mol profile true state fuel
                                                    rankedLeftFirst rankedRightFirst right]
                                                    at firstFactor
                                                  rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent mol profile true state fuel rankedRightFirst right] at firstFactor
                                                  cases first with
                                                  | lt =>
                                                      simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq,
                                                        rankLeftEq, rankRightEq, firstEq] at computed
                                                      subst decision
                                                      simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                                        denseRule4bReferenceCountPriority,
                                                        leftRefsEq, rightRefsEq,
                                                        totalRankedOccurrenceRule4bReferences, rankLeftEq,
                                                        rankRightEq, List.compareLex,
                                                        firstFactor]
                                                  | gt =>
                                                      simp [leftRead, rightRead, compareRule4b?, leftRefsEq, rightRefsEq,
                                                        rankLeftEq, rankRightEq, firstEq] at computed
                                                      subst decision
                                                      simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                                        denseRule4bReferenceCountPriority,
                                                        leftRefsEq, rightRefsEq,
                                                        totalRankedOccurrenceRule4bReferences, rankLeftEq,
                                                        rankRightEq, List.compareLex,
                                                        firstFactor]
                                                  | eq =>
                                                      cases secondEq : compareDescriptorAtTiedRoot? mol profile true state fuel
                                                          (.rule4b rankedLeftSecond rankedRightSecond) left right with
                                                      | none =>
                                                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq,
                                                            rightRefsEq, rankLeftEq, rankRightEq, firstEq,
                                                            secondEq] at computed
                                                      | some second =>
                                                          have secondFactor :=
                                                            compareOccurrenceDescriptorAtTiedRoot_success_factors mol profile true state fuel
                                                              (.rule4b rankedLeftSecond rankedRightSecond)
                                                                left right second
                                                              secondEq
                                                          rw [buildDenseTiedRoot_rule4b_left_local mol profile true state fuel
                                                            rankedLeftSecond rankedRightSecond left]
                                                            at secondFactor
                                                          rw [buildDenseTiedRoot_rule4b_right_local mol profile true state fuel
                                                            rankedLeftSecond rankedRightSecond right]
                                                            at secondFactor
                                                          rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent mol profile true state fuel rankedRightSecond right]
                                                            at secondFactor
                                                          simp [leftRead, rightRead, compareRule4b?, leftRefsEq,
                                                            rightRefsEq, rankLeftEq, rankRightEq, firstEq,
                                                            secondEq] at computed
                                                          subst decision
                                                          simp [leftRead, rightRead, buildDenseRule4bProjectedKey,
                                                            denseRule4bReferenceCountPriority, leftRefsEq,
                                                            rightRefsEq, totalRankedOccurrenceRule4bReferences,
                                                            rankLeftEq, rankRightEq, List.compareLex, firstFactor,
                                                            secondFactor]
                                                          cases second <;> rfl



end TetraStereo.OneCenter.FramedRule4bOrderingKey
