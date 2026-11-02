import TetraStereo.UniversalProof.NextFrontier.FramedConstitutionalOrderingKey
import TetraStereo.UniversalProof.NextFrontier.FramedRule4bOrderingKey
import TetraStereo.UniversalProof.NextFrontier.FramedRule4cOrderingKey

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TetraStereo.OneCenter.FramedSuccessfulOrderingTransitivity

open RawMolecule FrameRuntime FramedDescriptorProjectedOrderingKey
open FramedRule4bOrderingKey FramedRule4cOrderingKey

/-! The complete key is unary at fixed molecule/profile/mode/state/fuel. Empty-state production
short-circuit is represented by an empty descriptor tail. Only ordering is composed; no endpoint
success or metadata transitivity is asserted. -/

structure TailKey where
  rule4a : DenseRule4aProjectedKey
  rule4b : DenseRule4bProjectedKey
  rule4c : OptionalKey
  rule5 : DenseRule5ProjectedKey

def buildTailKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (cursor : Cursor) : TailKey :=
  { rule4a := buildDenseRule4aProjectedKey mol profile authoritative state fuel cursor
    rule4b := buildDenseRule4bProjectedKey mol profile authoritative state fuel cursor
    rule4c := buildOptionalKey mol profile authoritative state fuel cursor
    rule5 := buildDenseRule5ProjectedKey mol profile authoritative state fuel cursor }

def compareTailKey : TailKey → TailKey → Ordering :=
  compareLex (Ordering.byKey TailKey.rule4a compareDenseRule4aProjectedKeys)
    (compareLex (Ordering.byKey TailKey.rule4b compareDenseRule4bProjectedKeys)
      (compareLex (Ordering.byKey TailKey.rule4c compareOptionalKey)
        (Ordering.byKey TailKey.rule5 compareDenseRule5ProjectedKeys)))

theorem compareTailKey_transCmp : Std.TransCmp compareTailKey := by
  unfold compareTailKey
  letI := compareDenseRule4aProjectedKeys_transCmp
  letI := compareDenseRule4bProjectedKeys_transCmp
  letI := compareOptionalKey_transCmp
  letI := compareDenseRule5ProjectedKeys_transCmp
  infer_instance

structure FullKey where
  constitutional : FramedConstitutionalOrderingKey.Key
  tail : List TailKey

def buildFullKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (cursor : CanonicalRerootCursor) : FullKey :=
  { constitutional := FramedConstitutionalOrderingKey.buildKey mol profile authoritative fuel
      (.actual cursor)
    tail := if state.isEmpty then [] else
      [buildTailKey mol profile authoritative state fuel (.actual cursor)] }

def compareFullKey : FullKey → FullKey → Ordering :=
  compareLex (Ordering.byKey FullKey.constitutional FramedConstitutionalOrderingKey.compareKey)
    (Ordering.byKey FullKey.tail (List.compareLex compareTailKey))

theorem compareFullKey_transCmp : Std.TransCmp compareFullKey := by
  unfold compareFullKey
  letI := FramedConstitutionalOrderingKey.compareKey_transCmp
  letI := compareTailKey_transCmp
  infer_instance

private theorem decision_nonempty_success_factors
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (nonempty : state.isEmpty = false) :
    ∀ left right comparison,
    decisionComplete? mol profile authoritative state fuel left right = some comparison →
      compareFullKey (buildFullKey mol profile authoritative state fuel left)
        (buildFullKey mol profile authoritative state fuel right) = comparison.ordering := by
  intro left right comparison computed
  cases constitutionalEq : compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) with
  | none => simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq] at computed
  | some constitutional =>
      have constitutionalFactor :=
        FramedConstitutionalOrderingKey.compareBranch?_success_factors
            mol profile authoritative fuel (.actual left) (.actual right) constitutional constitutionalEq
      cases constitutional with
      | lt =>
          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq] at computed
          subst comparison
          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey, compareLex, Ordering.byKey,
            buildFullKey, constitutionalFactor]
      | gt =>
          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq] at computed
          subst comparison
          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey, compareLex, Ordering.byKey,
            buildFullKey, constitutionalFactor]
      | eq =>
          cases rule4aEq : compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
              (.actual left) (.actual right) with
          | none =>
              simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq] at computed
          | some rule4a =>
              have rule4aFactor := compareOccurrenceRule4a_tied_success_factors mol profile authoritative state fuel
                (.actual left) (.actual right) rule4a rule4aEq
              cases rule4a with
              | lt =>
                  simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq] at computed
                  subst comparison
                  simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey, compareLex,
                    Ordering.byKey, buildFullKey,
                    constitutionalFactor, rule4aFactor]
              | gt =>
                  simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq] at computed
                  subst comparison
                  simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey, compareLex,
                    Ordering.byKey, buildFullKey,
                    constitutionalFactor, rule4aFactor]
              | eq =>
                  cases rule4bEq : compareRule4b? mol profile authoritative state fuel (.actual left) (.actual right) with
                  | none =>
                      simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq, rule4bEq]
                        at computed
                  | some rule4b =>
                      have rule4bFactor := compareRule4b_success_factors mol profile authoritative state fuel
                        (.actual left) (.actual right) rule4b rule4bEq
                      cases rule4b with
                      | lt =>
                          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq, rule4bEq]
                            at computed
                          subst comparison
                          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey, compareLex,
                            Ordering.byKey, buildFullKey,
                            constitutionalFactor, rule4aFactor, rule4bFactor]
                      | gt =>
                          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq, rule4bEq]
                            at computed
                          subst comparison
                          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey, compareLex,
                            Ordering.byKey, buildFullKey,
                            constitutionalFactor, rule4aFactor, rule4bFactor]
                      | eq =>
                          cases lowercase : state.any fun fact => !fact.uppercase
                          · cases rule5Eq : compareRule5? mol profile authoritative state fuel (.actual left) (.actual right) with
                            | none =>
                                simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq,
                                  rule4bEq, lowercase, rule5Eq] at computed
                            | some rule5 =>
                                have rule5Factor :=
                                  compareOccurrenceRule5_ordering_success_factors mol profile authoritative state fuel
                                    (.actual left) (.actual right) rule5 rule5Eq
                                simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq,
                                  rule4bEq, lowercase, rule5Eq] at computed
                                subst comparison
                                simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey, compareLex,
                                  Ordering.byKey, buildFullKey,
                                  buildOptionalKey,
                                  compareOptionalKey, constitutionalFactor,
                                  rule4aFactor, rule4bFactor, lowercase, rule5Factor,
                                  List.compareLex]
                                cases rule5.ordering <;> rfl
                          · let before :=
                                compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c
                            cases rule4cEq : compareRule4cWithWitness? mol profile authoritative state before
                                before fuel [(.actual left, .actual right)] with
                            | none =>
                                simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq, rule4aEq,
                                  rule4bEq, lowercase, before, rule4cEq] at computed
                            | some rule4c =>
                                have rule4cFactor :=
                                  witness_success_factors
                                    mol profile authoritative state fuel (.actual left) (.actual right) rule4c
                                    (by simpa [before] using rule4cEq)
                                cases rule4c with
                                | mk rule4cOrdering rule4cCarrier =>
                                  cases rule4cOrdering with
                                  | lt =>
                                      simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq,
                                        rule4aEq, rule4bEq, lowercase, before, rule4cEq] at computed
                                      subst comparison
                                      simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey,
                                        compareLex, Ordering.byKey,
                                        buildFullKey,
                                        buildOptionalKey,
                                        compareOptionalKey, constitutionalFactor,
                                        rule4aFactor, rule4bFactor, rule4cFactor, lowercase,
                                        List.compareLex]
                                  | gt =>
                                      simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq,
                                        rule4aEq, rule4bEq, lowercase, before, rule4cEq] at computed
                                      subst comparison
                                      simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey,
                                        compareLex, Ordering.byKey,
                                        buildFullKey,
                                        buildOptionalKey,
                                        compareOptionalKey, constitutionalFactor,
                                        rule4aFactor, rule4bFactor, rule4cFactor, lowercase,
                                        List.compareLex]
                                  | eq =>
                                      cases rule5Eq : compareRule5? mol profile authoritative state fuel (.actual left) (.actual right) with
                                      | none =>
                                          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq,
                                            rule4aEq, rule4bEq, lowercase, before, rule4cEq,
                                            rule5Eq] at computed
                                      | some rule5 =>
                                          have rule5Factor :=
                                            compareOccurrenceRule5_ordering_success_factors mol profile authoritative state fuel (.actual left) (.actual right) rule5 rule5Eq
                                          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, decisionComplete?, constitutionalEq,
                                            rule4aEq, rule4bEq, lowercase, before, rule4cEq,
                                            rule5Eq] at computed
                                          subst comparison
                                          simp [nonempty, compareTailKey, buildTailKey, List.compareLex, compareFullKey,
                                            compareLex, Ordering.byKey,
                                            buildFullKey,
                                            buildOptionalKey,
                                            compareOptionalKey,
                                            constitutionalFactor, rule4aFactor, rule4bFactor,
                                            rule4cFactor, rule5Factor, lowercase, List.compareLex]
                                          cases rule5.ordering <;> rfl

/-- Actual production comparison factors through the constructed lawful key on every successful
execution. No factorization, ordering law, result or key is supplied by the caller. -/
theorem decisionComplete?_success_factors
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (result : OccurrenceComparison)
    (computed : decisionComplete? mol profile authoritative state fuel left right = some result) :
    compareFullKey (buildFullKey mol profile authoritative state fuel left)
      (buildFullKey mol profile authoritative state fuel right) = result.ordering := by
  cases empty : state.isEmpty with
  | false =>
      exact decision_nonempty_success_factors mol profile authoritative state fuel empty
        left right result computed
  | true =>
      cases hc : compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) with
      | none => simp [decisionComplete?, hc] at computed
      | some ordering =>
          have factor := FramedConstitutionalOrderingKey.compareBranch?_success_factors
            mol profile authoritative fuel (.actual left) (.actual right) ordering hc
          cases ordering <;>
            simp [decisionComplete?, hc, empty] at computed <;>
            subst result <;>
            simp [compareFullKey, buildFullKey, compareLex, Ordering.byKey, empty, factor,
              List.compareLex]

/-- Opposing strict comparisons do not determine the endpoint ordering. -/
def composeSuccessfulOrdering? : Ordering → Ordering → Option Ordering
  | .eq, ordering | ordering, .eq => some ordering
  | .gt, .gt => some .gt
  | .lt, .lt => some .lt
  | .gt, .lt | .lt, .gt => none

private theorem lawful_key_compose {left middle right : FullKey} {composed : Ordering}
    (composition : composeSuccessfulOrdering? (compareFullKey left middle)
      (compareFullKey middle right) = some composed) : compareFullKey left right = composed := by
  letI := compareFullKey_transCmp
  cases leftMiddleEq : compareFullKey left middle <;>
    cases middleRightEq : compareFullKey middle right <;>
    simp [composeSuccessfulOrdering?, leftMiddleEq, middleRightEq] at composition <;>
    subst composed
  · exact Std.TransCmp.lt_trans leftMiddleEq middleRightEq
  · exact Std.TransCmp.lt_of_lt_of_eq leftMiddleEq middleRightEq
  · exact Std.TransCmp.lt_of_eq_of_lt leftMiddleEq middleRightEq
  · exact Std.TransCmp.eq_trans leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_of_eq_of_gt leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_of_gt_of_eq leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_trans leftMiddleEq middleRightEq

/-- General production theorem: one fixed context, three actual successful comparisons and a
well-defined composition suffice. Endpoint success is an explicit premise, not a theorem output. -/
theorem decisionComplete?_ordering_compose_of_three_success
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : OccurrenceComparison} {composed : Ordering}
    (leftMiddleEq : decisionComplete? mol profile authoritative state fuel left middle = some leftMiddle)
    (middleRightEq : decisionComplete? mol profile authoritative state fuel middle right = some middleRight)
    (leftRightEq : decisionComplete? mol profile authoritative state fuel left right = some leftRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    leftRight.ordering = composed := by
  have lm := decisionComplete?_success_factors mol profile authoritative state fuel
    left middle leftMiddle leftMiddleEq
  have mr := decisionComplete?_success_factors mol profile authoritative state fuel
    middle right middleRight middleRightEq
  have lr := decisionComplete?_success_factors mol profile authoritative state fuel
    left right leftRight leftRightEq
  have keyComposition : composeSuccessfulOrdering?
      (compareFullKey (buildFullKey mol profile authoritative state fuel left)
        (buildFullKey mol profile authoritative state fuel middle))
      (compareFullKey (buildFullKey mol profile authoritative state fuel middle)
        (buildFullKey mol profile authoritative state fuel right)) = some composed := by
    rw [lm, mr]
    exact composition
  exact lr.symm.trans (lawful_key_compose keyComposition)

end TetraStereo.OneCenter.FramedSuccessfulOrderingTransitivity
