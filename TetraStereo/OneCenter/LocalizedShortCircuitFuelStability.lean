import TetraStereo.OneCenter.LocalizedShortCircuitFuelCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

private theorem mapM_eq_on_members {α β : Type} (left right : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, left value = right value) →
      values.mapM left = values.mapM right
  | [], _ => rfl
  | value :: values, agree => by
      rw [List.mapM_cons, List.mapM_cons, agree value (by simp)]
      rw [mapM_eq_on_members left right values (fun item present => agree item (by simp [present]))]

/-- Beyond the structural budget, certified callback-free keys are independent of additional fuel,
the descriptor target and the auxiliary-label view. This is equality of complete keys, not only
their root priorities. -/
theorem shortCircuitRule3Key_stable_above_budget
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (leftTarget rightTarget : input.LocalizedCIPOccurrence carrierFuel)
    (leftView : input.LocalizedDependencyView leftTarget)
    (rightView : input.LocalizedDependencyView rightTarget)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    ∀ leftFuel rightFuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor < leftFuel →
      input.localizedRerootCursorBudget cursor < rightFuel →
      input.buildLocalizedRerootShortCircuitRule3KeyExec?
        leftTarget leftView leftFuel excluded cursor =
      input.buildLocalizedRerootShortCircuitRule3KeyExec?
        rightTarget rightView rightFuel excluded cursor
  | 0, _, _, _, leftBound, _ => by omega
  | _, 0, _, _, _, rightBound => by omega
  | leftFuel + 1, rightFuel + 1, cursor, valid, leftBound, rightBound => by
      let children := input.executableLocalizedRerootChildren cursor
      have childrenComputed : input.executableLocalizedRerootChildren? cursor = some children := rfl
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      obtain ⟨certificate, _⟩ := ready.ready cursor.occurrence
      have leftComputed := certificate.computed leftTarget leftView
        (input.buildLocalizedShortCircuitRule3FrameExec? leftTarget leftView leftFuel) excluded
      have rightComputed := certificate.computed rightTarget rightView
        (input.buildLocalizedShortCircuitRule3FrameExec? rightTarget rightView rightFuel) excluded
      have childrenEqual : children.mapM
          (input.buildLocalizedRerootShortCircuitRule3KeyExec? leftTarget leftView leftFuel excluded) =
          children.mapM
          (input.buildLocalizedRerootShortCircuitRule3KeyExec? rightTarget rightView rightFuel excluded) := by
        apply mapM_eq_on_members
        intro child present
        have childValid := input.localizedRerootChild_valid cursor child children derived present
        have decreases := input.localizedRerootChild_budget_lt
          cursor child children valid derived present
        apply input.shortCircuitRule3Key_stable_above_budget
          ready leftTarget rightTarget leftView rightView excluded leftFuel rightFuel child childValid
        · omega
        · omega
      simp [buildLocalizedRerootShortCircuitRule3KeyExec?, childrenComputed,
        leftComputed, rightComputed, childrenEqual]

/-- Complete two-pass frames, including topology and physical exclusions, stabilize at the linear
bound for the automatically certified class. All refusals agree as well. -/
theorem shortCircuitRule3Frame_stable_above_linear_bound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (leftTarget rightTarget : input.LocalizedCIPOccurrence carrierFuel)
    (leftView : input.LocalizedDependencyView leftTarget)
    (rightView : input.LocalizedDependencyView rightTarget)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor)
    (leftFuel rightFuel : Nat)
    (leftBound : 2 * (carrierFuel + 1) + 2 ≤ leftFuel)
    (rightBound : 2 * (carrierFuel + 1) + 2 ≤ rightFuel) :
    input.buildLocalizedShortCircuitRule3FrameExec? leftTarget leftView leftFuel cursors =
    input.buildLocalizedShortCircuitRule3FrameExec? rightTarget rightView rightFuel cursors := by
  cases leftFuel with
  | zero => omega
  | succ leftFuel =>
      cases rightFuel with
      | zero => omega
      | succ rightFuel =>
          have passEqual : ∀ excluded, cursors.mapM
              (input.buildLocalizedRerootShortCircuitRule3KeyExec?
                leftTarget leftView leftFuel excluded) =
              cursors.mapM (input.buildLocalizedRerootShortCircuitRule3KeyExec?
                rightTarget rightView rightFuel excluded) := by
            intro excluded
            apply mapM_eq_on_members
            intro cursor present
            have budget := input.localizedRerootCursorBudget_le_twice cursor
            apply input.shortCircuitRule3Key_stable_above_budget
              ready leftTarget rightTarget leftView rightView excluded
              leftFuel rightFuel cursor (valid cursor present)
            · omega
            · omega
          simp only [buildLocalizedShortCircuitRule3FrameExec?, passEqual]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
