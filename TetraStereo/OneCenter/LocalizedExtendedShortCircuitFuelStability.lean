import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Input-derived evidence that the extended evaluator never needs a recursive endpoint frame.
It does not require geometry, any descriptor result, or a precomputed dependency ranking. -/
structure LocalizedExtendedRule3NoCallbackCertificate
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Type where
  empty : ∀ occurrence : input.LocalizedCIPOccurrence fuel,
    input.rule3ExtendedNodeCallbackRequests occurrence = []

def localizedExtendedRule3NoCallbackCertificate?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    Option (input.LocalizedExtendedRule3NoCallbackCertificate fuel) :=
  if checked : (input.localizedOccurrenceCarrier fuel).all
      (fun occurrence => (input.rule3ExtendedNodeCallbackRequests occurrence).isEmpty) = true then
    some
      { empty := fun occurrence => by
          have present := (List.all_eq_true.mp checked) occurrence
            (input.localizedOccurrenceCarrier_complete fuel occurrence)
          simpa using present }
  else none

private theorem mapM_eq_on_members {α β : Type} (left right : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, left value = right value) →
      values.mapM left = values.mapM right
  | [], _ => rfl
  | value :: values, agree => by
      rw [List.mapM_cons, List.mapM_cons, agree value (by simp)]
      rw [mapM_eq_on_members left right values (fun item present => agree item (by simp [present]))]

/-- Complete optional keys stabilize beyond the structural bound. This includes geometry
refusals and uses the new demand locality theorem, not successful node outputs. -/
theorem extendedShortCircuitRule3Key_stable_above_budget
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (ready : input.LocalizedExtendedRule3NoCallbackCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    ∀ leftFuel rightFuel (cursor : input.LocalizedRerootCursor fuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor < leftFuel →
      input.localizedRerootCursorBudget cursor < rightFuel →
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view leftFuel excluded cursor =
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view rightFuel excluded cursor
  | 0, _, _, _, leftBound, _ => by omega
  | _, 0, _, _, _, rightBound => by omega
  | leftFuel + 1, rightFuel + 1, cursor, valid, leftBound, rightBound => by
      let children := input.executableLocalizedRerootChildren cursor
      have childrenComputed : input.executableLocalizedRerootChildren? cursor = some children := rfl
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      have nodeEqual := input.rule3ExtendedNode_callback_local target cursor.occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view leftFuel)
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view rightFuel)
        (by intro cursors member; simp [ready.empty cursor.occurrence] at member) excluded
      have childrenEqual : children.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view leftFuel excluded) =
          children.mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view rightFuel excluded) := by
        apply mapM_eq_on_members
        intro child present
        have childValid := input.localizedRerootChild_valid cursor child children derived present
        have decreases := input.localizedRerootChild_budget_lt cursor child children valid derived present
        apply input.extendedShortCircuitRule3Key_stable_above_budget
          ready target view excluded leftFuel rightFuel child childValid
        · omega
        · omega
      simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?, childrenComputed,
        bind, Option.bind, nodeEqual, childrenEqual]

/-- The complete two-pass extended frame has a sufficient linear bound whenever the finite
molecular demand scan constructs the no-callback certificate. -/
theorem extendedShortCircuitRule3Frame_stable_above_linear_bound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (ready : input.LocalizedExtendedRule3NoCallbackCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor fuel))
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor)
    (leftFuel rightFuel : Nat)
    (leftBound : 2 * (fuel + 1) + 2 ≤ leftFuel)
    (rightBound : 2 * (fuel + 1) + 2 ≤ rightFuel) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view leftFuel cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view rightFuel cursors := by
  cases leftFuel with
  | zero => omega
  | succ leftFuel =>
      cases rightFuel with
      | zero => omega
      | succ rightFuel =>
          have passEqual : ∀ excluded, cursors.mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view leftFuel excluded) =
              cursors.mapM
                (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view rightFuel excluded) := by
            intro excluded
            apply mapM_eq_on_members
            intro cursor present
            have budget := input.localizedRerootCursorBudget_le_twice cursor
            apply input.extendedShortCircuitRule3Key_stable_above_budget
              ready target view excluded leftFuel rightFuel cursor (valid cursor present)
            · omega
            · omega
          simp only [buildLocalizedExtendedShortCircuitRule3FrameExec?, passEqual]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
