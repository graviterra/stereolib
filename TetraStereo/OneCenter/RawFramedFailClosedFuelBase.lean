import TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure
import TetraStereo.OneCenter.RawFramedConstitutionalFuelStability
import TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

























































namespace TetraStereo.OneCenter

namespace RawFramedFailClosedFuelBase

open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.FrameRuntime
open TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure
open TetraStereo.OneCenter.RawFramedConstitutionalFuelStability
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression

/-! ## The fail-closed candidate -/

/-- Fail-closed framed branch comparator.

Fuel `0` decides only on a strict immediate Rule-1a label, or on the complete root label cascade
when both cursors are runtime-terminal.  Every positive fuel uses exactly the recursive schedule of
`FrameRuntime.compareBranch?`, with the `before` callback replaced by this same comparator. -/
def failClosedCompareBranch? (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) :
    Nat → CanonicalRuleStage → Cursor → Cursor → Option Ordering
  | 0, stage, left, right => do
      let first ← label? mol profile authoritative .rule1a left right
      if first != Ordering.eq then some first else
      if terminal mol left && terminal mol right then
        throughLabels? mol profile authoritative stage left right
      else none
  | fuel + 1, stage, left, right => do
      let before := failClosedCompareBranch? mol profile authoritative fuel stage
      let first ← compareRule? mol profile authoritative before .rule1a (fuel + 1) [(left, right)]
      if first != Ordering.eq || stage == .rule1a then some first else
      let distance ←
        compareRule? mol profile authoritative before .rule1b (fuel + 1) [(left, right)]
      if distance != Ordering.eq || stage == .rule1b then some distance else
      compareRule? mol profile authoritative before .rule2 (fuel + 1) [(left, right)]

/-- The exact successor schedule, written as an explicit bind chain so that refinement can be
applied rule by rule.  It is definitionally the positive-fuel branch of
`failClosedCompareBranch?`. -/
private def failClosedSchedule? (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (before : Cursor → Cursor → Option Ordering)
    (fuel : Nat) (stage : CanonicalRuleStage) (left right : Cursor) : Option Ordering :=
  (compareRule? mol profile authoritative before .rule1a fuel [(left, right)]) >>= fun first =>
    if first != Ordering.eq || stage == .rule1a then some first else
    (compareRule? mol profile authoritative before .rule1b fuel [(left, right)]) >>= fun distance =>
      if distance != Ordering.eq || stage == .rule1b then some distance else
      compareRule? mol profile authoritative before .rule2 fuel [(left, right)]

/-- The positive-fuel branch is the explicit schedule with the candidate as its own callback. -/
private theorem failClosed_succ_eq (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage)
    (left right : Cursor) :
    failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage left right =
      failClosedSchedule? mol profile authoritative
        (failClosedCompareBranch? mol profile authoritative fuel stage) (Nat.succ fuel)
        stage left right := rfl

/-- The actual comparator's positive-fuel branch is the same explicit schedule, with the actual
comparator as its own callback. -/
private theorem compareBranch?_succ_eq_schedule (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage)
    (left right : Cursor) :
    FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage left right =
      failClosedSchedule? mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage) (Nat.succ fuel)
        stage left right := rfl

/-! ## Fuel-zero characterisations -/

/-- A strict immediate Rule-1a label is accepted at fuel `0` by the candidate. -/
theorem failClosed_zero_of_rule1a_strict
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (left right : Cursor) (ordering : Ordering)
    (hlabel : label? mol profile authoritative .rule1a left right = some ordering)
    (strict : ordering ≠ Ordering.eq) :
    failClosedCompareBranch? mol profile authoritative 0 stage left right = some ordering := by
  rw [failClosedCompareBranch?]
  rw [hlabel]
  cases ordering with
  | eq => exact absurd rfl strict
  | lt => rfl
  | gt => rfl

/-- A strict immediate Rule-1a label is also the answer at fuel `1`. -/
theorem failClosed_one_of_rule1a_strict
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (left right : Cursor) (ordering : Ordering)
    (hlabel : label? mol profile authoritative .rule1a left right = some ordering)
    (strict : ordering ≠ Ordering.eq) :
    failClosedCompareBranch? mol profile authoritative 1 stage left right = some ordering := by
  have computed :=
    compareRule?_singleton_of_label?_strict mol profile authoritative
      (failClosedCompareBranch? mol profile authoritative 0 stage) .rule1a 1 left right
      ordering hlabel strict
  rw [failClosed_succ_eq]
  simp only [failClosedSchedule?]
  rw [computed]
  cases ordering with
  | eq => exact absurd rfl strict
  | lt => simp
  | gt => simp

/-- On a runtime-terminal pair the candidate's fuel-zero answer is exactly the root label
cascade. -/
theorem failClosed_zero_eq_throughLabels_of_terminal
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (left right : Cursor)
    (hleft : terminal mol left = true) (hright : terminal mol right = true) :
    failClosedCompareBranch? mol profile authoritative 0 stage left right =
      throughLabels? mol profile authoritative stage left right := by
  rw [failClosedCompareBranch?]
  rw [hleft, hright]
  simp only [Bool.true_and]
  cases hfirst : label? mol profile authoritative .rule1a left right with
  | none => simp [throughLabels?, hfirst]
  | some ordering => cases ordering <;> simp [throughLabels?, hfirst]

/-- On a runtime-terminal pair the candidate is the root label cascade at every fuel. -/
theorem failClosed_eq_throughLabels_of_terminal
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool) :
    ∀ (fuel : Nat) (stage : CanonicalRuleStage) (left right : Cursor),
      terminal mol left = true → terminal mol right = true →
      failClosedCompareBranch? mol profile authoritative fuel stage left right =
        throughLabels? mol profile authoritative stage left right
  | 0, stage, left, right, hleft, hright =>
      failClosed_zero_eq_throughLabels_of_terminal mol profile authoritative stage left right
        hleft hright
  | fuel + 1, stage, left, right, hleft, hright => by
      rw [failClosed_succ_eq]
      simp only [failClosedSchedule?]
      rw [compareRule?_singleton_terminal mol profile authoritative
        (failClosedCompareBranch? mol profile authoritative fuel stage) .rule1a (fuel + 1)
        left right hleft hright]
      rw [compareRule?_singleton_terminal mol profile authoritative
        (failClosedCompareBranch? mol profile authoritative fuel stage) .rule1b (fuel + 1)
        left right hleft hright]
      rw [compareRule?_singleton_terminal mol profile authoritative
        (failClosedCompareBranch? mol profile authoritative fuel stage) .rule2 (fuel + 1)
        left right hleft hright]
      rw [throughLabels?]

/-- If all three immediate rules have a label, the root cascade succeeds. -/
theorem throughLabels?_exists (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (left right : Cursor)
    (h1a : ∃ ordering, label? mol profile authoritative .rule1a left right = some ordering)
    (h1b : ∃ ordering, label? mol profile authoritative .rule1b left right = some ordering)
    (h2 : ∃ ordering, label? mol profile authoritative .rule2 left right = some ordering) :
    ∃ ordering, throughLabels? mol profile authoritative stage left right = some ordering := by
  obtain ⟨first, hfirst⟩ := h1a
  cases first with
  | lt => exact ⟨.lt, by simp [throughLabels?, hfirst]⟩
  | gt => exact ⟨.gt, by simp [throughLabels?, hfirst]⟩
  | eq =>
      cases stage with
      | rule1a => exact ⟨.eq, by simp [throughLabels?, hfirst]⟩
      | rule1b =>
          obtain ⟨distance, hdistance⟩ := h1b
          cases distance with
          | lt => exact ⟨.lt, by simp [throughLabels?, hfirst, hdistance]⟩
          | gt => exact ⟨.gt, by simp [throughLabels?, hfirst, hdistance]⟩
          | eq => exact ⟨.eq, by simp [throughLabels?, hfirst, hdistance]⟩
      | rule2 =>
          obtain ⟨distance, hdistance⟩ := h1b
          cases distance with
          | lt => exact ⟨.lt, by simp [throughLabels?, hfirst, hdistance]⟩
          | gt => exact ⟨.gt, by simp [throughLabels?, hfirst, hdistance]⟩
          | eq =>
              obtain ⟨mass, hmass⟩ := h2
              exact ⟨mass, by simp [throughLabels?, hfirst, hdistance, hmass]⟩

/-! ## Unconditional successful-fuel monotonicity -/

/-- `compareRule?` refines when both its callback improves and its fuel grows by one. -/
theorem compareRule?_refines_succ (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool)
    (before₁ before₂ : Cursor → Cursor → Option Ordering)
    (refines : ∀ left right, SuccessRefines (before₁ left right) (before₂ left right))
    (rule : CanonicalRuleStage) (fuel : Nat) (pairs : List (Cursor × Cursor)) :
    SuccessRefines
      (compareRule? mol profile authoritative before₁ rule fuel pairs)
      (compareRule? mol profile authoritative before₂ rule (Nat.succ fuel) pairs) :=
  SuccessRefines.trans
    (compareRule?_refines mol profile authoritative before₁ before₂ refines rule fuel pairs)
    (compareRule?_fuel_refines mol profile authoritative before₂ rule fuel pairs)

/-- Fuel-zero-to-one monotonicity of the candidate. -/
theorem failClosed_refines_succ_zero (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (left right : Cursor) :
    SuccessRefines
      (failClosedCompareBranch? mol profile authoritative 0 stage left right)
      (failClosedCompareBranch? mol profile authoritative 1 stage left right) := by
  intro value computed
  cases hfirst : label? mol profile authoritative .rule1a left right with
  | none =>
      rw [failClosedCompareBranch?] at computed
      rw [hfirst] at computed
      simp at computed
  | some ordering =>
      cases ordering with
      | eq =>
          by_cases hterminal : terminal mol left = true ∧ terminal mol right = true
          · have hzero := failClosed_zero_eq_throughLabels_of_terminal mol profile authoritative
              stage left right hterminal.1 hterminal.2
            have hthrough : throughLabels? mol profile authoritative stage left right = some value := by
              rw [← hzero]
              exact computed
            have hone := failClosed_eq_throughLabels_of_terminal mol profile authoritative
              1 stage left right hterminal.1 hterminal.2
            rw [hone]
            exact hthrough
          · have hnone :
                failClosedCompareBranch? mol profile authoritative 0 stage left right = none := by
              rw [failClosedCompareBranch?]
              rw [hfirst]
              have hbool : (terminal mol left && terminal mol right) = false := by
                cases hleft : terminal mol left with
                | false => simp
                | true =>
                    cases hright : terminal mol right with
                    | false => simp
                    | true => exact absurd ⟨hleft, hright⟩ hterminal
              simp [hbool]
            rw [hnone] at computed
            exact absurd computed (by simp)
      | lt =>
          have hzero := failClosed_zero_of_rule1a_strict mol profile authoritative stage
            left right .lt hfirst (by decide)
          have hone := failClosed_one_of_rule1a_strict mol profile authoritative stage
            left right .lt hfirst (by decide)
          rw [hzero] at computed
          cases computed
          exact hone
      | gt =>
          have hzero := failClosed_zero_of_rule1a_strict mol profile authoritative stage
            left right .gt hfirst (by decide)
          have hone := failClosed_one_of_rule1a_strict mol profile authoritative stage
            left right .gt hfirst (by decide)
          rw [hzero] at computed
          cases computed
          exact hone

/-- One positive-fuel step: if the candidate refines at fuel `f`, then it refines at `f + 1`. -/
theorem failClosed_refines_succ_of_step (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (fuel : Nat)
    (step : ∀ left right,
      SuccessRefines
        (failClosedCompareBranch? mol profile authoritative fuel stage left right)
        (failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage left right)) :
    ∀ left right,
      SuccessRefines
        (failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage left right)
        (failClosedCompareBranch? mol profile authoritative (Nat.succ (Nat.succ fuel)) stage
          left right) := by
  intro left right
  rw [failClosed_succ_eq mol profile authoritative fuel stage left right]
  rw [failClosed_succ_eq mol profile authoritative (Nat.succ fuel) stage left right]
  simp only [failClosedSchedule?]
  apply SuccessRefines.bind
  · exact compareRule?_refines_succ mol profile authoritative
      (failClosedCompareBranch? mol profile authoritative fuel stage)
      (failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage)
      step .rule1a (Nat.succ fuel) [(left, right)]
  · intro first
    by_cases hfirst : (first != Ordering.eq || stage == .rule1a) = true
    · simp only [if_pos hfirst]
      exact SuccessRefines.refl _
    · simp only [if_neg hfirst]
      apply SuccessRefines.bind
      · exact compareRule?_refines_succ mol profile authoritative
          (failClosedCompareBranch? mol profile authoritative fuel stage)
          (failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage)
          step .rule1b (Nat.succ fuel) [(left, right)]
      · intro distance
        by_cases hdistance : (distance != Ordering.eq || stage == .rule1b) = true
        · simp only [if_pos hdistance]
          exact SuccessRefines.refl _
        · simp only [if_neg hdistance]
          exact compareRule?_refines_succ mol profile authoritative
            (failClosedCompareBranch? mol profile authoritative fuel stage)
            (failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage)
            step .rule2 (Nat.succ fuel) [(left, right)]

/-- **Unconditional one-step successful-fuel monotonicity** of the candidate. -/
theorem failClosed_refines_succ (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) :
    ∀ (fuel : Nat) (left right : Cursor),
      SuccessRefines
        (failClosedCompareBranch? mol profile authoritative fuel stage left right)
        (failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage left right) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right
      exact failClosed_refines_succ_zero mol profile authoritative stage left right
  | succ fuel ih =>
      intro left right
      exact failClosed_refines_succ_of_step mol profile authoritative stage fuel ih
        left right

/-- A successful candidate result is reproduced, with the same ordering, one fuel later. -/
theorem failClosed_success_succ (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (fuel : Nat)
    (left right : Cursor) (ordering : Ordering)
    (computed : failClosedCompareBranch? mol profile authoritative fuel stage left right =
      some ordering) :
    failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage left right =
      some ordering :=
  failClosed_refines_succ mol profile authoritative stage fuel left right ordering computed

/-- **Unconditional successful-fuel monotonicity** at every larger fuel. -/
theorem failClosed_success_mono (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) {fuel highFuel : Nat}
    {left right : Cursor} {ordering : Ordering}
    (computed : failClosedCompareBranch? mol profile authoritative fuel stage left right =
      some ordering)
    (le : fuel ≤ highFuel) :
    failClosedCompareBranch? mol profile authoritative highFuel stage left right =
      some ordering := by
  obtain ⟨count, rfl⟩ := Nat.le.dest le
  clear le
  induction count with
  | zero => simpa using computed
  | succ count ih =>
      have step := failClosed_success_succ mol profile authoritative stage (fuel + count)
        left right ordering ih
      exact step

/-! ## Success refinement into the actual comparator -/

/-- Fuel-zero success refinement into `FrameRuntime.compareBranch?`. -/
theorem failClosed_refines_main_zero (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) :
    ∀ left right,
      SuccessRefines
        (failClosedCompareBranch? mol profile authoritative 0 stage left right)
        (FrameRuntime.compareBranch? mol profile authoritative 0 stage left right) := by
  intro left right value computed
  cases hfirst : label? mol profile authoritative .rule1a left right with
  | none =>
      rw [failClosedCompareBranch?] at computed
      rw [hfirst] at computed
      simp at computed
  | some ordering =>
      cases ordering with
      | eq =>
          by_cases hterminal : terminal mol left = true ∧ terminal mol right = true
          · have hzero := failClosed_zero_eq_throughLabels_of_terminal mol profile authoritative
              stage left right hterminal.1 hterminal.2
            have hthrough : throughLabels? mol profile authoritative stage left right = some value := by
              rw [← hzero]
              exact computed
            rw [compareBranch?_eq_throughLabels?_of_terminal mol profile authoritative 0 stage
              left right hterminal.1 hterminal.2]
            exact hthrough
          · have hnone :
                failClosedCompareBranch? mol profile authoritative 0 stage left right = none := by
              rw [failClosedCompareBranch?]
              rw [hfirst]
              have hbool : (terminal mol left && terminal mol right) = false := by
                cases hleft : terminal mol left with
                | false => simp
                | true =>
                    cases hright : terminal mol right with
                    | false => simp
                    | true => exact absurd ⟨hleft, hright⟩ hterminal
              simp [hbool]
            rw [hnone] at computed
            exact absurd computed (by simp)
      | lt =>
          have hzero := failClosed_zero_of_rule1a_strict mol profile authoritative stage
            left right .lt hfirst (by decide)
          rw [hzero] at computed
          cases computed
          have hthrough : throughLabels? mol profile authoritative stage left right = some .lt := by
            simp [throughLabels?, hfirst]
          rw [FrameRuntime.compareBranch?]
          rw [hthrough]
          simp
      | gt =>
          have hzero := failClosed_zero_of_rule1a_strict mol profile authoritative stage
            left right .gt hfirst (by decide)
          rw [hzero] at computed
          cases computed
          have hthrough : throughLabels? mol profile authoritative stage left right = some .gt := by
            simp [throughLabels?, hfirst]
          rw [FrameRuntime.compareBranch?]
          rw [hthrough]
          simp

/-- One positive-fuel step of refinement into the actual comparator. -/
theorem failClosed_refines_main_succ (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (fuel : Nat)
    (step : ∀ left right,
      SuccessRefines
        (failClosedCompareBranch? mol profile authoritative fuel stage left right)
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage left right)) :
    ∀ left right,
      SuccessRefines
        (failClosedCompareBranch? mol profile authoritative (Nat.succ fuel) stage left right)
        (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage left right) := by
  intro left right
  rw [failClosed_succ_eq mol profile authoritative fuel stage left right]
  rw [compareBranch?_succ_eq_schedule mol profile authoritative fuel stage left right]
  simp only [failClosedSchedule?]
  apply SuccessRefines.bind
  · exact compareRule?_refines mol profile authoritative
      (failClosedCompareBranch? mol profile authoritative fuel stage)
      (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
      step .rule1a (Nat.succ fuel) [(left, right)]
  · intro first
    by_cases hfirst : (first != Ordering.eq || stage == .rule1a) = true
    · simp only [if_pos hfirst]
      exact SuccessRefines.refl _
    · simp only [if_neg hfirst]
      apply SuccessRefines.bind
      · exact compareRule?_refines mol profile authoritative
          (failClosedCompareBranch? mol profile authoritative fuel stage)
          (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
          step .rule1b (Nat.succ fuel) [(left, right)]
      · intro distance
        by_cases hdistance : (distance != Ordering.eq || stage == .rule1b) = true
        · simp only [if_pos hdistance]
          exact SuccessRefines.refl _
        · simp only [if_neg hdistance]
          exact compareRule?_refines mol profile authoritative
            (failClosedCompareBranch? mol profile authoritative fuel stage)
            (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
            step .rule2 (Nat.succ fuel) [(left, right)]

/-- **Success refinement into the actual comparator**: every successful candidate result is also
the actual `FrameRuntime.compareBranch?` result, at the same fuel and with the same ordering. -/
theorem failClosed_refines_main (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) :
    ∀ (fuel : Nat) (left right : Cursor),
      SuccessRefines
        (failClosedCompareBranch? mol profile authoritative fuel stage left right)
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage left right) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right
      exact failClosed_refines_main_zero mol profile authoritative stage left right
  | succ fuel ih =>
      intro left right
      exact failClosed_refines_main_succ mol profile authoritative stage fuel ih left right

/-! ## Totality of the candidate on supported cursor pairs -/

/-- At fuel `0`, a supported pair is runtime-terminal and the root label cascade succeeds. -/
theorem failClosed_zero_exists_of_support (mol : RawMolecule) (profile : Profile)
    (root : Nat) {center : CanonicalBranchNode}
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : profile? mol center = some profile) :
    ∀ (stage : CanonicalRuleStage) (left right : Cursor),
      FramedCursorSupport mol profile root 0 left →
      FramedCursorSupport mol profile root 0 right →
      ∃ ordering, failClosedCompareBranch? mol profile true 0 stage left right = some ordering := by
  intro stage left right leftSupport rightSupport
  have hleft := FramedCursorSupport.zero_terminal centerBound wellFormed left leftSupport
  have hright := FramedCursorSupport.zero_terminal centerBound wellFormed right rightSupport
  rw [failClosed_zero_eq_throughLabels_of_terminal mol profile true stage left right hleft hright]
  have h1a := label?_exists_of_support mol profile root 0 centerGenerated available .rule1a
    left right leftSupport rightSupport
  have h1b := label?_exists_of_support mol profile root 0 centerGenerated available .rule1b
    left right leftSupport rightSupport
  have h2 := label?_exists_of_support mol profile root 0 centerGenerated available .rule2
    left right leftSupport rightSupport
  exact throughLabels?_exists mol profile true stage left right h1a h1b h2

/-- **Candidate totality on supported cursor pairs, at every fuel.**  The induction mirrors the
actual runtime completeness argument; the only difference is the fail-closed fuel-zero decision,
which is total on supported (hence terminal) pairs. -/
theorem failClosed_compareBranch_exists_of_support
    (mol : RawMolecule) (profile : Profile) (root : Nat) {center : CanonicalBranchNode}
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : profile? mol center = some profile) :
    ∀ (fuel : Nat) (stage : CanonicalRuleStage) (left right : Cursor),
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering,
        failClosedCompareBranch? mol profile true fuel stage left right = some ordering := by
  intro fuel
  induction fuel with
  | zero =>
      intro stage left right leftSupport rightSupport
      exact failClosed_zero_exists_of_support mol profile root centerBound wellFormed
        centerGenerated available stage left right leftSupport rightSupport
  | succ fuel ih =>
      intro stage left right leftSupport rightSupport
      let before := failClosedCompareBranch? mol profile true fuel stage
      have beforeTotal : ∀ left right,
          FramedCursorSupport mol profile root fuel left →
          FramedCursorSupport mol profile root fuel right →
          ∃ ordering, before left right = some ordering := by
        intro left right leftSupport rightSupport
        exact ih stage left right leftSupport rightSupport
      have frontier : FramedFrontierSupport mol profile root (fuel + 1) [(left, right)] := by
        intro pair member
        have pairEq : pair = (left, right) := by simpa using member
        subst pair
        exact ⟨leftSupport, rightSupport⟩
      rcases compareRule?_exists_of_support mol profile root centerBound wellFormed bonding
          centerGenerated available fuel before beforeTotal .rule1a (fuel + 1) [(left, right)]
          (by omega) frontier with ⟨first, firstEq⟩
      cases first with
      | lt =>
          refine ⟨.lt, ?_⟩
          rw [failClosed_succ_eq]
          simp only [failClosedSchedule?]
          rw [firstEq]
          simp
      | gt =>
          refine ⟨.gt, ?_⟩
          rw [failClosed_succ_eq]
          simp only [failClosedSchedule?]
          rw [firstEq]
          simp
      | eq =>
          cases stage with
          | rule1a =>
              refine ⟨.eq, ?_⟩
              rw [failClosed_succ_eq]
              simp only [failClosedSchedule?]
              rw [firstEq]
              simp
          | rule1b =>
              rcases compareRule?_exists_of_support mol profile root centerBound wellFormed bonding
                  centerGenerated available fuel before beforeTotal .rule1b (fuel + 1)
                  [(left, right)] (by omega) frontier with ⟨distance, distanceEq⟩
              cases distance with
              | lt =>
                  refine ⟨.lt, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
              | gt =>
                  refine ⟨.gt, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
              | eq =>
                  refine ⟨.eq, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
          | rule2 =>
              rcases compareRule?_exists_of_support mol profile root centerBound wellFormed bonding
                  centerGenerated available fuel before beforeTotal .rule1b (fuel + 1)
                  [(left, right)] (by omega) frontier with ⟨distance, distanceEq⟩
              cases distance with
              | lt =>
                  refine ⟨.lt, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
              | gt =>
                  refine ⟨.gt, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
              | eq =>
                  rcases compareRule?_exists_of_support mol profile root centerBound wellFormed
                      bonding centerGenerated available fuel before beforeTotal .rule2 (fuel + 1)
                      [(left, right)] (by omega) frontier with ⟨mass, massEq⟩
                  refine ⟨mass, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq, massEq]
                  simp

/-! ## The explicit fuel bound and actual MAIN adequacy -/

/-- **Candidate fuel bound.**  Every pair of eligible ligand cursors of an admitted actual
center terminates within `2 * mol.atomCount + 2`. -/
theorem failClosed_compareBranch_rule2_fuel_bound (mol : RawMolecule) (profile : Profile)
    {center : CanonicalBranchNode} (root : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) :
    ∃ ordering,
      failClosedCompareBranch? mol profile true (2 * mol.atomCount + 2) .rule2
        (.actual left) (.actual right) = some ordering := by
  have leftHeight : moleculeCursorHeight mol left ≤ 2 * mol.atomCount + 1 :=
    moleculeCursorHeight_le_two_mul_atomCount_add_one centerBound wellFormed leftEligible
  have rightHeight : moleculeCursorHeight mol right ≤ 2 * mol.atomCount + 1 :=
    moleculeCursorHeight_le_two_mul_atomCount_add_one centerBound wellFormed rightEligible
  have leftSupport : FramedCursorSupport mol profile root (2 * mol.atomCount + 2) (.actual left) :=
    .actual (2 * mol.atomCount + 2) left leftEligible (by omega)
  have rightSupport : FramedCursorSupport mol profile root (2 * mol.atomCount + 2) (.actual right) :=
    .actual (2 * mol.atomCount + 2) right rightEligible (by omega)
  exact failClosed_compareBranch_exists_of_support mol profile root centerBound wellFormed
    bonding centerGenerated available (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right)
    leftSupport rightSupport

/-- **Candidate totality on an actual admitted profile.**  The root, the well-formedness and the
profile are extracted from the executable gate, not assumed. -/
theorem failClosed_compareBranch_rule2_of_admitted_profile (mol : RawMolecule) (profile : Profile)
    {center : CanonicalBranchNode}
    (wellFormed : mol.WellFormed)
    (bonding : ∀ root, CanonicalCenterBondingNumberSix mol root)
    (available : profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center) :
    ∃ ordering,
      failClosedCompareBranch? mol profile true (2 * mol.atomCount + 2) .rule2
        (.actual left) (.actual right) = some ordering := by
  rcases profile_center_generated available with ⟨root, _rootTail, rootBound, _wellFormed,
    centerGenerated⟩
  have leftEligible : CanonicalCenterRerootCursor mol root left :=
    occurrenceLigandCursor_eligible centerGenerated leftMember
  have rightEligible : CanonicalCenterRerootCursor mol root right :=
    occurrenceLigandCursor_eligible centerGenerated rightMember
  exact failClosed_compareBranch_rule2_fuel_bound mol profile root rootBound wellFormed
    (bonding root) centerGenerated available leftEligible rightEligible

/-- **Actual MAIN adequacy from the fail-closed candidate.**  At fuel `2 * mol.atomCount + 2` the
actual comparator `FrameRuntime.compareBranch?` is total on every admitted all-real profile,
obtained from candidate totality plus success refinement.  `FrameRuntime.compareBranch?` itself is
not modified. -/
theorem main_compareBranch_rule2_of_admitted_profile_via_failClosed
    (mol : RawMolecule) (profile : Profile) {center : CanonicalBranchNode}
    (wellFormed : mol.WellFormed)
    (bonding : ∀ root, CanonicalCenterBondingNumberSix mol root)
    (available : profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center) :
    ∃ ordering,
      FrameRuntime.compareBranch? mol profile true (2 * mol.atomCount + 2) .rule2
        (.actual left) (.actual right) = some ordering := by
  rcases failClosed_compareBranch_rule2_of_admitted_profile mol profile wellFormed bonding
    available leftMember rightMember with ⟨ordering, computed⟩
  exact ⟨ordering, failClosed_refines_main mol profile true .rule2
    (2 * mol.atomCount + 2) (.actual left) (.actual right) ordering computed⟩

/-- Candidate totality at every fuel at or above the explicit bound. -/
theorem failClosed_compareBranch_rule2_of_admitted_profile_ge
    (mol : RawMolecule) (profile : Profile) {center : CanonicalBranchNode}
    (wellFormed : mol.WellFormed)
    (bonding : ∀ root, CanonicalCenterBondingNumberSix mol root)
    (available : profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center)
    {fuel : Nat} (bound : 2 * mol.atomCount + 2 ≤ fuel) :
    ∃ ordering,
      failClosedCompareBranch? mol profile true fuel .rule2
        (.actual left) (.actual right) = some ordering := by
  rcases failClosed_compareBranch_rule2_of_admitted_profile mol profile wellFormed bonding
    available leftMember rightMember with ⟨ordering, computed⟩
  exact ⟨ordering, failClosed_success_mono mol profile true .rule2 computed bound⟩

/-- Actual MAIN totality at every fuel at or above the explicit bound, still without mutating the
actual comparator. -/
theorem main_compareBranch_rule2_of_admitted_profile_ge
    (mol : RawMolecule) (profile : Profile) {center : CanonicalBranchNode}
    (wellFormed : mol.WellFormed)
    (bonding : ∀ root, CanonicalCenterBondingNumberSix mol root)
    (available : profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center)
    {fuel : Nat} (bound : 2 * mol.atomCount + 2 ≤ fuel) :
    ∃ ordering,
      FrameRuntime.compareBranch? mol profile true fuel .rule2
        (.actual left) (.actual right) = some ordering := by
  rcases failClosed_compareBranch_rule2_of_admitted_profile_ge mol profile wellFormed bonding
    available leftMember rightMember bound with ⟨ordering, computed⟩
  exact ⟨ordering, failClosed_refines_main mol profile true .rule2 fuel
    (.actual left) (.actual right) ordering computed⟩





theorem zero_fuel_fail_closed_none :
    failClosedCompareBranch? expandedMolecule profile true 0 .rule2 ethyl fluoromethyl = none := by
  decide

/-- At fuel `1` the same witness yields the exhaustive Rule-1a answer `lt`. -/
theorem one_fuel_fail_closed_lt :
    failClosedCompareBranch? expandedMolecule profile true 1 .rule2 ethyl fluoromethyl = some .lt := by
  decide

/-- The actual comparator still returns its premature fuel-zero Rule-2 answer on the witness. -/
theorem zero_fuel_main_gt :
    FrameRuntime.compareBranch? expandedMolecule profile true 0 .rule2 ethyl fluoromethyl =
      some .gt :=
  zero_fuel_compare_gt

/-- The actual comparator and the candidate agree at fuel `1`. -/
theorem one_fuel_main_lt :
    FrameRuntime.compareBranch? expandedMolecule profile true 1 .rule2 ethyl fluoromethyl =
      some .lt :=
  one_fuel_compare_lt

/-- Candidate monotonicity transports the exhaustive fuel-one answer to every larger fuel. -/
theorem fail_closed_counter_lt_of_one_le {fuel : Nat} (le : 1 ≤ fuel) :
    failClosedCompareBranch? expandedMolecule profile true fuel .rule2 ethyl fluoromethyl =
      some .lt :=
  failClosed_success_mono expandedMolecule profile true .rule2 one_fuel_fail_closed_lt le

/-- On the counter the actual comparator's fuel-zero `gt` is refined by the candidate only at
strictly positive fuel: the candidate refuses at `0` and hence in particular does not reproduce the
premature answer. -/
theorem fail_closed_counter_zero_not_main_gt :
    failClosedCompareBranch? expandedMolecule profile true 0 .rule2 ethyl fluoromethyl ≠
      some .gt := by
  rw [zero_fuel_fail_closed_none]
  simp

end RawFramedFailClosedFuelBase

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosedCompareBranch?
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_zero_of_rule1a_strict
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_one_of_rule1a_strict
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_zero_eq_throughLabels_of_terminal
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_eq_throughLabels_of_terminal
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.throughLabels?_exists
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.compareRule?_refines_succ
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_refines_succ_zero
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_refines_succ_of_step
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_refines_succ
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_success_succ
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_success_mono
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_refines_main_zero
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_refines_main_succ
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_refines_main
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_zero_exists_of_support
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_compareBranch_exists_of_support
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_compareBranch_rule2_fuel_bound
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_compareBranch_rule2_of_admitted_profile
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.main_compareBranch_rule2_of_admitted_profile_via_failClosed
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.failClosed_compareBranch_rule2_of_admitted_profile_ge
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.main_compareBranch_rule2_of_admitted_profile_ge
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.zero_fuel_fail_closed_none
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.one_fuel_fail_closed_lt
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.zero_fuel_main_gt
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.one_fuel_main_lt
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.fail_closed_counter_lt_of_one_le
assert_kernel_only
  TetraStereo.OneCenter.RawFramedFailClosedFuelBase.fail_closed_counter_zero_not_main_gt
