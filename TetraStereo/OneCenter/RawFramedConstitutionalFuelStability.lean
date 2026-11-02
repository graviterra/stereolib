import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.RawFramedConstitutionalIndependence
import TetraStereo.KernelOnly

/-!
# Fuel stability of successful raw framed constitutional comparisons

This module proves that a *successful* result of the actual framed constitutional comparator
`FrameRuntime.compareBranch? mol profile authoritative fuel stage left right` cannot change when the
fuel is increased, under a precisely stated per-stage refinement hypothesis on the actual
`FrameRuntime.Cursor` support of the shared profile.

The refinement hypothesis is stated in terms of the runtime's own support test
`FrameRuntime.cursor? mol profile cursor` (`CursorSupported`): for every pair of supported cursors,
a successful comparison at fuel `f` is still produced, with the same value, at fuel `f + 1`
(`SupportedRefinesAt`).  Nothing is assumed about refusals: a `none` at low fuel may become a
`some` at higher fuel, and the main theorem only transports existing successes.  Equivalently, a
refusal at the larger fuel forces a refusal at the smaller fuel
(`compareBranch?_eq_none_of_larger_eq_none`).

The refinement hypothesis is *not* a consequence of the definitions alone: higher fuel changes both
the recursive schedule of `FrameRuntime.compareRule?` and the sibling order used by
`FrameRuntime.ranked?` through the `before` comparator.  Section
"One-step propagation" proves how a single supported check at fuel `f` propagates to every larger
fuel; this reduces the global monotonicity obligation to one check at the starting fuel.

Unconditional corollaries (`compareBranch?_eq_of_rule1a_label?_strict`,
`compareBranch?_eq_throughLabels?_of_terminal`, `compareBranch?_success_stable_of_terminal`) cover
the two cases in which the actual comparator does not depend on fuel at all: a strict Rule-1a label
on the compared pair, and a pair whose two cursors are both runtime-terminal.  The three stages
`rule1a`, `rule1b`, `rule2` are handled uniformly (the comparator-specific theorem quantifies over
the stage).  The actual root frame is connected through
`RawFramedConstitutionalIndependence.RootsConstitutionallySeparated`, the declarative separation
predicate over the real `occurrenceLigandFrame?` roots: it transports to every larger fuel
(`rootsConstitutionallySeparated_mono`).

No alternative comparator, no assumed sort result, and no normative claim about which frame is
preferred is introduced.  The original-versus-rebased observer policy is exactly the one of the
existing `FrameRuntime`; this module only reads it.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo
namespace OneCenter
namespace RawFramedConstitutionalFuelStability

open RawMolecule

/-! ## Successful-value refinement -/

/-- `SuccessRefines before after` says every successful value of `before` is also produced by
`after`.  It is the one-sided refinement relation used throughout: refusals are never related. -/
def SuccessRefines {α : Type*} (before after : Option α) : Prop :=
  ∀ value, before = some value → after = some value

namespace SuccessRefines

theorem refl {α : Type*} (value : Option α) : SuccessRefines value value :=
  fun _ computed => computed

theorem trans {α : Type*} {first second third : Option α}
    (forward : SuccessRefines first second) (onward : SuccessRefines second third) :
    SuccessRefines first third :=
  fun value computed => onward value (forward value computed)

theorem bind {α β : Type} {before after : Option α}
    {left right : α → Option β}
    (head : SuccessRefines before after)
    (tail : ∀ value, SuccessRefines (left value) (right value)) :
    SuccessRefines (before >>= left) (after >>= right) := by
  intro result computed
  cases source : before with
  | none => simp [source] at computed
  | some value =>
      have next : after = some value := head value source
      simpa [next] using tail value result (by simpa [source] using computed)

end SuccessRefines

/-! ## Runtime support of a cursor in the shared profile -/

/-- The runtime's own support test for a cursor: `FrameRuntime.cursor?` accepts it. -/
def CursorSupported (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (cursor : FrameRuntime.Cursor) : Prop :=
  (FrameRuntime.cursor? mol profile cursor).isSome = true

theorem cursor?_eq_none_of_not_supported (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (cursor : FrameRuntime.Cursor) (unsupported : ¬ CursorSupported mol profile cursor) :
    FrameRuntime.cursor? mol profile cursor = none := by
  cases computed : FrameRuntime.cursor? mol profile cursor with
  | none => rfl
  | some distance => exact absurd (by simp [CursorSupported, computed]) unsupported

/-! ## An unsupported cursor refuses before any rule is read -/

theorem label?_eq_none_of_cursor?_left (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (rule : CanonicalRuleStage) (left right : FrameRuntime.Cursor)
    (hleft : FrameRuntime.cursor? mol profile left = none) :
    FrameRuntime.label? mol profile authoritative rule left right = none := by
  simp [FrameRuntime.label?, hleft]

theorem label?_eq_none_of_cursor?_right (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (rule : CanonicalRuleStage) (left right : FrameRuntime.Cursor)
    (hright : FrameRuntime.cursor? mol profile right = none) :
    FrameRuntime.label? mol profile authoritative rule left right = none := by
  cases hleft : FrameRuntime.cursor? mol profile left with
  | none => exact label?_eq_none_of_cursor?_left mol profile authoritative rule left right hleft
  | some distance => simp [FrameRuntime.label?, hleft, hright]

theorem pairLabels?_cons_none_of_label?_none (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (rule : CanonicalRuleStage) (left right : FrameRuntime.Cursor)
    (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor))
    (hlabel : FrameRuntime.label? mol profile authoritative rule left right = none) :
    FrameRuntime.pairLabels? mol profile authoritative rule ((left, right) :: pairs) = none := by
  rw [FrameRuntime.pairLabels?]
  rw [hlabel]
  simp

/-- The width cap can never fire on a singleton frontier: there the frontier length is one and the
cap is the actual runtime constant. -/
theorem singleton_cap_eq_false (authoritative : Bool) (left right : FrameRuntime.Cursor) :
    (!authoritative && RawMolecule.defaultBranchWidthCap <
        ([(left, right)] : List (FrameRuntime.Cursor × FrameRuntime.Cursor)).length) = false := by
  have hlen : ([(left, right)] : List (FrameRuntime.Cursor × FrameRuntime.Cursor)).length = 1 := rfl
  rw [hlen]
  cases authoritative <;> decide

theorem compareRule?_singleton_none_of_pairLabels?_none
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (rule : CanonicalRuleStage) (fuel : Nat) (left right : FrameRuntime.Cursor)
    (hpair : FrameRuntime.pairLabels? mol profile authoritative rule [(left, right)] = none) :
    FrameRuntime.compareRule? mol profile authoritative before rule fuel [(left, right)] = none := by
  rw [FrameRuntime.compareRule?]
  by_cases hcap : (!authoritative && RawMolecule.defaultBranchWidthCap <
      ([(left, right)] : List (FrameRuntime.Cursor × FrameRuntime.Cursor)).length) = true
  · rw [singleton_cap_eq_false authoritative left right] at hcap
    simp at hcap
  · rw [if_neg hcap]
    rw [hpair]
    simp

theorem compareRule?_singleton_none_of_cursor?_left
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (rule : CanonicalRuleStage) (fuel : Nat) (left right : FrameRuntime.Cursor)
    (hleft : FrameRuntime.cursor? mol profile left = none) :
    FrameRuntime.compareRule? mol profile authoritative before rule fuel [(left, right)] = none :=
  compareRule?_singleton_none_of_pairLabels?_none mol profile authoritative before rule fuel
    left right
    (pairLabels?_cons_none_of_label?_none mol profile authoritative rule left right []
      (label?_eq_none_of_cursor?_left mol profile authoritative rule left right hleft))

theorem compareRule?_singleton_none_of_cursor?_right
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (rule : CanonicalRuleStage) (fuel : Nat) (left right : FrameRuntime.Cursor)
    (hright : FrameRuntime.cursor? mol profile right = none) :
    FrameRuntime.compareRule? mol profile authoritative before rule fuel [(left, right)] = none :=
  compareRule?_singleton_none_of_pairLabels?_none mol profile authoritative before rule fuel
    left right
    (pairLabels?_cons_none_of_label?_none mol profile authoritative rule left right []
      (label?_eq_none_of_cursor?_right mol profile authoritative rule left right hright))

theorem compareBranch?_eq_none_of_cursor?_left
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (stage : CanonicalRuleStage) {left right : FrameRuntime.Cursor}
    (hleft : FrameRuntime.cursor? mol profile left = none) :
    FrameRuntime.compareBranch? mol profile authoritative fuel stage left right = none := by
  cases fuel with
  | zero =>
      rw [FrameRuntime.compareBranch?]
      have hthrough : FrameRuntime.throughLabels? mol profile authoritative stage left right = none := by
        simp [FrameRuntime.throughLabels?, FrameRuntime.label?, hleft]
      rw [hthrough]
      simp
  | succ fuel =>
      rw [FrameRuntime.compareBranch?]
      rw [compareRule?_singleton_none_of_cursor?_left mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
        CanonicalRuleStage.rule1a (Nat.succ fuel) left right hleft]
      simp

theorem compareBranch?_eq_none_of_cursor?_right
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (stage : CanonicalRuleStage) {left right : FrameRuntime.Cursor}
    (hright : FrameRuntime.cursor? mol profile right = none) :
    FrameRuntime.compareBranch? mol profile authoritative fuel stage left right = none := by
  cases fuel with
  | zero =>
      rw [FrameRuntime.compareBranch?]
      have hthrough : FrameRuntime.throughLabels? mol profile authoritative stage left right = none := by
        have hlabel : FrameRuntime.label? mol profile authoritative CanonicalRuleStage.rule1a
            left right = none :=
          label?_eq_none_of_cursor?_right mol profile authoritative CanonicalRuleStage.rule1a
            left right hright
        simp [FrameRuntime.throughLabels?, hlabel]
      rw [hthrough]
      simp
  | succ fuel =>
      rw [FrameRuntime.compareBranch?]
      rw [compareRule?_singleton_none_of_cursor?_right mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
        CanonicalRuleStage.rule1a (Nat.succ fuel) left right hright]
      simp

/-! ## A single pair: one strict label stops the expansion immediately -/

/-- `pairLabels?` on a singleton frontier is exactly the underlying label comparison. -/
theorem pairLabels?_singleton_eq_label? (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (rule : CanonicalRuleStage) (left right : FrameRuntime.Cursor) :
    FrameRuntime.pairLabels? mol profile authoritative rule [(left, right)] =
      FrameRuntime.label? mol profile authoritative rule left right := by
  rw [FrameRuntime.pairLabels?]
  cases hlabel : FrameRuntime.label? mol profile authoritative rule left right with
  | none => simp [FrameRuntime.pairLabels?, hlabel]
  | some cmp => cases cmp <;> simp [FrameRuntime.pairLabels?, hlabel]

/-- A strict single label ends the sphere expansion of `compareRule?`: the recursive fuel is never
consumed, so the result is the same at every fuel. -/
theorem compareRule?_singleton_of_label?_strict
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (rule : CanonicalRuleStage) (fuel : Nat) (left right : FrameRuntime.Cursor)
    (order : Ordering)
    (hlabel : FrameRuntime.label? mol profile authoritative rule left right = some order)
    (strict : order ≠ Ordering.eq) :
    FrameRuntime.compareRule? mol profile authoritative before rule fuel [(left, right)] =
      some order := by
  rw [FrameRuntime.compareRule?]
  by_cases hcap : (!authoritative && RawMolecule.defaultBranchWidthCap <
      ([(left, right)] : List (FrameRuntime.Cursor × FrameRuntime.Cursor)).length) = true
  · rw [singleton_cap_eq_false authoritative left right] at hcap
    simp at hcap
  · rw [if_neg hcap]
    rw [pairLabels?_singleton_eq_label?, hlabel]
    cases order with
    | lt => simp
    | gt => simp
    | eq => exact absurd rfl strict

/-- On a runtime-terminal pair the frontier never expands, so `compareRule?` is exactly the label
comparison at every fuel. -/
theorem compareRule?_singleton_terminal
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (rule : CanonicalRuleStage) (fuel : Nat) (left right : FrameRuntime.Cursor)
    (hleft : FrameRuntime.terminal mol left = true)
    (hright : FrameRuntime.terminal mol right = true) :
    FrameRuntime.compareRule? mol profile authoritative before rule fuel [(left, right)] =
      FrameRuntime.label? mol profile authoritative rule left right := by
  rw [FrameRuntime.compareRule?]
  by_cases hcap : (!authoritative && RawMolecule.defaultBranchWidthCap <
      ([(left, right)] : List (FrameRuntime.Cursor × FrameRuntime.Cursor)).length) = true
  · rw [singleton_cap_eq_false authoritative left right] at hcap
    simp at hcap
  · rw [if_neg hcap]
    rw [pairLabels?_singleton_eq_label?]
    have hnext : FrameRuntime.nextPairs? mol profile authoritative before [(left, right)] =
        some [] := by
      simp [FrameRuntime.nextPairs?, hleft, hright]
    rw [hnext]
    cases hlabel : FrameRuntime.label? mol profile authoritative rule left right with
    | none => simp [hlabel]
    | some cmp => cases cmp <;> simp [hlabel]

/-! ## Unconditional fuel independence at the branch level -/

/-- A strict Rule-1a result on the compared pair is returned by the branch comparator at every fuel
and every stage: the first scheduled rule stops before any fuel is consumed. -/
theorem compareBranch?_eq_of_rule1a_label?_strict
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (stage : CanonicalRuleStage) (left right : FrameRuntime.Cursor)
    (order : Ordering)
    (hlabel : FrameRuntime.label? mol profile authoritative CanonicalRuleStage.rule1a left right =
      some order)
    (strict : order ≠ Ordering.eq) :
    FrameRuntime.compareBranch? mol profile authoritative fuel stage left right = some order := by
  cases fuel with
  | zero =>
      rw [FrameRuntime.compareBranch?]
      rw [FrameRuntime.throughLabels?, hlabel]
      cases order with
      | lt => simp
      | gt => simp
      | eq => exact absurd rfl strict
  | succ fuel =>
      rw [FrameRuntime.compareBranch?]
      rw [compareRule?_singleton_of_label?_strict mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
        CanonicalRuleStage.rule1a (Nat.succ fuel) left right order hlabel strict]
      cases order with
      | lt => simp
      | gt => simp
      | eq => exact absurd rfl strict

/-- On runtime-terminal pairs the branch comparator is the root label cascade at every fuel. -/
theorem compareBranch?_eq_throughLabels?_of_terminal
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (stage : CanonicalRuleStage) (left right : FrameRuntime.Cursor)
    (hleft : FrameRuntime.terminal mol left = true)
    (hright : FrameRuntime.terminal mol right = true) :
    FrameRuntime.compareBranch? mol profile authoritative fuel stage left right =
      FrameRuntime.throughLabels? mol profile authoritative stage left right := by
  cases fuel with
  | zero =>
      rw [FrameRuntime.compareBranch?]
      rw [hleft, hright]
      cases hthrough : FrameRuntime.throughLabels? mol profile authoritative stage left right with
      | none => simp [hthrough]
      | some cmp => simp [hthrough]
  | succ fuel =>
      rw [FrameRuntime.compareBranch?]
      rw [compareRule?_singleton_terminal mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
        CanonicalRuleStage.rule1a (Nat.succ fuel) left right hleft hright]
      rw [compareRule?_singleton_terminal mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
        CanonicalRuleStage.rule1b (Nat.succ fuel) left right hleft hright]
      rw [compareRule?_singleton_terminal mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
        CanonicalRuleStage.rule2 (Nat.succ fuel) left right hleft hright]
      rw [FrameRuntime.throughLabels?]

/-- Fuel stability of a successful comparison on a runtime-terminal pair, with no side condition
on the shared profile. -/
theorem compareBranch?_success_stable_of_terminal
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) {fuel highFuel : Nat} {left right : FrameRuntime.Cursor}
    {decision : Ordering}
    (hleft : FrameRuntime.terminal mol left = true)
    (hright : FrameRuntime.terminal mol right = true)
    (computed : FrameRuntime.compareBranch? mol profile authoritative fuel stage left right =
      some decision) :
    FrameRuntime.compareBranch? mol profile authoritative highFuel stage left right =
      some decision := by
  rw [compareBranch?_eq_throughLabels?_of_terminal mol profile authoritative fuel stage
    left right hleft hright] at computed
  rw [compareBranch?_eq_throughLabels?_of_terminal mol profile authoritative highFuel stage
    left right hleft hright]
  exact computed

/-! ## Refinement of the insertion sort frontier -/

theorem insert?_refines
    (before₁ before₂ : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (refines : ∀ left right, SuccessRefines (before₁ left right) (before₂ left right))
    (candidate : FrameRuntime.Cursor) :
    ∀ input : List FrameRuntime.Cursor,
      SuccessRefines (FrameRuntime.insert? before₁ candidate input)
        (FrameRuntime.insert? before₂ candidate input) := by
  intro input
  induction input with
  | nil =>
      intro output computed
      simpa [FrameRuntime.insert?] using computed
  | cons head tail ih =>
      intro output computed
      simp only [FrameRuntime.insert?] at computed ⊢
      cases decision : before₁ candidate head with
      | none => simp [decision] at computed
      | some cmp =>
          have decision₂ : before₂ candidate head = some cmp :=
            refines candidate head cmp decision
          cases cmp with
          | lt =>
              cases rest : FrameRuntime.insert? before₁ candidate tail with
              | none => simp [decision, rest] at computed
              | some sorted =>
                  have rest₂ : FrameRuntime.insert? before₂ candidate tail = some sorted :=
                    ih sorted rest
                  simp [decision, decision₂, rest, rest₂] at computed ⊢
                  exact computed
          | eq =>
              simp [decision, decision₂] at computed ⊢
              exact computed
          | gt =>
              simp [decision, decision₂] at computed ⊢
              exact computed

theorem sort?_refines
    (before₁ before₂ : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (refines : ∀ left right, SuccessRefines (before₁ left right) (before₂ left right)) :
    ∀ input : List FrameRuntime.Cursor,
      SuccessRefines (FrameRuntime.sort? before₁ input) (FrameRuntime.sort? before₂ input) := by
  intro input
  induction input with
  | nil =>
      intro output computed
      simpa [FrameRuntime.sort?] using computed
  | cons head tail ih =>
      simp only [FrameRuntime.sort?]
      apply SuccessRefines.bind ih
      intro sorted
      exact insert?_refines before₁ before₂ refines head sorted

/-- `ranked?` only consults `before` through its insertion sort of the actual child frontier; a
pointwise refinement of `before` therefore refines every successful ranked expansion. -/
theorem ranked?_refines
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before₁ before₂ : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (refines : ∀ left right, SuccessRefines (before₁ left right) (before₂ left right))
    (parent : FrameRuntime.Cursor) :
    SuccessRefines (FrameRuntime.ranked? mol profile authoritative before₁ parent)
      (FrameRuntime.ranked? mol profile authoritative before₂ parent) := by
  let originalChildren := ((parent.original mol).children mol).map FrameRuntime.Cursor.actual
  let slots := if authoritative then RawMolecule.authoritativeChildSlots else 3
  change SuccessRefines
      ((FrameRuntime.cursor? mol profile parent).bind fun _ =>
      if slots < originalChildren.length then none else
      (originalChildren.mapM (FrameRuntime.cursor? mol profile)).bind fun _ =>
      (FrameRuntime.sort? before₁ originalChildren).bind fun sorted =>
      some (sorted ++ List.replicate (slots - sorted.length)
        (FrameRuntime.Cursor.padding parent)))
      ((FrameRuntime.cursor? mol profile parent).bind fun _ =>
      if slots < originalChildren.length then none else
      (originalChildren.mapM (FrameRuntime.cursor? mol profile)).bind fun _ =>
      (FrameRuntime.sort? before₂ originalChildren).bind fun sorted =>
      some (sorted ++ List.replicate (slots - sorted.length)
        (FrameRuntime.Cursor.padding parent)))
  apply SuccessRefines.bind
    (SuccessRefines.refl (FrameRuntime.cursor? mol profile parent))
  intro distance
  by_cases tooWide : slots < originalChildren.length
  · simp only [if_pos tooWide]
    exact SuccessRefines.refl _
  · simp only [if_neg tooWide]
    apply SuccessRefines.bind
      (SuccessRefines.refl (originalChildren.mapM (FrameRuntime.cursor? mol profile)))
    intro validated
    apply SuccessRefines.bind (sort?_refines before₁ before₂ refines originalChildren)
    intro sorted
    exact SuccessRefines.refl _

theorem nextPairs?_refines
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before₁ before₂ : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (refines : ∀ left right, SuccessRefines (before₁ left right) (before₂ left right)) :
    ∀ pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor),
      SuccessRefines
        (FrameRuntime.nextPairs? mol profile authoritative before₁ pairs)
        (FrameRuntime.nextPairs? mol profile authoritative before₂ pairs)
  | [] => by
      intro output computed
      simpa [FrameRuntime.nextPairs?] using computed
  | (left, right) :: pairs => by
      simp only [FrameRuntime.nextPairs?]
      apply SuccessRefines.bind
        (nextPairs?_refines mol profile authoritative before₁ before₂ refines pairs)
      intro rest
      by_cases terminalPair :
          (FrameRuntime.terminal mol left && FrameRuntime.terminal mol right) = true
      · simp only [if_pos terminalPair]
        exact SuccessRefines.refl _
      · simp only [if_neg terminalPair]
        apply SuccessRefines.bind
          (ranked?_refines mol profile authoritative before₁ before₂ refines left)
        intro lc
        apply SuccessRefines.bind
          (ranked?_refines mol profile authoritative before₁ before₂ refines right)
        intro rc
        exact SuccessRefines.refl _

/-! ## Refinement of the sphere expansion -/

/-- `compareRule?` is refined when its `before` comparator is refined at the same fuel.  The
recursion depth is unchanged, so the induction is on the fuel. -/
theorem compareRule?_refines
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before₁ before₂ : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (refines : ∀ left right, SuccessRefines (before₁ left right) (before₂ left right))
    (rule : CanonicalRuleStage) :
    ∀ (fuel : Nat) (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor)),
      SuccessRefines
        (FrameRuntime.compareRule? mol profile authoritative before₁ rule fuel pairs)
        (FrameRuntime.compareRule? mol profile authoritative before₂ rule fuel pairs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs output computed
      rw [FrameRuntime.compareRule?] at computed
      rw [FrameRuntime.compareRule?]
      by_cases hcap : (!authoritative && RawMolecule.defaultBranchWidthCap <
          pairs.length) = true
      · rw [if_pos hcap] at computed ⊢
        simp at computed
      · rw [if_neg hcap] at computed ⊢
        cases hlabels : FrameRuntime.pairLabels? mol profile authoritative rule pairs with
        | none =>
            simp only [hlabels, Option.bind_none] at computed
            simp at computed
        | some cmp =>
            simp only [hlabels, Option.bind_some] at computed ⊢
            cases cmp with
            | lt =>
                simp at computed ⊢
                exact computed
            | gt =>
                simp at computed ⊢
                exact computed
            | eq =>
                cases hnext : FrameRuntime.nextPairs? mol profile authoritative before₁ pairs with
                | none =>
                    simp only [hnext, Option.bind_none] at computed
                    simp at computed
                | some next =>
                    have hnext₂ :
                        FrameRuntime.nextPairs? mol profile authoritative before₂ pairs =
                          some next :=
                      nextPairs?_refines mol profile authoritative before₁ before₂ refines
                        pairs next hnext
                    cases next with
                    | nil =>
                        simp only [hnext, hnext₂, Option.bind_some] at computed ⊢
                        simp at computed ⊢
                        exact computed
                    | cons head tail =>
                        simp only [hnext, Option.bind_some] at computed
                        simp at computed
  | succ fuel ih =>
      intro pairs output computed
      rw [FrameRuntime.compareRule?] at computed
      rw [FrameRuntime.compareRule?]
      by_cases hcap : (!authoritative && RawMolecule.defaultBranchWidthCap <
          pairs.length) = true
      · rw [if_pos hcap] at computed ⊢
        simp at computed
      · rw [if_neg hcap] at computed ⊢
        cases hlabels : FrameRuntime.pairLabels? mol profile authoritative rule pairs with
        | none =>
            simp only [hlabels, Option.bind_none] at computed
            simp at computed
        | some cmp =>
            simp only [hlabels, Option.bind_some] at computed ⊢
            cases cmp with
            | lt =>
                simp at computed ⊢
                exact computed
            | gt =>
                simp at computed ⊢
                exact computed
            | eq =>
                cases hnext : FrameRuntime.nextPairs? mol profile authoritative before₁ pairs with
                | none =>
                    simp only [hnext, Option.bind_none] at computed
                    simp at computed
                | some next =>
                    have hnext₂ :
                        FrameRuntime.nextPairs? mol profile authoritative before₂ pairs =
                          some next :=
                      nextPairs?_refines mol profile authoritative before₁ before₂ refines
                        pairs next hnext
                    cases next with
                    | nil =>
                        simp only [hnext, hnext₂, Option.bind_some] at computed ⊢
                        simp at computed ⊢
                        exact computed
                    | cons head tail =>
                        have recursive :
                            FrameRuntime.compareRule? mol profile authoritative before₁ rule
                              fuel (head :: tail) = some output := by
                          simpa [hlabels, hnext, Option.bind_some] using computed
                        have refined :
                            FrameRuntime.compareRule? mol profile authoritative before₂ rule
                              fuel (head :: tail) = some output :=
                          ih (head :: tail) output recursive
                        simpa [hlabels, hnext₂, Option.bind_some] using refined

/-- `compareRule?` at fuel `n + 1` refines its own result at fuel `n` with the same `before`
comparator.  This is the fuel half of the one-step propagation; the `before` comparator is held
fixed, so no sorting behaviour is assumed. -/
theorem compareRule?_fuel_refines
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (rule : CanonicalRuleStage) :
    ∀ (fuel : Nat) (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor)),
      SuccessRefines
        (FrameRuntime.compareRule? mol profile authoritative before rule fuel pairs)
        (FrameRuntime.compareRule? mol profile authoritative before rule (Nat.succ fuel) pairs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs output computed
      rw [FrameRuntime.compareRule?] at computed
      rw [FrameRuntime.compareRule?]
      by_cases hcap : (!authoritative && RawMolecule.defaultBranchWidthCap <
          pairs.length) = true
      · rw [if_pos hcap] at computed ⊢
        simp at computed
      · rw [if_neg hcap] at computed ⊢
        cases hlabels : FrameRuntime.pairLabels? mol profile authoritative rule pairs with
        | none =>
            simp only [hlabels, Option.bind_none] at computed
            simp at computed
        | some cmp =>
            simp only [hlabels, Option.bind_some] at computed ⊢
            cases cmp with
            | lt =>
                simp at computed ⊢
                exact computed
            | gt =>
                simp at computed ⊢
                exact computed
            | eq =>
                cases hnext : FrameRuntime.nextPairs? mol profile authoritative before pairs with
                | none =>
                    simp only [hnext, Option.bind_none] at computed
                    simp at computed
                | some next =>
                    cases next with
                    | nil =>
                        simp only [hnext, Option.bind_some] at computed ⊢
                        simp at computed ⊢
                        exact computed
                    | cons head tail =>
                        simp only [hnext, Option.bind_some] at computed
                        simp at computed
  | succ fuel ih =>
      intro pairs output computed
      rw [FrameRuntime.compareRule?] at computed
      rw [FrameRuntime.compareRule?]
      by_cases hcap : (!authoritative && RawMolecule.defaultBranchWidthCap <
          pairs.length) = true
      · rw [if_pos hcap] at computed ⊢
        simp at computed
      · rw [if_neg hcap] at computed ⊢
        cases hlabels : FrameRuntime.pairLabels? mol profile authoritative rule pairs with
        | none =>
            simp only [hlabels, Option.bind_none] at computed
            simp at computed
        | some cmp =>
            simp only [hlabels, Option.bind_some] at computed ⊢
            cases cmp with
            | lt =>
                simp at computed ⊢
                exact computed
            | gt =>
                simp at computed ⊢
                exact computed
            | eq =>
                cases hnext : FrameRuntime.nextPairs? mol profile authoritative before pairs with
                | none =>
                    simp only [hnext, Option.bind_none] at computed
                    simp at computed
                | some next =>
                    cases next with
                    | nil =>
                        simp only [hnext, Option.bind_some] at computed ⊢
                        simp at computed ⊢
                        exact computed
                    | cons head tail =>
                        have recursive :
                            FrameRuntime.compareRule? mol profile authoritative before rule
                              fuel (head :: tail) = some output := by
                          simpa [hlabels, hnext, Option.bind_some] using computed
                        have refined :
                            FrameRuntime.compareRule? mol profile authoritative before rule
                              (Nat.succ fuel) (head :: tail) = some output :=
                          ih (head :: tail) output recursive
                        simpa [hlabels, hnext, Option.bind_some] using refined

/-! ## The branch schedule and one-step propagation -/

/-- The exact rule schedule of the successor-fuel case of `FrameRuntime.compareBranch?`, written as
an explicit bind chain so that refinement can be applied rule by rule. -/
private def schedule? (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (fuel : Nat) (stage : CanonicalRuleStage) (left right : FrameRuntime.Cursor) :
    Option Ordering :=
  (FrameRuntime.compareRule? mol profile authoritative before CanonicalRuleStage.rule1a fuel
      [(left, right)]) >>= fun first =>
    if first != Ordering.eq || stage == CanonicalRuleStage.rule1a then some first else
    (FrameRuntime.compareRule? mol profile authoritative before CanonicalRuleStage.rule1b fuel
        [(left, right)]) >>= fun distance =>
      if distance != Ordering.eq || stage == CanonicalRuleStage.rule1b then some distance else
      FrameRuntime.compareRule? mol profile authoritative before CanonicalRuleStage.rule2 fuel
        [(left, right)]

/-- The runtime schedule is definitionally the explicit chain of `schedule?`. -/
private theorem compareBranch?_succ_eq (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage)
    (left right : FrameRuntime.Cursor) :
    FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage left right =
      schedule? mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage) (Nat.succ fuel)
        stage left right := rfl

/-- One-step propagation for a fixed stage: if every supported pair refines from fuel `f` to
`f + 1`, then every pair (supported or not) refines from `f + 1` to `f + 2`.  The three scheduled
rules are refined with the `before` refinement supplied by `step` at the lower fuel, while the
fuel itself is refined by `compareRule?_fuel_refines`. -/
theorem compareBranch?_refines_succ
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (fuel : Nat)
    (step : ∀ left right,
      SuccessRefines
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage left right)
        (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage left right)) :
    ∀ left right,
      SuccessRefines
        (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage left right)
        (FrameRuntime.compareBranch? mol profile authoritative
          (Nat.succ (Nat.succ fuel)) stage left right) := by
  intro left right
  rw [compareBranch?_succ_eq]
  rw [compareBranch?_succ_eq]
  simp only [schedule?]
  apply SuccessRefines.bind
  · exact SuccessRefines.trans
      (compareRule?_refines mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
        (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage)
        step CanonicalRuleStage.rule1a (Nat.succ fuel) [(left, right)])
      (compareRule?_fuel_refines mol profile authoritative
        (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage)
        CanonicalRuleStage.rule1a (Nat.succ fuel) [(left, right)])
  · intro first
    by_cases hfirst :
        (first != Ordering.eq || stage == CanonicalRuleStage.rule1a) = true
    · simp only [if_pos hfirst]
      exact SuccessRefines.refl _
    · simp only [if_neg hfirst]
      apply SuccessRefines.bind
      · exact SuccessRefines.trans
          (compareRule?_refines mol profile authoritative
            (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
            (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage)
            step CanonicalRuleStage.rule1b (Nat.succ fuel) [(left, right)])
          (compareRule?_fuel_refines mol profile authoritative
            (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage)
            CanonicalRuleStage.rule1b (Nat.succ fuel) [(left, right)])
      · intro distance
        by_cases hdistance :
            (distance != Ordering.eq || stage == CanonicalRuleStage.rule1b) = true
        · simp only [if_pos hdistance]
          exact SuccessRefines.refl _
        · simp only [if_neg hdistance]
          exact SuccessRefines.trans
            (compareRule?_refines mol profile authoritative
              (FrameRuntime.compareBranch? mol profile authoritative fuel stage)
              (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage)
              step CanonicalRuleStage.rule2 (Nat.succ fuel) [(left, right)])
            (compareRule?_fuel_refines mol profile authoritative
              (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage)
              CanonicalRuleStage.rule2 (Nat.succ fuel) [(left, right)])

/-! ## The supported-frame refinement hypothesis -/

/-- Pointwise one-step refinement over all cursor pairs. -/
def AllCursorRefinesAt (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (fuel : Nat) : Prop :=
  ∀ left right,
    SuccessRefines
      (FrameRuntime.compareBranch? mol profile authoritative fuel stage left right)
      (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage left right)

/-- Pointwise one-step refinement restricted to cursors that the shared profile actually supports.
This is the only support hypothesis used by the stability theorem. -/
def SupportedRefinesAt (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (fuel : Nat) : Prop :=
  ∀ left right,
    CursorSupported mol profile left → CursorSupported mol profile right →
    SuccessRefines
      (FrameRuntime.compareBranch? mol profile authoritative fuel stage left right)
      (FrameRuntime.compareBranch? mol profile authoritative (Nat.succ fuel) stage left right)

/-- Unsupported cursor pairs refuse at every fuel, so a supported-pair refinement extends to all
cursor pairs without any further hypothesis. -/
theorem allCursorRefinesAt_of_supported (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (fuel : Nat)
    (supported : SupportedRefinesAt mol profile authoritative stage fuel) :
    AllCursorRefinesAt mol profile authoritative stage fuel := by
  intro left right value computed
  by_cases hleft : CursorSupported mol profile left
  · by_cases hright : CursorSupported mol profile right
    · exact supported left right hleft hright value computed
    · rw [compareBranch?_eq_none_of_cursor?_right mol profile authoritative fuel stage
        (cursor?_eq_none_of_not_supported mol profile right hright)] at computed
      simp at computed
  · rw [compareBranch?_eq_none_of_cursor?_left mol profile authoritative fuel stage
      (cursor?_eq_none_of_not_supported mol profile left hleft)] at computed
    simp at computed

/-- A single supported one-step check propagates one fuel step. -/
theorem supportedRefinesAt_succ (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (fuel : Nat)
    (supported : SupportedRefinesAt mol profile authoritative stage fuel) :
    SupportedRefinesAt mol profile authoritative stage (Nat.succ fuel) := by
  intro left right _ _
  exact compareBranch?_refines_succ mol profile authoritative stage fuel
    (allCursorRefinesAt_of_supported mol profile authoritative stage fuel supported)
    left right

/-- Iterating the one-step propagation: the supported refinement holds at fuel `f + count` for
every count. -/
theorem supportedRefinesAt_add (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (stage : CanonicalRuleStage) (fuel : Nat)
    (supported : SupportedRefinesAt mol profile authoritative stage fuel) :
    ∀ count : Nat, SupportedRefinesAt mol profile authoritative stage (fuel + count) := by
  intro count
  induction count with
  | zero => simpa using supported
  | succ count ih =>
      have step := supportedRefinesAt_succ mol profile authoritative stage (fuel + count) ih
      simpa using step

/-! ## Success stability -/

/-- **Main theorem.**  If the actual framed comparator refines from fuel `fuel` to `fuel + 1` on
every pair of cursors supported by the resolved shared profile, then every successful
`FrameRuntime.compareBranch?` result at `fuel` is reproduced, with the same ordering, at every
larger fuel and for every stage. -/
theorem compareBranch?_success_stable
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (fuel : Nat)
    (supported : SupportedRefinesAt mol profile authoritative stage fuel)
    {left right : FrameRuntime.Cursor} {decision : Ordering}
    (computed : FrameRuntime.compareBranch? mol profile authoritative fuel stage left right =
      some decision)
    {highFuel : Nat} (le : fuel ≤ highFuel) :
    FrameRuntime.compareBranch? mol profile authoritative highFuel stage left right =
      some decision := by
  obtain ⟨count, rfl⟩ := Nat.le.dest le
  have allAt : ∀ count, AllCursorRefinesAt mol profile authoritative stage (fuel + count) :=
    fun count => allCursorRefinesAt_of_supported mol profile authoritative stage (fuel + count)
      (supportedRefinesAt_add mol profile authoritative stage fuel supported count)
  have chain : ∀ count, SuccessRefines
      (FrameRuntime.compareBranch? mol profile authoritative fuel stage left right)
      (FrameRuntime.compareBranch? mol profile authoritative (fuel + count) stage left right) := by
    intro count
    induction count with
    | zero => exact SuccessRefines.refl _
    | succ count ih =>
        exact SuccessRefines.trans ih (allAt count left right)
  exact chain count decision computed

/-- Contrapositive form of success stability: a refusal at the larger fuel forces a refusal at the
smaller fuel.  Refusals at the smaller fuel may still become successes. -/
theorem compareBranch?_eq_none_of_larger_eq_none
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (fuel : Nat)
    (supported : SupportedRefinesAt mol profile authoritative stage fuel)
    {left right : FrameRuntime.Cursor} {highFuel : Nat} (le : fuel ≤ highFuel)
    (computed : FrameRuntime.compareBranch? mol profile authoritative highFuel stage left right =
      none) :
    FrameRuntime.compareBranch? mol profile authoritative fuel stage left right = none := by
  cases low : FrameRuntime.compareBranch? mol profile authoritative fuel stage left right with
  | none => rfl
  | some value =>
      have highSome := compareBranch?_success_stable mol profile authoritative stage fuel
        supported low le
      rw [highSome] at computed
      simp at computed

/-- Sufficient-fuel form: once the actual comparator's supported one-step refinement holds at some
threshold fuel, every successful comparison at any fuel at or above the threshold is reproduced,
with the same ordering, at every larger fuel.  Nothing is claimed at smaller fuels: in particular
no zero-fuel success is asserted to be stable. -/
theorem compareBranch?_success_stable_of_threshold
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (threshold : Nat)
    (resolved : ∀ fuel, threshold ≤ fuel →
      SupportedRefinesAt mol profile authoritative stage fuel)
    {fuel highFuel : Nat} (thresholdLe : threshold ≤ fuel) (le : fuel ≤ highFuel)
    {left right : FrameRuntime.Cursor} {decision : Ordering}
    (computed : FrameRuntime.compareBranch? mol profile authoritative fuel stage left right =
      some decision) :
    FrameRuntime.compareBranch? mol profile authoritative highFuel stage left right =
      some decision :=
  compareBranch?_success_stable mol profile authoritative stage fuel
    (resolved fuel thresholdLe) computed le

/-! ## Transport over the actual root frame -/

/-- The declarative constitutional separation of the actual `occurrenceLigandFrame?` roots is stable
under larger fuel: every strict `compareBranch?` witness over the real root cursors survives, so the
predicate `RootsConstitutionallySeparated` holds at every larger fuel. -/
theorem rootsConstitutionallySeparated_mono
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : Nat)
    (roots : List CanonicalRerootCursor)
    (supported : SupportedRefinesAt mol profile true CanonicalRuleStage.rule2 fuel)
    (separated : RawFramedConstitutionalIndependence.RootsConstitutionallySeparated
      mol profile fuel roots)
    {highFuel : Nat} (le : fuel ≤ highFuel) :
    RawFramedConstitutionalIndependence.RootsConstitutionallySeparated
      mol profile highFuel roots := by
  refine ⟨separated.1, ?_⟩
  intro left hleft right hright distinct
  obtain ⟨order, strict, computed⟩ := separated.2 left hleft right hright distinct
  exact ⟨order, strict, compareBranch?_success_stable mol profile true
    CanonicalRuleStage.rule2 fuel supported computed le⟩

/-! ## Kernel-authority guards -/

assert_kernel_only pairLabels?_singleton_eq_label?
assert_kernel_only compareRule?_singleton_of_label?_strict
assert_kernel_only compareRule?_singleton_terminal
assert_kernel_only compareBranch?_eq_of_rule1a_label?_strict
assert_kernel_only compareBranch?_eq_throughLabels?_of_terminal
assert_kernel_only compareBranch?_success_stable_of_terminal
assert_kernel_only compareBranch?_eq_none_of_cursor?_left
assert_kernel_only compareBranch?_eq_none_of_cursor?_right
assert_kernel_only insert?_refines
assert_kernel_only sort?_refines
assert_kernel_only ranked?_refines
assert_kernel_only nextPairs?_refines
assert_kernel_only compareRule?_refines
assert_kernel_only compareRule?_fuel_refines
assert_kernel_only compareBranch?_refines_succ
assert_kernel_only allCursorRefinesAt_of_supported
assert_kernel_only supportedRefinesAt_succ
assert_kernel_only supportedRefinesAt_add
assert_kernel_only compareBranch?_success_stable
assert_kernel_only compareBranch?_eq_none_of_larger_eq_none
assert_kernel_only compareBranch?_success_stable_of_threshold
assert_kernel_only rootsConstitutionallySeparated_mono

end RawFramedConstitutionalFuelStability
end OneCenter
end TetraStereo
