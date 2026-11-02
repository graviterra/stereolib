import TetraStereo.OneCenter.LocalizedRerootRule5Relabel
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Executable

set_option autoImplicit false

/-!
# Reuse Rule-4c keys when constructing Rule-5 readings

For a selected Rule-4b reference, the existing relabeling theorem determines both common-reference
Rule-5 keys from one Rule-4c key. The executable builder below therefore expands that hierarchy
once, rather than once for each common reference. Its equality theorem covers arbitrary inputs,
views, fuel, cursors and prior records, including failure. With a certificate for an already
computed Rule-4c key, the stronger reuse theorem removes this expansion too.

The empty-reference case retains the two existing executable stage builds. No rule, sibling order,
reference selection, descriptor meaning or production definition changes here.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-- Assemble the two common-reference keys by relabeling a Rule-4c key. -/
def rule5ReadingFromRule4c
    (prior : input.LocalizedRerootRule4bcReading) (reference : RS)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    input.LocalizedRerootRule5Reading :=
  { prior := prior
    commonR := input.rule5LiftKey (.R == reference) key
    commonS := input.rule5LiftKey (.S == reference) key }

/-- Executable relabeling equality, including the exhausted-fuel case. -/
theorem buildLocalizedRerootCumulativeRule45KeyExec?_rule5
    {carrierFuel : Nat} (reference common : RS)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCumulativeRule45KeyExec?
        (.rule5 reference common) target view fuel cursor =
      (input.buildLocalizedRerootCumulativeRule45KeyExec?
        (.rule4c reference) target view fuel cursor).map
          (input.rule5LiftKey (common == reference)) := by
  rw [input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build,
    input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build]
  exact input.buildLocalizedRerootCumulativeRule45Key?_rule5
    reference common target view fuel cursor

/-- Share the Rule-4c expansion when a reference is selected. Without a reference, use the
original two stages, since their sort is not covered by the selected-reference relabeling law. -/
def buildLocalizedRerootRule5ReadingShared?
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    Option input.LocalizedRerootRule5Reading :=
  match prior.reference? with
  | some reference => do
      let key ← input.buildLocalizedRerootCumulativeRule45KeyExec?
        (.rule4c reference) target view fuel cursor
      some (input.rule5ReadingFromRule4c prior reference key)
  | none => do
      let commonR ← input.buildLocalizedRerootCumulativeRule45KeyExec?
        (.rule5NoRule4bReference .R) target view fuel cursor
      let commonS ← input.buildLocalizedRerootCumulativeRule45KeyExec?
        (.rule5NoRule4bReference .S) target view fuel cursor
      some { prior := prior, commonR := commonR, commonS := commonS }

/-- Sharing is exactly the existing production reading builder for every input, including
invalid or exhausted prior records. No successful-build premise is required. -/
theorem buildLocalizedRerootRule5ReadingShared?_eq_build
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    input.buildLocalizedRerootRule5ReadingShared? target view fuel cursor prior =
      input.buildLocalizedRerootRule5Reading? target view fuel cursor prior := by
  unfold buildLocalizedRerootRule5ReadingShared? buildLocalizedRerootRule5Reading?
  cases selected : prior.reference? with
  | none =>
      simp only [localizedRule5StageFor]
      rw [input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build,
        input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build]
  | some reference =>
      simp only [localizedRule5StageFor]
      rw [input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build,
        input.buildLocalizedRerootCumulativeRule45Key?_rule5,
        input.buildLocalizedRerootCumulativeRule45Key?_rule5]
      cases input.buildLocalizedRerootCumulativeRule45Key?
        (.rule4c reference) target view fuel cursor <;> rfl

/-- A caller already holding the successful Rule-4c key needs no further hierarchy expansion. -/
theorem buildLocalizedRerootRule5Reading?_eq_reuse
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) (reference : RS)
    (selected : prior.reference? = some reference)
    (built : input.buildLocalizedRerootCumulativeRule45KeyExec?
      (.rule4c reference) target view fuel cursor = some prior.rule4cKey) :
    input.buildLocalizedRerootRule5Reading? target view fuel cursor prior =
      some (input.rule5ReadingFromRule4c prior reference prior.rule4cKey) := by
  rw [← input.buildLocalizedRerootRule5ReadingShared?_eq_build]
  simp only [buildLocalizedRerootRule5ReadingShared?, selected, built]
  rfl

/-- The shared executable builder retains the existing declarative reading derivation. -/
theorem buildLocalizedRerootRule5ReadingShared?_sound
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5ReadingShared?
      target view fuel cursor prior = some reading) :
    input.DeclarativeLocalizedRerootRule5Reading target view fuel cursor prior reading := by
  rw [input.buildLocalizedRerootRule5ReadingShared?_eq_build] at computed
  exact input.buildLocalizedRerootRule5Reading?_sound target view fuel cursor prior reading computed

assert_kernel_only buildLocalizedRerootCumulativeRule45KeyExec?_rule5
assert_kernel_only buildLocalizedRerootRule5ReadingShared?_eq_build
assert_kernel_only buildLocalizedRerootRule5Reading?_eq_reuse
assert_kernel_only buildLocalizedRerootRule5ReadingShared?_sound

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
