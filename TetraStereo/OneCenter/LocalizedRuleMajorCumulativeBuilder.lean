import TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Executable
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Whole-rule cumulative sorting over actual occurrence expansion. The root observations,
expansion, constitutional assembly and table merges are the existing implementation. The changed
operation compares each earlier rule over the entire hierarchy before consulting a later rule.
Build availability is derived for every callback and adequate cursor budget; no physical rigidity
or assumption about successful sorting is used. -/

namespace TetraStereo.OneCenter
open CertifiedLocalizedCIPInput

namespace CertifiedLocalizedCIPInput

def ruleMajorStageWidth (stage : LocalizedCumulativeRule45Stage) : Nat :=
  (localizedCumulativeRule45Priority stage none).length

def sortRuleMajorCumulativeKeys (input : CertifiedLocalizedCIPInput)
    (stage : LocalizedCumulativeRule45Stage) :
    List input.LocalizedRerootCumulativeRule45Key → List input.LocalizedRerootCumulativeRule45Key :=
  sortKeysBy (input.compareRuleMajorCumulativeDescriptor (ruleMajorStageWidth stage))

noncomputable def buildRuleMajorCumulativeWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    Nat → input.LocalizedRerootCursor carrierFuel → Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← input.localizedRerootChildren? cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
      else none
  | fuel + 1, cursor => do
      let children ← input.localizedRerootChildren? cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
      else
        let keys ← children.mapM (input.buildRuleMajorCumulativeWithRead? stage read fuel)
        some (localizedCumulativeRule45StepKey input stage cursor (read cursor)
          (input.sortRuleMajorCumulativeKeys stage keys))

/-- The same construction over the certified executable child enumerator. -/
def buildRuleMajorCumulativeWithReadExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    Nat → input.LocalizedRerootCursor carrierFuel → Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
      else none
  | fuel + 1, cursor => do
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
      else
        let keys ← children.mapM (input.buildRuleMajorCumulativeWithReadExec? stage read fuel)
        some (localizedCumulativeRule45StepKey input stage cursor (read cursor)
          (input.sortRuleMajorCumulativeKeys stage keys))

private theorem mapM_same_availability {α β γ : Type*} (f : α → Option β) (g : α → Option γ)
    (same : ∀ x, (f x).isSome = (g x).isSome) :
    ∀ xs : List α, (xs.mapM f).isSome = (xs.mapM g).isSome
  | [] => rfl
  | x :: xs => by
      have head := same x
      have tail := mapM_same_availability f g same xs
      cases hf : f x <;> cases hg : g x <;>
        simp [List.mapM_cons, hf, hg] at head ⊢
      cases htf : xs.mapM f <;> cases htg : xs.mapM g <;>
        simp [htf, htg] at tail ⊢

private theorem mapM_same_values {α β : Type*} (f g : α → Option β)
    (same : ∀ x, f x = g x) : ∀ xs : List α, xs.mapM f = xs.mapM g
  | [] => rfl
  | x :: xs => by simp [List.mapM_cons, same x, mapM_same_values f g same xs]

/-- Replacing sibling ordering cannot introduce an expansion or budget failure. -/
theorem buildRuleMajorCumulativeWithRead_isSome_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel cursor,
      (input.buildRuleMajorCumulativeWithRead? stage read fuel cursor).isSome =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor).isSome
  | 0, cursor => by
      unfold buildRuleMajorCumulativeWithRead? buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases h : input.localizedRerootChildren? cursor <;> simp
  | fuel + 1, cursor => by
      unfold buildRuleMajorCumulativeWithRead? buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases h : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          by_cases empty : children = []
          · simp [empty]
          · have available := mapM_same_availability
              (input.buildRuleMajorCumulativeWithRead? stage read fuel)
              (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel)
              (buildRuleMajorCumulativeWithRead_isSome_eq input stage read fuel) children
            cases hm : children.mapM (input.buildRuleMajorCumulativeWithRead? stage read fuel) <;>
              cases ho : children.mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel) <;>
              simp [empty, hm, ho] at available ⊢

/-- The executable builder implements exactly the proof-facing recurrence. -/
theorem buildRuleMajorCumulativeWithReadExec_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel cursor,
      input.buildRuleMajorCumulativeWithReadExec? stage read fuel cursor =
        input.buildRuleMajorCumulativeWithRead? stage read fuel cursor
  | 0, cursor => by
      unfold buildRuleMajorCumulativeWithReadExec? buildRuleMajorCumulativeWithRead?
      rw [input.executableLocalizedRerootChildren?_eq_localizedRerootChildren]
  | fuel + 1, cursor => by
      unfold buildRuleMajorCumulativeWithReadExec? buildRuleMajorCumulativeWithRead?
      rw [input.executableLocalizedRerootChildren?_eq_localizedRerootChildren]
      cases h : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          have mapped := mapM_same_values
            (input.buildRuleMajorCumulativeWithReadExec? stage read fuel)
            (input.buildRuleMajorCumulativeWithRead? stage read fuel)
            (buildRuleMajorCumulativeWithReadExec_eq input stage read fuel) children
          by_cases empty : children = [] <;> simp [empty, mapped]

theorem exists_buildRuleMajorCumulativeWithRead_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildRuleMajorCumulativeWithRead? stage read
      (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨old, built⟩ :=
    WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input stage read cursor valid
  have available := input.buildRuleMajorCumulativeWithRead_isSome_eq stage read
    (2 * (carrierFuel + 1)) cursor
  rw [built] at available
  cases h : input.buildRuleMajorCumulativeWithRead? stage read (2 * (carrierFuel + 1)) cursor with
  | none => simp [h] at available
  | some key => exact ⟨key, rfl⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead_isSome_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithReadExec_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildRuleMajorCumulativeWithRead_at_twice
