import TetraStereo.OneCenter.LocalizedRerootCarrierCache
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundBuilder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Carrier sharing for the whole-rule builder

Use one certified occurrence cache across whole-rule stages. The cache preserves the original
ordered child lists; the recursive sibling sort remains the whole-rule sort. Exact equality with
the existing executable builder includes failure and requires no assumptions about the molecular
domain, auxiliary reader, reference count or successful sorting.

The compound entry point retains the original Rule-4a stage and the same dependency reader for
later stages, exactly as `buildActualRuleMajorCompoundRule45KeyExec?` does. This changes execution
cost only; it neither equates the older node-major builder with this one nor establishes new
chemical correctness.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootCarrierCache

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- The existing whole-rule recurrence with a shared certified carrier. -/
def ruleMajorCumulative? (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← cache.readChildren cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
      else none
  | fuel + 1, cursor => do
      let children ← cache.readChildren cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
      else
        let keys ← children.mapM (cache.ruleMajorCumulative? stage read fuel)
        some (localizedCumulativeRule45StepKey input stage cursor (read cursor)
          (input.sortRuleMajorCumulativeKeys stage keys))

theorem ruleMajorCumulative_eq
    (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel cursor, cache.ruleMajorCumulative? stage read fuel cursor =
      input.buildRuleMajorCumulativeWithReadExec? stage read fuel cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor
      simp only [ruleMajorCumulative?, buildRuleMajorCumulativeWithReadExec?,
        cache.readChildren_eq]
  | succ fuel ih =>
      intro cursor
      have recEq : cache.ruleMajorCumulative? stage read fuel =
          input.buildRuleMajorCumulativeWithReadExec? stage read fuel := funext ih
      simp only [ruleMajorCumulative?, buildRuleMajorCumulativeWithReadExec?,
        cache.readChildren_eq, recEq]

/-- Preserve the actual compound entry point's original Rule-4a callback. -/
def ruleMajorStageCompiler (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) : input.RuleMajorCompoundStageCompiler carrierFuel :=
  fun stage cursor => match stage with
    | .rule4a => WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
        input cache.readChildren .rule4a target view fuel cursor
    | other => cache.ruleMajorCumulative? other
        (input.localizedDependencyLabel target view) fuel cursor

theorem ruleMajorStageCompiler_eq
    (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    cache.ruleMajorStageCompiler target view fuel stage cursor =
      input.ruleMajorCompoundStageCompilerExec target view
        (input.localizedDependencyLabel target view) fuel stage cursor := by
  cases stage <;>
    simp only [ruleMajorStageCompiler, CertifiedLocalizedCIPInput.ruleMajorCompoundStageCompilerExec,
      cache.cumulative_eq, cache.ruleMajorCumulative_eq]

/-- The complete actual whole-rule key using one cache for every cumulative stage. -/
def actualRuleMajorCompound45? (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key :=
  input.buildRuleMajorCompoundRule45KeyWith?
    (cache.ruleMajorStageCompiler target view fuel) cursor

theorem actualRuleMajorCompound45_eq
    (cache : input.LocalizedRerootCarrierCache carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    cache.actualRuleMajorCompound45? target view fuel cursor =
      input.buildActualRuleMajorCompoundRule45KeyExec? target view fuel cursor := by
  apply input.buildRuleMajorCompoundRule45KeyWith?_eq
  intro stage
  exact cache.ruleMajorStageCompiler_eq target view fuel stage cursor

assert_kernel_only ruleMajorCumulative_eq
assert_kernel_only ruleMajorStageCompiler_eq
assert_kernel_only actualRuleMajorCompound45_eq

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootCarrierCache
