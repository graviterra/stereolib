import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleChildren
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-! The actual ordinary comparator with the proven finite child reader substituted. This
representation is intended for kernel evaluation; it changes no ranking or reference policy. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCompiler

open CertifiedLocalizedCIPInput LocalizedChemicalRingCyclicExampleInput
open LocalizedChemicalRingCyclicExampleChildren
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedRetainedStateReader

def cumulative (stage : LocalizedCumulativeRule45Stage)
    (read : Cursor → Option LocalizedAuxiliaryLabel) :
    Nat → Cursor → Option certified.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← readChildren cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey certified stage cursor (read cursor))
      else none
  | fuel + 1, cursor => do
      let children ← readChildren cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey certified stage cursor (read cursor))
      else
        let keys ← children.mapM (cumulative stage read fuel)
        some (localizedCumulativeRule45StepKey certified stage cursor (read cursor)
          (certified.sortRuleMajorCumulativeKeys stage keys))

theorem cumulative_eq (stage : LocalizedCumulativeRule45Stage)
    (read : Cursor → Option LocalizedAuxiliaryLabel) (fuel : Nat) :
    cumulative stage read fuel = certified.buildRuleMajorCumulativeWithReadExec? stage read fuel := by
  induction fuel with
  | zero => funext cursor; simp [cumulative, buildRuleMajorCumulativeWithReadExec?, readChildren_eq]
  | succ fuel ih =>
      funext cursor
      simp [cumulative, buildRuleMajorCumulativeWithReadExec?, readChildren_eq, ih]

def stageCompiler (target : Occ) (view : certified.LocalizedDependencyView target)
    (read : Cursor → Option LocalizedAuxiliaryLabel) (fuel : Nat) :
    certified.RuleMajorCompoundStageCompiler 10 :=
  fun stage cursor => match stage with
    | .rule4a => WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
        certified readChildren .rule4a target view fuel cursor
    | other => cumulative other read fuel cursor

theorem stageCompiler_eq (target : Occ) (view : certified.LocalizedDependencyView target)
    (read : Cursor → Option LocalizedAuxiliaryLabel) (fuel : Nat) :
    stageCompiler target view read fuel =
      certified.ruleMajorCompoundStageCompilerExec target view read fuel := by
  funext stage cursor
  cases stage <;> simp only [stageCompiler, ruleMajorCompoundStageCompilerExec, cumulative_eq,
    WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?_eq_original
      certified readChildren readChildren_eq]

def compound (target : Occ) (view : certified.LocalizedDependencyView target)
    (fuel : Nat) (cursor : Cursor) : Option certified.LocalizedRerootCompoundRule45Key :=
  certified.buildRuleMajorCompoundRule45KeyWith?
    (stageCompiler target view (certified.localizedDependencyLabel target view) fuel) cursor

theorem compound_eq (target : Occ) (view : certified.LocalizedDependencyView target)
    (fuel : Nat) (cursor : Cursor) : compound target view fuel cursor =
    certified.buildActualRuleMajorCompoundRule45KeyExec? target view fuel cursor := by
  unfold compound buildActualRuleMajorCompoundRule45KeyExec? buildRuleMajorCompoundRule45KeyExec?
  rw [stageCompiler_eq]

def frame (target : Occ) : Option (certified.LocalizedOccurrenceFourLigandFrame 10) :=
  WithChildren.localizedNoDoubleFourLigandFrameExec? certified readChildren target

theorem frame_eq (target : Occ) : frame target = certified.localizedNoDoubleFourLigandFrameExec? target :=
  WithChildren.localizedNoDoubleFourLigandFrameExec?_eq_original certified readChildren readChildren_eq target

def before (state : OccurrenceAuxState) (target : Occ)
    (base : certified.LocalizedOccurrenceFourLigandFrame 10) (left right : Fin 4) : Option Ordering :=
  (do
    let budget := localizedOccurrenceRerootEvaluationFuel 10
    let leftKey ← compound target (rawStateView certified state target) budget (base.cursorAt left)
    let rightKey ← compound target (rawStateView certified state target) budget (base.cursorAt right)
    some (localizedOccurrenceRule45ComparisonRecord
      (certified.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))).map
    ConstitutionalDescriptorHierarchyComparison.ordering

theorem before_eq (state : OccurrenceAuxState) (target : Occ)
    (base : certified.LocalizedOccurrenceFourLigandFrame 10) :
    before state target base = rawStateBefore certified state target base := by
  funext left right
  unfold before rawStateBefore compareRuleMajorOccurrenceExecAt?
  simp only [compound_eq]
  rfl

def partition (state : OccurrenceAuxState) (target : Occ) :
    Option (List (Fin 4) × List (Option Ordering)) := do
  let base ← frame target
  let sorted ← sortBy? (before state target base) (List.finRange 4)
  some (sorted, adjacentBy (before state target base) sorted)

theorem partition_eq (state : OccurrenceAuxState) (target : Occ) :
    partition state target = ordinaryPartition? certified state target := by
  unfold partition ordinaryPartition?
  simp only [frame_eq, before_eq]
  rfl

def ordinary (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    Option (List Nat × List (Option Ordering)) := do
  let target ← lookup node
  let atoms ← LocalizedGenericMarkedRecalculation.frameAtoms? mol node
  let base ← frame target
  let ranked ← partition state target
  let positions ← positions? certified atoms base ranked.1
  some (positions, ranked.2)

theorem ordinary_eq (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    ordinary state node = ops.ordinary state node := by
  change ordinary state node = LocalizedMarkedRetainedOperations.ordinary certified mol state node
  unfold ordinary LocalizedMarkedRetainedOperations.ordinary
  simp only [lookup_eq, frame_eq, partition_eq]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCompiler

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCompiler.cumulative_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCompiler.compound_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCompiler.ordinary_eq
