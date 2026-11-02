import TetraStereo.OneCenter.LocalizedRetainedContextStageGraphIso
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Saturation of successful rule-major builds and traces

Once an actual cumulative build succeeds, increasing its fuel preserves the complete key and
its exact decorated-tree trace. Thus recursive subtrees built at decreasing budgets can be
compared with fixed adequate-budget reconstructions without assuming their fuels agree.
The cross-fuel isomorphism below preserves erased rooted graphs and occurrence labels; it does
not identify different readers' auxiliary labels or assert chemical meaning.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree Rule4aTableBridge DeclarativeCIP

private theorem mapM_transfer {α β : Type} (f g : α → Option β)
    (transfer : ∀ x y, f x = some y → g x = some y) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.mapM g = some ys
  | [], ys, built => by simpa using built
  | x :: xs, ys, built => by
      cases hx : f x with
      | none => simp [List.mapM_cons, hx] at built
      | some y =>
          cases hxs : xs.mapM f with
          | none => simp [List.mapM_cons, hx, hxs] at built
          | some tail =>
              have head := transfer x y hx
              have rest := mapM_transfer f g transfer xs tail hxs
              simpa [List.mapM_cons, head, rest] using
                (show some (y :: tail) = some ys by simpa [List.mapM_cons, hx, hxs] using built)

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
  (stage : LocalizedCumulativeRule45Stage)
  (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)

/-- Success implies the same key at every larger evaluation budget. No validity hypothesis is
needed: the successful expansion itself certifies that no budget truncation occurred. -/
theorem build_mono :
    ∀ fuel more, fuel ≤ more → ∀ cursor key,
      input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key →
      input.buildRuleMajorCumulativeWithRead? stage read more cursor = some key := by
  intro fuel
  induction fuel with
  | zero =>
      intro more _ cursor key built
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => simp [buildRuleMajorCumulativeWithRead?, childrenEq] at built
      | some children =>
          by_cases empty : children = []
          · cases more <;> simpa [buildRuleMajorCumulativeWithRead?, childrenEq, empty] using built
          · simp [buildRuleMajorCumulativeWithRead?, childrenEq, empty] at built
  | succ fuel ih =>
      intro more bound cursor key built
      cases more with
      | zero => omega
      | succ more =>
          cases childrenEq : input.localizedRerootChildren? cursor with
          | none => simp [buildRuleMajorCumulativeWithRead?, childrenEq] at built
          | some children =>
              by_cases empty : children = []
              · simpa [buildRuleMajorCumulativeWithRead?, childrenEq, empty] using built
              · cases keysEq : children.mapM
                    (input.buildRuleMajorCumulativeWithRead? stage read fuel) with
                | none => simp [buildRuleMajorCumulativeWithRead?, childrenEq, empty, keysEq] at built
                | some keys =>
                    have lifted := mapM_transfer
                      (input.buildRuleMajorCumulativeWithRead? stage read fuel)
                      (input.buildRuleMajorCumulativeWithRead? stage read more)
                      (fun child childKey computed => ih more (by omega) child childKey computed)
                      children keys keysEq
                    simpa [buildRuleMajorCumulativeWithRead?, childrenEq, empty, keysEq, lifted]
                      using built

/-- Executable counterpart, preserving the actual key byte for byte. -/
theorem buildExec_mono (fuel more : Nat) (bound : fuel ≤ more)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (built : input.buildRuleMajorCumulativeWithReadExec? stage read fuel cursor = some key) :
    input.buildRuleMajorCumulativeWithReadExec? stage read more cursor = some key := by
  rw [input.buildRuleMajorCumulativeWithReadExec_eq] at built ⊢
  exact build_mono input stage read fuel more bound cursor key built

/-- Every trace lifts with precisely the same decorated tree, keys and sibling sort. -/
theorem trace_mono :
    ∀ fuel more, fuel ≤ more →
      ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
        (key : input.LocalizedRerootCumulativeRule45Key),
        LocalizedRuleMajorSortTrace input stage read fuel tree key →
        LocalizedRuleMajorSortTrace input stage read more tree key := by
  intro fuel
  induction fuel with
  | zero =>
      intro more _ tree key trace
      cases trace with
      | terminal _ cursor children computed empty matched realized =>
          exact .terminal more cursor children computed empty matched realized
  | succ fuel ih =>
      intro more bound tree key trace
      cases trace with
      | terminal _ cursor children computed empty matched realized =>
          exact .terminal more cursor children computed empty matched realized
      | node _ cursor children childKeys sortedKeys sortedTrees computed nonempty built
          sorted constitutional descending matched realized traced =>
          cases more with
          | zero => omega
          | succ more =>
              have bound' : fuel ≤ more := by omega
              apply LocalizedRuleMajorSortTrace.node more cursor children childKeys sortedKeys
                sortedTrees computed nonempty
              · exact mapM_transfer _ _
                  (fun child childKey h => build_mono input stage read fuel more bound' child childKey h)
                  children childKeys built
              · exact sorted
              · exact constitutional
              · exact descending
              · exact matched
              · exact realized
              · apply LocalizedRuleMajorSortTraceList.of_forall₂
                exact (LocalizedRuleMajorSortTraceList.to_forall₂ traced).imp
                  (fun _ _ h => ih more bound' _ _ h)

/-- The actual full compound is independent of every evaluation budget above the derived
carrier bound, under the unchanged target and dependency view. -/
theorem compoundExec_eq_of_adequate
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) (fuel more : Nat)
    (first : 2 * (carrierFuel + 1) ≤ fuel) (second : 2 * (carrierFuel + 1) ≤ more) :
    input.buildActualRuleMajorCompoundRule45KeyExec? target view fuel cursor =
      input.buildActualRuleMajorCompoundRule45KeyExec? target view more cursor := by
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq,
    input.buildActualRuleMajorCompoundRule45KeyExec?_eq,
    input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor,
    input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
  apply input.buildRuleMajorCompoundRule45KeyWith?_eq
  intro component
  obtain ⟨key, built⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice component
    (input.localizedDependencyLabel target view) cursor valid
  rw [build_mono input component (input.localizedDependencyLabel target view) _ _ first _ _ built,
    build_mono input component (input.localizedDependencyLabel target view) _ _ second _ _ built]

/-- A same-source stage isomorphism no longer requires equal evaluation budgets. Both successful
traces are lifted to their common maximum before applying the existing structural theorem. -/
theorem graphIso_of_sameSource_crossFuel
    (readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (stageR : LocalizedCumulativeRule45Stage) (fuelL fuelR : Nat)
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (left : LocalizedRuleMajorSortTrace input stage read fuelL treeL keyL)
    (right : LocalizedRuleMajorSortTrace input stageR readR fuelR treeR keyR)
    (same : treeL.source = treeR.source) :
    Nonempty (RootedDigraph.Iso (ruleMajorTreeGraph treeL) (ruleMajorTreeGraph treeR)) :=
  ruleMajorTreeGraph_iso_nonempty_of_sameSourceCrossReaderTraces read readR (max fuelL fuelR)
    (trace_mono input stage read fuelL _ (Nat.le_max_left _ _) treeL keyL left)
    (trace_mono input stageR readR fuelR _ (Nat.le_max_right _ _) treeR keyR right) same

end TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation.build_mono
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation.buildExec_mono
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation.trace_mono
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation.graphIso_of_sameSource_crossFuel

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation.compoundExec_eq_of_adequate
