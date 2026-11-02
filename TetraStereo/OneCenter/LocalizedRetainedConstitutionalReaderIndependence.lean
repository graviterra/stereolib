import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Reader independence of rule-major constitutional keys

`ruleMajorTreeGraph_iso_nonempty_of_sameSourceCrossReaderTraces` identifies the erased stage
graphs of two actual rule-major traces at one source cursor.  That isomorphism preserves
topology, `current?` and provenance.  It does not identify cumulative keys.

The production builder
`buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_seam` already sends a successful
`buildLocalizedRerootCumulativeRule45KeyWithRead?` compilation to
`DeclarativeLocalizedRerootRuleMajorKey`.  A `LocalizedRuleMajorSortTrace` is a different
certificate: its sibling order is `sortRuleMajorCumulativeKeys`, whose comparator is
`compareRuleMajorCumulativeDescriptor`.  This module is the corresponding bridge for that trace.

The bridge uses the trace's own data.  A terminal trace is the official root key.  At a branch,
the actual `mapM` children satisfy the bridge by the fuel induction; the stored sort equation is
a permutation (`sortKeysBy_ruleMajorCumulative_perm`); and the stored
`OfficialRuleMajorKey.Descending` projection is already the refinement of the rule-major sibling
order by the constitutional order.  `OfficialRuleMajorKey.assemble` is the trace constructor's
constitutional merge.  `declarative_constitutional_observable_unique` then identifies the
Rule-1a/1b/2 tables.  Tied children may be reordered by a stereo reader; the observable sequence
is the one fixed by that existing uniqueness lemma.

## Consumer

`LocalizedCyclicSpatialRootLetter` can instantiate either reader with the generated dependency
reader and the other with `fun _ => none`.  The two builds must succeed at the same source
cursor.  Their fuels may differ.  No agreement between the readers, no availability hypothesis
for `none`, and no `SimpleBonded` or `Acyclic` hypothesis is required.  The conclusion is the
constitutional tables only.  Descriptor columns, exact labels and ranked labels stay with the
reader that produced them.

## What this file does not assemble

It does not execute a reference state, choose a concrete atomic-number order, or prove a
ring-letter judgement.
-/

namespace TetraStereo.OneCenter.RetainedConstitutionalReaderIndependence

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- A successful rule-major child pass carries one constitutional derivation per frame cursor. -/
private theorem mapM_ruleMajor_constitutional
    {fuel : Nat} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (sound : ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key →
        input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildRuleMajorCumulativeWithRead? stage read fuel) = some keys →
        input.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors
          (keys.map fun key => key.constitutional)
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeLocalizedRerootRuleMajorKeyList.nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildRuleMajorCumulativeWithRead? stage read fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildRuleMajorCumulativeWithRead? stage read fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeLocalizedRerootRuleMajorKeyList.cons
                (sound cursor head headComputed)
                (mapM_ruleMajor_constitutional sound cursors tail tailComputed)

/-- Every actual rule-major trace, at any stage and any label reader, is a pure constitutional
derivation at its source cursor. -/
theorem ruleMajorSortTrace_constitutional_declarative :
    ∀ (fuel : Nat) {stage : LocalizedCumulativeRule45Stage}
      {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
      {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
      {key : input.LocalizedRerootCumulativeRule45Key},
      LocalizedRuleMajorSortTrace input stage read fuel tree key →
        input.DeclarativeLocalizedRerootRuleMajorKey fuel tree.source key.constitutional := by
  intro fuel
  induction fuel with
  | zero =>
      intro stage read tree key trace
      cases trace with
      | terminal _fuel cursor children childrenComputed terminalChildren _fullMatch _realizes =>
          exact DeclarativeLocalizedRerootRuleMajorKey.terminal
            (input.localizedRerootChildren?_sound cursor children childrenComputed)
            terminalChildren
  | succ fuel ih =>
      intro stage read tree key trace
      rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
        ⟨cursor, children, treeEq, keyEq, _childrenEq, childrenComputed, empty⟩ |
        ⟨cursor, children, childKeys, sortedKeys, _sortedTrees, treeEq, keyEq, _childrenEq,
          childrenComputed, nonempty, childKeysComputed, sortedEq, descending, _sortedDescending,
          _traced⟩
      · have sourceEq : tree.source = cursor := by
          rw [treeEq]
          rfl
        rw [sourceEq, keyEq, localizedCumulativeRule45TerminalKey]
        exact DeclarativeLocalizedRerootRuleMajorKey.terminal
          (input.localizedRerootChildren?_sound cursor children childrenComputed) empty
      · have sourceEq : tree.source = cursor := by
          rw [treeEq]
          rfl
        have childSound : ∀ (child : input.LocalizedRerootCursor carrierFuel)
            (childKey : input.LocalizedRerootCumulativeRule45Key),
            input.buildRuleMajorCumulativeWithRead? stage read fuel child = some childKey →
              input.DeclarativeLocalizedRerootRuleMajorKey fuel child childKey.constitutional := by
          intro child childKey built
          obtain ⟨childTree, childSource, childTrace⟩ :=
            exists_ruleMajorTrace_of_buildWithRead input stage read fuel child childKey built
          exact childSource ▸ ih childTrace
        have ranking :
            (sortedKeys.map fun child => child.constitutional).Perm
              (childKeys.map fun child => child.constitutional) := by
          rw [sortedEq]
          exact (input.sortKeysBy_ruleMajorCumulative_perm
            (ruleMajorStageWidth stage) childKeys).map fun child => child.constitutional
        rw [sourceEq, keyEq, localizedCumulativeRule45StepKey]
        exact DeclarativeLocalizedRerootRuleMajorKey.branch
          (input.localizedRerootChildren?_sound cursor children childrenComputed)
          nonempty
          (mapM_ruleMajor_constitutional childSound children childKeys childKeysComputed)
          ranking descending

/-- Two actual rule-major traces at one source cursor have equal Rule-1a/1b/2 tables.
The stages, label readers and fuels are independent. -/
theorem ruleMajorSortTrace_constitutionalObservable_eq
    {fuelL fuelR : Nat} {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (traceL : LocalizedRuleMajorSortTrace input stageL readL fuelL treeL keyL)
    (traceR : LocalizedRuleMajorSortTrace input stageR readR fuelR treeR keyR)
    (sourceEq : treeL.source = treeR.source) :
    constitutionalObservable keyL.constitutional =
      constitutionalObservable keyR.constitutional := by
  have leftDerived := ruleMajorSortTrace_constitutional_declarative fuelL traceL
  have rightDerived := ruleMajorSortTrace_constitutional_declarative fuelR traceR
  have rightAtLeft : input.DeclarativeLocalizedRerootRuleMajorKey fuelR treeL.source
      keyR.constitutional := by
    simpa [sourceEq] using rightDerived
  exact input.declarative_constitutional_observable_unique fuelL fuelR treeL.source
    keyL.constitutional keyR.constitutional leftDerived rightAtLeft

/-- The three constitutional tables, named separately for rewriting. -/
theorem ruleMajorSortTrace_constitutionalTables_eq
    {fuelL fuelR : Nat} {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (traceL : LocalizedRuleMajorSortTrace input stageL readL fuelL treeL keyL)
    (traceR : LocalizedRuleMajorSortTrace input stageR readR fuelR treeR keyR)
    (sourceEq : treeL.source = treeR.source) :
    keyL.constitutional.rule1a = keyR.constitutional.rule1a ∧
      keyL.constitutional.rule1b = keyR.constitutional.rule1b ∧
      keyL.constitutional.rule2 = keyR.constitutional.rule2 := by
  have tables := ruleMajorSortTrace_constitutionalObservable_eq traceL traceR sourceEq
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg LocalizedConstitutionalObservable.rule1a tables
  · exact congrArg LocalizedConstitutionalObservable.rule1b tables
  · exact congrArg LocalizedConstitutionalObservable.rule2 tables

/-- Successful rule-major builds at one cursor have equal constitutional tables, for arbitrary
stages, readers and fuels.  `fun _ => none` is an admissible reader and needs no agreement with
the other reader. -/
theorem ruleMajorBuild_constitutionalObservable_eq
    {fuelL fuelR : Nat} (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL cursor = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR cursor = some keyR) :
    constitutionalObservable keyL.constitutional =
      constitutionalObservable keyR.constitutional := by
  obtain ⟨treeL, sourceL, traceL⟩ :=
    exists_ruleMajorTrace_of_buildWithRead input stageL readL fuelL cursor keyL builtL
  obtain ⟨treeR, sourceR, traceR⟩ :=
    exists_ruleMajorTrace_of_buildWithRead input stageR readR fuelR cursor keyR builtR
  exact ruleMajorSortTrace_constitutionalObservable_eq traceL traceR
    (sourceL.trans sourceR.symm)

/-- Rule-1a, Rule-1b and Rule-2 tables of two successful rule-major builds at one cursor. -/
theorem ruleMajorBuild_constitutionalTables_eq
    {fuelL fuelR : Nat} (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL cursor = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR cursor = some keyR) :
    keyL.constitutional.rule1a = keyR.constitutional.rule1a ∧
      keyL.constitutional.rule1b = keyR.constitutional.rule1b ∧
      keyL.constitutional.rule2 = keyR.constitutional.rule2 := by
  have tables := ruleMajorBuild_constitutionalObservable_eq stageL stageR readL readR cursor
    builtL builtR
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg LocalizedConstitutionalObservable.rule1a tables
  · exact congrArg LocalizedConstitutionalObservable.rule1b tables
  · exact congrArg LocalizedConstitutionalObservable.rule2 tables

/-- The first `n` Rule-1a spheres.  `n = 2` is the root sphere together with the first child
sphere. -/
theorem ruleMajorBuild_rule1a_take_eq
    {fuelL fuelR : Nat} (n : Nat) (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL cursor = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR cursor = some keyR) :
    keyL.constitutional.rule1a.take n = keyR.constitutional.rule1a.take n := by
  have tables := ruleMajorBuild_constitutionalTables_eq stageL stageR readL readR cursor
    builtL builtR
  exact congrArg (fun layers => layers.take n) tables.1

/-- First two Rule-1a spheres of a generated-reader build and a constant-`none` build at one
cursor.  The constant reader is `fun _ => none`; it is not required to coincide with the
generated reader at any cursor. -/
theorem ruleMajorBuild_rule1a_firstTwo_eq_constNone
    {fuelL fuelR : Nat} (stageL stageR : LocalizedCumulativeRule45Stage)
    (generated : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL generated fuelL cursor = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR (fun _ => none) fuelR cursor =
      some keyR) :
    keyL.constitutional.rule1a.take 2 = keyR.constitutional.rule1a.take 2 :=
  ruleMajorBuild_rule1a_take_eq 2 stageL stageR generated (fun _ => none) cursor builtL builtR

/-- A constitutional comparison of two cursors is unchanged when each cursor's rule-major build
is replaced by a build at another stage, reader or fuel.  One reader on each side may be
`fun _ => none`. -/
theorem ruleMajorBuild_constitutional_compare_congr
    {fuelL fuelR fuelL₀ fuelR₀ : Nat}
    (stageL stageR stageL₀ stageR₀ : LocalizedCumulativeRule45Stage)
    (readL readR readL₀ readR₀ :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursorL cursorR : input.LocalizedRerootCursor carrierFuel)
    {keyL keyR keyL₀ keyR₀ : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL cursorL = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR cursorR = some keyR)
    (builtL₀ : input.buildRuleMajorCumulativeWithRead? stageL₀ readL₀ fuelL₀ cursorL = some keyL₀)
    (builtR₀ : input.buildRuleMajorCumulativeWithRead? stageR₀ readR₀ fuelR₀ cursorR =
      some keyR₀) :
    OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional =
      OfficialRuleMajorKey.compare keyL₀.constitutional keyR₀.constitutional :=
  ruleMajor_compare_congr keyL.constitutional keyR.constitutional
    keyL₀.constitutional keyR₀.constitutional
    (ruleMajorBuild_constitutionalObservable_eq stageL stageL₀ readL readL₀ cursorL builtL builtL₀)
    (ruleMajorBuild_constitutionalObservable_eq stageR stageR₀ readR readR₀ cursorR builtR builtR₀)

assert_kernel_only ruleMajorSortTrace_constitutional_declarative
assert_kernel_only ruleMajorSortTrace_constitutionalObservable_eq
assert_kernel_only ruleMajorSortTrace_constitutionalTables_eq
assert_kernel_only ruleMajorBuild_constitutionalObservable_eq
assert_kernel_only ruleMajorBuild_constitutionalTables_eq
assert_kernel_only ruleMajorBuild_rule1a_take_eq
assert_kernel_only ruleMajorBuild_rule1a_firstTwo_eq_constNone
assert_kernel_only ruleMajorBuild_constitutional_compare_congr

end TetraStereo.OneCenter.RetainedConstitutionalReaderIndependence
