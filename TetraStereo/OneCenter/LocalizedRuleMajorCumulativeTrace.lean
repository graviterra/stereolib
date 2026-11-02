import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeBuilder
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeOrder
import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.KernelOnly
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree

/-!
# Actual recursive trace of the rule-major cumulative builder

`LocalizedRuleMajorCumulativeBuilder` introduces a distinct recursive key builder whose sibling
sort compares the complete cumulative descriptor columns in rule order. This module connects that
builder's successful `mapM` and sort steps to the decorated occurrence trees and source expansion
provenance already described by `LocalizedCumulativeTreeFullMatch` and
`LocalizedCumulativeTreeRealizes`.

`LocalizedRuleMajorSortTrace` is the resulting recursive certificate, indexed by stage, label
reader, fuel, decorated tree and actual key. It records the exact raw child keys produced by the
builder, the exact rule-major sort applied to those keys, the sort's descending invariant, and the
recursive certificates for the corresponding actual child trees. The constitutional descending
projection is proved here from the fact that constitution is the first component of the new
comparator; it is not an application of the prior builder's sorting theorem.

## What one certificate records

* `fullMatch` and `realizes`: the same tree's table/label match and its provenance through actual
  `localizedRerootChildren?` frames.
* At a nonterminal node of fuel `fuel + 1`:
  * the actual `localizedRerootChildren? cursor = some children` frame and its non-emptiness;
  * the actual raw child keys `childKeys` with
    `children.mapM (buildRuleMajorCumulativeWithRead? … fuel) = some childKeys`;
  * the exact sorted keys `sortedKeys = input.sortRuleMajorCumulativeKeys stage childKeys`,
    using the new rule-major comparator;
  * both `input.RuleMajorCumulativeKeysDescending ... sortedKeys` and the derived constitutional
    descending order of the same sorted keys;
  * a `List.Forall₂` pairing each sorted key with the corresponding actual child tree
    `tree.children`, where every pair is again a certificate at the decreased fuel `fuel`.
* At a terminal occurrence the constructor records the actual frame together with
  `children = []`; there is no sorting step.

No sort-order premise is supplied by the caller: both descending facts are derived from the
rule-major sort theorem and the comparator's constitutional first component. This module concerns
the builder's actual sorting and tree provenance; it does not claim that the new comparator agrees
with the independent declarative or physical comparison semantics.

## Main results

* `exists_ruleMajorTrace_of_buildWithRead` — any successful rule-major build yields a traced tree
  whose source is the actual cursor.
* `fullMatch_of_trace` / `realizes_of_trace` — recover the tree match and actual expansion
  provenance from a trace.
* `structure_of_trace` / `node_structure_of_trace` — expose the exact per-node build and sort
  data, both order facts, and the recursive child certificates.
* `sortedDescending_of_trace` / `childrenTraced_of_trace` — project the sort and child-recursion
  facts.
* `exists_ruleMajorTrace_at_twice` — for any label reader and path-valid cursor, derive adequate
  fuel success and a trace from `exists_buildRuleMajorCumulativeWithRead_at_twice`.
* `exists_ruleMajorRootArm` — obtain the same traced expansion at an actual original ligand root,
  including generated-source and faithful-expansion facts.
-/








private theorem map_eq_map_of_forall₂_actual {α β γ : Type*} {r : α → β → Prop}
    {f : α → γ} {g : β → γ} (left : List α) (right : List β)
    (hrel : List.Forall₂ r left right) (hfg : ∀ a b, r a b → f a = g b) :
    left.map f = right.map g := by
  induction hrel with
  | nil => rfl
  | cons hab htail ih => simp [hfg _ _ hab, ih]

/-- Membership on the right of a `Forall₂` exposes the paired left element and its relation. -/
private theorem exists_of_mem_right_forall₂_actual {α β : Type*} {r : α → β → Prop}
    {left : List α} {right : List β} (hrel : List.Forall₂ r left right) :
    ∀ b ∈ right, ∃ a ∈ left, r a b := by
  induction hrel with
  | nil =>
      intro b member
      simp at member
  | cons head tail ih =>
      intro b member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, by simp, head⟩
      · obtain ⟨a, aMember, related⟩ := ih b member
        exact ⟨a, by simp [aMember], related⟩

/-- Witness lifting through an actual successful child `mapM`: the resulting child sources are
exactly the actual child cursors and every actual child key is matched by its tree. -/
private theorem witnesses_of_mapM_some_actual
    {A B T : Type*} (f : A → Option B) (source : T → A)
    (R : B → T → Prop)
    (witness : ∀ a b, f a = some b → ∃ t, source t = a ∧ R b t) :
    ∀ xs ys, xs.mapM f = some ys →
      ∃ ts, ts.map source = xs ∧ List.Forall₂ R ys ts
  | [], ys, computed => by
      simp at computed
      subst ys
      exact ⟨[], rfl, List.Forall₂.nil⟩
  | x :: xs, ys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f x with
      | none => simp [headComputed] at computed
      | some y =>
          cases tailComputed : xs.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst ys
              obtain ⟨tree, treeSource, treeGood⟩ := witness x y headComputed
              obtain ⟨trees, treesSource, treesGood⟩ :=
                witnesses_of_mapM_some_actual f source R witness xs tail tailComputed
              exact ⟨tree :: trees, by simp [treeSource, treesSource],
                List.Forall₂.cons treeGood treesGood⟩

/-- A terminal actual key is matched by the terminal decorated occurrence at the same cursor. -/
private theorem treeTableMatch_localizedRootTree_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel) :
    LocalizedCumulativeTreeTableMatch stage
      (localizedRootTree input cursor label [])
      { constitutional :=
          input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
        labels := [[([], label)]]
        rankedLabels := [[([], label)]] } := by
  unfold LocalizedCumulativeTreeTableMatch
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tables_rule1a, table_eq_root_merge]
    simp [localizedRootTree, mergeLocalizedTreeChildTables,
      localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [tables_rule1b, table_eq_root_merge]
    simp [localizedRootTree, mergeLocalizedTreeChildTables,
      localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [tables_rule2, table_eq_root_merge]
    simp [localizedRootTree, mergeLocalizedTreeChildTables,
      localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [tables_descriptor, table_eq_root_merge]
    simp [localizedRootTree, mergeLocalizedTreeChildTables,
      localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs]

/-- A terminal actual key's exact-label table is the terminal occurrence's root-only label
table. -/
private theorem labelTable_localizedRootTree_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel) :
    LocalizedCumulativeTreeLabelMatch
      (localizedRootTree input cursor label [])
      { constitutional :=
          input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
        labels := [[([], label)]]
        rankedLabels := [[([], label)]] } := by
  unfold LocalizedCumulativeTreeLabelMatch
  rw [labelTable_eq_table, table_eq_root_merge]
  simp [localizedRootTree, mergeLocalizedTreeChildTables,
    localizedTreeChildLayerCount, SparseAddress.mergePairTable,
    SparseAddress.mergePairs]

/-- A branching actual key is matched by the decorated occurrence rooted at the same cursor with
the actual sorted child trees; the argument is the actual sort permutation lifted over the actual
per-child witnesses. -/
private theorem treeTableMatch_localizedRootTree_branch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (hrel : List.Forall₂
      (fun key tree => LocalizedCumulativeTreeTableMatch stage tree key)
      sortedKeys sortedTrees) :
    LocalizedCumulativeTreeTableMatch stage
      (localizedRootTree input cursor label sortedTrees)
      { constitutional := OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
          (sortedKeys.map fun child => child.constitutional)
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
          input.mergeLocalizedRerootDescriptorChildren sortedKeys
        labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sortedKeys
        rankedLabels := [[([], label)]] ++
          input.mergeLocalizedRerootRankedLabelChildren sortedKeys } := by
  unfold LocalizedCumulativeTreeTableMatch
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmap :
        sortedKeys.map (fun key => key.constitutional.rule1a) =
          sortedTrees.map (table (fun node => node.atomicNumber)) :=
      map_eq_map_of_forall₂_actual sortedKeys sortedTrees hrel
        (fun key tree matched => by
          simpa only [tables_rule1a] using matched.1.symm)
    rw [tables_rule1a, table_eq_root_merge]
    simp only [localizedRootTree]
    rw [← hmap, mergeLocalizedTreeChildTables_map_comp_eq_mergeChildren]
    simp only [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]
  · have hmap :
        sortedKeys.map (fun key => key.constitutional.rule1b) =
          sortedTrees.map (table (fun node => node.rule1bDistance)) :=
      map_eq_map_of_forall₂_actual sortedKeys sortedTrees hrel
        (fun key tree matched => by
          simpa only [tables_rule1b] using matched.2.1.symm)
    rw [tables_rule1b, table_eq_root_merge]
    simp only [localizedRootTree]
    rw [← hmap, mergeLocalizedTreeChildTables_map_comp_eq_mergeChildren]
    simp only [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]
  · have hmap :
        sortedKeys.map (fun key => key.constitutional.rule2) =
          sortedTrees.map (table (fun node => node.isotopeMass)) :=
      map_eq_map_of_forall₂_actual sortedKeys sortedTrees hrel
        (fun key tree matched => by
          simpa only [tables_rule2] using matched.2.2.1.symm)
    rw [tables_rule2, table_eq_root_merge]
    simp only [localizedRootTree]
    rw [← hmap, mergeLocalizedTreeChildTables_map_comp_eq_mergeChildren]
    simp only [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]
  · have hmap :
        sortedKeys.map (fun key => key.descriptor) =
          sortedTrees.map
            (table (fun node => localizedCumulativeRule45Priority stage node.label)) :=
      map_eq_map_of_forall₂_actual sortedKeys sortedTrees hrel
        (fun key tree matched => by
          simpa only [tables_descriptor] using matched.2.2.2.symm)
    rw [tables_descriptor, table_eq_root_merge]
    simp only [localizedRootTree]
    rw [← hmap, mergeLocalizedTreeChildTables_descriptor_eq]

/-- A branching actual key's exact-label table is composed from the actual sorted child label
tables by the actual label merge. -/
private theorem labelTable_localizedRootTree_branch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (hrel : List.Forall₂
      (fun key tree => LocalizedCumulativeTreeLabelMatch tree key)
      sortedKeys sortedTrees) :
    LocalizedCumulativeTreeLabelMatch
      (localizedRootTree input cursor label sortedTrees)
      { constitutional := OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
          (sortedKeys.map fun child => child.constitutional)
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
          input.mergeLocalizedRerootDescriptorChildren sortedKeys
        labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sortedKeys
        rankedLabels := [[([], label)]] ++
          input.mergeLocalizedRerootRankedLabelChildren sortedKeys } := by
  unfold LocalizedCumulativeTreeLabelMatch
  have hmap :
      sortedKeys.map (fun key => key.labels) =
        sortedTrees.map (table (fun node => node.label)) :=
    map_eq_map_of_forall₂_actual sortedKeys sortedTrees hrel
      (fun key tree matched => by
        have treeEq : tree.labelTable = key.labels := matched
        exact treeEq.symm)
  rw [labelTable_eq_table, table_eq_root_merge]
  simp only [localizedRootTree]
  rw [← hmap, mergeLocalizedTreeChildTables_label_eq]

/-- A strict constitutional comparison is the first component of the rule-major comparator. -/
theorem constitutionalCompare_ne_lt_of_ruleMajor_ne_lt
    (input : CertifiedLocalizedCIPInput) (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (notLess : input.compareRuleMajorCumulativeDescriptor width left right ≠ Ordering.lt) :
    OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.lt := by
  intro constitutionalLess
  unfold compareRuleMajorCumulativeDescriptor at notLess
  simp only [compareLex, Ordering.byKey] at notLess
  rw [constitutionalLess] at notLess
  simp [Ordering.then] at notLess

/-- Rule-major descending order projects to descending constitutional keys. -/
theorem constitutionalDescending_of_ruleMajorDescending
    (input : CertifiedLocalizedCIPInput) (width : Nat)
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (descending : input.RuleMajorCumulativeKeysDescending width keys) :
    OfficialRuleMajorKey.Descending (keys.map fun key => key.constitutional) := by
  change keys.Pairwise (fun left right =>
    input.compareRuleMajorCumulativeDescriptor width left right ≠ Ordering.lt) at descending
  change (keys.map fun key => key.constitutional).Pairwise (fun left right =>
    OfficialRuleMajorKey.compare left right ≠ Ordering.lt)
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp ?_ descending
  intro left right notLess
  exact constitutionalCompare_ne_lt_of_ruleMajor_ne_lt input width left right notLess

/-! ## The recursive actual build/sort certificate -/

mutual














  inductive LocalizedRuleMajorSortTrace
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
      Nat → LocalizedCumulativeDecoratedTree input carrierFuel →
        input.LocalizedRerootCumulativeRule45Key → Prop where
    | terminal (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
        (children : List (input.LocalizedRerootCursor carrierFuel))
        (childrenComputed : input.localizedRerootChildren? cursor = some children)
        (terminalChildren : children = [])
        (fullMatch : LocalizedCumulativeTreeFullMatch stage
          (localizedRootTree input cursor (read cursor) [])
          (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)))
        (realizes : LocalizedCumulativeTreeRealizes input read
          (localizedRootTree input cursor (read cursor) [])) :
        LocalizedRuleMajorSortTrace input stage read fuel
          (localizedRootTree input cursor (read cursor) [])
          (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
    | node (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
        (children : List (input.LocalizedRerootCursor carrierFuel))
        (childKeys sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
        (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
        (childrenComputed : input.localizedRerootChildren? cursor = some children)
        (nonempty : children ≠ [])
        (childKeysComputed : children.mapM
          (input.buildRuleMajorCumulativeWithRead? stage read fuel) =
            some childKeys)
        (sortedEq : sortedKeys = input.sortRuleMajorCumulativeKeys stage childKeys)
        (constitutionalDescending : OfficialRuleMajorKey.Descending
          (sortedKeys.map fun child => child.constitutional))
        (sortedDescending : input.RuleMajorCumulativeKeysDescending
          (CertifiedLocalizedCIPInput.ruleMajorStageWidth stage) sortedKeys)
        (fullMatch : LocalizedCumulativeTreeFullMatch stage
          (localizedRootTree input cursor (read cursor) sortedTrees)
          (localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys))
        (realizes : LocalizedCumulativeTreeRealizes input read
          (localizedRootTree input cursor (read cursor) sortedTrees))
        (childrenTraced : LocalizedRuleMajorSortTraceList input stage read fuel
          sortedKeys sortedTrees) :
        LocalizedRuleMajorSortTrace input stage read (fuel + 1)
          (localizedRootTree input cursor (read cursor) sortedTrees)
          (localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys)

  /-- The list form of the recursive certificate: a certificate for every sorted key together with
  the matching actual child tree, at one common fuel. -/
  inductive LocalizedRuleMajorSortTraceList
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
      Nat → List input.LocalizedRerootCumulativeRule45Key →
        List (LocalizedCumulativeDecoratedTree input carrierFuel) → Prop where
    | nil (fuel : Nat) :
        LocalizedRuleMajorSortTraceList input stage read fuel [] []
    | cons (fuel : Nat)
        (headKey : input.LocalizedRerootCumulativeRule45Key)
        (tailKeys : List input.LocalizedRerootCumulativeRule45Key)
        (headTree : LocalizedCumulativeDecoratedTree input carrierFuel)
        (tailTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
        (head : LocalizedRuleMajorSortTrace input stage read fuel headTree headKey)
        (tail : LocalizedRuleMajorSortTraceList input stage read fuel tailKeys tailTrees) :
        LocalizedRuleMajorSortTraceList input stage read fuel
          (headKey :: tailKeys) (headTree :: tailTrees)
end

/-- A `Forall₂` pairing of sorted keys with trees through traces is exactly a list certificate. -/
theorem LocalizedRuleMajorSortTraceList.of_forall₂
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} :
    ∀ {keys : List input.LocalizedRerootCumulativeRule45Key}
      {trees : List (LocalizedCumulativeDecoratedTree input carrierFuel)},
      List.Forall₂
        (fun key tree => LocalizedRuleMajorSortTrace input stage read fuel tree key)
        keys trees →
      LocalizedRuleMajorSortTraceList input stage read fuel keys trees
  | _, _, .nil => .nil fuel
  | _, _, .cons head tail => .cons fuel _ _ _ _ head (of_forall₂ tail)

/-- A list certificate exposes the `Forall₂` pairing of sorted keys with trees through traces. -/
theorem LocalizedRuleMajorSortTraceList.to_forall₂
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} :
    ∀ {keys : List input.LocalizedRerootCumulativeRule45Key}
      {trees : List (LocalizedCumulativeDecoratedTree input carrierFuel)},
      LocalizedRuleMajorSortTraceList input stage read fuel keys trees →
      List.Forall₂
        (fun key tree => LocalizedRuleMajorSortTrace input stage read fuel tree key)
        keys trees
  | _, _, .nil _ => .nil
  | _, _, .cons _ _ _ _ _ head tail => .cons head (to_forall₂ tail)

/-! ## Projections of the certificate -/


theorem LocalizedRuleMajorSortTrace.fullMatch_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key) :
    LocalizedCumulativeTreeFullMatch stage tree key := by
  cases trace with
  | terminal fuel cursor children childrenComputed terminalChildren fullMatch realizes =>
      exact fullMatch
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq constitutionalDescending sortedDescending fullMatch realizes childrenTraced =>
      exact fullMatch


theorem LocalizedRuleMajorSortTrace.realizes_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key) :
    LocalizedCumulativeTreeRealizes input read tree := by
  cases trace with
  | terminal fuel cursor children childrenComputed terminalChildren fullMatch realizes =>
      exact realizes
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq constitutionalDescending sortedDescending fullMatch realizes childrenTraced =>
      exact realizes

/-- **Complete per-node case analysis of a trace at a nonterminal fuel.**

Either the occurrence is terminal — the actual frame's children are `[]`, the tree is the
root-only tree at the actual cursor and the key is the terminal key — or it is a genuine builder
step, exposing the actual frame, the actual raw child keys of the actual `mapM` at the decreased
fuel, the exact production sort equation, the rule-major descending order of the actual sorted
keys and the recursive certificate for every sorted child. -/
theorem LocalizedRuleMajorSortTrace.structure_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read (fuel + 1) tree key) :
    (∃ (cursor : input.LocalizedRerootCursor carrierFuel)
        (children : List (input.LocalizedRerootCursor carrierFuel)),
        tree = localizedRootTree input cursor (read cursor) [] ∧
          key = localizedCumulativeRule45TerminalKey input stage cursor (read cursor) ∧
            tree.children = [] ∧
              input.localizedRerootChildren? cursor = some children ∧ children = []) ∨
      (∃ (cursor : input.LocalizedRerootCursor carrierFuel)
          (children : List (input.LocalizedRerootCursor carrierFuel))
          (childKeys sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
          (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel)),
          tree = localizedRootTree input cursor (read cursor) sortedTrees ∧
            key = localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys ∧
              tree.children = sortedTrees ∧
                input.localizedRerootChildren? cursor = some children ∧
                  children ≠ [] ∧
                    children.mapM
                        (input.buildRuleMajorCumulativeWithRead? stage read fuel) =
                      some childKeys ∧
                      sortedKeys = input.sortRuleMajorCumulativeKeys stage childKeys ∧
                        OfficialRuleMajorKey.Descending (sortedKeys.map fun child => child.constitutional) ∧
                        input.RuleMajorCumulativeKeysDescending (CertifiedLocalizedCIPInput.ruleMajorStageWidth stage) sortedKeys ∧
                          LocalizedRuleMajorSortTraceList input stage read fuel
                            sortedKeys sortedTrees) := by
  cases trace with
  | terminal fuel cursor children childrenComputed terminalChildren fullMatch realizes =>
      exact Or.inl ⟨cursor, children, rfl, rfl, rfl, childrenComputed, terminalChildren⟩
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq constitutionalDescending sortedDescending fullMatch realizes childrenTraced =>
      exact Or.inr ⟨cursor, children, childKeys, sortedKeys, sortedTrees, rfl, rfl, rfl,
        childrenComputed, nonempty, childKeysComputed, sortedEq, constitutionalDescending, sortedDescending,
        childrenTraced⟩

/-- **Nonterminal node interface.**  A trace whose tree actually has children exposes the actual
frame, the actual raw child keys of the actual `mapM` at the decreased fuel, the exact production
sort equation, the rule-major descending order of the actual sorted keys, and the
recursive certificate pairing those sorted keys with `tree.children`. -/
theorem LocalizedRuleMajorSortTrace.node_structure_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read (fuel + 1) tree key)
    (nonemptyTree : tree.children ≠ []) :
    ∃ (cursor : input.LocalizedRerootCursor carrierFuel)
      (children : List (input.LocalizedRerootCursor carrierFuel))
      (childKeys sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
      (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel)),
      tree = localizedRootTree input cursor (read cursor) sortedTrees ∧
        key = localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys ∧
          tree.children = sortedTrees ∧
            input.localizedRerootChildren? cursor = some children ∧
              children ≠ [] ∧
                children.mapM
                    (input.buildRuleMajorCumulativeWithRead? stage read fuel) =
                  some childKeys ∧
                  sortedKeys = input.sortRuleMajorCumulativeKeys stage childKeys ∧
                    OfficialRuleMajorKey.Descending (sortedKeys.map fun child => child.constitutional) ∧
                    input.RuleMajorCumulativeKeysDescending (CertifiedLocalizedCIPInput.ruleMajorStageWidth stage) sortedKeys ∧
                      LocalizedRuleMajorSortTraceList input stage read fuel
                        sortedKeys sortedTrees := by
  rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
    ⟨_, _, _, _, terminalChildren, _, _⟩ | nodeData
  · exact absurd terminalChildren nonemptyTree
  · exact nodeData





theorem LocalizedRuleMajorSortTrace.sortedDescending_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read (fuel + 1) tree key)
    (nonemptyTree : tree.children ≠ []) :
    ∃ (childKeys sortedKeys : List input.LocalizedRerootCumulativeRule45Key),
      sortedKeys = input.sortRuleMajorCumulativeKeys stage childKeys ∧
        OfficialRuleMajorKey.Descending (sortedKeys.map fun child => child.constitutional) ∧
        input.RuleMajorCumulativeKeysDescending (CertifiedLocalizedCIPInput.ruleMajorStageWidth stage) sortedKeys := by
  obtain ⟨_, _, childKeys, sortedKeys, _, _, _, _, _, _, _, sortedEq, constitutionalDescending, descending, _⟩ :=
    LocalizedRuleMajorSortTrace.node_structure_of_trace trace nonemptyTree
  exact ⟨childKeys, sortedKeys, sortedEq, constitutionalDescending, descending⟩

/-- **Recursive sub-certificates.**  Every actual child tree of a nonterminal traced node is
paired with its actual sorted key through a trace at the decreased fuel, in the `Forall₂` form. -/
theorem LocalizedRuleMajorSortTrace.childrenTraced_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read (fuel + 1) tree key)
    (nonemptyTree : tree.children ≠ []) :
    ∃ sortedKeys : List input.LocalizedRerootCumulativeRule45Key,
      List.Forall₂
        (fun childKey childTree =>
          LocalizedRuleMajorSortTrace input stage read fuel childTree childKey)
        sortedKeys tree.children := by
  obtain ⟨_, _, _, sortedKeys, sortedTrees, _, _, childrenEq, _, _, _, _, _, _,
    childrenTraced⟩ :=
    LocalizedRuleMajorSortTrace.node_structure_of_trace trace nonemptyTree
  exact ⟨sortedKeys, by
    rw [childrenEq]
    exact LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced⟩

/-! ## Extraction from an actual successful build -/









theorem exists_ruleMajorTrace_of_buildWithRead
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?
        input stage read fuel cursor = some key →
      ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
        tree.source = cursor ∧
          LocalizedRuleMajorSortTrace input stage read fuel tree key := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key built
      unfold CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?
        at built
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at built
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at built
            subst key
            exact ⟨localizedRootTree input cursor (read cursor) [], rfl,
              LocalizedRuleMajorSortTrace.terminal 0 cursor children childrenComputed
                terminal
                ⟨treeTableMatch_localizedRootTree_terminal input stage cursor (read cursor),
                  labelTable_localizedRootTree_terminal input stage cursor (read cursor)⟩
                (LocalizedCumulativeTreeRealizes.mk cursor children [] childrenComputed
                  (by simp [terminal]) (by intro tree member; simp at member))⟩
          · simp [childrenComputed, terminal] at built
  | succ fuel ih =>
      intro cursor key built
      unfold CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?
        at built
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at built
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at built
            subst key
            exact ⟨localizedRootTree input cursor (read cursor) [], rfl,
              LocalizedRuleMajorSortTrace.terminal (fuel + 1) cursor children
                childrenComputed terminal
                ⟨treeTableMatch_localizedRootTree_terminal input stage cursor (read cursor),
                  labelTable_localizedRootTree_terminal input stage cursor (read cursor)⟩
                (LocalizedCumulativeTreeRealizes.mk cursor children [] childrenComputed
                  (by simp [terminal]) (by intro tree member; simp at member))⟩
          · cases childKeysComputed : children.mapM
                (CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?
                  input stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at built
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at built
                subst key
                have stepWitness : ∀ (child : input.LocalizedRerootCursor carrierFuel)
                    (childKey : input.LocalizedRerootCumulativeRule45Key),
                    CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?
                      input stage read fuel child = some childKey →
                    ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
                      tree.source = child ∧
                        LocalizedRuleMajorSortTrace input stage read fuel tree childKey := by
                  intro child childKey childBuilt
                  exact ih child childKey childBuilt
                obtain ⟨childTrees, childSource, childRel⟩ :=
                  witnesses_of_mapM_some_actual
                    (CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?
                      input stage read fuel)
                    (fun tree => tree.source)
                    (fun key tree =>
                      LocalizedRuleMajorSortTrace input stage read fuel tree key)
                    stepWitness children childKeys childKeysComputed
                obtain ⟨sortedTrees, sortedRel, sortedPerm⟩ :=
                  List.perm_comp_forall₂
                    (input.sortKeysBy_ruleMajorCumulative_perm (CertifiedLocalizedCIPInput.ruleMajorStageWidth stage) childKeys) childRel
                have sourcePerm :
                    (sortedTrees.map (fun tree => tree.source)).Perm children := by
                  simpa [childSource] using sortedPerm.map (fun tree => tree.source)
                have sortedTableRel : List.Forall₂
                    (fun key tree => LocalizedCumulativeTreeTableMatch stage tree key)
                    (input.sortRuleMajorCumulativeKeys stage childKeys) sortedTrees :=
                  List.Forall₂.imp (fun key tree related =>
                    (LocalizedRuleMajorSortTrace.fullMatch_of_trace related).tableMatch)
                    sortedRel
                have sortedLabelRel : List.Forall₂
                    (fun key tree => LocalizedCumulativeTreeLabelMatch tree key)
                    (input.sortRuleMajorCumulativeKeys stage childKeys) sortedTrees :=
                  List.Forall₂.imp (fun key tree related =>
                    (LocalizedRuleMajorSortTrace.fullMatch_of_trace related).labelMatch)
                    sortedRel
                have sortedRealizes : ∀ tree ∈ sortedTrees,
                    LocalizedCumulativeTreeRealizes input read tree := by
                  intro tree member
                  obtain ⟨key, _, related⟩ :=
                    exists_of_mem_right_forall₂_actual sortedRel tree member
                  exact LocalizedRuleMajorSortTrace.realizes_of_trace related
                have sortedTraced : LocalizedRuleMajorSortTraceList input stage read fuel
                    (input.sortRuleMajorCumulativeKeys stage childKeys) sortedTrees :=
                  LocalizedRuleMajorSortTraceList.of_forall₂ sortedRel
                refine ⟨localizedRootTree input cursor (read cursor) sortedTrees, rfl, ?_⟩
                exact LocalizedRuleMajorSortTrace.node fuel cursor children childKeys
                  (input.sortRuleMajorCumulativeKeys stage childKeys) sortedTrees
                  childrenComputed terminal childKeysComputed rfl
                  (constitutionalDescending_of_ruleMajorDescending input
                    (CertifiedLocalizedCIPInput.ruleMajorStageWidth stage)
                    (input.sortRuleMajorCumulativeKeys stage childKeys)
                    (input.sortKeysBy_ruleMajorCumulative_descending
                      (CertifiedLocalizedCIPInput.ruleMajorStageWidth stage) childKeys))
                  (input.sortKeysBy_ruleMajorCumulative_descending
                    (CertifiedLocalizedCIPInput.ruleMajorStageWidth stage) childKeys)
                  ⟨treeTableMatch_localizedRootTree_branch stage cursor (read cursor)
                      (input.sortRuleMajorCumulativeKeys stage childKeys) sortedTrees
                      sortedTableRel,
                    labelTable_localizedRootTree_branch stage cursor (read cursor)
                      (input.sortRuleMajorCumulativeKeys stage childKeys) sortedTrees
                      sortedLabelRel⟩
                  (LocalizedCumulativeTreeRealizes.mk cursor children sortedTrees
                    childrenComputed sourcePerm sortedRealizes)
                  sortedTraced

/-! ## Adequate-budget existence wrappers

Both wrappers *derive* the build's success from the existing structural at-twice availability
theorems.  Neither takes a successful build as a premise. -/

/-- **Parametric adequate-budget trace existence.**  At twice the carrier depth every path-valid
cursor admits an actual recursive sort trace, for an arbitrary label reader.  The build success is
derived from `exists_buildRuleMajorCumulativeWithRead?_at_twice`. -/
theorem exists_ruleMajorTrace_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
        input.buildRuleMajorCumulativeWithRead? stage read (2 * (carrierFuel + 1)) cursor = some key ∧
          LocalizedRuleMajorSortTrace input stage read (2 * (carrierFuel + 1)) tree key := by
  obtain ⟨key, built⟩ :=
    input.exists_buildRuleMajorCumulativeWithRead_at_twice stage read cursor valid
  obtain ⟨tree, source, trace⟩ :=
    exists_ruleMajorTrace_of_buildWithRead input stage read (2 * (carrierFuel + 1)) cursor key built
  exact ⟨tree, key, source, built, trace⟩

/-! ## Actual original-root arm for the rule-major builder -/

namespace CertifiedLocalizedCIPInput

/-- A successful rule-major builder trace at an actual ligand root, retaining the exact same
tree through the table match, source provenance, generated source tree, faithful expansion and
recursive trace. -/
structure RuleMajorRootArm (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel) where
  key : input.LocalizedRerootCumulativeRule45Key
  tree : LocalizedCumulativeDecoratedTree input
    (input.certified.input.molecule.atomCount + 1)
  built : input.buildRuleMajorCumulativeWithRead? stage read
    (2 * (input.certified.input.molecule.atomCount + 1 + 1))
    (input.localizedLigandRootCursor center index) = some key
  source : tree.source = input.localizedLigandRootCursor center index
  tableMatch : LocalizedCumulativeTreeTableMatch stage tree key
  realizes : LocalizedCumulativeTreeRealizes input read tree
  generated : (toOfficialSourceTree tree).GeneratedBy input.executableOfficialCIPChildren
  root : (toOfficialSourceTree tree).source =
    OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index)
  faithful : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
    (input.canonicalLigandAtom center index) (toOfficialSourceTree tree).toDeclarativeDigraph
  trace : LocalizedRuleMajorSortTrace input stage read
    (2 * (input.certified.input.molecule.atomCount + 1 + 1)) tree key

/-- Every actual original-root cursor has a rule-major-sorted arm at adequate fuel, for an
arbitrary reader. -/
theorem exists_ruleMajorRootArm
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (index : Fin 4) (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel) :
    Nonempty (input.RuleMajorRootArm center index stage read) := by
  let cursor := input.localizedLigandRootCursor center index
  have incoming : LocalizedRerootCursorIncomingParent input cursor :=
    input.localizedLigandRootCursor_incoming center index
  have valid : input.LocalizedRerootCursorValid cursor :=
    input.localizedRerootCursorValid_of_incoming cursor incoming
  obtain ⟨tree, key, source, built, trace⟩ :=
    exists_ruleMajorTrace_at_twice input stage read cursor valid
  have tableMatch : LocalizedCumulativeTreeTableMatch stage tree key :=
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace trace).tableMatch
  have realizes : LocalizedCumulativeTreeRealizes input read tree :=
    LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have positive : LocalizedCumulativeTreePositive tree :=
    input.localizedCumulativeTreePositive_of_atomCount_le
      (fuel := input.certified.input.molecule.atomCount + 1) (by omega) tree
  have treeIncoming : LocalizedCumulativeTreeIncoming input tree := by
    apply input.localizedCumulativeTreeIncoming_of_realizes read tree realizes
    rwa [source]
  have generated : (toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren :=
    input.toOfficialSourceTree_generatedBy read tree realizes positive treeIncoming
  have treeRoot : (toOfficialSourceTree tree).source =
      OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index) := by
    rw [toOfficialSourceTree_source, source]
    exact input.localizedLigandRootNode_eq_rootFromEdge center index
  have faithful : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph
      center.1 (input.canonicalLigandAtom center index)
      (toOfficialSourceTree tree).toDeclarativeDigraph :=
    input.generatedExecutableSourceTree_faithfulExactExpansion (toOfficialSourceTree tree)
      center.1 (input.canonicalLigandAtom center index) generated treeRoot
      (input.canonicalLigandAtom_adj center index)
  exact ⟨⟨key, tree, built, source, tableMatch, realizes, generated, treeRoot, faithful, trace⟩⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTrace
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTraceList
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTraceList.of_forall₂
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTraceList.to_forall₂
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTrace.fullMatch_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTrace.realizes_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTrace.structure_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTrace.node_structure_of_trace
assert_kernel_only TetraStereo.OneCenter.constitutionalCompare_ne_lt_of_ruleMajor_ne_lt
assert_kernel_only TetraStereo.OneCenter.constitutionalDescending_of_ruleMajorDescending
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTrace.sortedDescending_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorSortTrace.childrenTraced_of_trace
assert_kernel_only TetraStereo.OneCenter.exists_ruleMajorTrace_of_buildWithRead
assert_kernel_only TetraStereo.OneCenter.exists_ruleMajorTrace_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorRootArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_ruleMajorRootArm
