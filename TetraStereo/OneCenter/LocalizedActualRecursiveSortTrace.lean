import TetraStereo.OneCenter.LocalizedCumulativeTreeObservableFaithfulness
import TetraStereo.OneCenter.LocalizedOuterDigraphConstitutionalPriority
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.FullStateParentNoninterference
import TetraStereo.KernelOnly
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
































































/-! ## The actual key emitted at one builder step -/

/-- The exact cumulative Rules-4a--5 key emitted by the actual builder at a terminal occurrence:
the raw official root-node observations together with the root-only descriptor, label and
ranked-label spheres.  This is the literal structure produced by the shipped builder's terminal
branch. -/
abbrev localizedCumulativeRule45TerminalKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel) :
    input.LocalizedRerootCumulativeRule45Key :=
  { constitutional := input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
    labels := [[([], label)]]
    rankedLabels := [[([], label)]] }

/-- The exact cumulative Rules-4a--5 key emitted by the actual builder at a nonterminal
occurrence: the actual `OfficialRuleMajorKey.assemble` of the raw root projection with the
*actual sorted* child constitutional components, followed by the actual descriptor, label and
ranked-label merges over those same sorted child keys. -/
abbrev localizedCumulativeRule45StepKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (sortedKeys : List input.LocalizedRerootCumulativeRule45Key) :
    input.LocalizedRerootCumulativeRule45Key :=
  { constitutional := OfficialRuleMajorKey.assemble
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
      (sortedKeys.map fun child => child.constitutional)
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
      input.mergeLocalizedRerootDescriptorChildren sortedKeys
    labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sortedKeys
    rankedLabels := [[([], label)]] ++ input.mergeLocalizedRerootRankedLabelChildren sortedKeys }








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

/-! ## The recursive actual build/sort certificate -/

mutual














  inductive LocalizedActualRecursiveSortTrace
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
        LocalizedActualRecursiveSortTrace input stage read fuel
          (localizedRootTree input cursor (read cursor) [])
          (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
    | node (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
        (children : List (input.LocalizedRerootCursor carrierFuel))
        (childKeys sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
        (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
        (childrenComputed : input.localizedRerootChildren? cursor = some children)
        (nonempty : children ≠ [])
        (childKeysComputed : children.mapM
          (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel) =
            some childKeys)
        (sortedEq : sortedKeys = input.sortLocalizedRerootCumulativeRule45Keys childKeys)
        (constitutionalDescending : OfficialRuleMajorKey.Descending
          (sortedKeys.map fun child => child.constitutional))
        (fullMatch : LocalizedCumulativeTreeFullMatch stage
          (localizedRootTree input cursor (read cursor) sortedTrees)
          (localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys))
        (realizes : LocalizedCumulativeTreeRealizes input read
          (localizedRootTree input cursor (read cursor) sortedTrees))
        (childrenTraced : LocalizedActualRecursiveSortTraceList input stage read fuel
          sortedKeys sortedTrees) :
        LocalizedActualRecursiveSortTrace input stage read (fuel + 1)
          (localizedRootTree input cursor (read cursor) sortedTrees)
          (localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys)

  /-- The list form of the recursive certificate: a certificate for every sorted key together with
  the matching actual child tree, at one common fuel. -/
  inductive LocalizedActualRecursiveSortTraceList
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
      Nat → List input.LocalizedRerootCumulativeRule45Key →
        List (LocalizedCumulativeDecoratedTree input carrierFuel) → Prop where
    | nil (fuel : Nat) :
        LocalizedActualRecursiveSortTraceList input stage read fuel [] []
    | cons (fuel : Nat)
        (headKey : input.LocalizedRerootCumulativeRule45Key)
        (tailKeys : List input.LocalizedRerootCumulativeRule45Key)
        (headTree : LocalizedCumulativeDecoratedTree input carrierFuel)
        (tailTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
        (head : LocalizedActualRecursiveSortTrace input stage read fuel headTree headKey)
        (tail : LocalizedActualRecursiveSortTraceList input stage read fuel tailKeys tailTrees) :
        LocalizedActualRecursiveSortTraceList input stage read fuel
          (headKey :: tailKeys) (headTree :: tailTrees)
end

/-- A `Forall₂` pairing of sorted keys with trees through traces is exactly a list certificate. -/
theorem LocalizedActualRecursiveSortTraceList.of_forall₂
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} :
    ∀ {keys : List input.LocalizedRerootCumulativeRule45Key}
      {trees : List (LocalizedCumulativeDecoratedTree input carrierFuel)},
      List.Forall₂
        (fun key tree => LocalizedActualRecursiveSortTrace input stage read fuel tree key)
        keys trees →
      LocalizedActualRecursiveSortTraceList input stage read fuel keys trees
  | _, _, .nil => .nil fuel
  | _, _, .cons head tail => .cons fuel _ _ _ _ head (of_forall₂ tail)

/-- A list certificate exposes the `Forall₂` pairing of sorted keys with trees through traces. -/
theorem LocalizedActualRecursiveSortTraceList.to_forall₂
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} :
    ∀ {keys : List input.LocalizedRerootCumulativeRule45Key}
      {trees : List (LocalizedCumulativeDecoratedTree input carrierFuel)},
      LocalizedActualRecursiveSortTraceList input stage read fuel keys trees →
      List.Forall₂
        (fun key tree => LocalizedActualRecursiveSortTrace input stage read fuel tree key)
        keys trees
  | _, _, .nil _ => .nil
  | _, _, .cons _ _ _ _ _ head tail => .cons head (to_forall₂ tail)

/-! ## Projections of the certificate -/


theorem LocalizedActualRecursiveSortTrace.fullMatch_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read fuel tree key) :
    LocalizedCumulativeTreeFullMatch stage tree key := by
  cases trace with
  | terminal fuel cursor children childrenComputed terminalChildren fullMatch realizes =>
      exact fullMatch
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq constitutionalDescending fullMatch realizes childrenTraced =>
      exact fullMatch


theorem LocalizedActualRecursiveSortTrace.realizes_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read fuel tree key) :
    LocalizedCumulativeTreeRealizes input read tree := by
  cases trace with
  | terminal fuel cursor children childrenComputed terminalChildren fullMatch realizes =>
      exact realizes
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq constitutionalDescending fullMatch realizes childrenTraced =>
      exact realizes

/-- **Complete per-node case analysis of a trace at a nonterminal fuel.**

Either the occurrence is terminal — the actual frame's children are `[]`, the tree is the
root-only tree at the actual cursor and the key is the terminal key — or it is a genuine builder
step, exposing the actual frame, the actual raw child keys of the actual `mapM` at the decreased
fuel, the exact production sort equation, the constitutional descending order of the actual sorted
keys and the recursive certificate for every sorted child. -/
theorem LocalizedActualRecursiveSortTrace.structure_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read (fuel + 1) tree key) :
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
                        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel) =
                      some childKeys ∧
                      sortedKeys = input.sortLocalizedRerootCumulativeRule45Keys childKeys ∧
                        OfficialRuleMajorKey.Descending
                          (sortedKeys.map fun child => child.constitutional) ∧
                          LocalizedActualRecursiveSortTraceList input stage read fuel
                            sortedKeys sortedTrees) := by
  cases trace with
  | terminal fuel cursor children childrenComputed terminalChildren fullMatch realizes =>
      exact Or.inl ⟨cursor, children, rfl, rfl, rfl, childrenComputed, terminalChildren⟩
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq constitutionalDescending fullMatch realizes childrenTraced =>
      exact Or.inr ⟨cursor, children, childKeys, sortedKeys, sortedTrees, rfl, rfl, rfl,
        childrenComputed, nonempty, childKeysComputed, sortedEq, constitutionalDescending,
        childrenTraced⟩





theorem LocalizedActualRecursiveSortTrace.node_structure_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read (fuel + 1) tree key)
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
                    (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel) =
                  some childKeys ∧
                  sortedKeys = input.sortLocalizedRerootCumulativeRule45Keys childKeys ∧
                    OfficialRuleMajorKey.Descending
                      (sortedKeys.map fun child => child.constitutional) ∧
                      LocalizedActualRecursiveSortTraceList input stage read fuel
                        sortedKeys sortedTrees := by
  rcases LocalizedActualRecursiveSortTrace.structure_of_trace trace with
    ⟨_, _, _, _, terminalChildren, _, _⟩ | nodeData
  · exact absurd terminalChildren nonemptyTree
  · exact nodeData





theorem LocalizedActualRecursiveSortTrace.constitutionalDescending_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read (fuel + 1) tree key)
    (nonemptyTree : tree.children ≠ []) :
    ∃ (childKeys sortedKeys : List input.LocalizedRerootCumulativeRule45Key),
      sortedKeys = input.sortLocalizedRerootCumulativeRule45Keys childKeys ∧
        OfficialRuleMajorKey.Descending (sortedKeys.map fun child => child.constitutional) := by
  obtain ⟨_, _, childKeys, sortedKeys, _, _, _, _, _, _, _, sortedEq, descending, _⟩ :=
    LocalizedActualRecursiveSortTrace.node_structure_of_trace trace nonemptyTree
  exact ⟨childKeys, sortedKeys, sortedEq, descending⟩

/-- **Recursive sub-certificates.**  Every actual child tree of a nonterminal traced node is
paired with its actual sorted key through a trace at the decreased fuel, in the `Forall₂` form. -/
theorem LocalizedActualRecursiveSortTrace.childrenTraced_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read (fuel + 1) tree key)
    (nonemptyTree : tree.children ≠ []) :
    ∃ sortedKeys : List input.LocalizedRerootCumulativeRule45Key,
      List.Forall₂
        (fun childKey childTree =>
          LocalizedActualRecursiveSortTrace input stage read fuel childTree childKey)
        sortedKeys tree.children := by
  obtain ⟨_, _, _, sortedKeys, sortedTrees, _, _, childrenEq, _, _, _, _, _,
    childrenTraced⟩ :=
    LocalizedActualRecursiveSortTrace.node_structure_of_trace trace nonemptyTree
  exact ⟨sortedKeys, by
    rw [childrenEq]
    exact LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced⟩

/-! ## Extraction from an actual successful build -/









theorem exists_trace_of_buildWithRead
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
        input stage read fuel cursor = some key →
      ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
        tree.source = cursor ∧
          LocalizedActualRecursiveSortTrace input stage read fuel tree key := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key built
      unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
        at built
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at built
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at built
            subst key
            exact ⟨localizedRootTree input cursor (read cursor) [], rfl,
              LocalizedActualRecursiveSortTrace.terminal 0 cursor children childrenComputed
                terminal
                ⟨treeTableMatch_localizedRootTree_terminal input stage cursor (read cursor),
                  labelTable_localizedRootTree_terminal input stage cursor (read cursor)⟩
                (LocalizedCumulativeTreeRealizes.mk cursor children [] childrenComputed
                  (by simp [terminal]) (by intro tree member; simp at member))⟩
          · simp [childrenComputed, terminal] at built
  | succ fuel ih =>
      intro cursor key built
      unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
        at built
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at built
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at built
            subst key
            exact ⟨localizedRootTree input cursor (read cursor) [], rfl,
              LocalizedActualRecursiveSortTrace.terminal (fuel + 1) cursor children
                childrenComputed terminal
                ⟨treeTableMatch_localizedRootTree_terminal input stage cursor (read cursor),
                  labelTable_localizedRootTree_terminal input stage cursor (read cursor)⟩
                (LocalizedCumulativeTreeRealizes.mk cursor children [] childrenComputed
                  (by simp [terminal]) (by intro tree member; simp at member))⟩
          · cases childKeysComputed : children.mapM
                (CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  input stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at built
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at built
                subst key
                have stepWitness : ∀ (child : input.LocalizedRerootCursor carrierFuel)
                    (childKey : input.LocalizedRerootCumulativeRule45Key),
                    CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      input stage read fuel child = some childKey →
                    ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
                      tree.source = child ∧
                        LocalizedActualRecursiveSortTrace input stage read fuel tree childKey := by
                  intro child childKey childBuilt
                  exact ih child childKey childBuilt
                obtain ⟨childTrees, childSource, childRel⟩ :=
                  witnesses_of_mapM_some_actual
                    (CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      input stage read fuel)
                    (fun tree => tree.source)
                    (fun key tree =>
                      LocalizedActualRecursiveSortTrace input stage read fuel tree key)
                    stepWitness children childKeys childKeysComputed
                obtain ⟨sortedTrees, sortedRel, sortedPerm⟩ :=
                  List.perm_comp_forall₂
                    (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys) childRel
                have sourcePerm :
                    (sortedTrees.map (fun tree => tree.source)).Perm children := by
                  simpa [childSource] using sortedPerm.map (fun tree => tree.source)
                have sortedTableRel : List.Forall₂
                    (fun key tree => LocalizedCumulativeTreeTableMatch stage tree key)
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys) sortedTrees :=
                  List.Forall₂.imp (fun key tree related =>
                    (LocalizedActualRecursiveSortTrace.fullMatch_of_trace related).tableMatch)
                    sortedRel
                have sortedLabelRel : List.Forall₂
                    (fun key tree => LocalizedCumulativeTreeLabelMatch tree key)
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys) sortedTrees :=
                  List.Forall₂.imp (fun key tree related =>
                    (LocalizedActualRecursiveSortTrace.fullMatch_of_trace related).labelMatch)
                    sortedRel
                have sortedRealizes : ∀ tree ∈ sortedTrees,
                    LocalizedCumulativeTreeRealizes input read tree := by
                  intro tree member
                  obtain ⟨key, _, related⟩ :=
                    exists_of_mem_right_forall₂_actual sortedRel tree member
                  exact LocalizedActualRecursiveSortTrace.realizes_of_trace related
                have sortedTraced : LocalizedActualRecursiveSortTraceList input stage read fuel
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys) sortedTrees :=
                  LocalizedActualRecursiveSortTraceList.of_forall₂ sortedRel
                refine ⟨localizedRootTree input cursor (read cursor) sortedTrees, rfl, ?_⟩
                exact LocalizedActualRecursiveSortTrace.node fuel cursor children childKeys
                  (input.sortLocalizedRerootCumulativeRule45Keys childKeys) sortedTrees
                  childrenComputed terminal childKeysComputed rfl
                  (input.sortLocalizedRerootCumulativeRule45Keys_constitutional_descending
                    childKeys)
                  ⟨treeTableMatch_localizedRootTree_branch stage cursor (read cursor)
                      (input.sortLocalizedRerootCumulativeRule45Keys childKeys) sortedTrees
                      sortedTableRel,
                    labelTable_localizedRootTree_branch stage cursor (read cursor)
                      (input.sortLocalizedRerootCumulativeRule45Keys childKeys) sortedTrees
                      sortedLabelRel⟩
                  (LocalizedCumulativeTreeRealizes.mk cursor children sortedTrees
                    childrenComputed sourcePerm sortedRealizes)
                  sortedTraced

/-! ## Adequate-budget existence wrappers

Both wrappers *derive* the build's success from the existing structural at-twice availability
theorems.  Neither takes a successful build as a premise. -/

/-- **Parametric adequate-budget trace existence.**  At twice the carrier depth every path-valid
cursor admits an actual recursive sort trace, for an arbitrary label reader.  The build success is
derived from `exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice`. -/
theorem exists_trace_of_buildWithRead_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
        LocalizedActualRecursiveSortTrace input stage read (2 * (carrierFuel + 1)) tree key := by
  obtain ⟨key, built⟩ :=
    CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input stage read cursor valid
  obtain ⟨tree, source, trace⟩ :=
    exists_trace_of_buildWithRead input stage read (2 * (carrierFuel + 1)) cursor key built
  exact ⟨tree, key, source, trace⟩

/-- **Production adequate-budget trace existence.**  At twice the carrier depth every path-valid
cursor admits an actual recursive sort trace for the shipped production builder.  The production
build is first transported to the parametric builder by
`buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel`, and its success is
derived from `exists_buildLocalizedRerootCumulativeRule45Key?_at_twice`; no build success is
assumed. -/
theorem exists_trace_of_build_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
        LocalizedCumulativeTreeFullMatch stage tree key ∧
          LocalizedCumulativeTreeRealizes input
              (fun occurrence => input.localizedDependencyLabel target view occurrence) tree ∧
            LocalizedActualRecursiveSortTrace input stage
              (fun occurrence => input.localizedDependencyLabel target view occurrence)
              (2 * (carrierFuel + 1)) tree key := by
  obtain ⟨key, built⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      stage target view cursor valid
  have withRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun occurrence => input.localizedDependencyLabel target view occurrence)
      (2 * (carrierFuel + 1)) cursor = some key := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      stage target view]
    exact built
  obtain ⟨tree, source, trace⟩ :=
    exists_trace_of_buildWithRead input stage
      (fun occurrence => input.localizedDependencyLabel target view occurrence)
      (2 * (carrierFuel + 1)) cursor key withRead
  exact ⟨tree, key, source,
    LocalizedActualRecursiveSortTrace.fullMatch_of_trace trace,
    LocalizedActualRecursiveSortTrace.realizes_of_trace trace, trace⟩

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.localizedCumulativeRule45TerminalKey
assert_kernel_only TetraStereo.OneCenter.localizedCumulativeRule45StepKey
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTraceList
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTraceList.of_forall₂
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTraceList.to_forall₂
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace.fullMatch_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace.realizes_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace.structure_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace.node_structure_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace.constitutionalDescending_of_trace
assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace.childrenTraced_of_trace
assert_kernel_only TetraStereo.OneCenter.exists_trace_of_buildWithRead
assert_kernel_only TetraStereo.OneCenter.exists_trace_of_buildWithRead_at_twice
assert_kernel_only TetraStereo.OneCenter.exists_trace_of_build_at_twice
