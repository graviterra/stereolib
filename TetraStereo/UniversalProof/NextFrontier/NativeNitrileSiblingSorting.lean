import TetraStereo.UniversalProof.NextFrontier.NativeNitrileNitrogenChildren

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

private theorem leaf_self_fast (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    (label : CIPAtomicLabel) (observed : mol.canonicalRule1aLabel? cursor.node = some label)
    (leaf : cursor.node.forcedLeaf = true) (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAt mol fuel stage cursor cursor = some .eq := by
  have nodes (rule : CanonicalRuleStage) :
      mol.compareCanonicalNodeRule? rule cursor.node cursor.node = some .eq := by
    cases rule <;> simp [compareCanonicalNodeRule?, compareCanonicalNodeRule, observed]
  have terminal : cursorTerminal mol cursor = true := by simp [cursorTerminal, leaf]
  cases fuel <;> cases stage <;>
    simp [compareCursorBranchAt, compareCanonicalNodeThrough?, nodes,
      compareCursorRule, compareCursorPairLabels, nextCursorPairs?, terminal,
      defaultBranchWidthCap]

private theorem leaf_self_authoritative (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    (label : CIPAtomicLabel)
    (observed : mol.canonicalRule1aLabelAuthoritative? cursor.node = some label)
    (leaf : cursor.node.forcedLeaf = true) (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? mol fuel stage cursor cursor = some .eq := by
  have nodes (rule : CanonicalRuleStage) :
      mol.compareCanonicalNodeRuleAuthoritative? rule cursor.node cursor.node = some .eq := by
    cases rule <;> simp [compareCanonicalNodeRuleAuthoritative?, compareCanonicalNodeRule, observed]
  have terminal : cursorTerminal mol cursor = true := by simp [cursorTerminal, leaf]
  cases fuel <;> cases stage <;>
    simp [compareCursorBranchAtAuthoritative?, compareCanonicalNodeThroughAuthoritative?, nodes,
      compareCursorRuleAuthoritative?, compareCursorPairLabelsAuthoritative?,
      nextCursorPairsAuthoritative?, terminal]

theorem nitrile_sibling_label_table (parity : TetrahedralInputParity) (n : Nat) :
    ((expanded parity n).canonicalRule1aLabel? realNitrileNitrogen = some ⟨7, 1⟩ ∧
      (expanded parity n).canonicalRule1aLabelAuthoritative? realNitrileNitrogen = some ⟨7, 1⟩) ∧
    ((expanded parity n).canonicalRule1aLabel? nitrileDuplicate = some ⟨7, 1⟩ ∧
      (expanded parity n).canonicalRule1aLabelAuthoritative? nitrileDuplicate = some ⟨7, 1⟩) ∧
    ((expanded parity n).canonicalRule1aLabel? nitrileParentDuplicate = some ⟨6, 1⟩ ∧
      (expanded parity n).canonicalRule1aLabelAuthoritative? nitrileParentDuplicate = some ⟨6, 1⟩) := by
  rcases expanded_local_atomic_numbers parity n with ⟨_, _, carbon, nitrogen, _⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [realNitrileNitrogen, nitrogen] using expanded_natural_labels parity n
      realNitrileNitrogen (by intro distance; simp [realNitrileNitrogen])
  · simpa [nitrileDuplicate, nitrogen] using expanded_natural_labels parity n
      nitrileDuplicate (by intro distance; simp [nitrileDuplicate])
  · simpa [nitrileParentDuplicate, carbon] using expanded_natural_labels parity n
      nitrileParentDuplicate (by intro distance; simp [nitrileParentDuplicate])

theorem actual_nitrile_duplicate_self (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    compareCursorBranchAt (expanded parity n) fuel stage duplicateNitrileCursor
        duplicateNitrileCursor = some .eq ∧
      compareCursorBranchAtAuthoritative? (expanded parity n) fuel stage duplicateNitrileCursor
        duplicateNitrileCursor = some .eq := by
  have labels := (nitrile_sibling_label_table parity n).2.1
  exact ⟨leaf_self_fast _ _ _ labels.1 rfl fuel stage,
    leaf_self_authoritative _ _ _ labels.2 rfl fuel stage⟩

theorem actual_nitrile_parent_duplicate_self (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    compareCursorBranchAt (expanded parity n) fuel stage nitrileParentDuplicateCursor
        nitrileParentDuplicateCursor = some .eq ∧
      compareCursorBranchAtAuthoritative? (expanded parity n) fuel stage nitrileParentDuplicateCursor
        nitrileParentDuplicateCursor = some .eq := by
  have labels := (nitrile_sibling_label_table parity n).2.2
  exact ⟨leaf_self_fast _ _ _ labels.1 rfl fuel stage,
    leaf_self_authoritative _ _ _ labels.2 rfl fuel stage⟩

private def siblingPhantom (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    CanonicalRerootCursor :=
  ⟨mol.canonicalPhantom cursor.node.atom (cursor.node.rule1bRootDistance + 1), none⟩

/-- At positive comparison fuel the real N outranks its terminal duplicate because the real N
has two duplicate carbon children. This is derived from the actual production ranker. -/
theorem actual_real_nitrogen_gt_duplicate_fast (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    compareCursorBranchAt (expanded parity n) (fuel + 1) stage
      realNitrileCursor duplicateNitrileCursor = some .gt := by
  let mol := expanded parity n
  let before := compareCursorBranchAt mol fuel stage
  let leftPad := siblingPhantom mol realNitrileCursor
  let rightPad := siblingPhantom mol duplicateNitrileCursor
  let pairs := [(nitrileParentDuplicateCursor, rightPad),
    (nitrileParentDuplicateCursor, rightPad), (leftPad, rightPad)]
  have table := nitrile_sibling_label_table parity n
  have childSelf := (actual_nitrile_parent_duplicate_self parity n fuel stage).1
  have rootLabel : compareCursorPairLabels mol .rule1a
      [(realNitrileCursor, duplicateNitrileCursor)] = some .eq := by
    simp [compareCursorPairLabels, compareCanonicalNodeRule?, realNitrileCursor,
      duplicateNitrileCursor, mol, table.1.1, table.2.1.1]
  have leftRank : rankedCursorChildren? mol before realNitrileCursor =
      some [nitrileParentDuplicateCursor, nitrileParentDuplicateCursor, leftPad] := by
    simp [rankedCursorChildren?, expanded_real_nitrogen_cursor_children, mol,
      sortCursorsBy?, insertCursorBy?, before, childSelf, leftPad, siblingPhantom]
  have rightRank : rankedCursorChildren? mol before duplicateNitrileCursor =
      some [rightPad, rightPad, rightPad] := by
    simp [rankedCursorChildren?, expanded_duplicate_nitrogen_cursor_children, mol,
      sortCursorsBy?, rightPad, siblingPhantom]
  have leftTerminal : cursorTerminal mol realNitrileCursor = false := by
    unfold cursorTerminal
    change (false || (realNitrileCursor.children (expanded parity n)).isEmpty) = false
    rw [expanded_real_nitrogen_cursor_children]
    rfl
  have rightTerminal : cursorTerminal mol duplicateNitrileCursor = true := rfl
  have next : nextCursorPairs? mol before [(realNitrileCursor, duplicateNitrileCursor)] =
      some pairs := by
    simp [nextCursorPairs?, leftTerminal, rightTerminal, leftRank, rightRank, pairs]
  have childLabels : compareCursorPairLabels mol .rule1a pairs = some .gt := by
    have padLabel : mol.canonicalRule1aLabel? rightPad.node = some ⟨0, 1⟩ := rfl
    have parentLabel : mol.canonicalRule1aLabel? nitrileParentDuplicateCursor.node =
        some ⟨6, 1⟩ := table.2.2.1
    have leading : mol.compareCanonicalNodeRule? .rule1a
        nitrileParentDuplicateCursor.node rightPad.node = some .gt := by
      simp only [compareCanonicalNodeRule?, parentLabel, padLabel, Bind.bind, Option.bind]
      rfl
    simp only [pairs, compareCursorPairLabels, leading]
  have second (depth : Nat) : compareCursorRule mol before .rule1a depth pairs = some .gt := by
    cases depth <;> simp [compareCursorRule, childLabels, pairs, defaultBranchWidthCap]
  have first : compareCursorRule mol before .rule1a (fuel + 1)
      [(realNitrileCursor, duplicateNitrileCursor)] = some .gt := by
    simp [compareCursorRule, rootLabel, next, second, defaultBranchWidthCap]
  dsimp only [before, mol] at first
  simp only [compareCursorBranchAt, first]

theorem actual_real_nitrogen_gt_duplicate_authoritative (parity : TetrahedralInputParity)
    (n fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? (expanded parity n) (fuel + 1) stage
      realNitrileCursor duplicateNitrileCursor = some .gt := by
  let mol := expanded parity n
  let before := compareCursorBranchAtAuthoritative? mol fuel stage
  let leftPad := siblingPhantom mol realNitrileCursor
  let rightPad := siblingPhantom mol duplicateNitrileCursor
  let pairs := [(nitrileParentDuplicateCursor, rightPad),
    (nitrileParentDuplicateCursor, rightPad), (leftPad, rightPad),
    (leftPad, rightPad), (leftPad, rightPad)]
  have table := nitrile_sibling_label_table parity n
  have childSelf := (actual_nitrile_parent_duplicate_self parity n fuel stage).2
  have rootLabel : compareCursorPairLabelsAuthoritative? mol .rule1a
      [(realNitrileCursor, duplicateNitrileCursor)] = some .eq := by
    simp [compareCursorPairLabelsAuthoritative?, compareCanonicalNodeRuleAuthoritative?,
      realNitrileCursor, duplicateNitrileCursor, mol, table.1.2, table.2.1.2]
  have leftRank : rankedCursorChildrenAuthoritative? mol before realNitrileCursor =
      some [nitrileParentDuplicateCursor, nitrileParentDuplicateCursor,
        leftPad, leftPad, leftPad] := by
    simp [rankedCursorChildrenAuthoritative?, expanded_real_nitrogen_cursor_children, mol,
      sortCursorsBy?, insertCursorBy?, before, childSelf, leftPad, siblingPhantom,
      authoritativeChildSlots]
  have rightRank : rankedCursorChildrenAuthoritative? mol before duplicateNitrileCursor =
      some [rightPad, rightPad, rightPad, rightPad, rightPad] := by
    simp [rankedCursorChildrenAuthoritative?, expanded_duplicate_nitrogen_cursor_children, mol,
      sortCursorsBy?, rightPad, siblingPhantom, authoritativeChildSlots]
  have leftTerminal : cursorTerminal mol realNitrileCursor = false := by
    unfold cursorTerminal
    change (false || (realNitrileCursor.children (expanded parity n)).isEmpty) = false
    rw [expanded_real_nitrogen_cursor_children]
    rfl
  have rightTerminal : cursorTerminal mol duplicateNitrileCursor = true := rfl
  have next : nextCursorPairsAuthoritative? mol before
      [(realNitrileCursor, duplicateNitrileCursor)] = some pairs := by
    simp [nextCursorPairsAuthoritative?, leftTerminal, rightTerminal,
      leftRank, rightRank, pairs]
  have childLabels : compareCursorPairLabelsAuthoritative? mol .rule1a pairs = some .gt := by
    have padLabel : mol.canonicalRule1aLabelAuthoritative? rightPad.node = some ⟨0, 1⟩ := rfl
    have parentLabel : mol.canonicalRule1aLabelAuthoritative? nitrileParentDuplicateCursor.node =
        some ⟨6, 1⟩ := table.2.2.2
    have leading : mol.compareCanonicalNodeRuleAuthoritative? .rule1a
        nitrileParentDuplicateCursor.node rightPad.node = some .gt := by
      simp only [compareCanonicalNodeRuleAuthoritative?, parentLabel, padLabel, Bind.bind, Option.bind]
      rfl
    simp only [pairs, compareCursorPairLabelsAuthoritative?, leading]
  have second (depth : Nat) :
      compareCursorRuleAuthoritative? mol before .rule1a depth pairs = some .gt := by
    cases depth <;> simp [compareCursorRuleAuthoritative?, childLabels]
  have first : compareCursorRuleAuthoritative? mol before .rule1a (fuel + 1)
      [(realNitrileCursor, duplicateNitrileCursor)] = some .gt := by
    simp [compareCursorRuleAuthoritative?, rootLabel, next, second]
  dsimp only [before, mol] at first
  simp only [compareCursorBranchAtAuthoritative?, first]

theorem actual_nitrile_sibling_sort (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    sortCursorsBy? (compareCursorBranchAt (expanded parity n) (fuel + 1) stage)
        (nitrileCursor.children (expanded parity n)) =
        some [realNitrileCursor, duplicateNitrileCursor, duplicateNitrileCursor] ∧
      sortCursorsBy? (compareCursorBranchAtAuthoritative? (expanded parity n) (fuel + 1) stage)
        (nitrileCursor.children (expanded parity n)) =
        some [realNitrileCursor, duplicateNitrileCursor, duplicateNitrileCursor] := by
  have self := actual_nitrile_duplicate_self parity n (fuel + 1) stage
  have fast := actual_real_nitrogen_gt_duplicate_fast parity n fuel stage
  have authoritative := actual_real_nitrogen_gt_duplicate_authoritative parity n fuel stage
  simp [expanded_nitrile_cursor_children, sortCursorsBy?, insertCursorBy?,
    self.1, self.2, fast, authoritative]

/-- The second sorted N is the actual duplicate occurrence emitted by the triple bond.
This reads the production sort result, including its branch comparison callbacks. -/
theorem actual_sorted_second_nitrogen_provenance (parity : TetrahedralInputParity)
    (n fuel : Nat) (stage : CanonicalRuleStage) :
    (sortCursorsBy? (compareCursorBranchAtAuthoritative? (expanded parity n) (fuel + 1) stage)
      (nitrileCursor.children (expanded parity n))).bind (fun sorted =>
        (sorted[1]?).map (fun cursor => cursor.node.provenance)) =
      some (.multipleBondDuplicate 1) := by
  rw [(actual_nitrile_sibling_sort parity n fuel stage).2]
  rfl

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
