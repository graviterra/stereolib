import TetraStereo.UniversalProof.NextFrontier.NativeNitrileRuntimeSecondSphere
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileCycleExclusion
import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge

/-!
The initial descriptor seed consumes canonical nodes through `compareBranches?`, separately from
the occurrence-cursor comparator. The family results below derive its actual child ranks and
dispatch guards from the expanded physical records, for every tail length and both parities.
They do not assert discovery, a source-model correspondence, or external chemical approval.
-/

private theorem supported_leaf_self (mol : RawMolecule) (node : CanonicalBranchNode)
    (label : CIPAtomicLabel) (observed : mol.canonicalRule1aLabel? node = some label)
    (leaf : node.forcedLeaf = true) (fuel : Nat) (stage : CanonicalRuleStage) :
    mol.compareCanonicalBranchAtSupported? fuel stage node node = some .eq := by
  have labels (rule : CanonicalRuleStage) :
      mol.compareCanonicalNodeRule? rule node node = some .eq := by
    cases rule <;> simp [compareCanonicalNodeRule?, compareCanonicalNodeRule, observed]
  have terminal : mol.canonicalTerminal node = true := by simp [canonicalTerminal, leaf]
  cases fuel <;> cases stage <;>
    simp [compareCanonicalBranchAtSupported?, compareCanonicalNodeThrough?, labels,
      compareCanonicalRuleSupported?, compareCanonicalPairLabels?, nextCanonicalPairs?,
      terminal, defaultBranchWidthCap]

/-- An exact next-sphere triple and its strict local label decision suffice. Neither premise
asserts the requested root comparison, and family callers derive both from production ranks. -/
private theorem supported_of_next_three (mol : RawMolecule) (fuel : Nat)
    (stage : CanonicalRuleStage) (left right a b c d e f : CanonicalBranchNode)
    (decision : Ordering)
    (rootTie : mol.compareCanonicalNodeRule? .rule1a left right = some .eq)
    (next : mol.nextCanonicalPairs? (mol.compareCanonicalBranchAtSupported? fuel stage)
      [(left, right)] = some [(a, d), (b, e), (c, f)])
    (labels : mol.compareCanonicalPairLabels? .rule1a [(a, d), (b, e), (c, f)] =
      some decision) (strict : decision ≠ .eq) :
    mol.compareCanonicalBranchAtSupported? (fuel + 1) stage left right = some decision := by
  let before := mol.compareCanonicalBranchAtSupported? fuel stage
  have second (depth : Nat) :
      mol.compareCanonicalRuleSupported? before .rule1a defaultBranchWidthCap depth
        [(a, d), (b, e), (c, f)] = some decision := by
    cases depth <;> cases decision <;>
      simp_all [compareCanonicalRuleSupported?, defaultBranchWidthCap]
  have first : mol.compareCanonicalRuleSupported? before .rule1a defaultBranchWidthCap
      (fuel + 1) [(left, right)] = some decision := by
    simp [compareCanonicalRuleSupported?, compareCanonicalPairLabels?, rootTie,
      next, before, defaultBranchWidthCap]
    exact second fuel
  dsimp only [before] at first
  cases decision with
  | eq => exact (strict rfl).elim
  | lt => simp only [compareCanonicalBranchAtSupported?, first]
  | gt => simp only [compareCanonicalBranchAtSupported?, first]

/-- The real nitrogen outranks its nitrogen duplicate in the actual canonical-node sorter:
the former retains two carbon duplicates, while the latter is a forced leaf. -/
theorem actual_initial_real_nitrogen_gt_duplicate (parity : TetrahedralInputParity)
    (n fuel : Nat) (stage : CanonicalRuleStage) :
    (expanded parity n).compareCanonicalBranchAtSupported? (fuel + 1) stage
      realNitrileNitrogen nitrileDuplicate = some .gt := by
  let mol := expanded parity n
  let before := mol.compareCanonicalBranchAtSupported? fuel stage
  let leftPad := mol.canonicalPhantom realNitrileNitrogen.atom
    (realNitrileNitrogen.rule1bRootDistance + 1)
  let rightPad := mol.canonicalPhantom nitrileDuplicate.atom
    (nitrileDuplicate.rule1bRootDistance + 1)
  have table := nitrile_sibling_label_table parity n
  have childSelf : before nitrileParentDuplicate nitrileParentDuplicate = some .eq :=
    supported_leaf_self mol nitrileParentDuplicate _ table.2.2.1 rfl fuel stage
  have leftRank : mol.rankedCanonicalChildren? before realNitrileNitrogen =
      some [nitrileParentDuplicate, nitrileParentDuplicate, leftPad] := by
    simp [rankedCanonicalChildren?, expanded_nitrogen_children, mol,
      sortCanonicalBy?, insertCanonicalBy?, childSelf, leftPad]
  have rightChildren : mol.canonicalChildren nitrileDuplicate = [] := rfl
  have rightRank : mol.rankedCanonicalChildren? before nitrileDuplicate =
      some [rightPad, rightPad, rightPad] := by
    simp [rankedCanonicalChildren?, rightChildren, sortCanonicalBy?, rightPad]
  have leftLive : mol.canonicalTerminal realNitrileNitrogen = false := by
    change (false || ((expanded parity n).canonicalChildren realNitrileNitrogen).isEmpty) = false
    rw [expanded_nitrogen_children]
    rfl
  have rightLeaf : mol.canonicalTerminal nitrileDuplicate = true := rfl
  have rootTie : mol.compareCanonicalNodeRule? .rule1a realNitrileNitrogen nitrileDuplicate =
      some .eq := by
    simp [compareCanonicalNodeRule?, mol, table.1.1, table.2.1.1]
  apply supported_of_next_three mol fuel stage realNitrileNitrogen nitrileDuplicate
    nitrileParentDuplicate nitrileParentDuplicate leftPad rightPad rightPad rightPad .gt rootTie
  · simp [nextCanonicalPairs?, leftLive, rightLeaf, leftRank, rightRank, before]
  · have padLabel : mol.canonicalRule1aLabel? rightPad = some ⟨0, 1⟩ := rfl
    have parentLabel : mol.canonicalRule1aLabel? nitrileParentDuplicate = some ⟨6, 1⟩ := table.2.2.1
    have leading : mol.compareCanonicalNodeRule? .rule1a nitrileParentDuplicate rightPad = some .gt := by
      simp only [compareCanonicalNodeRule?, parentLabel, padLabel, Bind.bind, Option.bind]
      rfl
    simp only [compareCanonicalPairLabels?, leading]
  · decide

/-- The exact actual nitrile child block sorts to real N followed by its two duplicates. -/
theorem actual_initial_nitrile_sort (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    sortCanonicalBy? ((expanded parity n).compareCanonicalBranchAtSupported? (fuel + 1) stage)
      ((expanded parity n).canonicalChildren (canonicalRoot 0 2)) =
        some [realNitrileNitrogen, nitrileDuplicate, nitrileDuplicate] := by
  have self := supported_leaf_self (expanded parity n) nitrileDuplicate _
    (nitrile_sibling_label_table parity n).2.1.1 rfl (fuel + 1) stage
  have strict := actual_initial_real_nitrogen_gt_duplicate parity n fuel stage
  simp [expanded_nitrile_children_exact, sortCanonicalBy?, insertCanonicalBy?, self, strict]

theorem actual_initial_amino_children (parity : TetrahedralInputParity) (n : Nat) :
    ((expanded parity n).canonicalChildren (canonicalRoot 0 4)).Perm
      [(aminoChild (n + 8)).node, (aminoChild 5).node, (aminoChild 6).node] := by
  let physical := (recordNeighbors (expanded parity n) 4).erase 0
  have projected : physical.Perm [n + 8, 5, 6] := by
    simpa using (expanded_amino_records parity n).erase 0
  have fresh : ∀ atom ∈ physical, atom ∉ [4, 0] := by
    intro atom retained
    have member := projected.mem_iff.mp retained
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega
    · decide
    · decide
  have actual := actual_path_children (expanded parity n) 4 0 [] physical rfl
    (fun other retained => expanded_record_order_one parity n 4 other
      (by decide) (by decide) retained) fresh
  change (expanded parity n).canonicalChildren (canonicalRoot 0 4) =
    physical.map (fun atom => (aminoChild atom).node) at actual
  rw [actual]
  exact projected.map (fun atom => (aminoChild atom).node)

private theorem initial_amino_pair (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) (left right leftZ rightZ : Nat)
    (leftObserved : (expanded parity n).atomZAt left = leftZ)
    (rightObserved : (expanded parity n).atomZAt right = rightZ)
    (strict : compare leftZ rightZ ≠ .eq) :
    (expanded parity n).compareCanonicalBranchAtSupported? fuel stage
      (aminoChild left).node (aminoChild right).node = some (compare leftZ rightZ) := by
  have labels := compareCanonicalNodeRule?_rule1a_realAtom (expanded parity n)
    (aminoChild left).node (aminoChild right).node rfl rfl
  change (expanded parity n).compareCanonicalNodeRule? .rule1a _ _ =
    some (compare ((expanded parity n).atomZAt left) ((expanded parity n).atomZAt right)) at labels
  rw [leftObserved, rightObserved] at labels
  cases fuel with
  | zero => exact compareCanonicalNodeThrough?_eq_of_rule1a _ stage _ _ _ labels strict
  | succ fuel =>
      have sphere : (expanded parity n).compareCanonicalPairLabels? .rule1a
          [((aminoChild left).node, (aminoChild right).node)] =
          some (compare leftZ rightZ) := by
        cases decision : compare leftZ rightZ <;>
          simp_all [compareCanonicalPairLabels?]
      cases decision : compare leftZ rightZ <;>
        simp_all [compareCanonicalBranchAtSupported?, compareCanonicalRuleSupported?,
          defaultBranchWidthCap]

/-- The actual aminoalkyl canonical children sort N, C, H, including the n=0 methyl case. -/
theorem actual_initial_amino_sort (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    sortCanonicalBy? ((expanded parity n).compareCanonicalBranchAtSupported? fuel stage)
      ((expanded parity n).canonicalChildren (canonicalRoot 0 4)) =
        some [(aminoChild 5).node, (aminoChild 6).node, (aminoChild (n + 8)).node] := by
  rcases expanded_local_atomic_numbers parity n with
    ⟨_, _, _, _, _, nitrogen, carbon, _, hydrogen⟩
  have nc := initial_amino_pair parity n fuel stage 5 6 7 6 nitrogen carbon (by decide)
  have nh := initial_amino_pair parity n fuel stage 5 (n + 8) 7 1 nitrogen hydrogen (by decide)
  have ch := initial_amino_pair parity n fuel stage 6 (n + 8) 6 1 carbon hydrogen (by decide)
  have cn := initial_amino_pair parity n fuel stage 6 5 6 7 carbon nitrogen (by decide)
  have hn := initial_amino_pair parity n fuel stage (n + 8) 5 1 7 hydrogen nitrogen (by decide)
  have hc := initial_amino_pair parity n fuel stage (n + 8) 6 1 6 hydrogen carbon (by decide)
  change _ = some Ordering.gt at nc
  change _ = some Ordering.gt at nh
  change _ = some Ordering.gt at ch
  change _ = some Ordering.lt at cn
  change _ = some Ordering.lt at hn
  change _ = some Ordering.lt at hc
  have retained := List.mem_permutations'.mpr (actual_initial_amino_children parity n)
  change (expanded parity n).canonicalChildren (canonicalRoot 0 4) ∈
    [[(aminoChild (n + 8)).node, (aminoChild 5).node, (aminoChild 6).node],
     [(aminoChild 5).node, (aminoChild (n + 8)).node, (aminoChild 6).node],
     [(aminoChild 5).node, (aminoChild 6).node, (aminoChild (n + 8)).node],
     [(aminoChild (n + 8)).node, (aminoChild 6).node, (aminoChild 5).node],
     [(aminoChild 6).node, (aminoChild (n + 8)).node, (aminoChild 5).node],
     [(aminoChild 6).node, (aminoChild 5).node, (aminoChild (n + 8)).node]] at retained
  simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
  rcases retained with orderEq | orderEq | orderEq | orderEq | orderEq | orderEq <;>
    simp [orderEq, sortCanonicalBy?, insertCanonicalBy?, nc, nh, ch, cn, hn, hc]

/-- Both actual canonical comparisons use the tied first N pair and strict duplicate-N/C pair.
The extra fuel step establishes the real-N/duplicate-N ordering used by the recursive sorter. -/
theorem actual_initial_supported_both (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    (expanded parity n).compareCanonicalBranchAtSupported? (fuel + 2) stage
        (canonicalRoot 0 2) (canonicalRoot 0 4) = some .gt ∧
      (expanded parity n).compareCanonicalBranchAtSupported? (fuel + 2) stage
        (canonicalRoot 0 4) (canonicalRoot 0 2) = some .lt := by
  let mol := expanded parity n
  let before := mol.compareCanonicalBranchAtSupported? (fuel + 1) stage
  have leftCount : (mol.canonicalChildren (canonicalRoot 0 2)).length = 3 := by
    rw [expanded_nitrile_children_exact]
    rfl
  have rightCount : (mol.canonicalChildren (canonicalRoot 0 4)).length = 3 :=
    (actual_initial_amino_children parity n).length_eq
  have leftRank : mol.rankedCanonicalChildren? before (canonicalRoot 0 2) =
      some [realNitrileNitrogen, nitrileDuplicate, nitrileDuplicate] := by
    simp [rankedCanonicalChildren?, leftCount, before,
      actual_initial_nitrile_sort parity n fuel stage, mol]
  have rightRank : mol.rankedCanonicalChildren? before (canonicalRoot 0 4) =
      some [(aminoChild 5).node, (aminoChild 6).node, (aminoChild (n + 8)).node] := by
    simp [rankedCanonicalChildren?, rightCount, before,
      actual_initial_amino_sort parity n (fuel + 1) stage, mol]
  have leftLive : mol.canonicalTerminal (canonicalRoot 0 2) = false := by
    change (false || (mol.canonicalChildren (canonicalRoot 0 2)).isEmpty) = false
    rw [expanded_nitrile_children_exact]
    rfl
  have rightLive : mol.canonicalTerminal (canonicalRoot 0 4) = false := by
    have nonempty : mol.canonicalChildren (canonicalRoot 0 4) ≠ [] := by
      intro empty
      rw [empty] at rightCount
      cases rightCount
    change (false || (mol.canonicalChildren (canonicalRoot 0 4)).isEmpty) = false
    simpa only [Bool.false_or, List.isEmpty_eq_false_iff] using nonempty
  rcases expanded_local_atomic_numbers parity n with ⟨_, _, nitrileZ, _, aminoZ, _⟩
  have rootForward := compareCanonicalNodeRule?_rule1a_realAtom mol
    (canonicalRoot 0 2) (canonicalRoot 0 4) rfl rfl
  have rootReverse := compareCanonicalNodeRule?_rule1a_realAtom mol
    (canonicalRoot 0 4) (canonicalRoot 0 2) rfl rfl
  change mol.compareCanonicalNodeRule? .rule1a _ _ =
    some (compare (mol.atomZAt 2) (mol.atomZAt 4)) at rootForward
  change mol.compareCanonicalNodeRule? .rule1a _ _ =
    some (compare (mol.atomZAt 4) (mol.atomZAt 2)) at rootReverse
  rw [nitrileZ, aminoZ] at rootForward rootReverse
  have observations := actual_nitrile_amino_child_labels parity n
  have forwardFirst : mol.compareCanonicalNodeRule? .rule1a realNitrileNitrogen (aminoChild 5).node =
      some .eq := observations.1.1
  have forwardSecond : mol.compareCanonicalNodeRule? .rule1a nitrileDuplicate (aminoChild 6).node =
      some .gt := observations.2.1.1
  have reverseFirst : mol.compareCanonicalNodeRule? .rule1a (aminoChild 5).node realNitrileNitrogen =
      some .eq := observations.2.2.1.1
  have reverseSecond : mol.compareCanonicalNodeRule? .rule1a (aminoChild 6).node nitrileDuplicate =
      some .lt := observations.2.2.2.1
  constructor
  · apply supported_of_next_three mol (fuel + 1) stage (canonicalRoot 0 2) (canonicalRoot 0 4)
      realNitrileNitrogen nitrileDuplicate nitrileDuplicate
      (aminoChild 5).node (aminoChild 6).node (aminoChild (n + 8)).node .gt rootForward
    · simp [nextCanonicalPairs?, leftLive, rightLive, leftRank, rightRank, before]
    · simp only [compareCanonicalPairLabels?, forwardFirst, forwardSecond]
    · decide
  · apply supported_of_next_three mol (fuel + 1) stage (canonicalRoot 0 4) (canonicalRoot 0 2)
      (aminoChild 5).node (aminoChild 6).node (aminoChild (n + 8)).node
      realNitrileNitrogen nitrileDuplicate nitrileDuplicate .lt rootReverse
    · simp [nextCanonicalPairs?, leftLive, rightLive, leftRank, rightRank, before]
    · simp only [compareCanonicalPairLabels?, reverseFirst, reverseSecond]
    · decide

theorem actual_initial_structural_both (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).compareCanonicalBranchesStructurally? (analysisFuel (expanded parity n))
        0 2 4 = some .gt ∧
      (expanded parity n).compareCanonicalBranchesStructurally? (analysisFuel (expanded parity n))
        0 4 2 = some .lt := by
  have depth : (expanded parity n).atomCount + 1 ≤ analysisFuel (expanded parity n) := by
    unfold analysisFuel
    omega
  have positive : 0 < (expanded parity n).atomCount := by rw [expanded_atomCount]; omega
  have steps : (expanded parity n).atomCount - 1 + 2 = (expanded parity n).atomCount + 1 := by
    omega
  simpa only [compareCanonicalBranchesStructurally?, depth, ↓reduceIte, steps] using
    actual_initial_supported_both parity n ((expanded parity n).atomCount - 1) .rule2

theorem actual_initial_terminal_shells_none (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).compareTerminalHydrogenShellRoots? (canonicalRoot 0 2)
        (canonicalRoot 0 4) = none ∧
      (expanded parity n).compareTerminalHydrogenShellRoots? (canonicalRoot 0 4)
        (canonicalRoot 0 2) = none := by
  rcases expanded_local_atomic_numbers parity n with ⟨_, _, _, nitrogen, _⟩
  have leftNone : (expanded parity n).terminalHydrogenMasses? (canonicalRoot 0 2) = none := by
    simp [terminalHydrogenMasses?, expanded_nitrile_children_exact,
      realNitrileNitrogen, nitrogen]
  constructor
  · simp [compareTerminalHydrogenShellRoots?, leftNone]
  · unfold compareTerminalHydrogenShellRoots?
    rw [leftNone]
    cases (expanded parity n).terminalHydrogenMasses? (canonicalRoot 0 4) <;> rfl

/-- Actual initial-seed branch decisions. Physical acyclicity disables the legacy automorphism
precheck; the terminal-H shortcut is inapplicable, and the structural route supplies the result. -/
theorem actual_initial_compareBranches_both (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).compareBranches? (analysisFuel (expanded parity n)) 0 2 4 = some .gt ∧
      (expanded parity n).compareBranches? (analysisFuel (expanded parity n)) 0 4 2 = some .lt := by
  rcases expanded_local_atomic_numbers parity n with ⟨_, _, nitrileZ, _, aminoZ, _⟩
  have shells := actual_initial_terminal_shells_none parity n
  have structural := actual_initial_structural_both parity n
  have acyclic := expanded_nitrile_acyclic parity n (analysisFuel (expanded parity n))
  constructor <;> simp [compareBranches?,
    TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_root_rule1a,
    nitrileZ, aminoZ, shells.1, shells.2, acyclic, structural.1, structural.2]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
