import TetraStereo.UniversalProof.NextFrontier.NativeRingInitialNodeSorting
import TetraStereo.UniversalProof.NextFrontier.NativeRingAutomorphismRejection

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingInitialComparison

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingRuntimeChildren
open TetraStereo.UniversalProof.NativeRingInitialNodeSorting
open TetraStereo.UniversalProof.NativeRingAutomorphismRejection
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery

/-- The initial seed's structural comparator reaches a strict leading child pair at every
positive depth. Both supplied ranks are the production ranks at the recursive callback fuel. -/
theorem supported_of_ranked_three (raw : RawMolecule) (fuel : Nat)
    (stage : CanonicalRuleStage) (left right a b c d e f : CanonicalBranchNode)
    (decision : Ordering) (leftReal : left.provenance = .realAtom)
    (rightReal : right.provenance = .realAtom)
    (sameZ : raw.atomZAt left.atom = raw.atomZAt right.atom)
    (leftNonterminal : raw.canonicalTerminal left = false)
    (rightNonterminal : raw.canonicalTerminal right = false)
    (leftRanked : raw.rankedCanonicalChildren?
      (raw.compareCanonicalBranchAtSupported? fuel stage) left = some [a, b, c])
    (rightRanked : raw.rankedCanonicalChildren?
      (raw.compareCanonicalBranchAtSupported? fuel stage) right = some [d, e, f])
    (leading : raw.compareCanonicalNodeRule? .rule1a a d = some decision)
    (strict : decision ≠ .eq) :
    raw.compareCanonicalBranchAtSupported? (fuel + 1) stage left right = some decision := by
  let before := raw.compareCanonicalBranchAtSupported? fuel stage
  let pairs := [(a, d), (b, e), (c, f)]
  have rootTie := compareCanonicalNodeRule?_rule1a_realAtom raw left right leftReal rightReal
  rw [sameZ] at rootTie
  have expandedPairs : raw.nextCanonicalPairs? before [(left, right)] = some pairs := by
    simp [nextCanonicalPairs?, leftNonterminal, rightNonterminal, leftRanked, rightRanked,
      before, pairs]
  have labels : raw.compareCanonicalPairLabels? .rule1a pairs = some decision := by
    cases decision <;> simp_all [pairs, compareCanonicalPairLabels?]
  have second (depth : Nat) :
      raw.compareCanonicalRuleSupported? before .rule1a defaultBranchWidthCap depth pairs =
        some decision := by
    cases depth <;> cases decision <;>
      simp_all [compareCanonicalRuleSupported?, pairs, defaultBranchWidthCap]
  have first : raw.compareCanonicalRuleSupported? before .rule1a defaultBranchWidthCap
      (fuel + 1) [(left, right)] = some decision := by
    simp [compareCanonicalRuleSupported?, compareCanonicalPairLabels?, rootTie,
      expandedPairs, defaultBranchWidthCap]
    exact second fuel
  dsimp only [before] at first
  cases decision with
  | eq => exact (strict rfl).elim
  | lt => simp only [compareCanonicalBranchAtSupported?, first]
  | gt => simp only [compareCanonicalBranchAtSupported?, first]

theorem node_nonterminal_of_three (raw : RawMolecule) (node : CanonicalBranchNode)
    (real : node.provenance = .realAtom) (count : (raw.canonicalChildren node).length = 3) :
    raw.canonicalTerminal node = false := by
  have nonempty : raw.canonicalChildren node ≠ [] := by
    intro empty
    rw [empty] at count
    cases count
  simpa only [canonicalTerminal, CanonicalBranchNode.forcedLeaf, real,
    Bool.false_or, List.isEmpty_eq_false_iff] using nonempty

theorem actual_supported_both (n fuel : Nat) (parity : TetrahedralInputParity)
    (stage : CanonicalRuleStage) :
    (expanded n parity).compareCanonicalBranchAtSupported? (fuel + 1) stage
      (rootNode 2) (rootNode (n + 4)) = some .gt ∧
    (expanded n parity).compareCanonicalBranchAtSupported? (fuel + 1) stage
      (rootNode (n + 4)) (rootNode 2) = some .lt := by
  let raw := expanded n parity
  have leftCount : (raw.canonicalChildren (rootNode 2)).length = 3 :=
    (actual_left_nodes n parity).length_eq
  have rightCount : (raw.canonicalChildren (rootNode (n + 4))).length = 3 :=
    (actual_right_nodes n parity).length_eq
  have leftSorted := actual_left_sorted n fuel parity stage
  obtain ⟨firstH, secondH, rightSorted⟩ : ∃ firstH secondH,
      sortCanonicalBy? (raw.compareCanonicalBranchAtSupported? fuel stage)
        (raw.canonicalChildren (rootNode (n + 4))) =
      some [armNode (n + 4) (rightPredecessor n), firstH, secondH] := by
    rcases actual_right_sorted n fuel parity stage with sorted | sorted
    · exact ⟨_, _, sorted⟩
    · exact ⟨_, _, sorted⟩
  have leftRanked : raw.rankedCanonicalChildren?
      (raw.compareCanonicalBranchAtSupported? fuel stage) (rootNode 2) =
      some [armNode 2 3, armNode 2 4, armNode 2 (n + 6)] := by
    simp [rankedCanonicalChildren?, leftCount, leftSorted, raw]
  have rightRanked : raw.rankedCanonicalChildren?
      (raw.compareCanonicalBranchAtSupported? fuel stage) (rootNode (n + 4)) =
      some [armNode (n + 4) (rightPredecessor n), firstH, secondH] := by
    simp [rankedCanonicalChildren?, rightCount, rightSorted]
  have leftLive := node_nonterminal_of_three raw (rootNode 2) rfl leftCount
  have rightLive := node_nonterminal_of_three raw (rootNode (n + 4)) rfl rightCount
  have sameZ : raw.atomZAt (rootNode 2).atom = raw.atomZAt (rootNode (n + 4)).atom :=
    (expanded_left_z n parity).trans (expanded_chain_z n parity n (by omega)).symm
  have forward := compareCanonicalNodeRule?_rule1a_realAtom raw
    (armNode 2 3) (armNode (n + 4) (rightPredecessor n)) rfl rfl
  have reverse := compareCanonicalNodeRule?_rule1a_realAtom raw
    (armNode (n + 4) (rightPredecessor n)) (armNode 2 3) rfl rfl
  change raw.compareCanonicalNodeRule? .rule1a _ _ =
    some (compare (raw.atomZAt 3) (raw.atomZAt (rightPredecessor n))) at forward
  change raw.compareCanonicalNodeRule? .rule1a _ _ =
    some (compare (raw.atomZAt (rightPredecessor n)) (raw.atomZAt 3)) at reverse
  have predecessorZ : raw.atomZAt (rightPredecessor n) = 6 := expanded_right_predecessor_z n parity
  rw [expanded_chlorine_z n parity, predecessorZ] at forward reverse
  exact ⟨supported_of_ranked_three raw fuel stage _ _ _ _ _ _ _ _ .gt rfl rfl sameZ
      leftLive rightLive leftRanked rightRanked forward (by decide),
    supported_of_ranked_three raw fuel stage _ _ _ _ _ _ _ _ .lt rfl rfl sameZ.symm
      rightLive leftLive rightRanked leftRanked reverse (by decide)⟩

theorem actual_structural_both (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).compareCanonicalBranchesStructurally? (analysisFuel (expanded n parity))
      0 2 (n + 4) = some .gt ∧
    (expanded n parity).compareCanonicalBranchesStructurally? (analysisFuel (expanded n parity))
      0 (n + 4) 2 = some .lt := by
  have depth : (expanded n parity).atomCount + 1 ≤ analysisFuel (expanded n parity) := by
    unfold analysisFuel
    omega
  simpa only [compareCanonicalBranchesStructurally?, depth, ↓reduceIte, rootNode] using
    actual_supported_both n (expanded n parity).atomCount parity .rule2

theorem actual_terminal_shells_none (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).compareTerminalHydrogenShellRoots? (rootNode 2) (rootNode (n + 4)) = none ∧
    (expanded n parity).compareTerminalHydrogenShellRoots? (rootNode (n + 4)) (rootNode 2) = none := by
  have member : armNode 2 3 ∈ (expanded n parity).canonicalChildren (rootNode 2) :=
    (actual_left_nodes n parity).mem_iff.mpr (by simp)
  have notAll : ((expanded n parity).canonicalChildren (rootNode 2)).all (fun child =>
      child.provenance == .realAtom && (expanded n parity).atomZAt child.atom == 1 &&
        (expanded n parity).canonicalTerminal child) = false := by
    apply Bool.eq_false_iff.mpr
    intro allHydrogens
    have chlorine := List.all_eq_true.mp allHydrogens (armNode 2 3) member
    simp [armNode, NativeRingSingleBondChildren.pathNode,
      expanded_chlorine_z n parity] at chlorine
  have leftNone : (expanded n parity).terminalHydrogenMasses? (rootNode 2) = none := by
    simp only [terminalHydrogenMasses?, notAll, Bool.false_eq_true, ↓reduceIte]
  constructor
  · simp [compareTerminalHydrogenShellRoots?, leftNone]
  · unfold compareTerminalHydrogenShellRoots?
    rw [leftNone]
    cases (expanded n parity).terminalHydrogenMasses? (rootNode (n + 4)) <;> rfl

/-- Both actual carbon comparisons used by the initial descriptor seed. The cyclic
automorphism precheck is rejected from the executable search, independently of the target order. -/
theorem actual_compareBranches_both (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).compareBranches? (analysisFuel (expanded n parity)) 0 2 (n + 4) = some .gt ∧
    (expanded n parity).compareBranches? (analysisFuel (expanded n parity)) 0 (n + 4) 2 = some .lt := by
  have leftZ := expanded_left_z n parity
  have rightZ := expanded_chain_z n parity n (by omega)
  have shells := actual_terminal_shells_none n parity
  simp only [rootNode] at shells
  have structural := actual_structural_both n parity
  have noSwap := actual_no_carbon_swap n parity
  constructor <;> simp [compareBranches?,
    NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_root_rule1a,
    leftZ, rightZ, shells.1, shells.2, noSwap.1, noSwap.2, structural.1, structural.2]

end TetraStereo.UniversalProof.NativeRingInitialComparison
