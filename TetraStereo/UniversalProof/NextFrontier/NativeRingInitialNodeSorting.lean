import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeChildren
import TetraStereo.UniversalProof.SecondSphereInitialSeedBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingInitialNodeSorting

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingRuntimeChildren
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeRingSingleBondChildren

def rootNode (atom : Nat) : CanonicalBranchNode := canonicalRoot 0 atom

def armNode (parent atom : Nat) : CanonicalBranchNode := pathNode atom [parent, 0]

theorem actual_left_nodes (n : Nat) (parity : TetrahedralInputParity) :
    ((expanded n parity).canonicalChildren (rootNode 2)).Perm
      [armNode 2 (n + 6), armNode 2 3, armNode 2 4] := by
  let physical := (recordNeighbors (expanded n parity) 2).erase 0
  have projected := left_erased_records n parity
  have actual := actual_path_children (expanded n parity) 2 0 [] physical rfl
    (expanded_record_bond_one n parity 2) (by
      intro other member
      have retained := projected.mem_iff.mp member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
      rcases retained with rfl | rfl | rfl <;> simp)
  change (expanded n parity).canonicalChildren (rootNode 2) =
    physical.map (armNode 2) at actual
  rw [actual]
  exact projected.map (armNode 2)

theorem actual_right_nodes (n : Nat) (parity : TetrahedralInputParity) :
    ((expanded n parity).canonicalChildren (rootNode (n + 4))).Perm
      [armNode (n + 4) (rightPredecessor n), armNode (n + 4) (3 * n + 7),
        armNode (n + 4) (3 * n + 8)] := by
  let physical := (recordNeighbors (expanded n parity) (n + 4)).erase 0
  have projected := right_erased_records n parity
  have actual := actual_path_children (expanded n parity) (n + 4) 0 [] physical rfl
    (expanded_record_bond_one n parity (n + 4)) (by
      intro other member
      have retained := projected.mem_iff.mp member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
      rcases retained with rfl | rfl | rfl
      · unfold rightPredecessor
        split <;> simp_all
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        omega)
  change (expanded n parity).canonicalChildren (rootNode (n + 4)) =
    physical.map (armNode (n + 4)) at actual
  rw [actual]
  exact projected.map (armNode (n + 4))

theorem node_comparison_of_z (raw : RawMolecule)
    (left right parent leftZ rightZ fuel : Nat) (stage : CanonicalRuleStage)
    (observedLeft : raw.atomZAt left = leftZ) (observedRight : raw.atomZAt right = rightZ)
    (strict : compare leftZ rightZ ≠ .eq) :
    raw.compareCanonicalBranchAtSupported? fuel stage (armNode parent left)
      (armNode parent right) = some (compare leftZ rightZ) := by
  apply SecondSphereInitialSeedBridge.supported_strict_real raw fuel stage _ _ rfl rfl
    (compare leftZ rightZ) _ strict
  change compare (raw.atomZAt left) (raw.atomZAt right) = _
  rw [observedLeft, observedRight]

theorem sort_strict_three
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (items : List CanonicalBranchNode) (a b c : CanonicalBranchNode)
    (permutation : items.Perm [a, b, c])
    (ab : before a b = some .gt) (ba : before b a = some .lt)
    (ac : before a c = some .gt) (ca : before c a = some .lt)
    (bc : before b c = some .gt) (cb : before c b = some .lt) :
    sortCanonicalBy? before items = some [a, b, c] := by
  rcases perm_three_cases items a b c permutation with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sortCanonicalBy?, insertCanonicalBy?,
      ab, ba, ac, ca, bc, cb]

theorem sort_three_tied_tail
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (items : List CanonicalBranchNode) (a b c : CanonicalBranchNode)
    (permutation : items.Perm [a, b, c])
    (ab : before a b = some .gt) (ba : before b a = some .lt)
    (ac : before a c = some .gt) (ca : before c a = some .lt)
    (bc : before b c = some .eq) (cb : before c b = some .eq) :
    sortCanonicalBy? before items = some [a, b, c] ∨
      sortCanonicalBy? before items = some [a, c, b] := by
  rcases perm_three_cases items a b c permutation with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sortCanonicalBy?, insertCanonicalBy?,
      ab, ba, ac, ca, bc, cb, true_or, or_true]

theorem actual_left_sorted (n fuel : Nat) (parity : TetrahedralInputParity)
    (stage : CanonicalRuleStage) :
    sortCanonicalBy? ((expanded n parity).compareCanonicalBranchAtSupported? fuel stage)
      ((expanded n parity).canonicalChildren (rootNode 2)) =
        some [armNode 2 3, armNode 2 4, armNode 2 (n + 6)] := by
  have permutation := (actual_left_nodes n parity).trans
    (show [armNode 2 (n + 6), armNode 2 3, armNode 2 4].Perm
      [armNode 2 3, armNode 2 4, armNode 2 (n + 6)] from
        List.perm_append_comm (l₁ := [armNode 2 (n + 6)]) (l₂ := [armNode 2 3, armNode 2 4]))
  have chlorine := expanded_chlorine_z n parity
  have carbon := expanded_chain_z n parity 0 (by omega)
  have hydrogen := expanded_hydrogen_z n parity (n + 6) (by omega) (by omega)
  apply sort_strict_three _ _ _ _ _ permutation
  · exact node_comparison_of_z _ 3 4 2 17 6 fuel stage chlorine carbon (by decide)
  · exact node_comparison_of_z _ 4 3 2 6 17 fuel stage carbon chlorine (by decide)
  · exact node_comparison_of_z _ 3 (n + 6) 2 17 1 fuel stage chlorine hydrogen (by decide)
  · exact node_comparison_of_z _ (n + 6) 3 2 1 17 fuel stage hydrogen chlorine (by decide)
  · exact node_comparison_of_z _ 4 (n + 6) 2 6 1 fuel stage carbon hydrogen (by decide)
  · exact node_comparison_of_z _ (n + 6) 4 2 1 6 fuel stage hydrogen carbon (by decide)

theorem right_hydrogen_facts (n : Nat) (parity : TetrahedralInputParity)
    (atom : Nat) (member : atom ∈ [3 * n + 7, 3 * n + 8]) :
    (expanded n parity).canonicalTerminal (armNode (n + 4) atom) = true ∧
    (expanded n parity).atomZAt atom = 1 ∧
    (expanded n parity).atomMassAt atom = rule2MassPico Element.H none := by
  have lower : n + 5 ≤ atom := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> omega
  have upper : atom < 3 * n + 9 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> omega
  have row : recordNeighbors (expanded n parity) atom = [n + 4] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (expanded_right_hydrogen_records n parity).1
    · exact (expanded_right_hydrogen_records n parity).2
  have children := actual_path_children (expanded n parity) atom (n + 4) [0] []
    (by rw [row]; simp) (expanded_record_bond_one n parity atom) (by simp)
  constructor
  · change (expanded n parity).canonicalChildren (armNode (n + 4) atom) = [] at children
    change (false || ((expanded n parity).canonicalChildren (armNode (n + 4) atom)).isEmpty) = true
    rw [children]
    rfl
  · exact ⟨expanded_hydrogen_z n parity atom lower upper,
      observed_naturalHydrogen_mass _ atom
        ⟨AtomSpec.aliphatic .H, expanded_fresh_hydrogen n parity atom lower upper, rfl, rfl⟩⟩

theorem right_hydrogen_tie (n fuel : Nat) (parity : TetrahedralInputParity)
    (stage : CanonicalRuleStage) (left right : Nat)
    (leftMember : left ∈ [3 * n + 7, 3 * n + 8])
    (rightMember : right ∈ [3 * n + 7, 3 * n + 8]) :
    (expanded n parity).compareCanonicalBranchAtSupported? fuel stage
      (armNode (n + 4) left) (armNode (n + 4) right) = some .eq := by
  have leftFacts := right_hydrogen_facts n parity left leftMember
  have rightFacts := right_hydrogen_facts n parity right rightMember
  apply SecondSphereInitialSeedBridge.supported_terminal_real_tie _ fuel stage _ _
    rfl rfl leftFacts.1 rightFacts.1
  · exact leftFacts.2.1.trans rightFacts.2.1.symm
  · rfl
  · exact leftFacts.2.2.trans rightFacts.2.2.symm

theorem actual_right_sorted (n fuel : Nat) (parity : TetrahedralInputParity)
    (stage : CanonicalRuleStage) :
    let before := (expanded n parity).compareCanonicalBranchAtSupported? fuel stage
    let children := (expanded n parity).canonicalChildren (rootNode (n + 4))
    sortCanonicalBy? before children = some [armNode (n + 4) (rightPredecessor n),
      armNode (n + 4) (3 * n + 7), armNode (n + 4) (3 * n + 8)] ∨
    sortCanonicalBy? before children = some [armNode (n + 4) (rightPredecessor n),
      armNode (n + 4) (3 * n + 8), armNode (n + 4) (3 * n + 7)] := by
  have carbon := expanded_right_predecessor_z n parity
  have firstH := expanded_hydrogen_z n parity (3 * n + 7) (by omega) (by omega)
  have secondH := expanded_hydrogen_z n parity (3 * n + 8) (by omega) (by omega)
  apply sort_three_tied_tail _ _ _ _ _ (actual_right_nodes n parity)
  · exact node_comparison_of_z _ (rightPredecessor n) (3 * n + 7) (n + 4)
      6 1 fuel stage carbon firstH (by decide)
  · exact node_comparison_of_z _ (3 * n + 7) (rightPredecessor n) (n + 4)
      1 6 fuel stage firstH carbon (by decide)
  · exact node_comparison_of_z _ (rightPredecessor n) (3 * n + 8) (n + 4)
      6 1 fuel stage carbon secondH (by decide)
  · exact node_comparison_of_z _ (3 * n + 8) (rightPredecessor n) (n + 4)
      1 6 fuel stage secondH carbon (by decide)
  · exact right_hydrogen_tie n fuel parity stage _ _ (by simp) (by simp)
  · exact right_hydrogen_tie n fuel parity stage _ _ (by simp) (by simp)

end TetraStereo.UniversalProof.NativeRingInitialNodeSorting
