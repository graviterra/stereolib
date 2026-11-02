import TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking

set_option autoImplicit false

namespace TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery

/-!
Finite termination of the ACTUAL uncapped canonical occurrence-tree collector.
For any well-formed finite raw graph and in-range center, fuel atomCount+1 suffices.
Real paths have at most atomCount entries; the final ring/multiple-bond duplicate may have
one additional entry and is terminal. No leaf, acyclicity, bonding-width, frontier-size,
expected tree or collector-success premise is required.

This proves downward canonical-tree collection, not arbitrary reroot comparison totality.
OnlyCenterTagged additionally constructs the actual empty auxiliary environment. A separate
leaf-domain corollary closes the earlier generic public-fact collector premise. Multiple tagged
centers, general tied/nonleaf descriptor assignment, normalization/export refinement and human
scientific/source adoption remain OPEN. These are proposed kernel checks until the root gate.
-/

/-- The actual breadth-first frontier, retaining duplicate occurrences and input ordering. -/
def frontier (raw : RawMolecule) (center : Nat) : Nat → List CanonicalBranchNode
  | 0 => [canonicalCenterRoot center]
  | level + 1 => (frontier raw center level).flatMap raw.canonicalChildren

theorem frontier_zero (raw : RawMolecule) (center : Nat) :
    frontier raw center 0 = [canonicalCenterRoot center] := rfl

theorem frontier_succ (raw : RawMolecule) (center level : Nat) :
    frontier raw center (level + 1) =
      (frontier raw center level).flatMap raw.canonicalChildren := rfl

theorem frontier_generated (raw : RawMolecule) (center level : Nat)
    (node : CanonicalBranchNode) (member : node ∈ frontier raw center level) :
    CanonicalCenterTreeNode raw center node := by
  induction level generalizing node with
  | zero =>
      change node ∈ [canonicalCenterRoot center] at member
      have equal := List.mem_singleton.mp member
      subst node
      exact .root
  | succ level ih =>
      rw [frontier_succ] at member
      rcases List.mem_flatMap.mp member with ⟨parent, parentMember, childMember⟩
      exact .child (ih parent parentMember) childMember

theorem frontier_history_length (raw : RawMolecule) (center level : Nat)
    (node : CanonicalBranchNode) (member : node ∈ frontier raw center level) :
    node.history.length = level + 1 := by
  induction level generalizing node with
  | zero =>
      change node ∈ [canonicalCenterRoot center] at member
      have equal := List.mem_singleton.mp member
      subst node
      rfl
  | succ level ih =>
      rw [frontier_succ] at member
      rcases List.mem_flatMap.mp member with ⟨parent, parentMember, childMember⟩
      rw [child_history_length childMember, ih parent parentMember]

/-- The final terminal duplicate is included: its bound is one larger than a real path. -/
theorem generated_history_bound (raw : RawMolecule) (center : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount)
    (node : CanonicalBranchNode) (generated : CanonicalCenterTreeNode raw center node) :
    node.history.length ≤ raw.atomCount + 1 := by
  cases generated with
  | root =>
      change 1 ≤ raw.atomCount + 1
      omega
  | @child parent child parentGenerated member =>
      have parentReal := real_of_child_mem member
      have parentBound := parentGenerated.real_history_length_le_atomCount
        centerBound well parentReal
      rw [child_history_length member]
      omega

theorem frontier_exhausted (raw : RawMolecule) (center : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount) :
    frontier raw center (raw.atomCount + 1) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node member
  have length := frontier_history_length raw center (raw.atomCount + 1) node member
  have bound := generated_history_bound raw center well centerBound node
    (frontier_generated raw center (raw.atomCount + 1) node member)
  omega

theorem frontier_empty_add (raw : RawMolecule) (center start extra : Nat)
    (empty : frontier raw center start = []) :
    frontier raw center (start + extra) = [] := by
  induction extra with
  | zero => exact empty
  | succ extra ih =>
      rw [Nat.add_succ, frontier_succ, ih]
      rfl

theorem frontier_exhausted_of_fuel (raw : RawMolecule) (center fuel : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount)
    (enough : raw.atomCount + 1 ≤ fuel) : frontier raw center fuel = [] := by
  have empty := frontier_empty_add raw center (raw.atomCount + 1)
    (fuel - (raw.atomCount + 1)) (frontier_exhausted raw center well centerBound)
  simpa only [Nat.add_sub_of_le enough] using empty

/-- Ordered output of the actual frontiers; this is a definition, not a supplied tree witness. -/
def prefixTree (raw : RawMolecule) (center start : Nat) : Nat → List CanonicalBranchNode
  | 0 => []
  | fuel + 1 => frontier raw center start ++ prefixTree raw center (start + 1) fuel

/-- The empty-frontier branch agrees with the ordinary recursive equation at every fuel. -/
theorem actual_collector_step (raw : RawMolecule) (fuel : Nat)
    (nodes : List CanonicalBranchNode) :
    collectCanonicalTreeAuthoritative raw (fuel + 1) nodes =
      (collectCanonicalTreeAuthoritative raw fuel (nodes.flatMap raw.canonicalChildren)).bind
        (fun tail => some (nodes ++ tail)) := by
  cases nodes with
  | nil =>
      change some [] = (collectCanonicalTreeAuthoritative raw fuel []).bind
        (fun tail => some ([] ++ tail))
      rw [collected_empty]
      rfl
  | cons node nodes => rfl

/-- A reusable operational lemma; the final finite-graph theorem derives its end-frontier fact. -/
theorem actual_collector_prefix (raw : RawMolecule) (center fuel start : Nat)
    (empty : frontier raw center (start + fuel) = []) :
    collectCanonicalTreeAuthoritative raw fuel (frontier raw center start) =
      some (prefixTree raw center start fuel) := by
  induction fuel generalizing start with
  | zero =>
      have atStart : frontier raw center start = [] := empty
      change collectCanonicalTreeAuthoritative raw 0 (frontier raw center start) = some []
      rw [atStart]
      rfl
  | succ fuel ih =>
      have shifted : frontier raw center ((start + 1) + fuel) = [] := by
        have indexEqual : (start + 1) + fuel = start + (fuel + 1) := by omega
        rw [indexEqual]
        exact empty
      have tail := ih (start + 1) shifted
      rw [actual_collector_step]
      change (collectCanonicalTreeAuthoritative raw fuel
        (frontier raw center (start + 1))).bind
          (fun nodes => some (frontier raw center start ++ nodes)) =
            some (frontier raw center start ++ prefixTree raw center (start + 1) fuel)
      rw [tail]
      rfl

/-- General actual collector success from finite graph records alone, including cyclic graphs. -/
theorem actual_collector_complete (raw : RawMolecule) (center fuel : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount)
    (enough : raw.atomCount + 1 ≤ fuel) :
    collectCanonicalTreeAuthoritative raw fuel [canonicalCenterRoot center] =
      some (prefixTree raw center 0 fuel) := by
  exact actual_collector_prefix raw center fuel 0
    (by simpa only [Nat.zero_add] using
      frontier_exhausted_of_fuel raw center fuel well centerBound enough)

theorem actual_collector_at_atomCount (raw : RawMolecule) (center : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount) :
    collectCanonicalTreeAuthoritative raw (raw.atomCount + 1) [canonicalCenterRoot center] =
      some (prefixTree raw center 0 (raw.atomCount + 1)) :=
  actual_collector_complete raw center (raw.atomCount + 1) well centerBound (Nat.le_refl _)

theorem actual_collector_exists (raw : RawMolecule) (center fuel : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount)
    (enough : raw.atomCount + 1 ≤ fuel) :
    ∃ nodes, collectCanonicalTreeAuthoritative raw fuel [canonicalCenterRoot center] = some nodes :=
  ⟨prefixTree raw center 0 fuel, actual_collector_complete raw center fuel well centerBound enough⟩

/-- All collected nodes are genuinely generated by the original production child relation. -/
theorem prefixTree_generated (raw : RawMolecule) (center fuel start : Nat)
    (node : CanonicalBranchNode) (member : node ∈ prefixTree raw center start fuel) :
    CanonicalCenterTreeNode raw center node := by
  induction fuel generalizing start with
  | zero => exact False.elim (List.not_mem_nil member)
  | succ fuel ih =>
      change node ∈ frontier raw center start ++ prefixTree raw center (start + 1) fuel at member
      rcases List.mem_append.mp member with here | later
      · exact frontier_generated raw center start node here
      · exact ih (start + 1) later

/-- Every structurally generated node occurs in its actual breadth-first level. -/
theorem generated_in_frontier (raw : RawMolecule) (center : Nat)
    (node : CanonicalBranchNode) (generated : CanonicalCenterTreeNode raw center node) :
    ∃ level, node ∈ frontier raw center level := by
  induction generated with
  | root => exact ⟨0, List.mem_singleton_self _⟩
  | @child parent child parentGenerated member ih =>
      obtain ⟨level, parentMember⟩ := ih
      exact ⟨level + 1, List.mem_flatMap.mpr ⟨parent, parentMember, member⟩⟩

theorem frontier_mem_prefixTree (raw : RawMolecule) (center fuel start level : Nat)
    (node : CanonicalBranchNode) (lower : start ≤ level) (upper : level < start + fuel)
    (member : node ∈ frontier raw center level) :
    node ∈ prefixTree raw center start fuel := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
      change node ∈ frontier raw center start ++ prefixTree raw center (start + 1) fuel
      by_cases equal : level = start
      · rw [equal] at member
        exact List.mem_append.mpr (Or.inl member)
      · have nextLower : start + 1 ≤ level := by omega
        have nextUpper : level < (start + 1) + fuel := by omega
        exact List.mem_append.mpr (Or.inr (ih (start + 1) nextLower nextUpper))

/-- Completeness is for every node of the actual production child relation, including duplicates. -/
theorem generated_mem_complete_tree (raw : RawMolecule) (center fuel : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount)
    (enough : raw.atomCount + 1 ≤ fuel) (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode raw center node) :
    node ∈ prefixTree raw center 0 fuel := by
  obtain ⟨level, member⟩ := generated_in_frontier raw center node generated
  have length := frontier_history_length raw center level node member
  have bound := generated_history_bound raw center well centerBound node generated
  apply frontier_mem_prefixTree raw center fuel 0 level node (Nat.zero_le _) _ member
  omega

theorem complete_tree_member_iff (raw : RawMolecule) (center fuel : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount)
    (enough : raw.atomCount + 1 ≤ fuel) (node : CanonicalBranchNode) :
    node ∈ prefixTree raw center 0 fuel ↔ CanonicalCenterTreeNode raw center node :=
  ⟨prefixTree_generated raw center fuel 0 node,
    generated_mem_complete_tree raw center fuel well centerBound enough node⟩

/-- Actual auxiliary construction now consumes an internally proved complete finite tree. -/
theorem actual_auxiliary_empty (raw : RawMolecule) (center fuel : Nat)
    (well : raw.WellFormed) (centerBound : center < raw.atomCount)
    (only : OnlyCenterTagged raw center) (enough : raw.atomCount + 1 ≤ fuel) :
    buildOccurrenceAuxStateFullyAuthoritative? raw fuel center = some [] :=
  auxiliary_state_empty_of_actual_tree raw fuel center only (prefixTree raw center 0 fuel)
    (actual_collector_complete raw center fuel well centerBound enough)

/-- The earlier genuine public entry point no longer asks for a successful collected tree.
The leaf domain here concerns local descriptor comparison, not collector termination. -/
theorem actual_leaf_public_fact (raw : RawMolecule) (center fuel : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) (only : OnlyCenterTagged raw center)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (enough : raw.atomCount + 1 ≤ fuel) :
    ∃ positions, tetrahedralOccurrenceFact? raw fuel center =
      some (recoveredPublicFact center positions (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions))) :=
  public_fact_exists_of_actual_tree raw fuel center domain written four only
    (prefixTree raw center 0 fuel)
    (actual_collector_complete raw center fuel domain.leaf.wellFormed domain.leaf.centerBound enough)
    spec atomObserved parity parityObserved

namespace CyclicNonleaf

/-- Two ordinary-single three-membered branches attached to an unannotated carbon center.
The fixture is independent raw graph evidence; no chemically approved structure is asserted. -/
def raw : RawMolecule :=
  { atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .C, AtomSpec.aliphatic .C,
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .Si, AtomSpec.aliphatic .C,
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .F, AtomSpec.aliphatic .Br]
    bonds := [⟨0, 1, .single⟩, ⟨0, 4, .single⟩, ⟨0, 7, .single⟩, ⟨0, 8, .single⟩,
      ⟨1, 2, .single⟩, ⟨2, 3, .single⟩, ⟨3, 1, .single⟩,
      ⟨4, 5, .single⟩, ⟨5, 6, .single⟩, ⟨6, 4, .single⟩]
    neighborOrder := [[1, 4, 7, 8], [0, 2, 3], [1, 3], [2, 1], [0, 5, 6],
      [4, 6], [5, 4], [0], [0]] }

theorem actual_admissible : raw.StereochemicalAdmissible := by
  apply (stereochemicalAdmissible?_eq_true_iff raw).mp
  decide +kernel

theorem actual_both_cyclic : raw.atomLiesInCycle 5 1 = true ∧
    raw.atomLiesInCycle 5 4 = true := by decide +kernel

theorem actual_nonleaf : (raw.incidentAtoms 1).length = 3 ∧
    (raw.incidentAtoms 4).length = 3 := by decide +kernel

theorem actual_only_center_tagged : OnlyCenterTagged raw 0 := by
  intro index spec observed tagged
  change Fin 9 at index
  fin_cases index <;> simp [raw, atomAt?, listGet?] at observed
  all_goals subst spec
  all_goals simp [AtomSpec.aliphatic] at tagged

theorem actual_collector (fuel : Nat) (enough : 10 ≤ fuel) :
    collectCanonicalTreeAuthoritative raw fuel [canonicalCenterRoot 0] =
      some (prefixTree raw 0 0 fuel) :=
  actual_collector_complete raw 0 fuel actual_admissible.1.1 (by decide +kernel) enough

theorem actual_frontier_exhausted : frontier raw 0 10 = [] :=
  frontier_exhausted raw 0 actual_admissible.1.1 (by decide +kernel)

theorem actual_auxiliary (fuel : Nat) (enough : 10 ≤ fuel) :
    buildOccurrenceAuxStateFullyAuthoritative? raw fuel 0 = some [] :=
  actual_auxiliary_empty raw 0 fuel actual_admissible.1.1 (by decide +kernel)
    actual_only_center_tagged enough

end CyclicNonleaf

end TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery
