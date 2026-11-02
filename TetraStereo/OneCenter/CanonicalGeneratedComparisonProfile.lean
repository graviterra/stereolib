import TetraStereo.OneCenter.CanonicalTreeProfile
import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.CanonicalComparisonFrame

/-!
# A finite actual canonical occurrence profile for rings and multiple bonds

The archived `CanonicalTreeProfile.profile?` admits only all-real generated trees, and caps the
total collected node count at `atomCount` — a bound that is inadequate on the root-generated
component whenever that component carries a cycle or a multiple bond (ring and multiple-bond
duplicates repeat a closing atom, and a dense root-generated component can exceed any fixed
polynomial bound). This is a statement about the component actually reached from the root: a
cycle in a disconnected component that is never reached is not necessarily collected, so it is
not claimed to make the archived profile fail.

This module keeps the original root graph and an explicit comparison center as *separate*
coordinates (a `root : Nat` and a `center : CanonicalBranchNode`), collects the actual
`canonicalChildren` tree with the maintained uncapped collector
`collectCanonicalTreeAuthoritative`, and derives an *adequate* finite cap from the proved
history-length bound `node.history.length ≤ mol.atomCount + 1` (fuel `mol.atomCount + 1`) rather
than from a total-node count. Duplicate terminal nodes (ring and multiple-bond duplicates) are
retained by the collector and are admitted by the relaxed path invariant `pathOK?`, which drops
the two checks that excluded them: `.realAtom`-only provenance and history `Nodup`.

Observation is kept explicitly partial: `Profile.observedDistance?` is `Option Nat` and refuses
(out of `none`, never `getD 0`) whenever `CanonicalComparisonFrame.observeNode` refuses a
duplicate frame coordinate. The existing real-tree profile embeds exactly.
-/

/-- A finite actual canonical occurrence profile. `root` is the original root graph coordinate;
`center` is the explicit comparison center; `frame` is the comparison origin; `generated` is the
actual `canonicalChildren` occurrence list (duplicates retained, in collector order). -/
structure Profile where
  root : Nat
  center : CanonicalBranchNode
  frame : CanonicalComparisonFrame.Frame
  generated : List CanonicalBranchNode
  deriving DecidableEq, Repr

/-- Explicit `Option`-valued observation; never totalized with a default distance. -/
def Profile.observedDistance? (p : Profile) : Option Nat :=
  observeNode p.frame p.center

theorem observedDistance?_real (p : Profile) (real : p.center.provenance = .realAtom) :
    p.observedDistance? = some (p.frame.realDistance p.center) := by
  unfold Profile.observedDistance?
  exact real_observation p.frame p.center real

theorem observedDistance?_multiple (p : Profile) (stored : Nat)
    (kind : p.center.provenance = .multipleBondDuplicate stored)
    (bound : stored + 1 ≤ p.center.history.tail.length) :
    p.observedDistance? = some (p.frame.duplicateDistance p.center stored) := by
  unfold Profile.observedDistance?
  exact multiple_observation p.frame p.center stored kind bound

theorem observedDistance?_ring (p : Profile) (stored : Nat)
    (kind : p.center.provenance = .ringDuplicate stored)
    (bound : stored + 1 ≤ p.center.history.tail.length) :
    p.observedDistance? = some (p.frame.duplicateDistance p.center stored) := by
  unfold Profile.observedDistance?
  exact ring_observation p.frame p.center stored kind bound

theorem observedDistance?_phantom_none (p : Profile) (stored : Nat)
    (kind : p.center.provenance = .phantom stored) :
    p.observedDistance? = none := by
  unfold Profile.observedDistance?
  exact raw_phantom_unobserved p.frame p.center stored kind

/-- A duplicate comparison center whose stored coordinate is out of bounds is refused, not
silently given a distance: the refusal stays `none` (no `getD 0`). -/
theorem observedDistance?_invalid_duplicate_none (p : Profile) (stored : Nat)
    (kind : p.center.provenance = .multipleBondDuplicate stored ∨
      p.center.provenance = .ringDuplicate stored)
    (invalid : ¬ stored + 1 ≤ p.center.history.tail.length) :
    p.observedDistance? = none := by
  unfold Profile.observedDistance?
  rcases kind with multiple | ring
  · unfold observeNode
    rw [multiple]
    exact invalid_duplicate_coordinate p.frame p.center stored invalid
  · unfold observeNode
    rw [ring]
    exact invalid_duplicate_coordinate p.frame p.center stored invalid

/-- Per-node path invariant of the general profile: the node starts at its own atom, ends at the
root graph coordinate, has a nonempty history, and every history atom is in range. It deliberately
does *not* require `.realAtom` provenance and does *not* require history `Nodup`, so ring and
multiple-bond duplicates are admitted. -/
def pathOK? (mol : RawMolecule) (root : Nat) (node : CanonicalBranchNode) : Bool :=
  node.history.head? == some node.atom &&
  node.history.getLast? == some root &&
  !node.history.isEmpty &&
  node.history.all (fun atom => decide (atom < mol.atomCount))

theorem pathOK?_true_iff (mol : RawMolecule) (root : Nat) (node : CanonicalBranchNode) :
    pathOK? mol root node = true ↔
      node.history.head? = some node.atom ∧
      node.history.getLast? = some root ∧
      (!node.history.isEmpty) = true ∧
      (∀ atom, atom ∈ node.history → atom < mol.atomCount) := by
  unfold pathOK?
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, and_assoc]

/-- The actual breadth-first frontier, retaining duplicate occurrences and input ordering. -/
def frontier (mol : RawMolecule) (root : Nat) : Nat → List CanonicalBranchNode
  | 0 => [canonicalCenterRoot root]
  | level + 1 => (frontier mol root level).flatMap mol.canonicalChildren

theorem frontier_zero (mol : RawMolecule) (root : Nat) :
    frontier mol root 0 = [canonicalCenterRoot root] := rfl

theorem frontier_succ (mol : RawMolecule) (root level : Nat) :
    frontier mol root (level + 1) =
      (frontier mol root level).flatMap mol.canonicalChildren := rfl

theorem frontier_generated (mol : RawMolecule) (root level : Nat)
    (node : CanonicalBranchNode) (member : node ∈ frontier mol root level) :
    CanonicalCenterTreeNode mol root node := by
  induction level generalizing node with
  | zero =>
      change node ∈ [canonicalCenterRoot root] at member
      have equal := List.mem_singleton.mp member
      subst node
      exact .root
  | succ level ih =>
      rw [frontier_succ] at member
      rcases List.mem_flatMap.mp member with ⟨parent, parentMember, childMember⟩
      exact .child (ih parent parentMember) childMember

theorem frontier_history_length (mol : RawMolecule) (root level : Nat)
    (node : CanonicalBranchNode) (member : node ∈ frontier mol root level) :
    node.history.length = level + 1 := by
  induction level generalizing node with
  | zero =>
      change node ∈ [canonicalCenterRoot root] at member
      have equal := List.mem_singleton.mp member
      subst node
      rfl
  | succ level ih =>
      rw [frontier_succ] at member
      rcases List.mem_flatMap.mp member with ⟨parent, parentMember, childMember⟩
      rw [child_history_length childMember, ih parent parentMember]

/-- The final terminal duplicate is included: its bound is one larger than a real path. -/
theorem generated_history_bound (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (node : CanonicalBranchNode) (generated : CanonicalCenterTreeNode mol root node) :
    node.history.length ≤ mol.atomCount + 1 := by
  cases generated with
  | root =>
      change 1 ≤ mol.atomCount + 1
      omega
  | @child parent child parentGenerated member =>
      have parentReal := real_of_child_mem member
      have parentBound := parentGenerated.real_history_length_le_atomCount
        rootBound well parentReal
      rw [child_history_length member]
      omega

theorem frontier_exhausted (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount) :
    frontier mol root (mol.atomCount + 1) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node member
  have length := frontier_history_length mol root (mol.atomCount + 1) node member
  have bound := generated_history_bound mol root well rootBound node
    (frontier_generated mol root (mol.atomCount + 1) node member)
  omega

theorem frontier_empty_add (mol : RawMolecule) (root start extra : Nat)
    (empty : frontier mol root start = []) :
    frontier mol root (start + extra) = [] := by
  induction extra with
  | zero => exact empty
  | succ extra ih =>
      rw [Nat.add_succ, frontier_succ, ih]
      rfl

theorem frontier_exhausted_of_fuel (mol : RawMolecule) (root fuel : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (enough : mol.atomCount + 1 ≤ fuel) : frontier mol root fuel = [] := by
  have empty := frontier_empty_add mol root (mol.atomCount + 1)
    (fuel - (mol.atomCount + 1)) (frontier_exhausted mol root well rootBound)
  simpa only [Nat.add_sub_of_le enough] using empty

/-- Ordered output of the actual frontiers; this is a definition, not a supplied tree witness. -/
def prefixTree (mol : RawMolecule) (root start : Nat) : Nat → List CanonicalBranchNode
  | 0 => []
  | fuel + 1 => frontier mol root start ++ prefixTree mol root (start + 1) fuel

/-- The empty-frontier branch of the maintained uncapped collector. -/
theorem collected_empty (mol : RawMolecule) (fuel : Nat) :
    collectCanonicalTreeAuthoritative mol fuel [] = some [] := by
  cases fuel <;> rfl

/-- The empty-frontier branch agrees with the ordinary recursive equation at every fuel. -/
theorem actual_collector_step (mol : RawMolecule) (fuel : Nat)
    (nodes : List CanonicalBranchNode) :
    collectCanonicalTreeAuthoritative mol (fuel + 1) nodes =
      (collectCanonicalTreeAuthoritative mol fuel (nodes.flatMap mol.canonicalChildren)).bind
        (fun tail => some (nodes ++ tail)) := by
  cases nodes with
  | nil =>
      change some [] = (collectCanonicalTreeAuthoritative mol fuel []).bind
        (fun tail => some ([] ++ tail))
      rw [collected_empty]
      rfl
  | cons node nodes => rfl

/-- A reusable operational lemma; the final finite-graph theorem derives its end-frontier fact. -/
theorem actual_collector_prefix (mol : RawMolecule) (root fuel start : Nat)
    (empty : frontier mol root (start + fuel) = []) :
    collectCanonicalTreeAuthoritative mol fuel (frontier mol root start) =
      some (prefixTree mol root start fuel) := by
  induction fuel generalizing start with
  | zero =>
      have atStart : frontier mol root start = [] := empty
      change collectCanonicalTreeAuthoritative mol 0 (frontier mol root start) = some []
      rw [atStart]
      rfl
  | succ fuel ih =>
      have shifted : frontier mol root ((start + 1) + fuel) = [] := by
        have indexEqual : (start + 1) + fuel = start + (fuel + 1) := by omega
        rw [indexEqual]
        exact empty
      have tail := ih (start + 1) shifted
      rw [actual_collector_step]
      change (collectCanonicalTreeAuthoritative mol fuel
        (frontier mol root (start + 1))).bind
          (fun nodes => some (frontier mol root start ++ nodes)) =
            some (frontier mol root start ++ prefixTree mol root (start + 1) fuel)
      rw [tail]
      rfl

/-- General actual collector success from finite graph records alone, including cyclic graphs. -/
theorem actual_collector_complete (mol : RawMolecule) (root fuel : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (enough : mol.atomCount + 1 ≤ fuel) :
    collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot root] =
      some (prefixTree mol root 0 fuel) := by
  exact actual_collector_prefix mol root fuel 0
    (by simpa only [Nat.zero_add] using
      frontier_exhausted_of_fuel mol root fuel well rootBound enough)

theorem actual_collector_at_atomCount (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount) :
    collectCanonicalTreeAuthoritative mol (mol.atomCount + 1) [canonicalCenterRoot root] =
      some (prefixTree mol root 0 (mol.atomCount + 1)) :=
  actual_collector_complete mol root (mol.atomCount + 1) well rootBound (Nat.le_refl _)

theorem actual_collector_exists (mol : RawMolecule) (root fuel : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (enough : mol.atomCount + 1 ≤ fuel) :
    ∃ nodes, collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot root] = some nodes :=
  ⟨prefixTree mol root 0 fuel, actual_collector_complete mol root fuel well rootBound enough⟩

/-- All collected nodes are genuinely generated by the original production child relation. -/
theorem prefixTree_generated (mol : RawMolecule) (root fuel start : Nat)
    (node : CanonicalBranchNode) (member : node ∈ prefixTree mol root start fuel) :
    CanonicalCenterTreeNode mol root node := by
  induction fuel generalizing start with
  | zero => exact False.elim (List.not_mem_nil member)
  | succ fuel ih =>
      change node ∈ frontier mol root start ++ prefixTree mol root (start + 1) fuel at member
      rcases List.mem_append.mp member with here | later
      · exact frontier_generated mol root start node here
      · exact ih (start + 1) later

/-- Every structurally generated node occurs in its actual breadth-first level. -/
theorem generated_in_frontier (mol : RawMolecule) (root : Nat)
    (node : CanonicalBranchNode) (generated : CanonicalCenterTreeNode mol root node) :
    ∃ level, node ∈ frontier mol root level := by
  induction generated with
  | root => exact ⟨0, List.mem_singleton_self _⟩
  | @child parent child parentGenerated member ih =>
      obtain ⟨level, parentMember⟩ := ih
      exact ⟨level + 1, List.mem_flatMap.mpr ⟨parent, parentMember, member⟩⟩

theorem frontier_mem_prefixTree (mol : RawMolecule) (root fuel start level : Nat)
    (node : CanonicalBranchNode) (lower : start ≤ level) (upper : level < start + fuel)
    (member : node ∈ frontier mol root level) :
    node ∈ prefixTree mol root start fuel := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
      change node ∈ frontier mol root start ++ prefixTree mol root (start + 1) fuel
      by_cases equal : level = start
      · rw [equal] at member
        exact List.mem_append.mpr (Or.inl member)
      · have nextLower : start + 1 ≤ level := by omega
        have nextUpper : level < (start + 1) + fuel := by omega
        exact List.mem_append.mpr (Or.inr (ih (start + 1) nextLower nextUpper))

/-- Completeness is for every node of the actual production child relation, including duplicates. -/
theorem generated_mem_complete_tree (mol : RawMolecule) (root fuel : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (enough : mol.atomCount + 1 ≤ fuel) (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root node) :
    node ∈ prefixTree mol root 0 fuel := by
  obtain ⟨level, member⟩ := generated_in_frontier mol root node generated
  have length := frontier_history_length mol root level node member
  have bound := generated_history_bound mol root well rootBound node generated
  apply frontier_mem_prefixTree mol root fuel 0 level node (Nat.zero_le _) _ member
  omega

theorem complete_tree_member_iff (mol : RawMolecule) (root fuel : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (enough : mol.atomCount + 1 ≤ fuel) (node : CanonicalBranchNode) :
    node ∈ prefixTree mol root 0 fuel ↔ CanonicalCenterTreeNode mol root node :=
  ⟨prefixTree_generated mol root fuel 0 node,
    generated_mem_complete_tree mol root fuel well rootBound enough node⟩

/-- The strong all-real node predicate of the archived profile implies the relaxed general path
predicate: dropping provenance and `Nodup` is a genuine weakening. -/
theorem strong_node_ok_imp_path_ok (mol : RawMolecule) (root : Nat) (node : CanonicalBranchNode) :
    (node.provenance == .realAtom && node.history.head? == some node.atom &&
      node.history.getLast? == some root && !node.history.isEmpty &&
      decide node.history.Nodup &&
      node.history.all (fun atom => decide (atom < mol.atomCount))) = true →
    pathOK? mol root node = true := by
  intro strong
  unfold pathOK?
  rcases Bool.and_eq_true_iff.mp strong with ⟨h1, hF⟩
  rcases Bool.and_eq_true_iff.mp h1 with ⟨h2, _hE⟩
  rcases Bool.and_eq_true_iff.mp h2 with ⟨h3, hD⟩
  rcases Bool.and_eq_true_iff.mp h3 with ⟨h4, hC⟩
  rcases Bool.and_eq_true_iff.mp h4 with ⟨_hA, hB⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hB, hC⟩, hD⟩,
     hF⟩

/-- The executable general profile: fuel-only, uncapped collector, duplicate-terminal admission,
root and center as separate coordinates, explicit partial observation downstream. -/
def profile? (mol : RawMolecule) (center : CanonicalBranchNode) : Option Profile := do
  let root ← center.history.getLast?
  if !(decide (root < mol.atomCount)) || !(mol.bonds.all mol.bondEndpointsOK?) then none else
  let generated ← collectCanonicalTreeAuthoritative mol (mol.atomCount + 1)
    [canonicalCenterRoot root]
  if !generated.contains center then none else
  if !(generated.all (pathOK? mol root)) then none else
    some ⟨root, center, ⟨center.history⟩, generated⟩

/-- Soundness of the general profile: every component is exactly the guarded coordinate. -/
theorem profile?_some (mol : RawMolecule) (center : CanonicalBranchNode) (p : Profile)
    (h : profile? mol center = some p) :
    center.history.getLast? = some p.root ∧
    p.center = center ∧
    p.frame = (⟨center.history⟩ : CanonicalComparisonFrame.Frame) ∧
    collectCanonicalTreeAuthoritative mol (mol.atomCount + 1) [canonicalCenterRoot p.root] =
      some p.generated ∧
    p.generated.contains center = true ∧
    p.generated.all (pathOK? mol p.root) = true := by
  cases hroot : center.history.getLast? with
  | none =>
      unfold profile? at h
      simp only [hroot, Bind.bind, Option.bind] at h
      cases h
  | some root =>
      unfold profile? at h
      simp only [hroot, Bind.bind, Option.bind] at h
      by_cases hguard : (!(decide (root < mol.atomCount)) ||
          !(mol.bonds.all mol.bondEndpointsOK?)) = true
      · rw [hguard] at h
        cases h
      · rw [Bool.eq_false_of_not_eq_true hguard] at h
        cases hgenerated : collectCanonicalTreeAuthoritative mol (mol.atomCount + 1)
            [canonicalCenterRoot root] with
        | none =>
            simp only [hgenerated] at h
            cases h
        | some generated =>
            simp only [hgenerated] at h
            by_cases hcontains : generated.contains center = true
            · rw [hcontains] at h
              by_cases hpath : generated.all (pathOK? mol root) = true
              · rw [hpath] at h
                have hp : p = ⟨root, center, ⟨center.history⟩, generated⟩ :=
                  (Option.some.inj h).symm
                subst p
                exact ⟨rfl, rfl, rfl, hgenerated, hcontains, hpath⟩
              · rw [Bool.eq_false_of_not_eq_true hpath] at h
                cases h
            · rw [Bool.eq_false_of_not_eq_true hcontains] at h
              cases h

/-- The capped archived collector, whenever it succeeds, agrees with the uncapped actual
collector at the same fuel: the total-node cap is never smaller than the actual occurrence list. -/
theorem collect_capped_imp_authoritative (mol : RawMolecule) :
    ∀ fuel cap frontier result,
      CanonicalTreeProfile.collect fuel cap mol frontier = some result →
      collectCanonicalTreeAuthoritative mol fuel frontier = some result := by
  intro fuel
  induction fuel with
  | zero =>
      intro cap frontier result computed
      cases frontier with
      | nil =>
          change some [] = some result at computed
          have resultEq : [] = result := Option.some.inj computed
          subst result
          rfl
      | cons head tail =>
          change none = some result at computed
          cases computed
  | succ fuel ih =>
      intro cap frontier result computed
      cases frontier with
      | nil =>
          change some [] = some result at computed
          have resultEq : [] = result := Option.some.inj computed
          subst result
          rfl
      | cons head tail =>
          rw [CanonicalTreeProfile.collect] at computed <;>
            try simp only [List.cons_ne_nil, imp_self]
          by_cases capExceeded : cap < (head :: tail).length
          · rw [if_pos capExceeded] at computed
            cases computed
          · rw [if_neg capExceeded] at computed
            cases restEq : CanonicalTreeProfile.collect fuel
                (cap - (head :: tail).length) mol
                ((head :: tail).flatMap mol.canonicalChildren) with
            | none =>
                rw [restEq] at computed
                change none = some result at computed
                cases computed
            | some rest =>
                rw [restEq] at computed
                have resultEq : result = (head :: tail) ++ rest :=
                  (Option.some.inj computed).symm
                subst result
                rw [actual_collector_step]
                rw [ih (cap - (head :: tail).length)
                  ((head :: tail).flatMap mol.canonicalChildren) rest restEq]
                rfl

/-- Embedding of an archived all-real profile into the general profile, sharing center, frame and
generated list; only the root coordinate is re-derived from the center history. -/
def embed (root : Nat) (p : CanonicalTreeProfile.Profile) : Profile :=
  { root := root, center := p.center, frame := p.frame, generated := p.generated }

/-- The existing real-tree profile embeds exactly: wherever the archived `profile?` succeeds,
the general `profile?` succeeds on the same center with the same frame and generated occurrence
list (and the same center history as the general root coordinate). -/
theorem profile_embeds (mol : RawMolecule) (center : CanonicalBranchNode)
    (p : CanonicalTreeProfile.Profile)
    (h : CanonicalTreeProfile.profile? mol center = some p) :
    ∃ root, center.history.getLast? = some root ∧
      profile? mol center = some (embed root p) := by
  cases hroot : center.history.getLast? with
  | none =>
      unfold CanonicalTreeProfile.profile? at h
      simp only [hroot, Bind.bind, Option.bind] at h
      cases h
  | some root =>
      unfold CanonicalTreeProfile.profile? at h
      simp only [hroot, Bind.bind, Option.bind] at h
      by_cases hguard : (!(decide (root < mol.atomCount)) ||
          !(mol.bonds.all mol.bondEndpointsOK?)) = true
      · rw [hguard] at h
        cases h
      · have hguardFalse : (!(decide (root < mol.atomCount)) ||
            !(mol.bonds.all mol.bondEndpointsOK?)) = false :=
          Bool.eq_false_of_not_eq_true hguard
        rw [hguardFalse] at h
        cases hgenerated : CanonicalTreeProfile.collect (mol.atomCount + 1) mol.atomCount mol
            [{ atom := root, parent := root, history := [root],
               provenance := .realAtom }] with
        | none =>
            simp only [hgenerated] at h
            cases h
        | some collected =>
            simp only [hgenerated] at h
            by_cases hcontains : collected.contains center = true
            · rw [hcontains] at h
              by_cases hall : (collected.all fun node =>
                  node.provenance == .realAtom && node.history.head? == some node.atom &&
                  node.history.getLast? == some root && !node.history.isEmpty &&
                  decide node.history.Nodup &&
                  node.history.all (fun atom => decide (atom < mol.atomCount))) = true
              · rw [hall] at h
                have hp : p = ⟨center, ⟨center.history⟩, collected⟩ :=
                  (Option.some.inj h).symm
                subst p
                have hpath : collected.all (pathOK? mol root) = true := by
                  apply List.all_eq_true.mpr
                  intro node member
                  have strong := List.all_eq_true.mp hall node member
                  exact strong_node_ok_imp_path_ok mol root node strong
                refine ⟨root, rfl, ?_⟩
                change profile? mol center = some ⟨root, center, ⟨center.history⟩, collected⟩
                unfold profile?
                simp only [hroot, Bind.bind, Option.bind]
                rw [hguardFalse]
                have hgen : collectCanonicalTreeAuthoritative mol (mol.atomCount + 1)
                    [canonicalCenterRoot root] = some collected :=
                  collect_capped_imp_authoritative mol (mol.atomCount + 1) mol.atomCount
                    [{ atom := root, parent := root, history := [root], provenance := .realAtom }]
                    collected hgenerated
                rw [hgen]
                simp only [hcontains, hpath, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              · rw [Bool.eq_false_of_not_eq_true hall] at h
                cases h
            · rw [Bool.eq_false_of_not_eq_true hcontains] at h
              cases h

end TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.generated_history_bound
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.frontier_exhausted
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.actual_collector_complete
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.actual_collector_at_atomCount
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.complete_tree_member_iff
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.pathOK?_true_iff
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.strong_node_ok_imp_path_ok
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.profile?_some
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.collect_capped_imp_authoritative
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.profile_embeds
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile.observedDistance?_invalid_duplicate_none
