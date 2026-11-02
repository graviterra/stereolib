import TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.CanonicalComparisonFrame
open TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile

/-!
# Domain completeness of the actual canonical generated profile

`CanonicalGeneratedComparisonProfile.profile?` accepts a comparison center only after the
uncapped collector succeeds, the center occurs in the collected list, and *every* collected node
passes `pathOK?`.  The profile module proves soundness (`profile?_some`) but does not prove that an
actual generated center satisfies those guards.  This module supplies that domain coverage.

The arguments are the explicit finite-graph hypotheses `mol.WellFormed` and
`root < mol.atomCount`; the comparison origin is the root recovered from `center.history` (the
coordinate used by the existing profile), not a separately supplied original root.

Main results:

* `generated_pathOK`: every node of the actual production child relation generated from the
  recovered root passes `pathOK?` (head, root tail, nonemptiness, and in-range history).
* `generated_duplicate_bound`: every generated node has no phantom provenance, and every stored
  multiple-bond / ring duplicate coordinate fits `stored + 1 ≤ node.history.tail.length`.
* `observe_isSome_of_generated`: hence `CanonicalComparisonFrame.observeNode` returns `some` for
  every actually generated node, for *any* frame.
* `profile?_complete`: for every actual generated center the new executable profile succeeds,
  returning the actual collector output; every member of that output passes `pathOK?`, satisfies
  the duplicate-bound/no-phantom invariant, and is observable.
* `every_generated_center_admitted` and `profile?_center_observed` are the corresponding
  pointwise and center-observation corollaries.

This is domain coverage of an executable definition, not a normative statement about 2013 CIP
policy.  Multiple-bond duplicate coordinates are the stored attachment depth
(`parent.depth = parent.history.length - 1`), a coordinate distinct from any represented-atom
distance; ring duplicate coordinates are the actual reversed-history index.
-/

/-! ## Index and history facts -/

/-- A member of a list is found at some index by `firstNatIndex?`. -/
theorem firstNatIndex?_isSome_of_mem (target : Nat) :
    ∀ values : List Nat, target ∈ values →
      ∃ index, firstNatIndex? target values = some index
  | [], member => by simp at member
  | value :: values, member => by
      by_cases equal : value = target
      · exact ⟨0, by simp [firstNatIndex?, equal]⟩
      · have tailMember : target ∈ values := by
          rw [List.mem_cons] at member
          exact member.resolve_left (fun headEqual => equal headEqual.symm)
        obtain ⟨index, indexEq⟩ := firstNatIndex?_isSome_of_mem target values tailMember
        exact ⟨index + 1, by simp [firstNatIndex?, equal, indexEq]⟩

/-- The stored rootward coordinate of a ring duplicate found in a history is a strict position
of that history. -/
theorem canonicalHistoryDistance_lt_of_mem (node : CanonicalBranchNode) (atom : Nat)
    (member : atom ∈ node.history) :
    canonicalHistoryDistance node atom < node.history.length := by
  obtain ⟨index, indexEq⟩ := firstNatIndex?_isSome_of_mem atom node.history.reverse
    (List.mem_reverse.mpr member)
  have indexLt : index < node.history.length := by
    have bounded := firstNatIndex?_eq_some_imp_lt_length atom node.history.reverse index indexEq
    simpa using bounded
  unfold canonicalHistoryDistance
  rw [indexEq]
  simpa using indexLt

/-- Every actually generated node history ends at the recovered root. -/
theorem generated_history_getLast (mol : RawMolecule) (root : Nat)
    {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    node.history.getLast? = some root := by
  induction generated with
  | root => rfl
  | @child parent child _parentGenerated childMember ih =>
      rw [mol.canonicalChildren_history parent child childMember]
      cases historyEq : parent.history with
      | nil => simp [historyEq] at ih
      | cons first rest => simpa [historyEq] using ih

/-- Every atom in an actually generated node history is a real atom index. -/
theorem generated_history_atoms_lt (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    ∀ atom, atom ∈ node.history → atom < mol.atomCount := by
  induction generated with
  | root =>
      intro atom member
      have atomEq : atom = root := by simpa [canonicalCenterRoot] using member
      subst atom
      exact rootBound
  | @child parent child _parentGenerated childMember ih =>
      rw [mol.canonicalChildren_history parent child childMember]
      intro atom member
      rw [List.mem_cons] at member
      rcases member with rfl | member
      · exact child_atom_lt_atomCount well childMember
      · exact ih atom member

/-- The relaxed general path invariant holds for every actually generated node. -/
theorem generated_pathOK (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    pathOK? mol root node = true := by
  rw [pathOK?_true_iff]
  have head := CanonicalCenterTreeNode.history_head generated
  refine ⟨head, generated_history_getLast mol root generated, ?_,
    generated_history_atoms_lt mol root well rootBound generated⟩
  cases historyEq : node.history with
  | nil => simp [historyEq] at head
  | cons first rest => rfl

/-! ## Duplicate coordinates of generated children -/

/-- Exact provenance data of a generated ring duplicate: the duplicated atom occurs in the parent
history and the stored coordinate is the actual reversed-history index. -/
theorem child_ringDuplicate_data (mol : RawMolecule)
    {parent child : CanonicalBranchNode}
    (childMember : child ∈ mol.canonicalChildren parent) (stored : Nat)
    (provenance : child.provenance = .ringDuplicate stored) :
    child.atom ∈ parent.history ∧
      stored = canonicalHistoryDistance parent child.atom := by
  unfold canonicalChildren at childMember
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at childMember
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at childMember
    obtain ⟨copy, _copyMember, rfl⟩ := childMember
    by_cases multiple : copy.2 != 0
    · simp [multiple] at provenance
    · by_cases ring : copy.1 ∈ parent.history
      · simp [multiple, ring] at provenance
        have distanceEq : stored = canonicalHistoryDistance parent copy.1 := by
          simpa using provenance.symm
        exact ⟨ring, distanceEq⟩
      · simp [multiple, ring] at provenance

/-- The duplicate coordinates of every generated child fit the tail of its history: multiple-bond
coordinates are the parent attachment depth and ring coordinates are actual history positions. -/
theorem child_duplicate_bound (mol : RawMolecule) {root : Nat}
    {parent child : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode mol root parent)
    (childMember : child ∈ mol.canonicalChildren parent) :
    (∀ stored, child.provenance = .multipleBondDuplicate stored →
      stored + 1 ≤ child.history.tail.length) ∧
    (∀ stored, child.provenance = .ringDuplicate stored →
      stored + 1 ≤ child.history.tail.length) := by
  have parentNonempty : parent.history ≠ [] := by
    have head := CanonicalCenterTreeNode.history_head parentGenerated
    intro empty
    rw [empty] at head
    simp at head
  constructor
  · intro stored provenance
    have distanceEq : stored = parent.depth :=
      canonicalChildren_multipleBondDuplicate_distance mol parent child childMember stored
        provenance
    rw [mol.canonicalChildren_history parent child childMember, distanceEq]
    simp only [List.tail_cons]
    unfold CanonicalBranchNode.depth
    have positive := List.length_pos_iff.mpr parentNonempty
    omega
  · intro stored provenance
    obtain ⟨atomMember, distanceEq⟩ :=
      child_ringDuplicate_data mol childMember stored provenance
    have distanceLt : canonicalHistoryDistance parent child.atom < parent.history.length :=
      canonicalHistoryDistance_lt_of_mem parent child.atom atomMember
    rw [mol.canonicalChildren_history parent child childMember, distanceEq]
    simp only [List.tail_cons]
    omega

/-- The complete per-node duplicate invariant on the actual generation relation: no phantom
provenance and stored coordinates bounded by the parent-history tail. -/
theorem generated_duplicate_bound (mol : RawMolecule) {root : Nat}
    {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    (∀ stored, node.provenance = .multipleBondDuplicate stored →
      stored + 1 ≤ node.history.tail.length) ∧
    (∀ stored, node.provenance = .ringDuplicate stored →
      stored + 1 ≤ node.history.tail.length) ∧
    (∀ stored, node.provenance ≠ .phantom stored) := by
  induction generated with
  | root =>
      refine ⟨?_, ?_, ?_⟩ <;> intro stored provenance <;> cases provenance
  | @child parent child parentGenerated childMember _ih =>
      have bounds := child_duplicate_bound mol parentGenerated childMember
      exact ⟨bounds.1, bounds.2,
        fun stored provenance =>
          canonicalChildren_provenance_ne_phantom mol parent child childMember stored
            provenance⟩

/-! ## Partial observation of every generated member -/

/-- `observeNode` is defined (returns `some`) on every actually generated node, for any frame.
Real nodes use their history distance; duplicate nodes use the guarded duplicate coordinate. -/
theorem observe_isSome_of_generated (mol : RawMolecule) (root : Nat)
    (frame : CanonicalComparisonFrame.Frame) {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    (observeNode frame node).isSome = true := by
  induction generated with
  | root =>
      simp [observeNode, canonicalCenterRoot]
  | @child parent child parentGenerated childMember _ih =>
      have bounds := child_duplicate_bound mol parentGenerated childMember
      cases provenance : child.provenance with
      | realAtom => simp [observeNode, provenance]
      | multipleBondDuplicate stored =>
          rw [multiple_observation frame child stored provenance
            (bounds.1 stored provenance)]
          rfl
      | ringDuplicate stored =>
          rw [ring_observation frame child stored provenance
            (bounds.2 stored provenance)]
          rfl
      | phantom stored =>
          exact False.elim
            (canonicalChildren_provenance_ne_phantom mol parent child childMember stored
              provenance)

/-! ## Admission completeness -/

/-- For every actual center generated from the recovered root, the executable general profile
succeeds.  The returned profile carries the actual collector output; every member of that output
passes `pathOK?`, carries no phantom provenance, has duplicate coordinates bounded by the history
tail, and is observed (`observeNode` returns `some`).  Nothing about an already-accepted profile is
assumed. -/
theorem profile?_complete (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root center) :
    ∃ p : Profile,
      profile? mol center = some p ∧
      p.root = root ∧
      p.center = center ∧
      p.frame = (⟨center.history⟩ : CanonicalComparisonFrame.Frame) ∧
      p.generated = prefixTree mol root 0 (mol.atomCount + 1) ∧
      center ∈ p.generated ∧
      (∀ node ∈ p.generated, pathOK? mol root node = true) ∧
      (∀ node ∈ p.generated,
        (∀ stored, node.provenance = .multipleBondDuplicate stored →
          stored + 1 ≤ node.history.tail.length) ∧
        (∀ stored, node.provenance = .ringDuplicate stored →
          stored + 1 ≤ node.history.tail.length) ∧
        (∀ stored, node.provenance ≠ .phantom stored) ∧
        (observeNode p.frame node).isSome = true) := by
  let collected := prefixTree mol root 0 (mol.atomCount + 1)
  have hlast : center.history.getLast? = some root :=
    generated_history_getLast mol root generated
  have hcollect : collectCanonicalTreeAuthoritative mol (mol.atomCount + 1)
      [canonicalCenterRoot root] = some collected :=
    actual_collector_at_atomCount mol root well rootBound
  have hmem : center ∈ collected :=
    generated_mem_complete_tree mol root (mol.atomCount + 1) well rootBound
      (Nat.le_refl _) center generated
  have hcontains : collected.contains center = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact hmem
  have hpathAll : collected.all (pathOK? mol root) = true := by
    apply List.all_eq_true.mpr
    intro node nodeMember
    exact generated_pathOK mol root well rootBound
      (prefixTree_generated mol root (mol.atomCount + 1) 0 node nodeMember)
  have hbonds : mol.bonds.all (mol.bondEndpointsOK?) = true :=
    (wellFormed_iff_all_bondEndpointsOK mol).mp well
  have hguard :
      (!(decide (root < mol.atomCount)) ||
        !(mol.bonds.all (mol.bondEndpointsOK?))) = false := by
    have rootLt : decide (root < mol.atomCount) = true := decide_eq_true rootBound
    rw [rootLt, hbonds]
    rfl
  let p : Profile := ⟨root, center, ⟨center.history⟩, collected⟩
  have hprofile : profile? mol center = some p := by
    change profile? mol center = some ⟨root, center, ⟨center.history⟩, collected⟩
    unfold profile?
    simp only [hlast, Bind.bind, Option.bind]
    rw [hguard]
    simp only [hcollect]
    split
    · rename_i impossible
      simp at impossible
    · split
      · rename_i impossible
        rw [hcontains] at impossible
        simp at impossible
      · split
        · rename_i impossible
          rw [hpathAll] at impossible
          simp at impossible
        · rfl
  refine ⟨p, hprofile, rfl, rfl, rfl, rfl, hmem, ?_, ?_⟩
  · intro node nodeMember
    exact generated_pathOK mol root well rootBound
      (prefixTree_generated mol root (mol.atomCount + 1) 0 node nodeMember)
  · intro node nodeMember
    have generatedNode : CanonicalCenterTreeNode mol root node :=
      prefixTree_generated mol root (mol.atomCount + 1) 0 node nodeMember
    have bounds := generated_duplicate_bound mol generatedNode
    exact ⟨bounds.1, bounds.2.1, bounds.2.2,
      observe_isSome_of_generated mol root p.frame generatedNode⟩

/-- Pointwise form of admission completeness: every actual generated center has a successful
profile whose generated members are all observable. -/
theorem every_generated_center_admitted (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount) :
    ∀ center, CanonicalCenterTreeNode mol root center →
      ∃ p : Profile,
        profile? mol center = some p ∧
        p.root = root ∧
        p.center = center ∧
        (∀ node ∈ p.generated, (observeNode p.frame node).isSome = true) := by
  intro center generated
  obtain ⟨p, hprofile, hroot, hcenter, _hframe, _hgenerated, _hmember, _hpath,
    hadmission⟩ := profile?_complete mol root well rootBound center generated
  exact ⟨p, hprofile, hroot, hcenter,
    fun node nodeMember => (hadmission node nodeMember).2.2.2⟩

/-- The admitted comparison center itself is observed by the returned frame. -/
theorem profile?_center_observed (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root center) :
    ∃ p : Profile,
      profile? mol center = some p ∧
      (observeNode p.frame p.center).isSome = true := by
  obtain ⟨p, hprofile, _hroot, hcenter, _hframe, _hgenerated, hmember, _hpath,
    hadmission⟩ := profile?_complete mol root well rootBound center generated
  refine ⟨p, hprofile, ?_⟩
  rw [hcenter]
  exact (hadmission center hmember).2.2.2

end TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.firstNatIndex?_isSome_of_mem
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.canonicalHistoryDistance_lt_of_mem
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.generated_history_getLast
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.generated_history_atoms_lt
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.generated_pathOK
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.child_ringDuplicate_data
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.child_duplicate_bound
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.generated_duplicate_bound
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.observe_isSome_of_generated
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.profile?_complete
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.every_generated_center_admitted
assert_kernel_only
  TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission.profile?_center_observed
