import TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability
import TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.CanonicalComparisonFrame
open TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile
open TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability
open TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant

/-!
# Exact plain atomic-number Rule-1a labels on actually generated nodes

`GeneratedDuplicateAtomicLabelAvailability` proves only that the actual authoritative Rule-1a
labeler *returns some label* on the non-mancude generated domain.  The constructed raw/localized
key transport (`RawLocalizedActualConstructedKeyTransport.ActualRule1aPlainDomain`) consumes the
stronger, exact statement

```lean
mol.canonicalRule1aLabel? node =
  some { numerator := mol.atomZAt node.atom, denominator := 1 }
```

for the *basic* production labeler `RawMolecule.canonicalRule1aLabel?`, and separately for the
authoritative labeler `RawMolecule.canonicalRule1aLabelAuthoritative?`.  Those two functions agree
on `.realAtom`, `.ringDuplicate` and `.phantom` provenance but deliberately differ on mancude
`.multipleBondDuplicate` branches (the basic labeler consults the capped
`mancudeRule1aLabel?`, the authoritative one the uncapped
`mancudeRule1aLabelAuthoritative?`).  Substituting one equality for the other on a mancude branch
would therefore be unsound; both are proved here from the actual non-mancude dispatch.

The results below:

* `generated_provenance_ne_phantom`: an actually generated node is never a phantom occurrence.
  This is *derived* from `CanonicalGeneratedProfileAdmission.generated_duplicate_bound`, whose
  child case is `RawMolecule.canonicalChildren_provenance_ne_phantom`; no no-phantom hypothesis is
  assumed by any generated theorem.
* `canonicalRule1aLabel?_eq_plain_of_node` /
  `canonicalRule1aLabelAuthoritative?_eq_plain_of_node`: independent per-node lemmas; no generation
  relation is required.  They are the compositional building blocks for any other reachability or
  provenance analysis.
* `generated_canonicalRule1aLabel?_eq_plain`,
  `generated_canonicalRule1aLabelAuthoritative?_eq_plain` and the bundled
  `generated_exact_plain_atomic_labels`: exact plain labels, for both labelers, on the actual
  production child relation `CanonicalCenterTreeNode`.
* `prefixTree_member_*` and `profile?_generated_*` corollaries: the same exact facts for members
  of the actual collected list `prefixTree` and of the actual admitted profile
  `CanonicalGeneratedComparisonProfile.profile?`.
* `generated_canonicalRule1aLabel?_eq_authoritative`: the basic and authoritative labelers are
  equal *as functions at a generated node*, not merely both successful.
* `reachable_of_centerTreeNode`, `centerTreeNode_of_reachable`: the actual production generation
  relation and `RawLocalizedOxidoPathInvariant.ReachableCanonical` from
  `canonicalCenterRoot root` are the same node set.
* `reachable_exact_plain_atomic_labels` (with a `canonicalSelfParentRoot` variant): the reachable
  form consumed by the constructed-key transport, again deriving no-phantom provenance from the
  reachability/generation relation.

The scope is the explicit `NonMancudeGeneratedDuplicates` domain.  Nothing here asserts a label
for a generated multiple-bond duplicate whose attached edge lies on the localized mancude graph;
that case is governed by `multipleBondDuplicate_label_none_iff` in the imported module and is not
reinterpreted as a plain atomic-number label.
-/

/-! ## Independent node-level exactness

The two labelers are handled separately.  The basic labeler and the authoritative labeler share
the `.realAtom`, `.ringDuplicate` and `.phantom` branches, but on `.multipleBondDuplicate` they
call different mancude engines.  The non-mancude guard makes both engines return the plain label
without evaluating either engine, so the two equalities are proved by their own dispatch lemmas.
-/

/-- A node with no phantom provenance and with every multiple-bond duplicate coordinate off the
localized mancude graph receives exactly the plain atomic-number label from the **basic**
production labeler.

This is stated per node: no generation, reachability, profile or desired-equality hypothesis is
involved.  It is the compositional form the raw/localized transport can instantiate from whatever
node-provenance and non-mancude facts it already has. -/
theorem canonicalRule1aLabel?_eq_plain_of_node (mol : RawMolecule)
    (node : CanonicalBranchNode)
    (noPhantom : ∀ stored, node.provenance ≠ .phantom stored)
    (nonMancude : ∀ stored, node.provenance = .multipleBondDuplicate stored →
      TetraStereo.OneCenter.RawMolecule.containsUndirectedEdge mol.localizedMancudeEdges
        node.parent node.atom = false) :
    mol.canonicalRule1aLabel? node =
      some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) := by
  cases provenance : node.provenance with
  | realAtom => simp [RawMolecule.canonicalRule1aLabel?, provenance]
  | multipleBondDuplicate stored =>
      have guard := nonMancude stored provenance
      simp [RawMolecule.canonicalRule1aLabel?, provenance,
        RawMolecule.mancudeRule1aLabel?, guard]
  | ringDuplicate stored => simp [RawMolecule.canonicalRule1aLabel?, provenance]
  | phantom stored => exact absurd provenance (noPhantom stored)

/-- Per-node exact plain label for the **authoritative** labeler, under the same derived
provenance/non-mancude conditions.  The `.multipleBondDuplicate` case is
`GeneratedDuplicateAtomicLabelAvailability.multipleBondDuplicate_label_of_nonMancude`, i.e. the
exact branch of the actual uncapped dispatch, not a substitution of the basic equality. -/
theorem canonicalRule1aLabelAuthoritative?_eq_plain_of_node (mol : RawMolecule)
    (node : CanonicalBranchNode)
    (noPhantom : ∀ stored, node.provenance ≠ .phantom stored)
    (nonMancude : ∀ stored, node.provenance = .multipleBondDuplicate stored →
      TetraStereo.OneCenter.RawMolecule.containsUndirectedEdge mol.localizedMancudeEdges
        node.parent node.atom = false) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) := by
  cases provenance : node.provenance with
  | realAtom =>
      exact GeneratedDuplicateAtomicLabelAvailability.realAtom_label mol node provenance
  | multipleBondDuplicate stored =>
      exact GeneratedDuplicateAtomicLabelAvailability.multipleBondDuplicate_label_of_nonMancude
        mol node stored provenance (nonMancude stored provenance)
  | ringDuplicate stored =>
      exact GeneratedDuplicateAtomicLabelAvailability.ringDuplicate_label mol node stored
        provenance
  | phantom stored => exact absurd provenance (noPhantom stored)

/-- The basic and authoritative labelers agree exactly at a node covered by the node-level
conditions.  This is a genuine function-level equality at that node, not merely two existential
success statements: the non-mancude guard makes both mancude engines unreachable. -/
theorem canonicalRule1aLabel?_eq_authoritative_of_node (mol : RawMolecule)
    (node : CanonicalBranchNode)
    (noPhantom : ∀ stored, node.provenance ≠ .phantom stored)
    (nonMancude : ∀ stored, node.provenance = .multipleBondDuplicate stored →
      TetraStereo.OneCenter.RawMolecule.containsUndirectedEdge mol.localizedMancudeEdges
        node.parent node.atom = false) :
    mol.canonicalRule1aLabel? node = mol.canonicalRule1aLabelAuthoritative? node := by
  rw [canonicalRule1aLabel?_eq_plain_of_node mol node noPhantom nonMancude,
    canonicalRule1aLabelAuthoritative?_eq_plain_of_node mol node noPhantom nonMancude]

/-! ## Derived no-phantom provenance on the actual generated relation -/

/-- **No phantom provenance on generated nodes.**  Derived from the actual admission invariant:
the root is `.realAtom`, and every generated child's provenance is not `.phantom` by
`RawMolecule.canonicalChildren_provenance_ne_phantom`.  No hypothesis about the desired label, no
desired no-phantom hypothesis, and no profile acceptance is assumed. -/
theorem generated_provenance_ne_phantom (mol : RawMolecule) {root : Nat}
    {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) (stored : Nat) :
    node.provenance ≠ .phantom stored :=
  (CanonicalGeneratedProfileAdmission.generated_duplicate_bound mol generated).2.2 stored

/-! ## Exact plain labels on the actual generated relation -/

/-- Exact plain label of the **basic** production labeler on every actually generated node of the
non-mancude generated-duplicate domain.  The no-phantom premise is derived from
`generated_provenance_ne_phantom`; the non-mancude premise is the actual generated-domain
predicate of the imported module. -/
theorem generated_canonicalRule1aLabel?_eq_plain (mol : RawMolecule) (root : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root node) :
    mol.canonicalRule1aLabel? node =
      some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) :=
  canonicalRule1aLabel?_eq_plain_of_node mol node
    (generated_provenance_ne_phantom mol generated)
    (fun stored provenance => nonMancude node generated stored provenance)

/-- Exact plain label of the **authoritative** labeler on every actually generated node of the
non-mancude generated-duplicate domain. -/
theorem generated_canonicalRule1aLabelAuthoritative?_eq_plain (mol : RawMolecule) (root : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root node) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) :=
  canonicalRule1aLabelAuthoritative?_eq_plain_of_node mol node
    (generated_provenance_ne_phantom mol generated)
    (fun stored provenance => nonMancude node generated stored provenance)

/-- **Basic versus authoritative exact equality on the actual generated domain.**  The two
labelers are equal as values at each generated node.  This is proved from their independent exact
dispatches above; the authoritative equality is never used as a substitute for the basic one. -/
theorem generated_canonicalRule1aLabel?_eq_authoritative (mol : RawMolecule) (root : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root node) :
    mol.canonicalRule1aLabel? node = mol.canonicalRule1aLabelAuthoritative? node := by
  rw [generated_canonicalRule1aLabel?_eq_plain mol root nonMancude node generated,
    generated_canonicalRule1aLabelAuthoritative?_eq_plain mol root nonMancude node generated]

/-- Bundled exact plain-label theorem on the actual generated relation: both labelers return the
plain atomic-number numerator over denominator one, and the two labelers agree at the node. -/
theorem generated_exact_plain_atomic_labels (mol : RawMolecule) (root : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root node) :
    mol.canonicalRule1aLabel? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
    mol.canonicalRule1aLabelAuthoritative? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
    mol.canonicalRule1aLabel? node = mol.canonicalRule1aLabelAuthoritative? node :=
  ⟨generated_canonicalRule1aLabel?_eq_plain mol root nonMancude node generated,
    generated_canonicalRule1aLabelAuthoritative?_eq_plain mol root nonMancude node generated,
    generated_canonicalRule1aLabel?_eq_authoritative mol root nonMancude node generated⟩

/-! ## Actual generated-list and admitted-profile members -/

/-- Every member of the actual collected list `prefixTree` is generated, hence has both exact
plain labels.  `prefixTree` is the executable collector output recorded by the admitted profile;
this corollary avoids assuming membership in any other list. -/
theorem prefixTree_member_exact_plain_of_nonMancude (mol : RawMolecule) (root fuel start : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    {node : CanonicalBranchNode}
    (member : node ∈ prefixTree mol root start fuel) :
    mol.canonicalRule1aLabel? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
    mol.canonicalRule1aLabelAuthoritative? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) :=
  ⟨generated_canonicalRule1aLabel?_eq_plain mol root nonMancude node
      (CanonicalGeneratedComparisonProfile.prefixTree_generated mol root fuel start node member),
    generated_canonicalRule1aLabelAuthoritative?_eq_plain mol root nonMancude node
      (CanonicalGeneratedComparisonProfile.prefixTree_generated mol root fuel start node member)⟩

/-- No member of the actual collected list `prefixTree` has phantom provenance. -/
theorem prefixTree_member_provenance_ne_phantom (mol : RawMolecule) (root fuel start : Nat)
    {node : CanonicalBranchNode}
    (member : node ∈ prefixTree mol root start fuel) (stored : Nat) :
    node.provenance ≠ .phantom stored :=
  generated_provenance_ne_phantom mol
    (CanonicalGeneratedComparisonProfile.prefixTree_generated mol root fuel start node member)
    stored

/-- Every member of an actual breadth-first frontier has both exact plain labels under the
non-mancude generated domain. -/
theorem frontier_member_exact_plain_of_nonMancude (mol : RawMolecule) (root level : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    {node : CanonicalBranchNode} (member : node ∈ frontier mol root level) :
    mol.canonicalRule1aLabel? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
    mol.canonicalRule1aLabelAuthoritative? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) :=
  ⟨generated_canonicalRule1aLabel?_eq_plain mol root nonMancude node
      (CanonicalGeneratedComparisonProfile.frontier_generated mol root level node member),
    generated_canonicalRule1aLabelAuthoritative?_eq_plain mol root nonMancude node
      (CanonicalGeneratedComparisonProfile.frontier_generated mol root level node member)⟩

/-- **Admitted-profile member corollary.**  For every actually generated comparison center the
executable profile succeeds, and every member of its actual collected list carries both exact
plain labels, the basic/authoritative exact equality, no phantom provenance and a defined
observation.

The profile is produced by `CanonicalGeneratedProfileAdmission.profile?_complete`; no profile
success, membership, label existence or no-phantom fact is assumed. -/
theorem profile?_generated_exact_plain_of_nonMancude (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      p.center = center ∧
      center ∈ p.generated ∧
      (∀ node ∈ p.generated,
        mol.canonicalRule1aLabel? node =
            some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
        mol.canonicalRule1aLabelAuthoritative? node =
            some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
        mol.canonicalRule1aLabel? node = mol.canonicalRule1aLabelAuthoritative? node ∧
        (∀ stored, node.provenance ≠ .phantom stored) ∧
        (observeNode p.frame node).isSome = true) := by
  obtain ⟨p, hprofile, hroot, hcenter, _hframe, hgenerated, hmember, _hpath, hadmission⟩ :=
    CanonicalGeneratedProfileAdmission.profile?_complete mol root well rootBound center
      centerGenerated
  refine ⟨p, hprofile, hroot, hcenter, hmember, ?_⟩
  intro node nodeMember
  have prefixMember : node ∈ prefixTree mol root 0 (mol.atomCount + 1) := by
    rwa [← hgenerated]
  have generated : CanonicalCenterTreeNode mol root node :=
    CanonicalGeneratedComparisonProfile.prefixTree_generated mol root (mol.atomCount + 1) 0
      node prefixMember
  exact ⟨generated_canonicalRule1aLabel?_eq_plain mol root nonMancude node generated,
    generated_canonicalRule1aLabelAuthoritative?_eq_plain mol root nonMancude node generated,
    generated_canonicalRule1aLabel?_eq_authoritative mol root nonMancude node generated,
    fun stored => (hadmission node nodeMember).2.2.1 stored,
    (hadmission node nodeMember).2.2.2⟩

/-- **Admitted-profile no-phantom corollary.**  Every member of the actual generated list of the
admitted profile has non-phantom provenance.  This is the list-level form of
`canonicalChildren_provenance_ne_phantom` exposed through the actual executable profile. -/
theorem profile?_generated_provenance_ne_phantom (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.center = center ∧
      center ∈ p.generated ∧
      (∀ node ∈ p.generated, ∀ stored, node.provenance ≠ .phantom stored) := by
  obtain ⟨p, hprofile, _hroot, hcenter, _hframe, _hgenerated, hmember, _hpath,
    hadmission⟩ :=
    CanonicalGeneratedProfileAdmission.profile?_complete mol root well rootBound center
      centerGenerated
  exact ⟨p, hprofile, hcenter, hmember,
    fun node nodeMember stored => (hadmission node nodeMember).2.2.1 stored⟩

/-! ## The reachable-node form used by the raw/localized transport -/

/-- The production center root marker and the transport's self-parent root marker are the same
node.  Both are the structure literal with `parent = atom` and singleton history. -/
theorem canonicalCenterRoot_eq_canonicalSelfParentRoot (atom : Nat) :
    canonicalCenterRoot atom =
      TetraStereo.OneCenter.RawLocalizedChildNodeTransport.canonicalSelfParentRoot atom := rfl

/-- Actual production generation from the center root implies reachability in the sense of
`RawLocalizedOxidoPathInvariant.ReachableCanonical`. -/
theorem reachable_of_centerTreeNode (mol : RawMolecule) (root : Nat) :
    ∀ {node : CanonicalBranchNode}, CanonicalCenterTreeNode mol root node →
      ReachableCanonical mol (canonicalCenterRoot root) node := by
  intro node generated
  induction generated with
  | root => exact ReachableCanonical.refl
  | @child parent child parentGenerated childMember ih =>
      exact ReachableCanonical.child parent child ih childMember

/-- Reachability from the production center root implies actual production generation.  Together
with `reachable_of_centerTreeNode` this identifies the reachable-node domain used by the
raw/localized transport with the generated-node domain. -/
theorem centerTreeNode_of_reachable (mol : RawMolecule) (root : Nat) :
    ∀ {node : CanonicalBranchNode},
      ReachableCanonical mol (canonicalCenterRoot root) node →
        CanonicalCenterTreeNode mol root node := by
  intro node reach
  induction reach with
  | refl => exact CanonicalCenterTreeNode.root
  | @child parent child reachParent childMember ih =>
      exact CanonicalCenterTreeNode.child ih childMember

/-- Reachable nodes have no phantom provenance. -/
theorem reachable_provenance_ne_phantom (mol : RawMolecule) (root : Nat)
    {node : CanonicalBranchNode}
    (reach : ReachableCanonical mol (canonicalCenterRoot root) node) (stored : Nat) :
    node.provenance ≠ .phantom stored :=
  generated_provenance_ne_phantom mol (centerTreeNode_of_reachable mol root reach) stored

/-- **Reachability corollary.**  On the non-mancude generated-duplicate domain, every node
reachable from the production center root has both exact plain labels and agreement between the
basic and authoritative labelers.

The no-phantom premise is derived from the reachability/generation relation, so this theorem is
directly composable with `RawLocalizedOxidoPathInvariant.reachableCIPChildren_forall₂_canonicalChildren`
and its descendants. -/
theorem reachable_exact_plain_atomic_labels (mol : RawMolecule) (root : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    {node : CanonicalBranchNode}
    (reach : ReachableCanonical mol (canonicalCenterRoot root) node) :
    mol.canonicalRule1aLabel? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
    mol.canonicalRule1aLabelAuthoritative? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
    mol.canonicalRule1aLabel? node = mol.canonicalRule1aLabelAuthoritative? node :=
  generated_exact_plain_atomic_labels mol root nonMancude node
    (centerTreeNode_of_reachable mol root reach)

/-- Reachability corollary phrased for the transport's `canonicalSelfParentRoot` marker. -/
theorem reachable_exact_plain_atomic_labels_selfParentRoot (mol : RawMolecule) (atom : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol atom)
    {node : CanonicalBranchNode}
    (reach : ReachableCanonical mol
      (TetraStereo.OneCenter.RawLocalizedChildNodeTransport.canonicalSelfParentRoot atom) node) :
    mol.canonicalRule1aLabel? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
    mol.canonicalRule1aLabelAuthoritative? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) ∧
    mol.canonicalRule1aLabel? node = mol.canonicalRule1aLabelAuthoritative? node := by
  apply reachable_exact_plain_atomic_labels mol atom nonMancude
  rwa [canonicalCenterRoot_eq_canonicalSelfParentRoot]

end TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.canonicalRule1aLabel?_eq_plain_of_node
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.canonicalRule1aLabelAuthoritative?_eq_plain_of_node
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.canonicalRule1aLabel?_eq_authoritative_of_node
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.generated_provenance_ne_phantom
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.generated_canonicalRule1aLabel?_eq_plain
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.generated_canonicalRule1aLabelAuthoritative?_eq_plain
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.generated_canonicalRule1aLabel?_eq_authoritative
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.generated_exact_plain_atomic_labels
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.prefixTree_member_exact_plain_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.prefixTree_member_provenance_ne_phantom
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.frontier_member_exact_plain_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.profile?_generated_exact_plain_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.profile?_generated_provenance_ne_phantom
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.canonicalCenterRoot_eq_canonicalSelfParentRoot
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.reachable_of_centerTreeNode
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.centerTreeNode_of_reachable
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.reachable_provenance_ne_phantom
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.reachable_exact_plain_atomic_labels
assert_kernel_only
  TetraStereo.OneCenter.GeneratedExactPlainAtomicLabels.reachable_exact_plain_atomic_labels_selfParentRoot
