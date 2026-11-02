import TetraStereo.OneCenter.DeclarativeCIP
import TetraStereo.KernelOnly
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Local child coverings of rooted hierarchical digraphs

`RootedDigraph.Iso` asks for one global node equivalence.  On a finite rooted tree the global
equivalence is determined by local data: the map sends the root to the root, preserves labels,
sends child edges to child edges, hits every target child of an image parent, and is injective on
the children of each source parent.  The target graph's unique-parent axiom then makes the map
injective by induction on depth, and target reachability makes it surjective.

No global injectivity, surjectivity, or isomorphism is assumed.  Source unique parents are not
assumed either; they follow from the target's unique parents once the map is known to be
injective.  Depth is not assumed; the two `child_depth` axioms compute it from the root.

This is representation-independent.  It does not mention molecules, cuts, cursors, or rule
stages.  A caller that already has a node map and a local child correspondence supplies those
facts; this module turns them into `RootedDigraph.Iso`.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
namespace RootedDigraph

open Classical

universe u

variable {Atom : Type u}

/-- The depth grading and root reachability make the root the only depth-zero node. -/
private theorem eq_root_of_depth_eq_zero
    (graph : RootedDigraph Atom) {node : graph.Node} (hzero : graph.depth node = 0) :
    node = graph.root := by
  have reachable := graph.reachable node
  cases reachable with
  | refl => rfl
  | @tail parent child _path edge =>
      rw [graph.child_depth edge] at hzero
      exact (Nat.succ_ne_zero (graph.depth parent) hzero).elim

/-- Every non-root node has a parent, because every node is reachable from the root. -/
private theorem exists_parent
    (graph : RootedDigraph Atom) {node : graph.Node} (hne : node ≠ graph.root) :
    ∃ parent, graph.child parent node := by
  have reachable := graph.reachable node
  cases reachable with
  | refl => exact (hne rfl).elim
  | @tail parent _child _path edge => exact ⟨parent, edge⟩

/-- A rooted-digraph map determined by root, labels, and a bijection on each parent's children.

`target_unique_parent` is the one global shape hypothesis.  It is the incoming-parent property
of the target tree, not a bijection of nodes.  Without it, sibling injectivity still allows two
nodes on different branches to share an image.  `child_surjective` is what forces every target
node, reached from the target root, to lie in the image; forward `child_map` alone does not.
-/
structure LocalChildCovering (left right : RootedDigraph Atom) where
  toFun : left.Node → right.Node
  map_root : toFun left.root = right.root
  map_label : ∀ node, left.label node = right.label (toFun node)
  child_map : ∀ {parent node}, left.child parent node → right.child (toFun parent) (toFun node)
  child_surjective : ∀ {parent target},
    right.child (toFun parent) target → ∃ node, left.child parent node ∧ toFun node = target
  sibling_injective : ∀ {parent node₁ node₂},
    left.child parent node₁ → left.child parent node₂ → toFun node₁ = toFun node₂ → node₁ = node₂
  target_unique_parent : ∀ {first second node},
    right.child first node → right.child second node → first = second

namespace LocalChildCovering

variable {left right : RootedDigraph Atom} (cover : LocalChildCovering left right)

/-- Depth is transported along the unique root-to-node path by the child-depth axioms. -/
theorem map_depth (node : left.Node) :
    left.depth node = right.depth (cover.toFun node) := by
  have reachable := left.reachable node
  induction reachable with
  | refl => rw [cover.map_root, left.root_depth, right.root_depth]
  | @tail _parent _node _path edge inductionHypothesis =>
      rw [left.child_depth edge, right.child_depth (cover.child_map edge), inductionHypothesis]

/-- Target unique parents and sibling injectivity make the local map injective. -/
theorem toFun_injective : Function.Injective cover.toFun := by
  intro a b hab
  suffices ∀ n, ∀ a : left.Node, left.depth a = n →
      ∀ b : left.Node, cover.toFun a = cover.toFun b → a = b by
    exact this (left.depth a) a rfl b hab
  intro n
  refine Nat.strong_induction_on n ?_
  intro k inductionHypothesis a hk b hab
  by_cases hroot : a = left.root
  · subst hroot
    have depthB : left.depth b = 0 := by
      rw [cover.map_depth b, ← hab, cover.map_root, right.root_depth]
    exact (eq_root_of_depth_eq_zero left depthB).symm
  · have hbRoot : b ≠ left.root := by
      intro hb
      subst hb
      have depthA : left.depth a = 0 := by
        rw [cover.map_depth a, hab, cover.map_root, right.root_depth]
      exact hroot (eq_root_of_depth_eq_zero left depthA)
    obtain ⟨pa, hpa⟩ := exists_parent left hroot
    obtain ⟨pb, hpb⟩ := exists_parent left hbRoot
    have parentImage : cover.toFun pa = cover.toFun pb :=
      cover.target_unique_parent (cover.child_map hpa)
        (hab.symm ▸ cover.child_map hpb)
    have paDepth : left.depth pa < k := by
      rw [← hk, left.child_depth hpa]
      exact Nat.lt_succ_self _
    have paEq : pa = pb :=
      inductionHypothesis (left.depth pa) paDepth pa rfl pb parentImage
    subst paEq
    exact cover.sibling_injective hpa hpb hab

/-- Every target node is hit, by induction along target reachability from the root. -/
theorem toFun_surjective : Function.Surjective cover.toFun := by
  intro target
  have reachable := right.reachable target
  induction reachable with
  | refl => exact ⟨left.root, cover.map_root⟩
  | @tail _parent node _path edge inductionHypothesis =>
      obtain ⟨sourceParent, hsource⟩ := inductionHypothesis
      have edge' : right.child (cover.toFun sourceParent) node := by
        rw [hsource]
        exact edge
      obtain ⟨sourceNode, _hchild, hmap⟩ := cover.child_surjective edge'
      exact ⟨sourceNode, hmap⟩

/-- A target edge between images comes from a source edge, by local child surjectivity. -/
theorem child_map_inv {a b : left.Node}
    (hedge : right.child (cover.toFun a) (cover.toFun b)) : left.child a b := by
  obtain ⟨c, hc, hfc⟩ := cover.child_surjective hedge
  have hcb : c = b := cover.toFun_injective hfc
  rw [← hcb]
  exact hc

/-- The source graph has unique parents as well.  This is derived, not assumed. -/
theorem source_unique_parent (cover : LocalChildCovering left right)
    {first second node : left.Node}
    (hfirst : left.child first node) (hsecond : left.child second node) : first = second := by
  exact cover.toFun_injective
    (cover.target_unique_parent (cover.child_map hfirst) (cover.child_map hsecond))

/-- Each source parent is in bijection with the target children of its image. -/
theorem childFiber_bijective (parent : left.Node) :
    Function.Bijective
      (fun node : {node : left.Node // left.child parent node} =>
        (⟨cover.toFun node.1, cover.child_map node.2⟩ :
          {node : right.Node // right.child (cover.toFun parent) node})) := by
  constructor
  · intro node₁ node₂ hsame
    apply Subtype.ext
    exact cover.sibling_injective node₁.2 node₂.2 (congrArg Subtype.val hsame)
  · intro target
    obtain ⟨node, hchild, hmap⟩ := cover.child_surjective target.2
    refine ⟨⟨node, hchild⟩, ?_⟩
    apply Subtype.ext
    exact hmap

/-- The local child covering is a rooted, labelled, depth-preserving digraph isomorphism. -/
noncomputable def toIso : Iso left right where
  toEquiv := Equiv.ofBijective cover.toFun ⟨cover.toFun_injective, cover.toFun_surjective⟩
  map_root := by simpa [Equiv.ofBijective_apply] using cover.map_root
  map_child := by
    intro a b
    constructor
    · intro hedge
      simpa [Equiv.ofBijective_apply] using cover.child_map hedge
    · intro hedge
      have hedge' : right.child (cover.toFun a) (cover.toFun b) := by
        simpa [Equiv.ofBijective_apply] using hedge
      exact cover.child_map_inv hedge'
  map_label := by
    intro node
    simpa [Equiv.ofBijective_apply] using cover.map_label node
  map_depth := by
    intro node
    simpa [Equiv.ofBijective_apply] using cover.map_depth node

end LocalChildCovering

end RootedDigraph

assert_kernel_only RootedDigraph.LocalChildCovering.map_depth
assert_kernel_only RootedDigraph.LocalChildCovering.toFun_injective
assert_kernel_only RootedDigraph.LocalChildCovering.toFun_surjective
assert_kernel_only RootedDigraph.LocalChildCovering.child_map_inv
assert_kernel_only RootedDigraph.LocalChildCovering.source_unique_parent
assert_kernel_only RootedDigraph.LocalChildCovering.childFiber_bijective
assert_kernel_only RootedDigraph.LocalChildCovering.toIso

end TetraStereo.OneCenter.DeclarativeCIP
