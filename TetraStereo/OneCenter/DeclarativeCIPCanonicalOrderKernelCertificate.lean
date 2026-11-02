import TetraStereo.OneCenter.DeclarativeCIPCanonicalOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Kernel-authority certificate for the generic path order and layout independence

This certificate covers the new public declarations of the generic canonical sphere key layer
(`TetraStereo.Certificate.CanonicalSphereKey`) and of the width/depth-independence layer
(`TetraStereo.OneCenter.DeclarativeCIP`):

* dense-slot/path conversion (`pathOf`, `pathOf_length`, `pathOf_digits`, `slotOf_pathOf`,
  `pathOf_slotOf`);
* the slot-free path observation of a key (`AddressBefore`, `pathObservationOf`,
  `keyObservation_eq_bot_of_out`, `pathObservationOf_pathOf`);
* key equality and order by the first path observation (`key_eq_iff_pathObservation`,
  `key_lt_iff_pathObservation`);
* the vector-key lift (`VectorWellShaped`, `vector_eq_iff_pathObservation`,
  `vector_lt_iff_pathObservation`);
* all public declarations of the canonical order module: the rule-index layout
  (`ruleOfIndex`, `ruleIndex_ruleOfIndex`), `ruleKey` shape and projections, the ranked children
  (`sortedChildren` and its permutation/sortedness lemmas), the path-observation recursion
  (`nodePathObservation_cons`, `depth_add_length_le_of_nodePathObservation`), the rule-major
  order/equality characterizations (`ruleKey_lt_iff`, `ruleKey_eq_iff`), and the layout-transport
  endpoints (`ruleKey_le_iff_of_observations`, `nodePathObservation_width_independent`,
  `ruleKey_le_iff_of_bounds`, `canonicalAddressing_iff_of_bounds`).

Every listed constant is checked by `assert_kernel_only`: its proof/definition closure may use only
`propext`, `Classical.choice`, and `Quot.sound`, and contains no `sorryAx`, project axiom, compiled
evaluator trust, or native decision procedure.

The certified scope is the mathematical one: a finite independent canonical order of nodes of one
rooted digraph, and invariance of its path observations, pair order, and addressing canonicality
under every adequate width/depth layout.  No claim is made about a production traversal, sparse-key
comparator agreement, chemical source fidelity, or runtime correctness; those remain with the
downstream integration and are not formalized here.  In particular, the node observation of a real
node stays the declarative `graph.depth + 1` distance of this module family; observer semantics are
unchanged.
-/

assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.pathOf
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.pathOf_length
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.pathOf_digits
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.slotOf_pathOf
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.pathOf_slotOf
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.AddressBefore
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.pathObservationOf
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.keyObservation_eq_bot_of_out
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.pathObservationOf_pathOf
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.key_eq_iff_pathObservation
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.key_lt_iff_pathObservation
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.VectorWellShaped
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.vector_eq_iff_pathObservation
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleOfIndex
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleIndex_ruleOfIndex
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_getD_of_index
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_getD_of_three_le
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_vectorWellShaped
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.nodePathObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.nodePathObservation_of_three_le
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.nodePathObservation_nil
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.sortedChildren
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.sortedChildren_perm
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.sortedChildren_pairwise
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.nodePathObservation_cons
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.depth_add_length_le_of_nodePathObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_eq_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_le_iff_of_observations
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.nodePathObservation_width_independent
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_le_iff_of_bounds
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.canonicalAddressing_iff_of_bounds
