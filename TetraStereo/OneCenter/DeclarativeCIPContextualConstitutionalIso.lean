import TetraStereo.OneCenter.DeclarativeCIPContextualConstitutional
import TetraStereo.OneCenter.DeclarativeCIPCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (sortDesc)

noncomputable section
open scoped Classical

universe u
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

section GenericIso

variable {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)
  (leftObserve : ConstitutionalRule → left.Node → ℤ)
  (rightObserve : ConstitutionalRule → right.Node → ℤ)

local instance leftIsoKeyNodeFintype : Fintype left.Node := left.nodeFintype
local instance rightIsoKeyNodeFintype : Fintype right.Node := right.nodeFintype

omit [Fintype Atom] [DecidableEq Atom] in
/-- The generic observer-parametric rule-major key is invariant under a rooted graph
isomorphism whenever the supplied observations are preserved by the isomorphism. -/
theorem ruleKeyWithObservations_iso (W D : ℕ)
    (observeEq : ∀ rule node, rightObserve rule (iso.toEquiv node) = leftObserve rule node) :
    ∀ node : left.Node,
      ruleKeyWithObservations right W D rightObserve (iso.toEquiv node) =
        ruleKeyWithObservations left W D leftObserve node := by
  refine node_induction left (motive := fun node =>
    ruleKeyWithObservations right W D rightObserve (iso.toEquiv node) =
      ruleKeyWithObservations left W D leftObserve node) ?_
  intro node ih
  rw [ruleKeyWithObservations_eq, ruleKeyWithObservations_eq]
  have hchildren :
      sortDesc ((right.childList (iso.toEquiv node)).map
        (ruleKeyWithObservations right W D rightObserve)) =
      sortDesc ((left.childList node).map
        (ruleKeyWithObservations left W D leftObserve)) := by
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      ((childList_iso_perm iso node).map (ruleKeyWithObservations right W D rightObserve)),
      List.map_map]
    congr 1
    exact List.map_congr_left fun child hchild =>
      ih child ((left.mem_childList).1 hchild)
  simp only [ruleComponentWithObservations, observeEq, hchildren]

end GenericIso

section ContextualIso

variable (molecule : MoleculeGraph Atom)
  {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)
  (outerRoot : Atom)

local instance leftContextIsoNodeFintype : Fintype left.Node := left.nodeFintype
local instance rightContextIsoNodeFintype : Fintype right.Node := right.nodeFintype

/-- Contextual observations use retained-root molecular distances and are invariant when a
rooted-digraph representation isomorphism preserves the represented atom labels. -/
theorem contextualNodeObservation_iso (rule : ConstitutionalRule) (node : left.Node) :
    contextualNodeObservation molecule right outerRoot rule (iso.toEquiv node) =
      contextualNodeObservation molecule left outerRoot rule node := by
  cases rule <;>
    simp only [contextualNodeObservation, contextualRuleValue,
      ← iso.map_label node, ← iso.map_depth node]

/-- Contextual constitutional keys are representation-invariant for one fixed molecule and
retained outer root. -/
theorem contextualRuleKey_iso (W D : ℕ) :
    ∀ node : left.Node,
      contextualRuleKey molecule right outerRoot W D (iso.toEquiv node) =
        contextualRuleKey molecule left outerRoot W D node := by
  intro node
  unfold contextualRuleKey
  exact ruleKeyWithObservations_iso iso
    (contextualNodeObservation molecule left outerRoot)
    (contextualNodeObservation molecule right outerRoot) W D
    (fun rule current => contextualNodeObservation_iso molecule iso outerRoot rule current)
    node

end ContextualIso

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKeyWithObservations_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualNodeObservation_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualRuleKey_iso
