import TetraStereo.OneCenter.DeclarativeCIPObservedOrdinaryKey
import TetraStereo.OneCenter.DeclarativeCIPContextualConstitutionalIso
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TetraStereo.OneCenter.DeclarativeCIP

noncomputable section
open scoped Classical
universe u

section ObservedOrdinaryIso

variable {Atom : Type u}
  {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)
  (leftObserve : ConstitutionalRule → left.Node → ℤ)
  (rightObserve : ConstitutionalRule → right.Node → ℤ)
  {leftEvidence : StereochemicalEvidence left}
  {rightEvidence : StereochemicalEvidence right}

local instance observedOrdinaryIsoLeftNodeFintype : Fintype left.Node := left.nodeFintype
local instance observedOrdinaryIsoRightNodeFintype : Fintype right.Node := right.nodeFintype

/-- The observed ordinary key is invariant under rooted isomorphisms preserving both supplied
constitutional observations and the explicit stereochemical evidence. -/
theorem ordinaryKeyWithObservations_iso (W D : ℕ)
    (observeEq : ∀ rule node,
      rightObserve rule (iso.toEquiv node) = leftObserve rule node)
    (evidencePreserved : RootedDigraph.Addressing.EvidencePreserved
      iso leftEvidence rightEvidence) :
    ∀ node : left.Node,
      ordinaryKeyWithObservations right rightObserve rightEvidence W D (iso.toEquiv node) =
        ordinaryKeyWithObservations left leftObserve leftEvidence W D node := by
  refine node_induction left (motive := fun node =>
    ordinaryKeyWithObservations right rightObserve rightEvidence W D (iso.toEquiv node) =
      ordinaryKeyWithObservations left leftObserve leftEvidence W D node) ?_
  intro node ih
  have hranked :
      rankedOrdinaryKeysWithObservations right rightObserve rightEvidence W D
          (iso.toEquiv node) =
        rankedOrdinaryKeysWithObservations left leftObserve leftEvidence W D node := by
    unfold rankedOrdinaryKeysWithObservations
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      ((childList_iso_perm iso node).map
        (ordinaryKeyWithObservations right rightObserve rightEvidence W D)),
      List.map_map]
    congr 1
    exact List.map_congr_left fun child hchild =>
      ih child ((left.mem_childList).1 hchild)
  rw [ordinaryKeyWithObservations_eq, ordinaryKeyWithObservations_eq, hranked]
  have evidenceLabelEq (rule : StereochemicalRule) :
      stereoLabel right rightEvidence rule (iso.toEquiv node) =
        stereoLabel left leftEvidence rule node := by
    unfold stereoLabel
    rw [← evidencePreserved node]
  simp only [ruleComponentWithObservations, stereoComponent, observeEq, evidenceLabelEq]

end ObservedOrdinaryIso

section ContextualIso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)
  (outerRoot : Atom)
  {leftEvidence : StereochemicalEvidence left}
  {rightEvidence : StereochemicalEvidence right}

local instance contextualOrdinaryIsoLeftNodeFintype : Fintype left.Node := left.nodeFintype
local instance contextualOrdinaryIsoRightNodeFintype : Fintype right.Node := right.nodeFintype

/-- Contextual ordinary keys are representation invariant for a fixed molecule and retained
outer root, provided the represented stereochemical evidence is preserved. -/
theorem contextualOrdinaryKey_iso (W D : ℕ) (node : left.Node)
    (evidencePreserved : RootedDigraph.Addressing.EvidencePreserved
      iso leftEvidence rightEvidence) :
    contextualOrdinaryKey right rightEvidence molecule outerRoot W D (iso.toEquiv node) =
      contextualOrdinaryKey left leftEvidence molecule outerRoot W D node := by
  unfold contextualOrdinaryKey
  exact ordinaryKeyWithObservations_iso iso
    (contextualNodeObservation molecule left outerRoot)
    (contextualNodeObservation molecule right outerRoot)
    W D
    (fun rule current => contextualNodeObservation_iso molecule iso outerRoot rule current)
    evidencePreserved node

end ContextualIso

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyWithObservations_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualOrdinaryKey_iso
