import TetraStereo.OneCenter.DeclarativeCIPContextualReferenceSelection
import TetraStereo.OneCenter.DeclarativeCIPMultiReferenceProblem
import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidenceNaturality
import TetraStereo.OneCenter.DeclarativeCIPObservedOrdinaryIso
import TetraStereo.OneCenter.DeclarativeCIPContextualConstitutionalIso
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Isomorphism invariance of observer-parametric P-92.5.2.1 selection. The ordinary rank key is
transported by the observed-key isomorphism theorem; eligibility and physical nearest-sphere
membership are transported by molecular evidence naturality. -/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
universe u

section ContextualSelectionIso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule)
  {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)
  (leftObserve : ConstitutionalRule → left.Node → ℤ)
  (rightObserve : ConstitutionalRule → right.Node → ℤ)
  (observeEq : ∀ rule node, rightObserve rule (iso.toEquiv node) = leftObserve rule node)

local instance contextualSelectionIsoLeftFintype : Fintype left.Node := left.nodeFintype
local instance contextualSelectionIsoRightFintype : Fintype right.Node := right.nodeFintype

include observeEq in
theorem observedRankKey_iso (node : left.Node) :
    observedRankKey molecule descriptorMap unit right rightObserve (iso.toEquiv node) =
      observedRankKey molecule descriptorMap unit left leftObserve node := by
  unfold observedRankKey
  rw [width_iso iso, height_iso iso]
  exact ordinaryKeyWithObservations_iso iso leftObserve rightObserve left.width left.height
    observeEq (rankEvidence_preserved molecule descriptorMap unit iso) node

include observeEq in
theorem observedRankPath_iso (node : left.Node) :
    observedRankPath molecule descriptorMap unit right rightObserve (iso.toEquiv node) =
      observedRankPath molecule descriptorMap unit left leftObserve node := by
  unfold observedRankPath
  rw [ancestorChain_iso iso node, List.map_map]
  apply List.map_congr_left
  intro ancestor _
  exact observedRankKey_iso molecule descriptorMap unit iso leftObserve rightObserve observeEq ancestor

include observeEq in
theorem observedInReferenceClass_iso (node : left.Node) :
    ObservedInReferenceClass molecule descriptorMap unit right rightObserve (iso.toEquiv node) ↔
      ObservedInReferenceClass molecule descriptorMap unit left leftObserve node := by
  unfold ObservedInReferenceClass
  constructor
  · rintro ⟨nearest, maximal⟩
    refine ⟨(nearestEligible_iso molecule descriptorMap unit iso node).mpr nearest, ?_⟩
    intro other hother
    have otherRight := (nearestEligible_iso molecule descriptorMap unit iso other).mp hother
    have hle := maximal (iso.toEquiv other) otherRight
    rw [observedRankPath_iso molecule descriptorMap unit iso leftObserve rightObserve observeEq other,
      observedRankPath_iso molecule descriptorMap unit iso leftObserve rightObserve observeEq node] at hle
    exact hle
  · rintro ⟨nearest, maximal⟩
    refine ⟨(nearestEligible_iso molecule descriptorMap unit iso node).mp nearest, ?_⟩
    intro other hother
    have otherLeft := (nearestEligible_iso molecule descriptorMap unit iso.symm other).mp hother
    have hle := maximal (iso.toEquiv.symm other) otherLeft
    have otherPath :
        observedRankPath molecule descriptorMap unit right rightObserve other =
          observedRankPath molecule descriptorMap unit left leftObserve (iso.toEquiv.symm other) := by
      simpa using observedRankPath_iso molecule descriptorMap unit iso leftObserve rightObserve
        observeEq (iso.toEquiv.symm other)
    have nodePath :
        observedRankPath molecule descriptorMap unit right rightObserve (iso.toEquiv node) =
          observedRankPath molecule descriptorMap unit left leftObserve node :=
      observedRankPath_iso molecule descriptorMap unit iso leftObserve rightObserve observeEq node
    calc
      observedRankPath molecule descriptorMap unit right rightObserve other ≤
          observedRankPath molecule descriptorMap unit right rightObserve (iso.toEquiv node) := by
        rw [otherPath, nodePath]
        exact hle

include iso observeEq in
theorem observedSeniorCount_iso :
    observedSeniorCount molecule descriptorMap unit right rightObserve =
      observedSeniorCount molecule descriptorMap unit left leftObserve := by
  unfold observedSeniorCount observedReferenceClass
  symm
  apply Finset.card_equiv iso.toEquiv
  intro node
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [observedInReferenceClass_iso molecule descriptorMap unit iso leftObserve rightObserve
      observeEq node,
    eligibleSense_iso molecule descriptorMap unit iso node]

include iso observeEq in
theorem observedJuniorCount_iso :
    observedJuniorCount molecule descriptorMap unit right rightObserve =
      observedJuniorCount molecule descriptorMap unit left leftObserve := by
  unfold observedJuniorCount observedReferenceClass
  symm
  apply Finset.card_equiv iso.toEquiv
  intro node
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [observedInReferenceClass_iso molecule descriptorMap unit iso leftObserve rightObserve
      observeEq node,
    eligibleSense_iso molecule descriptorMap unit iso node]

include iso observeEq in
theorem observedReferenceSelection_iso :
    observedReferenceSelection molecule descriptorMap unit right rightObserve =
      observedReferenceSelection molecule descriptorMap unit left leftObserve := by
  unfold observedReferenceSelection
  have existsRight : (∃ node, Eligible molecule descriptorMap unit right node) ↔
      (∃ node, Eligible molecule descriptorMap unit left node) := by
    constructor
    · rintro ⟨node, hn⟩
      exact ⟨iso.toEquiv.symm node,
        (eligible_iso molecule descriptorMap unit iso (iso.toEquiv.symm node)).2
          (by simpa using hn)⟩
    · rintro ⟨node, hn⟩
      exact ⟨iso.toEquiv node, (eligible_iso molecule descriptorMap unit iso node).1 hn⟩
  by_cases hleft : ∃ node, Eligible molecule descriptorMap unit left node
  · have hright := existsRight.mpr hleft
    rw [if_neg (not_not.mpr hleft), if_neg (not_not.mpr hright)]
    rw [observedJuniorCount_iso molecule descriptorMap unit iso leftObserve rightObserve observeEq,
      observedSeniorCount_iso molecule descriptorMap unit iso leftObserve rightObserve observeEq]
  · have hright : ¬ ∃ node, Eligible molecule descriptorMap unit right node := by
      intro h
      exact hleft (existsRight.mp h)
    rw [if_pos hleft, if_pos hright]

/-- Specialization: contextual reference selection on two faithful representations with the same
retained physical outer root is representation-independent. -/
theorem contextualReferenceSelection_iso (isomorphism : RootedDigraph.Iso left right)
    (outerRoot : Atom) :
    observedReferenceSelection molecule descriptorMap unit right
      (contextualNodeObservation molecule right outerRoot) =
    observedReferenceSelection molecule descriptorMap unit left
      (contextualNodeObservation molecule left outerRoot) := by
  apply observedReferenceSelection_iso molecule descriptorMap unit isomorphism
    (contextualNodeObservation molecule left outerRoot)
    (contextualNodeObservation molecule right outerRoot)
  intro rule node
  exact contextualNodeObservation_iso molecule isomorphism outerRoot rule node

end ContextualSelectionIso

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankKey_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankPath_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedInReferenceClass_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedSeniorCount_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedJuniorCount_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedReferenceSelection_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualReferenceSelection_iso
