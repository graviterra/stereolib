import TetraStereo.OneCenter.DeclarativeCIPMolecularReferenceSelection
import TetraStereo.OneCenter.DeclarativeCIPObservedOrdinaryKey
import TetraStereo.OneCenter.DeclarativeCIPContextualConstitutional
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! P-92.5.2.1 reference selection with an explicit constitutional observer.

Eligibility, nearest-sphere filtering, ancestor-chain ranking, equal-rank classes and majority
selection are unchanged from `referenceSelection`; only the ordinary key used for rank paths is
parameterized. This lets an auxiliary key retain its physical outer-root context. -/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
universe u

section ContextualSelection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)

local instance contextualSelectionNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Ordinary key used for ancestor ranking under an independent constitutional observer. -/
def observedRankKey (node : graph.Node) : OrdinaryKey :=
  ordinaryKeyWithObservations graph observe
    (rankEvidence molecule descriptorMap unit graph) graph.width graph.height node

/-- Ancestor rank path under the supplied constitutional observation. -/
def observedRankPath (node : graph.Node) : List OrdinaryKey :=
  (ancestorChain graph node).map (observedRankKey molecule descriptorMap unit graph observe)

/-- Nearest eligible occurrences of maximal observed ancestor rank path. -/
def ObservedInReferenceClass (node : graph.Node) : Prop :=
  NearestEligible molecule descriptorMap unit graph node ∧
    ∀ other, NearestEligible molecule descriptorMap unit graph other →
      observedRankPath molecule descriptorMap unit graph observe other ≤
        observedRankPath molecule descriptorMap unit graph observe node

def observedReferenceClass : Finset graph.Node :=
  Finset.univ.filter (ObservedInReferenceClass molecule descriptorMap unit graph observe)

def observedSeniorCount : ℕ :=
  ((observedReferenceClass molecule descriptorMap unit graph observe).filter fun node =>
    eligibleSense molecule descriptorMap unit graph node = some .senior).card

def observedJuniorCount : ℕ :=
  ((observedReferenceClass molecule descriptorMap unit graph observe).filter fun node =>
    eligibleSense molecule descriptorMap unit graph node = some .junior).card

/-- The normative P-92.5.2.1 result after ranking with the observer-parametric ordinary key. -/
def observedReferenceSelection : ReferenceSelection :=
  if ¬ ∃ node, Eligible molecule descriptorMap unit graph node then .empty
  else if observedJuniorCount molecule descriptorMap unit graph observe <
      observedSeniorCount molecule descriptorMap unit graph observe then .one .senior
  else if observedSeniorCount molecule descriptorMap unit graph observe <
      observedJuniorCount molecule descriptorMap unit graph observe then .one .junior
  else .both

theorem observedRankKey_congr
    (other : ConstitutionalRule → graph.Node → ℤ)
    (same : ∀ rule node, observe rule node = other rule node) (node : graph.Node) :
    observedRankKey molecule descriptorMap unit graph observe node =
      observedRankKey molecule descriptorMap unit graph other node := by
  unfold observedRankKey
  exact ordinaryKeyWithObservations_congr graph observe
    (rankEvidence molecule descriptorMap unit graph) other same graph.width graph.height node

theorem observedRankPath_congr
    (other : ConstitutionalRule → graph.Node → ℤ)
    (same : ∀ rule node, observe rule node = other rule node) (node : graph.Node) :
    observedRankPath molecule descriptorMap unit graph observe node =
      observedRankPath molecule descriptorMap unit graph other node := by
  unfold observedRankPath
  apply List.map_congr_left
  intro ancestor _
  exact observedRankKey_congr molecule descriptorMap unit graph observe other same ancestor

theorem observedReferenceSelection_congr
    (other : ConstitutionalRule → graph.Node → ℤ)
    (same : ∀ rule node, observe rule node = other rule node) :
    observedReferenceSelection molecule descriptorMap unit graph observe =
      observedReferenceSelection molecule descriptorMap unit graph other := by
  unfold observedReferenceSelection observedSeniorCount observedJuniorCount
    observedReferenceClass
  have classes :
      Finset.univ.filter (ObservedInReferenceClass molecule descriptorMap unit graph observe) =
        Finset.univ.filter (ObservedInReferenceClass molecule descriptorMap unit graph other) := by
    congr 1
    funext node
    apply propext
    unfold ObservedInReferenceClass
    constructor
    · rintro ⟨nearest, maximal⟩
      refine ⟨nearest, fun candidate hcand => ?_⟩
      simpa [observedRankPath_congr molecule descriptorMap unit graph observe other same candidate,
        observedRankPath_congr molecule descriptorMap unit graph observe other same node] using
          maximal candidate hcand
    · rintro ⟨nearest, maximal⟩
      refine ⟨nearest, fun candidate hcand => ?_⟩
      simpa [observedRankPath_congr molecule descriptorMap unit graph observe other same candidate,
        observedRankPath_congr molecule descriptorMap unit graph observe other same node] using
          maximal candidate hcand
  rw [classes]

/-- At the established node observer, contextual rank paths recover the existing P-92.5.2.1 paths. -/
theorem observedRankPath_eq_rankPath (node : graph.Node) :
    observedRankPath molecule descriptorMap unit graph (nodeObservation molecule graph) node =
      rankPath molecule descriptorMap unit graph node := by
  unfold observedRankPath rankPath observedRankKey rankKey
  apply List.map_congr_left
  intro ancestor _
  exact ordinaryKeyWithObservations_eq_ordinaryKey (graph := graph)
    (evidence := rankEvidence molecule descriptorMap unit graph) molecule
    graph.width graph.height ancestor

theorem observedReferenceSelection_eq_referenceSelection :
    observedReferenceSelection molecule descriptorMap unit graph
      (nodeObservation molecule graph) = referenceSelection molecule descriptorMap unit graph := by
  unfold observedReferenceSelection referenceSelection observedSeniorCount observedJuniorCount
    observedReferenceClass seniorCount juniorCount referenceClass
  have classes :
      Finset.univ.filter
        (ObservedInReferenceClass molecule descriptorMap unit graph (nodeObservation molecule graph)) =
      Finset.univ.filter (InReferenceClass molecule descriptorMap unit graph) := by
    congr 1
    funext node
    apply propext
    unfold ObservedInReferenceClass InReferenceClass
    constructor
    · rintro ⟨nearest, maximal⟩
      refine ⟨nearest, fun candidate hcand => ?_⟩
      simpa [observedRankPath_eq_rankPath molecule descriptorMap unit graph candidate,
        observedRankPath_eq_rankPath molecule descriptorMap unit graph node] using
          maximal candidate hcand
    · rintro ⟨nearest, maximal⟩
      refine ⟨nearest, fun candidate hcand => ?_⟩
      simpa [observedRankPath_eq_rankPath molecule descriptorMap unit graph candidate,
        observedRankPath_eq_rankPath molecule descriptorMap unit graph node] using
          maximal candidate hcand
  rw [classes]

/-- The specified retained-outer-root reference selection for a physical ligand occurrence. -/
def contextualReferenceSelection : ReferenceSelection :=
  observedReferenceSelection molecule descriptorMap unit graph
    (contextualNodeObservation molecule graph unit.1.root)

end ContextualSelection

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankKey_congr
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankPath_congr
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedReferenceSelection_congr
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankPath_eq_rankPath
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedReferenceSelection_eq_referenceSelection
