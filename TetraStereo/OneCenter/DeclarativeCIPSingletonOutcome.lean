import TetraStereo.OneCenter.DeclarativeCIPFinalTetrahedralOutcome
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Singleton terminal digraphs compare through their rule observations, not raw atom identities.
This algebra is consumed by the physical terminal-twin construction, which derives singleton
shape, absence of multiple bonds and outside-inventory readings from the actual molecular input. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open RootedDigraph
open Certificate.CanonicalSphereKey

universe u
noncomputable section
open scoped Classical

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

omit [Fintype Atom] [DecidableEq Atom] in
theorem singleton_childList_root (graph : RootedDigraph Atom)
    (singleton : ∀ node : graph.Node, node = graph.root) :
    graph.childList graph.root = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node member
  have depth := graph.child_depth ((graph.mem_childList).1 member)
  rw [singleton node, graph.root_depth] at depth
  omega

theorem singleton_rankedOrdinaryKeys (molecule : MoleculeGraph Atom)
    (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)
    (singleton : ∀ node : graph.Node, node = graph.root) (W D : Nat) :
    rankedOrdinaryKeys molecule graph evidence W D graph.root = [] := by
  simp [rankedOrdinaryKeys, singleton_childList_root graph singleton, sortDesc]

theorem selection_empty_of_singleton_outside
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
    (singleton : ∀ node : graph.Node, node = graph.root)
    (outside : occurrenceReading molecule descriptorMap unit graph graph.root = .outsideInventory) :
    referenceSelection molecule descriptorMap unit graph = .empty := by
  apply (referenceSelection_eq_empty_iff molecule descriptorMap unit graph).2
  rintro ⟨node, eligible⟩
  rw [singleton node] at eligible
  simp [Eligible, eligibleSense, outside] at eligible

section Pair

variable (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (left right : RootedDigraph Atom)
  (singletonL : ∀ node : left.Node, node = left.root)
  (singletonR : ∀ node : right.Node, node = right.root)
  (outsideL : occurrenceReading molecule descriptorMap unit left left.root = .outsideInventory)
  (outsideR : occurrenceReading molecule descriptorMap unit right right.root = .outsideInventory)
  (noMultipleL : ¬ HasMultipleBond molecule (left.label left.root))
  (noMultipleR : ¬ HasMultipleBond molecule (right.label right.root))

include singletonL singletonR noMultipleL noMultipleR in
theorem singleton_rule3Key_eq (W D : Nat) :
    ligandRule3Key molecule descriptorMap unit left W D =
      ligandRule3Key molecule descriptorMap unit right W D := by
  unfold ligandRule3Key
  rw [ordinaryKey_stereo_getD, ordinaryKey_stereo_getD,
    singleton_rankedOrdinaryKeys molecule left _ singletonL,
    singleton_rankedOrdinaryKeys molecule right _ singletonR]
  simp [stereoComponent, stereoLabel, stereoValue, rankEvidence,
    rule3Observation, noMultipleL, noMultipleR]

include singletonL singletonR outsideL outsideR in
theorem singleton_rule4aKey_eq (W D : Nat) :
    ligandRule4aKey molecule descriptorMap unit left W D =
      ligandRule4aKey molecule descriptorMap unit right W D := by
  unfold ligandRule4aKey rule4aComponent
  rw [ordinaryKey_stereo_getD, ordinaryKey_stereo_getD,
    singleton_rankedOrdinaryKeys molecule left _ singletonL,
    singleton_rankedOrdinaryKeys molecule right _ singletonR]
  simp [stereoComponent, stereoLabel, stereoValue, rankEvidence,
    rule4aObservation, outsideL, outsideR]

include singletonL singletonR outsideL outsideR in
theorem singleton_rule4cKey_eq (W D : Nat) :
    ligandRule4cKey molecule descriptorMap unit left W D =
      ligandRule4cKey molecule descriptorMap unit right W D := by
  unfold ligandRule4cKey
  rw [ordinaryKey_stereo_getD, ordinaryKey_stereo_getD,
    singleton_rankedOrdinaryKeys molecule left _ singletonL,
    singleton_rankedOrdinaryKeys molecule right _ singletonR]
  simp [stereoComponent, stereoLabel, stereoValue, molecularEvidence,
    rule4cObservation, outsideL, outsideR]

include singletonL singletonR outsideL outsideR in
theorem singleton_signature_eq (W D : Nat) :
    ligandSignatureAt molecule descriptorMap unit left W D =
      ligandSignatureAt molecule descriptorMap unit right W D := by
  simp [ligandSignatureAt,
    selection_empty_of_singleton_outside molecule descriptorMap unit left singletonL outsideL,
    selection_empty_of_singleton_outside molecule descriptorMap unit right singletonR outsideR]

include singletonL singletonR outsideL outsideR in
theorem singleton_rule5Stream_eq (path : List Nat) :
    ligandRule5Stream molecule descriptorMap unit left path =
      ligandRule5Stream molecule descriptorMap unit right path := by
  simp [ligandRule5Stream, headSense,
    selection_empty_of_singleton_outside molecule descriptorMap unit left singletonL outsideL,
    selection_empty_of_singleton_outside molecule descriptorMap unit right singletonR outsideR]

include singletonL singletonR outsideL outsideR noMultipleL noMultipleR in
/-- No later ordinary rule or Rule 6 can order two unmarked single nodes. -/
theorem singleton_later_judgment_not_gt (rule : SequenceRule)
    (later : 3 ≤ rule.rank) :
    ¬ MultiReferenceJudgment molecule descriptorMap unit rule left right .gt := by
  cases rule with
  | rule1aAtomicNumber => simp [SequenceRule.rank] at later
  | rule1bDuplicateNodeProximity => simp [SequenceRule.rank] at later
  | rule2AtomicMass => simp [SequenceRule.rank] at later
  | rule3DoubleBondGeometry =>
      simp only [MultiReferenceJudgment]
      rw [singleton_rule3Key_eq molecule descriptorMap unit left right singletonL singletonR
        noMultipleL noMultipleR]
      simp
  | rule4aStereogenicUnitKind =>
      simp only [MultiReferenceJudgment]
      rw [singleton_rule4aKey_eq molecule descriptorMap unit left right singletonL singletonR
        outsideL outsideR]
      simp
  | rule4bLikeUnlikeDescriptorPairs =>
      simp only [MultiReferenceJudgment]
      rw [singleton_signature_eq molecule descriptorMap unit left right singletonL singletonR
        outsideL outsideR]
      simp [ligandSignatureAt,
        selection_empty_of_singleton_outside molecule descriptorMap unit right singletonR outsideR,
        signatureCompare, List.compareLex]
  | rule4cPseudoasymmetricDescriptor =>
      simp only [MultiReferenceJudgment]
      rw [singleton_rule4cKey_eq molecule descriptorMap unit left right singletonL singletonR
        outsideL outsideR]
      simp
  | rule5EnantiomorphicDescriptor =>
      rintro ⟨path, decisive, _⟩
      rw [singleton_rule5Stream_eq molecule descriptorMap unit left right singletonL singletonR
        outsideL outsideR] at decisive
      simp at decisive
  | rule6ReferencePromotion => exact id

end Pair
end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.singleton_childList_root
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.selection_empty_of_singleton_outside
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.singleton_later_judgment_not_gt
