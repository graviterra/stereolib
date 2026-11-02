import TetraStereo.OneCenter.DeclarativeCIPObservedReadingKeyProjection
import TetraStereo.OneCenter.DeclarativeCIPContextualReferenceIso
import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingSignature
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Complete Rule-4b/4c readings under a retained physical outer-root observer.
The auxiliary constitutional context is explicit in every ordinary-key projection and in
reference selection. The empty uppercase-reference population keeps its separate Rule-4c
reading; possible lowercase descriptors remain part of that observation. -/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
universe u
open Certificate.CanonicalSphereKey (Key)

section ContextualReading

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance contextualCompleteReadingNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- A complete alternative reading at one shared layout, retaining the unit's physical outer
root in all constitutional observations. `none` is the genuine no-uppercase-reference case. -/
def contextualCompleteReadingAt (W D : ℕ) (reference : Option DescriptorSense) :
    CompleteReadingKey :=
  let observe := contextualNodeObservation molecule graph unit.1.root
  match reference with
  | none => toLex ([], observedRule4cComponent graph observe
      (noReferenceEvidence4c molecule descriptorMap unit graph) W D graph.root)
  | some sense => toLex
      (observedRule4bComponent graph observe
          (readingEvidence molecule descriptorMap unit graph sense) W D graph.root,
        observedRule4cComponent graph observe
          (readingEvidence4c molecule descriptorMap unit graph sense) W D graph.root)

/-- Complete alternatives in descending order under contextual Rule-4b then Rule-4c readings. -/
def contextualCompleteReadingsAt (W D : ℕ) : List CompleteReadingKey :=
  match contextualReferenceSelection molecule descriptorMap unit graph with
  | .empty => [contextualCompleteReadingAt molecule descriptorMap unit graph W D none]
  | .one sense => [contextualCompleteReadingAt molecule descriptorMap unit graph W D (some sense)]
  | .both =>
      let first := contextualCompleteReadingAt molecule descriptorMap unit graph W D (some .senior)
      let second := contextualCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
      [max first second, min first second]

/-- The contextual count, all Rule-4b readings, then all Rule-4c readings in one alternative
order. An empty reference population still contributes its genuine Rule-4c observation. -/
def contextualCompletePriorSignatureAt (W D : ℕ) : CompletePriorSignature :=
  let selection := contextualReferenceSelection molecule descriptorMap unit graph
  let readings := contextualCompleteReadingsAt molecule descriptorMap unit graph W D
  toLex (selection.countPriority, toLex
    ((if selection = .empty then [] else readings.map (fun key => (ofLex key).1)),
      readings.map (fun key => (ofLex key).2)))

theorem contextualCompleteReadingsAt_length (W D : ℕ) :
    (contextualCompleteReadingsAt molecule descriptorMap unit graph W D).length =
      if contextualReferenceSelection molecule descriptorMap unit graph = .both then 2 else 1 := by
  unfold contextualCompleteReadingsAt
  cases contextualReferenceSelection molecule descriptorMap unit graph <;> simp

theorem contextualCompletePriorSignatureAt_empty (W D : ℕ)
    (empty : contextualReferenceSelection molecule descriptorMap unit graph = .empty) :
    contextualCompletePriorSignatureAt molecule descriptorMap unit graph W D =
      toLex (0, toLex ([], [observedRule4cComponent graph
        (contextualNodeObservation molecule graph unit.1.root)
        (noReferenceEvidence4c molecule descriptorMap unit graph) W D graph.root])) := by
  simp [contextualCompletePriorSignatureAt, contextualCompleteReadingsAt,
    contextualCompleteReadingAt, empty, ReferenceSelection.countPriority]

end ContextualReading

section Reflection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)

local instance contextualReferenceReflectNodeFintype : Fintype graph.Node := graph.nodeFintype

theorem observedRankKey_reflect (node : graph.Node) :
    observedRankKey molecule descriptorMap.reflect unit graph observe node =
      observedRankKey molecule descriptorMap unit graph observe node := by
  unfold observedRankKey
  rw [rankEvidence_reflect]

theorem observedRankPath_reflect (node : graph.Node) :
    observedRankPath molecule descriptorMap.reflect unit graph observe node =
      observedRankPath molecule descriptorMap unit graph observe node := by
  unfold observedRankPath
  apply List.map_congr_left
  intro ancestor _
  exact observedRankKey_reflect molecule descriptorMap unit graph observe ancestor

theorem observedInReferenceClass_reflect (node : graph.Node) :
    ObservedInReferenceClass molecule descriptorMap.reflect unit graph observe node ↔
      ObservedInReferenceClass molecule descriptorMap unit graph observe node := by
  unfold ObservedInReferenceClass
  simp only [nearestEligible_reflect,
    observedRankPath_reflect molecule descriptorMap unit graph observe]

theorem observedReferenceClass_reflect :
    observedReferenceClass molecule descriptorMap.reflect unit graph observe =
      observedReferenceClass molecule descriptorMap unit graph observe := by
  unfold observedReferenceClass
  ext node
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    observedInReferenceClass_reflect molecule descriptorMap unit graph observe]

theorem observedSeniorCount_reflect :
    observedSeniorCount molecule descriptorMap.reflect unit graph observe =
      observedJuniorCount molecule descriptorMap unit graph observe := by
  unfold observedSeniorCount observedJuniorCount
  rw [observedReferenceClass_reflect]
  congr 1
  ext node
  simp only [Finset.mem_filter, eligibleSense_reflect]
  constructor
  · rintro ⟨hmem, h⟩
    refine ⟨hmem, ?_⟩
    cases hsense : eligibleSense molecule descriptorMap unit graph node with
    | none => simp [hsense] at h
    | some sense => cases sense <;> simp_all [DescriptorSense.mirror]
  · rintro ⟨hmem, h⟩
    exact ⟨hmem, by simp [h, DescriptorSense.mirror]⟩

theorem observedJuniorCount_reflect :
    observedJuniorCount molecule descriptorMap.reflect unit graph observe =
      observedSeniorCount molecule descriptorMap unit graph observe := by
  unfold observedJuniorCount observedSeniorCount
  rw [observedReferenceClass_reflect]
  congr 1
  ext node
  simp only [Finset.mem_filter, eligibleSense_reflect]
  constructor
  · rintro ⟨hmem, h⟩
    refine ⟨hmem, ?_⟩
    cases hsense : eligibleSense molecule descriptorMap unit graph node with
    | none => simp [hsense] at h
    | some sense => cases sense <;> simp_all [DescriptorSense.mirror]
  · rintro ⟨hmem, h⟩
    exact ⟨hmem, by simp [h, DescriptorSense.mirror]⟩

theorem observedReferenceSelection_reflect :
    observedReferenceSelection molecule descriptorMap.reflect unit graph observe =
      (observedReferenceSelection molecule descriptorMap unit graph observe).mirror := by
  unfold observedReferenceSelection
  simp only [eligible_reflect, observedJuniorCount_reflect molecule descriptorMap unit graph observe,
    observedSeniorCount_reflect molecule descriptorMap unit graph observe]
  by_cases hex : ∃ node, Eligible molecule descriptorMap unit graph node
  · simp only [hex, not_true_eq_false, if_false]
    by_cases hlt : observedSeniorCount molecule descriptorMap unit graph observe <
        observedJuniorCount molecule descriptorMap unit graph observe
    · have hnot := lt_asymm hlt
      simp [hlt, hnot, ReferenceSelection.mirror, DescriptorSense.mirror]
    · by_cases hgt : observedJuniorCount molecule descriptorMap unit graph observe <
          observedSeniorCount molecule descriptorMap unit graph observe
      · simp [hlt, hgt, ReferenceSelection.mirror, DescriptorSense.mirror]
      · simp [hlt, hgt, ReferenceSelection.mirror]
  · simp [hex, ReferenceSelection.mirror]

theorem contextualReferenceSelection_reflect :
    contextualReferenceSelection molecule descriptorMap.reflect unit graph =
      (contextualReferenceSelection molecule descriptorMap unit graph).mirror := by
  unfold contextualReferenceSelection
  exact observedReferenceSelection_reflect molecule descriptorMap unit graph
    (contextualNodeObservation molecule graph unit.1.root)

theorem contextualCompleteReadingAt_reflect (W D : ℕ) (reference : Option DescriptorSense) :
    contextualCompleteReadingAt molecule descriptorMap.reflect unit graph W D reference =
      contextualCompleteReadingAt molecule descriptorMap unit graph W D
        (reference.map DescriptorSense.mirror) := by
  cases reference with
  | none =>
      simp [contextualCompleteReadingAt, noReferenceEvidence4c_reflect]
  | some sense =>
      simp [contextualCompleteReadingAt, readingEvidence_reflect, readingEvidence4c_reflect]

theorem contextualCompleteReadingsAt_reflect (W D : ℕ) :
    contextualCompleteReadingsAt molecule descriptorMap.reflect unit graph W D =
      contextualCompleteReadingsAt molecule descriptorMap unit graph W D := by
  unfold contextualCompleteReadingsAt
  rw [contextualReferenceSelection_reflect molecule descriptorMap unit graph]
  cases contextualReferenceSelection molecule descriptorMap unit graph with
  | empty => simp [contextualCompleteReadingAt_reflect, ReferenceSelection.mirror]
  | one sense =>
      simp [contextualCompleteReadingAt_reflect, ReferenceSelection.mirror,
        DescriptorSense.mirror_mirror]
  | both =>
      simp only [ReferenceSelection.mirror, contextualCompleteReadingAt_reflect,
        Option.map_some, DescriptorSense.mirror]
      rw [max_comm, min_comm]

theorem contextualCompletePriorSignatureAt_reflect (W D : ℕ) :
    contextualCompletePriorSignatureAt molecule descriptorMap.reflect unit graph W D =
      contextualCompletePriorSignatureAt molecule descriptorMap unit graph W D := by
  unfold contextualCompletePriorSignatureAt
  simp only [contextualReferenceSelection_reflect molecule descriptorMap unit graph,
    contextualCompleteReadingsAt_reflect molecule descriptorMap unit graph]
  cases contextualReferenceSelection molecule descriptorMap unit graph <;> rfl

end Reflection

section Iso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)

local instance contextualCompleteIsoLeftNodeFintype : Fintype left.Node := left.nodeFintype
local instance contextualCompleteIsoRightNodeFintype : Fintype right.Node := right.nodeFintype

private theorem contextualObservedRule4bComponent_iso
    (isomorphism : RootedDigraph.Iso left right) (W D : ℕ) (sense : DescriptorSense) :
    observedRule4bComponent right (contextualNodeObservation molecule right unit.1.root)
        (readingEvidence molecule descriptorMap unit right sense) W D right.root =
      observedRule4bComponent left (contextualNodeObservation molecule left unit.1.root)
        (readingEvidence molecule descriptorMap unit left sense) W D left.root := by
  unfold observedRule4bComponent
  rw [← isomorphism.map_root]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4bLikeUnlikeDescriptorPairs) [])
    (ordinaryKeyWithObservations_iso isomorphism
      (contextualNodeObservation molecule left unit.1.root)
      (contextualNodeObservation molecule right unit.1.root)
      W D
      (fun rule node => contextualNodeObservation_iso molecule isomorphism unit.1.root rule node)
      (readingEvidence_preserved molecule descriptorMap unit isomorphism sense) left.root)

private theorem contextualObservedRule4cComponent_reading_iso
    (isomorphism : RootedDigraph.Iso left right) (W D : ℕ) (sense : DescriptorSense) :
    observedRule4cComponent right (contextualNodeObservation molecule right unit.1.root)
        (readingEvidence4c molecule descriptorMap unit right sense) W D right.root =
      observedRule4cComponent left (contextualNodeObservation molecule left unit.1.root)
        (readingEvidence4c molecule descriptorMap unit left sense) W D left.root := by
  unfold observedRule4cComponent
  rw [← isomorphism.map_root]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) [])
    (ordinaryKeyWithObservations_iso isomorphism
      (contextualNodeObservation molecule left unit.1.root)
      (contextualNodeObservation molecule right unit.1.root)
      W D
      (fun rule node => contextualNodeObservation_iso molecule isomorphism unit.1.root rule node)
      (readingEvidence4c_preserved molecule descriptorMap unit isomorphism sense) left.root)

private theorem contextualObservedRule4cComponent_noReference_iso
    (isomorphism : RootedDigraph.Iso left right) (W D : ℕ) :
    observedRule4cComponent right (contextualNodeObservation molecule right unit.1.root)
        (noReferenceEvidence4c molecule descriptorMap unit right) W D right.root =
      observedRule4cComponent left (contextualNodeObservation molecule left unit.1.root)
        (noReferenceEvidence4c molecule descriptorMap unit left) W D left.root := by
  unfold observedRule4cComponent
  rw [← isomorphism.map_root]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) [])
    (ordinaryKeyWithObservations_iso isomorphism
      (contextualNodeObservation molecule left unit.1.root)
      (contextualNodeObservation molecule right unit.1.root)
      W D
      (fun rule node => contextualNodeObservation_iso molecule isomorphism unit.1.root rule node)
      (noReferenceEvidence4c_preserved molecule descriptorMap unit isomorphism) left.root)

theorem contextualCompleteReadingAt_iso
    (isomorphism : RootedDigraph.Iso left right) (W D : ℕ)
    (reference : Option DescriptorSense) :
    contextualCompleteReadingAt molecule descriptorMap unit right W D reference =
      contextualCompleteReadingAt molecule descriptorMap unit left W D reference := by
  cases reference with
  | none =>
      exact congrArg (fun key : Key StereoLabel => toLex ([], key))
        (contextualObservedRule4cComponent_noReference_iso molecule descriptorMap unit
          isomorphism W D)
  | some sense =>
      exact congrArg (fun pair : Key StereoLabel × Key StereoLabel => toLex pair)
        (Prod.ext
          (contextualObservedRule4bComponent_iso molecule descriptorMap unit isomorphism W D sense)
          (contextualObservedRule4cComponent_reading_iso molecule descriptorMap unit
            isomorphism W D sense))

include iso in
theorem contextualCompleteReadingsAt_iso (W D : ℕ) :
    contextualCompleteReadingsAt molecule descriptorMap unit right W D =
      contextualCompleteReadingsAt molecule descriptorMap unit left W D := by
  unfold contextualCompleteReadingsAt
  simp only [contextualReferenceSelection]
  rw [contextualReferenceSelection_iso molecule descriptorMap unit iso unit.1.root]
  simp only [contextualCompleteReadingAt_iso molecule descriptorMap unit iso W D]

include iso in
theorem contextualCompletePriorSignatureAt_iso (W D : ℕ) :
    contextualCompletePriorSignatureAt molecule descriptorMap unit right W D =
      contextualCompletePriorSignatureAt molecule descriptorMap unit left W D := by
  unfold contextualCompletePriorSignatureAt
  simp only [contextualReferenceSelection]
  simp_rw [contextualReferenceSelection_iso molecule descriptorMap unit iso unit.1.root,
    contextualCompleteReadingsAt_iso molecule descriptorMap unit iso W D]

end Iso
end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteReadingsAt_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompletePriorSignatureAt_empty
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankKey_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankPath_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedInReferenceClass_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedReferenceClass_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedSeniorCount_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedJuniorCount_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedReferenceSelection_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualReferenceSelection_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteReadingAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteReadingsAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompletePriorSignatureAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteReadingAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteReadingsAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompletePriorSignatureAt_iso
