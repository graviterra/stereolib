import TetraStereo.OneCenter.DeclarativeCIPObservedCompleteReadingSignature
import TetraStereo.OneCenter.DeclarativeCIPCompleteRule5Order
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Complete Rule-5 order after retaining the physical outer-root observer in every
constitutional comparison.  The prior portion uses the contextual Rule-4b/4c signature;
the final stream decodes each alternative to the common absolute-R convention. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
open scoped Classical
open Certificate.CanonicalSphereKey (Key)
open Rule4aTableBridge (code)
universe u

abbrev ContextualCompleteLigandRule5Key := CompleteLigandRule5Key

section ContextualRule5

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance contextualRule5NodeFintype : Fintype graph.Node := graph.nodeFintype

private def contextualRule5ZeroLabel (_ : StereoLabel) : StereoLabel := code 0

/-- Alternative references in descending retained-context Rule-4b/4c order.  Ties keep the
stable senior-sense-first convention; no occurrence identity enters this ordering. -/
def contextualTaggedAlternativeReferencesAt (W D : ℕ) : List (Option DescriptorSense) :=
  match contextualReferenceSelection molecule descriptorMap unit graph with
  | .empty => [none]
  | .one sense => [some sense]
  | .both =>
      let senior := contextualCompleteReadingAt molecule descriptorMap unit graph W D
        (some .senior)
      let junior := contextualCompleteReadingAt molecule descriptorMap unit graph W D
        (some .junior)
      if compare senior junior = .lt then [some .junior, some .senior]
      else [some .senior, some .junior]

/-- Forgetting contextual reference tags recovers the contextual complete-reading order. -/
theorem contextualTaggedAlternativeReferencesAt_projection (W D : ℕ) :
    (contextualTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map
        (fun reference => contextualCompleteReadingAt molecule descriptorMap unit graph W D
          reference) =
      contextualCompleteReadingsAt molecule descriptorMap unit graph W D := by
  unfold contextualTaggedAlternativeReferencesAt contextualCompleteReadingsAt
  cases contextualReferenceSelection molecule descriptorMap unit graph with
  | empty => rfl
  | one sense => rfl
  | both =>
      let senior := contextualCompleteReadingAt molecule descriptorMap unit graph W D
        (some .senior)
      let junior := contextualCompleteReadingAt molecule descriptorMap unit graph W D
        (some .junior)
      have pair := completeReading_descendingPair senior junior
      have mapped :
          (if compare senior junior = .lt then [some .junior, some .senior]
            else [some .senior, some .junior]).map
              (fun reference => contextualCompleteReadingAt molecule descriptorMap unit graph
                W D reference) =
            if compare senior junior = .lt then [junior, senior] else [senior, junior] := by
        by_cases h : compare senior junior = .lt
        · simp only [if_pos h, List.map_cons, List.map_nil, contextualCompleteReadingAt]
          rfl
        · simp only [if_neg h, List.map_cons, List.map_nil, contextualCompleteReadingAt]
          rfl
      rw [mapped]
      exact pair

/-- Decode one contextual complete alternative into the common absolute-R or absolute-S
seniority convention.  A genuine no-reference alternative keeps its Rule-4c support while
all Rule-5 bits are zero. -/
def contextualCompleteRule5ReadingAt (W D : ℕ) (reference : Option DescriptorSense)
    (common : DescriptorSense := .senior) : Key StereoLabel :=
  match reference with
  | none => mapObservationKey contextualRule5ZeroLabel
      (ofLex (contextualCompleteReadingAt molecule descriptorMap unit graph W D none)).2
  | some own => mapObservationKey (absoluteRule5Label own common)
      (ofLex (contextualCompleteReadingAt molecule descriptorMap unit graph W D
        (some own))).1

/-- The full contextual Rule-5 stream in the contextual complete-reading order. -/
def contextualCompleteRule5ReadingsAt (W D : ℕ)
    (common : DescriptorSense := .senior) : List (Key StereoLabel) :=
  (contextualTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map
    fun reference => contextualCompleteRule5ReadingAt molecule descriptorMap unit graph W D
      reference common

theorem contextualCompleteRule5ReadingsAt_length (W D : ℕ) (common : DescriptorSense) :
    (contextualCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common).length =
      if contextualReferenceSelection molecule descriptorMap unit graph = .both then 2 else 1 := by
  unfold contextualCompleteRule5ReadingsAt
  calc
    _ = (contextualTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).length := by
      simp
    _ = ((contextualTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map
        (fun reference => contextualCompleteReadingAt molecule descriptorMap unit graph W D
          reference)).length := by
      simp
    _ = (contextualCompleteReadingsAt molecule descriptorMap unit graph W D).length := by
      rw [contextualTaggedAlternativeReferencesAt_projection]
    _ = if contextualReferenceSelection molecule descriptorMap unit graph = .both then 2 else 1 :=
      contextualCompleteReadingsAt_length molecule descriptorMap unit graph W D

/-- The Rule-1/2/3/4a pair key under the retained physical outer-root observer. -/
def contextualMolecularRankPairAt (W D : ℕ) : MolecularRankPair :=
  observedPairKey graph (contextualNodeObservation molecule graph unit.1.root)
    (rankEvidence molecule descriptorMap unit graph) W D graph.root

/-- The Rule-1/2/3/4a prefix followed by the retained-observer complete Rule-4b/4c signature. -/
def contextualCompleteLigandPriorKeyAt (W D : ℕ) : CompleteLigandPriorKey :=
  toLex (contextualMolecularRankPairAt molecule descriptorMap unit graph W D,
    contextualCompletePriorSignatureAt molecule descriptorMap unit graph W D)

/-- Complete contextual ligand order through Rule 5, with one common absolute-R stream. -/
def contextualCompleteLigandRule5KeyAt (W D : ℕ) : ContextualCompleteLigandRule5Key :=
  toLex (contextualCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D,
    contextualCompleteRule5ReadingsAt molecule descriptorMap unit graph W D .senior)

theorem contextualCompleteLigandRule5KeyAt_prior (W D : ℕ) :
    (ofLex (contextualCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D)).1 =
      contextualCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D := rfl

theorem contextualCompleteLigandRule5KeyAt_rule5 (W D : ℕ) :
    (ofLex (contextualCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D)).2 =
      contextualCompleteRule5ReadingsAt molecule descriptorMap unit graph W D .senior := rfl

end ContextualRule5

section Iso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)

local instance contextualRule5IsoLeftNodeFintype : Fintype left.Node := left.nodeFintype
local instance contextualRule5IsoRightNodeFintype : Fintype right.Node := right.nodeFintype

include iso in
private theorem contextualCompleteRule5ReadingAt_iso (W D : ℕ)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    contextualCompleteRule5ReadingAt molecule descriptorMap unit right W D reference common =
      contextualCompleteRule5ReadingAt molecule descriptorMap unit left W D reference common := by
  cases reference with
  | none =>
      simp only [contextualCompleteRule5ReadingAt]
      exact congrArg (fun key : CompleteReadingKey =>
        mapObservationKey contextualRule5ZeroLabel (ofLex key).2)
        (contextualCompleteReadingAt_iso molecule descriptorMap unit iso W D none)
  | some own =>
      exact congrArg (fun key : CompleteReadingKey =>
        mapObservationKey (absoluteRule5Label own common) (ofLex key).1)
        (contextualCompleteReadingAt_iso molecule descriptorMap unit iso W D (some own))

include iso in
theorem contextualTaggedAlternativeReferencesAt_iso (W D : ℕ) :
    contextualTaggedAlternativeReferencesAt molecule descriptorMap unit right W D =
      contextualTaggedAlternativeReferencesAt molecule descriptorMap unit left W D := by
  unfold contextualTaggedAlternativeReferencesAt
  unfold contextualReferenceSelection
  rw [contextualReferenceSelection_iso molecule descriptorMap unit iso unit.1.root]
  cases h : observedReferenceSelection molecule descriptorMap unit left
      (contextualNodeObservation molecule left unit.1.root) with
  | empty => rfl
  | one sense => rfl
  | both =>
      rw [contextualCompleteReadingAt_iso molecule descriptorMap unit iso W D (some .senior),
        contextualCompleteReadingAt_iso molecule descriptorMap unit iso W D (some .junior)]

include iso in
theorem contextualCompleteRule5ReadingsAt_iso (W D : ℕ) (common : DescriptorSense) :
    contextualCompleteRule5ReadingsAt molecule descriptorMap unit right W D common =
      contextualCompleteRule5ReadingsAt molecule descriptorMap unit left W D common := by
  unfold contextualCompleteRule5ReadingsAt
  rw [contextualTaggedAlternativeReferencesAt_iso molecule descriptorMap unit iso W D]
  apply List.map_congr_left
  intro reference _
  exact contextualCompleteRule5ReadingAt_iso molecule descriptorMap unit iso W D reference common

include iso in
theorem contextualMolecularRankPairAt_iso (W D : ℕ) :
    contextualMolecularRankPairAt molecule descriptorMap unit right W D =
      contextualMolecularRankPairAt molecule descriptorMap unit left W D := by
  unfold contextualMolecularRankPairAt observedPairKey observedRule4aComponent
  rw [← iso.map_root]
  have observerEq := fun rule node =>
    contextualNodeObservation_iso molecule iso unit.1.root rule node
  have keyEq := ordinaryKeyWithObservations_iso iso
    (contextualNodeObservation molecule left unit.1.root)
    (contextualNodeObservation molecule right unit.1.root)
    W D observerEq
    (rankEvidence_preserved molecule descriptorMap unit iso) left.root
  exact congrArg (fun pair : List (Key ℤ) × Key StereoLabel => toLex pair)
    (Prod.ext
      (ruleKeyWithObservations_iso iso
        (contextualNodeObservation molecule left unit.1.root)
        (contextualNodeObservation molecule right unit.1.root)
        W D observerEq left.root)
      (congrArg (fun key =>
        (ofLex key).2.getD (stereoIndex .rule4aStereogenicUnitKind) []) keyEq))

include iso in
theorem contextualCompleteLigandPriorKeyAt_iso (W D : ℕ) :
    contextualCompleteLigandPriorKeyAt molecule descriptorMap unit right W D =
      contextualCompleteLigandPriorKeyAt molecule descriptorMap unit left W D := by
  unfold contextualCompleteLigandPriorKeyAt
  exact congrArg (fun pair : MolecularRankPair × CompletePriorSignature => toLex pair)
    (Prod.ext (contextualMolecularRankPairAt_iso molecule descriptorMap unit iso W D)
      (contextualCompletePriorSignatureAt_iso molecule descriptorMap unit iso W D))

include iso in
theorem contextualCompleteLigandRule5KeyAt_iso (W D : ℕ) :
    contextualCompleteLigandRule5KeyAt molecule descriptorMap unit right W D =
      contextualCompleteLigandRule5KeyAt molecule descriptorMap unit left W D := by
  unfold contextualCompleteLigandRule5KeyAt
  exact congrArg (fun pair : CompleteLigandPriorKey × List (Key StereoLabel) => toLex pair)
    (Prod.ext (contextualCompleteLigandPriorKeyAt_iso molecule descriptorMap unit iso W D)
      (contextualCompleteRule5ReadingsAt_iso molecule descriptorMap unit iso W D .senior))

end Iso

section Reflection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance contextualRule5ReflectNodeFintype : Fintype graph.Node := graph.nodeFintype

private theorem absoluteRule5Label_mirror (own common : DescriptorSense) (value : StereoLabel) :
    absoluteRule5Label own.mirror common.mirror value = absoluteRule5Label own common value := by
  cases own <;> cases common <;> rfl

theorem contextualCompleteRule5ReadingAt_reflect (W D : ℕ)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    contextualCompleteRule5ReadingAt molecule descriptorMap.reflect unit graph W D
        (reference.map DescriptorSense.mirror) common.mirror =
      contextualCompleteRule5ReadingAt molecule descriptorMap unit graph W D reference common := by
  cases reference with
  | none =>
      simp only [contextualCompleteRule5ReadingAt]
      exact congrArg (fun key : CompleteReadingKey =>
        mapObservationKey contextualRule5ZeroLabel (ofLex key).2)
        (contextualCompleteReadingAt_reflect molecule descriptorMap unit graph W D none)
  | some own =>
      have reading :
          contextualCompleteReadingAt molecule descriptorMap.reflect unit graph W D
              (some own.mirror) =
            contextualCompleteReadingAt molecule descriptorMap unit graph W D (some own) := by
        simpa using contextualCompleteReadingAt_reflect molecule descriptorMap unit graph W D
          (some own.mirror)
      change mapObservationKey (absoluteRule5Label own.mirror common.mirror)
          (ofLex (contextualCompleteReadingAt molecule descriptorMap.reflect unit graph W D
            (some own.mirror))).1 =
        mapObservationKey (absoluteRule5Label own common)
          (ofLex (contextualCompleteReadingAt molecule descriptorMap unit graph W D
            (some own))).1
      rw [reading]
      congr 1
      funext value
      exact absoluteRule5Label_mirror own common value

end Reflection
end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteLigandRule5KeyAt_prior
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteLigandRule5KeyAt_rule5
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualTaggedAlternativeReferencesAt_projection
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteRule5ReadingsAt_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualTaggedAlternativeReferencesAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteRule5ReadingsAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualMolecularRankPairAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteLigandPriorKeyAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteLigandRule5KeyAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualCompleteRule5ReadingAt_reflect
