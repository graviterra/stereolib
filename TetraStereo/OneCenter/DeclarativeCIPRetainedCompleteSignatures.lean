import TetraStereo.OneCenter.DeclarativeCIPRetainedContextObservation
import TetraStereo.OneCenter.DeclarativeCIPRetainedStereoEvidence
import TetraStereo.OneCenter.DeclarativeCIPContextualRule5Order
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Retained-context complete signatures for ring comparison.

Selection ranks ancestor paths by `retainedContextNodeObservation` and `retainedRankEvidence`
at the digraph's own width and height, so every path depth in the graph participates. A node
enters that population only through molecular `eligibleSense`. A ring duplicate has
`occurrenceReading = .unavailable`, so its sense is `none` even though retained Rule 4a evidence
stores the present nonstereogenic code. Runtime rank labels are not consulted.

Complete readings, the count / Rule-4b list / Rule-4c list signature, and the Rule-5 ligand key
use one caller layout `(W, D)` in every column. Their alternative order is the independent
contextual order consumed by the full compound comparison:

* empty reference: one `none` reading, whose Rule-4b component is absent and whose Rule-4c
  component is the retained no-reference reading;
* one reference: that sense alone;
* both references: descending complete Rule-4b-then-Rule-4c order. The value list is
  `[max, min]`. The tagged list used by Rule 5 is `[junior, senior]` when the senior reading is
  strictly smaller, and `[senior, junior]` otherwise, including a complete tie.

The Rule-5 stream decodes those tagged alternatives into the common absolute-senior convention.
A `none` alternative keeps its Rule-4c support and writes zero Rule-5 bits. `retainedRule5Observation`
is not installed as a key column. This module does not identify retained paths with runtime
paths, and it does not use faithful-expansion uniqueness.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
open scoped Classical
open Certificate.CanonicalSphereKey (Key)
open Rule4aTableBridge (code)
universe u

abbrev RetainedCompleteLigandRule5Key := CompleteLigandRule5Key

section Selection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance retainedSelectionNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- A ring duplicate is not a Rule-4b reference. Eligibility reads the molecular occurrence,
not the present nonstereogenic code stored for that address. -/
theorem eligibleSense_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    eligibleSense molecule descriptorMap unit graph node = none := by
  unfold eligibleSense
  rw [occurrenceReading_of_ringDuplicate molecule descriptorMap unit graph node distance duplicate]

theorem not_Eligible_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    ¬ Eligible molecule descriptorMap unit graph node := by
  intro eligible
  unfold Eligible at eligible
  rw [eligibleSense_ringDuplicate molecule descriptorMap unit graph node distance duplicate]
    at eligible
  simp at eligible

/-- Ordinary rank key under the retained constitutional observer and retained pre-Rule-4b evidence.
The layout is the digraph's own width and height. -/
def retainedRankKey (node : graph.Node) : OrdinaryKey :=
  ordinaryKeyWithObservations graph (retainedContextNodeObservation molecule graph unit)
    (retainedRankEvidence molecule descriptorMap unit graph) graph.width graph.height node

/-- Ancestor rank path, root first, at that same native layout. -/
def retainedRankPath (node : graph.Node) : List OrdinaryKey :=
  (ancestorChain graph node).map (retainedRankKey molecule descriptorMap unit graph)

/-- Nearest eligible node whose retained ancestor path is maximal. -/
def RetainedInReferenceClass (node : graph.Node) : Prop :=
  NearestEligible molecule descriptorMap unit graph node ∧
    ∀ other, NearestEligible molecule descriptorMap unit graph other →
      retainedRankPath molecule descriptorMap unit graph other ≤
        retainedRankPath molecule descriptorMap unit graph node

theorem not_RetainedInReferenceClass_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    ¬ RetainedInReferenceClass molecule descriptorMap unit graph node := by
  intro included
  exact not_Eligible_ringDuplicate molecule descriptorMap unit graph node distance duplicate
    included.1.1

def retainedReferenceClass : Finset graph.Node :=
  Finset.univ.filter (RetainedInReferenceClass molecule descriptorMap unit graph)

def retainedSeniorCount : ℕ :=
  ((retainedReferenceClass molecule descriptorMap unit graph).filter fun node =>
    eligibleSense molecule descriptorMap unit graph node = some .senior).card

def retainedJuniorCount : ℕ :=
  ((retainedReferenceClass molecule descriptorMap unit graph).filter fun node =>
    eligibleSense molecule descriptorMap unit graph node = some .junior).card

/-- Empty, one sense, or both senses. Majority uses molecular senior and junior counts. -/
def retainedReferenceSelection : ReferenceSelection :=
  if ¬ ∃ node, Eligible molecule descriptorMap unit graph node then .empty
  else if retainedJuniorCount molecule descriptorMap unit graph <
      retainedSeniorCount molecule descriptorMap unit graph then .one .senior
  else if retainedSeniorCount molecule descriptorMap unit graph <
      retainedJuniorCount molecule descriptorMap unit graph then .one .junior
  else .both

end Selection

section Readings

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance retainedReadingNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- One complete alternative at layout `(W, D)`. `none` keeps the retained no-reference Rule-4c
reading and contributes no Rule-4b component. -/
def retainedCompleteReadingAt (W D : ℕ) (reference : Option DescriptorSense) :
    CompleteReadingKey :=
  match reference with
  | none => toLex ([], observedRule4cComponent graph
      (retainedContextNodeObservation molecule graph unit)
      (retainedNoReferenceEvidence4c molecule descriptorMap unit graph) W D graph.root)
  | some sense => toLex
      (observedRule4bComponent graph (retainedContextNodeObservation molecule graph unit)
          (retainedReadingEvidence molecule descriptorMap unit graph sense) W D graph.root,
        observedRule4cComponent graph (retainedContextNodeObservation molecule graph unit)
          (retainedReadingEvidence4c molecule descriptorMap unit graph sense) W D graph.root)

/-- Descending complete alternatives. A tie has one observable list because `max` and `min` do
not consult occurrence identity. -/
def retainedCompleteReadingsAt (W D : ℕ) : List CompleteReadingKey :=
  match retainedReferenceSelection molecule descriptorMap unit graph with
  | .empty => [retainedCompleteReadingAt molecule descriptorMap unit graph W D none]
  | .one sense => [retainedCompleteReadingAt molecule descriptorMap unit graph W D (some sense)]
  | .both =>
      let first := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior)
      let second := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
      [max first second, min first second]

/-- Count, then every Rule-4b component, then every Rule-4c component, in that alternative order.
The empty population contributes no Rule-4b list and one retained Rule-4c reading. -/
def retainedCompletePriorSignatureAt (W D : ℕ) : CompletePriorSignature :=
  let selection := retainedReferenceSelection molecule descriptorMap unit graph
  let readings := retainedCompleteReadingsAt molecule descriptorMap unit graph W D
  toLex (selection.countPriority, toLex
    ((if selection = .empty then [] else readings.map (fun key => (ofLex key).1)),
      readings.map (fun key => (ofLex key).2)))

theorem retainedCompleteReadingsAt_length (W D : ℕ) :
    (retainedCompleteReadingsAt molecule descriptorMap unit graph W D).length =
      if retainedReferenceSelection molecule descriptorMap unit graph = .both then 2 else 1 := by
  unfold retainedCompleteReadingsAt
  cases retainedReferenceSelection molecule descriptorMap unit graph <;> simp

theorem retainedCompletePriorSignatureAt_count (W D : ℕ) :
    (ofLex (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D)).1 =
      (retainedReferenceSelection molecule descriptorMap unit graph).countPriority := by
  simp [retainedCompletePriorSignatureAt]

theorem retainedCompletePriorSignatureAt_empty (W D : ℕ)
    (empty : retainedReferenceSelection molecule descriptorMap unit graph = .empty) :
    retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D =
      toLex (0, toLex ([], [observedRule4cComponent graph
        (retainedContextNodeObservation molecule graph unit)
        (retainedNoReferenceEvidence4c molecule descriptorMap unit graph) W D graph.root])) := by
  simp [retainedCompletePriorSignatureAt, retainedCompleteReadingsAt, retainedCompleteReadingAt,
    empty, ReferenceSelection.countPriority]

/-- Tagged alternatives in the order used by Rule 5. A complete tie keeps senior before junior. -/
def retainedTaggedAlternativeReferencesAt (W D : ℕ) : List (Option DescriptorSense) :=
  match retainedReferenceSelection molecule descriptorMap unit graph with
  | .empty => [none]
  | .one sense => [some sense]
  | .both =>
      let senior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior)
      let junior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
      if compare senior junior = .lt then [some .junior, some .senior]
      else [some .senior, some .junior]

theorem retainedTaggedAlternativeReferencesAt_projection (W D : ℕ) :
    (retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map
        (fun reference => retainedCompleteReadingAt molecule descriptorMap unit graph W D
          reference) =
      retainedCompleteReadingsAt molecule descriptorMap unit graph W D := by
  unfold retainedTaggedAlternativeReferencesAt retainedCompleteReadingsAt
  cases retainedReferenceSelection molecule descriptorMap unit graph with
  | empty => rfl
  | one sense => rfl
  | both =>
      let senior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior)
      let junior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
      have pair := completeReading_descendingPair senior junior
      have mapped :
          (if compare senior junior = .lt then [some .junior, some .senior]
            else [some .senior, some .junior]).map
              (fun reference => retainedCompleteReadingAt molecule descriptorMap unit graph W D
                reference) =
            if compare senior junior = .lt then [junior, senior] else [senior, junior] := by
        by_cases h : compare senior junior = .lt
        · simp only [if_pos h, List.map_cons, List.map_nil]
          rfl
        · simp only [if_neg h, List.map_cons, List.map_nil]
          rfl
      rw [mapped]
      exact pair

private def retainedRule5ZeroLabel (_ : StereoLabel) : StereoLabel := code 0

/-- Decode one alternative into a common absolute convention. `none` preserves Rule-4c support. -/
def retainedCompleteRule5ReadingAt (W D : ℕ) (reference : Option DescriptorSense)
    (common : DescriptorSense := .senior) : Key StereoLabel :=
  match reference with
  | none => mapObservationKey retainedRule5ZeroLabel
      (ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D none)).2
  | some own => mapObservationKey (absoluteRule5Label own common)
      (ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some own))).1

/-- Rule-5 stream in the tagged alternative order. -/
def retainedCompleteRule5ReadingsAt (W D : ℕ)
    (common : DescriptorSense := .senior) : List (Key StereoLabel) :=
  (retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map
    fun reference => retainedCompleteRule5ReadingAt molecule descriptorMap unit graph W D
      reference common

theorem retainedCompleteRule5ReadingsAt_length (W D : ℕ) (common : DescriptorSense) :
    (retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common).length =
      if retainedReferenceSelection molecule descriptorMap unit graph = .both then 2 else 1 := by
  unfold retainedCompleteRule5ReadingsAt
  calc
    _ = (retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).length := by
      simp
    _ = ((retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map
        (fun reference => retainedCompleteReadingAt molecule descriptorMap unit graph W D
          reference)).length := by
      simp
    _ = (retainedCompleteReadingsAt molecule descriptorMap unit graph W D).length := by
      rw [retainedTaggedAlternativeReferencesAt_projection]
    _ = if retainedReferenceSelection molecule descriptorMap unit graph = .both then 2 else 1 :=
      retainedCompleteReadingsAt_length molecule descriptorMap unit graph W D

/-- Rule-1/2/3/4a pair at the same `(W, D)` as the later columns. -/
def retainedMolecularRankPairAt (W D : ℕ) : MolecularRankPair :=
  observedPairKey graph (retainedContextNodeObservation molecule graph unit)
    (retainedRankEvidence molecule descriptorMap unit graph) W D graph.root

/-- Retained rank pair, then the count / Rule-4b / Rule-4c signature. -/
def retainedCompleteLigandPriorKeyAt (W D : ℕ) : CompleteLigandPriorKey :=
  toLex (retainedMolecularRankPairAt molecule descriptorMap unit graph W D,
    retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D)

/-- Prior key, then the absolute-senior Rule-5 stream. -/
def retainedCompleteLigandRule5KeyAt (W D : ℕ) : RetainedCompleteLigandRule5Key :=
  toLex (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D,
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D .senior)

theorem retainedCompleteLigandPriorKeyAt_rank (W D : ℕ) :
    (ofLex (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D)).1 =
      retainedMolecularRankPairAt molecule descriptorMap unit graph W D := rfl

theorem retainedCompleteLigandPriorKeyAt_signature (W D : ℕ) :
    (ofLex (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D)).2 =
      retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D := rfl

theorem retainedCompleteLigandRule5KeyAt_prior (W D : ℕ) :
    (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D)).1 =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D := rfl

theorem retainedCompleteLigandRule5KeyAt_rule5 (W D : ℕ) :
    (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D)).2 =
      retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D .senior := rfl

end Readings

section Algebra

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule)

local instance retainedAlgebraNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem retainedCompleteLigandPriorKeyAt_compare_eq_then
    (left right : RootedDigraph Atom) (W D : ℕ) :
    compare (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D)
        (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D) =
      (compare (retainedMolecularRankPairAt molecule descriptorMap unit left W D)
          (retainedMolecularRankPairAt molecule descriptorMap unit right W D)).then
        (compare (retainedCompletePriorSignatureAt molecule descriptorMap unit left W D)
          (retainedCompletePriorSignatureAt molecule descriptorMap unit right W D)) := rfl

theorem retainedCompleteLigandRule5KeyAt_compare_eq_then
    (left right : RootedDigraph Atom) (W D : ℕ) :
    compare (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) =
      (compare (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D)
          (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)).then
        (compare (retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior)
          (retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior)) := rfl

/-- The empty population erases its absent Rule-4b component. Comparison still agrees with the
signature that maps that component, because the component is the empty key. -/
private def unmaskedRetainedPriorSignatureAt (graph : RootedDigraph Atom) (W D : ℕ) :
    CompletePriorSignature :=
  let selection := retainedReferenceSelection molecule descriptorMap unit graph
  let readings := retainedCompleteReadingsAt molecule descriptorMap unit graph W D
  toLex (selection.countPriority, toLex
    (readings.map (fun key => (ofLex key).1), readings.map (fun key => (ofLex key).2)))

theorem compare_unmaskedRetainedPriorSignature_eq (left right : RootedDigraph Atom) (W D : ℕ) :
    compare (unmaskedRetainedPriorSignatureAt molecule descriptorMap unit left W D)
        (unmaskedRetainedPriorSignatureAt molecule descriptorMap unit right W D) =
      compare (retainedCompletePriorSignatureAt molecule descriptorMap unit left W D)
        (retainedCompletePriorSignatureAt molecule descriptorMap unit right W D) := by
  unfold unmaskedRetainedPriorSignatureAt retainedCompletePriorSignatureAt
  cases hL : retainedReferenceSelection molecule descriptorMap unit left <;>
    cases hR : retainedReferenceSelection molecule descriptorMap unit right <;>
    simp only [ReferenceSelection.countPriority, reduceCtorEq, ↓reduceIte]
  all_goals first
    | rfl
    | (simp only [retainedCompleteReadingsAt, hL, hR, retainedCompleteReadingAt,
        List.map_cons, List.map_nil, ofLex_toLex]; rfl)

end Algebra

section Reflection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance retainedReflectNodeFintype : Fintype graph.Node := graph.nodeFintype

theorem retainedRule4aObservation_reflect (node : graph.Node) :
    retainedRule4aObservation molecule descriptorMap.reflect unit graph node =
      retainedRule4aObservation molecule descriptorMap unit graph node := by
  cases h : (graph.label node).provenance with
  | ringDuplicate _ => simp [retainedRule4aObservation, neutralizeRingDuplicate, h]
  | realAtom =>
      simp [retainedRule4aObservation, neutralizeRingDuplicate, h, rule4aObservation_reflect]
  | multipleBondDuplicate _ =>
      simp [retainedRule4aObservation, neutralizeRingDuplicate, h, rule4aObservation_reflect]
  | phantom _ =>
      simp [retainedRule4aObservation, neutralizeRingDuplicate, h, rule4aObservation_reflect]
  | lonePair _ =>
      simp [retainedRule4aObservation, neutralizeRingDuplicate, h, rule4aObservation_reflect]
  | auxiliary _ =>
      simp [retainedRule4aObservation, neutralizeRingDuplicate, h, rule4aObservation_reflect]

theorem retainedRule4cObservation_reflect (node : graph.Node) :
    retainedRule4cObservation molecule descriptorMap.reflect unit graph node =
      retainedRule4cObservation molecule descriptorMap unit graph node := by
  cases h : (graph.label node).provenance with
  | ringDuplicate _ => simp [retainedRule4cObservation, neutralizeRingDuplicate, h]
  | realAtom =>
      simp [retainedRule4cObservation, neutralizeRingDuplicate, h, rule4cObservation_reflect]
  | multipleBondDuplicate _ =>
      simp [retainedRule4cObservation, neutralizeRingDuplicate, h, rule4cObservation_reflect]
  | phantom _ =>
      simp [retainedRule4cObservation, neutralizeRingDuplicate, h, rule4cObservation_reflect]
  | lonePair _ =>
      simp [retainedRule4cObservation, neutralizeRingDuplicate, h, rule4cObservation_reflect]
  | auxiliary _ =>
      simp [retainedRule4cObservation, neutralizeRingDuplicate, h, rule4cObservation_reflect]

theorem retainedRankEvidence_reflect :
    retainedRankEvidence molecule descriptorMap.reflect unit graph =
      retainedRankEvidence molecule descriptorMap unit graph := by
  funext node
  simp only [retainedRankEvidence, rule3Observation_reflect,
    retainedRule4aObservation_reflect molecule descriptorMap unit graph]

theorem retainedReadingEvidence_reflect (reference : DescriptorSense) :
    retainedReadingEvidence molecule descriptorMap.reflect unit graph reference =
      retainedReadingEvidence molecule descriptorMap unit graph reference.mirror := by
  funext node
  simp only [retainedReadingEvidence, rule3Observation_reflect,
    retainedRule4aObservation_reflect molecule descriptorMap unit graph, eligibleSense_reflect]
  congr 1
  cases eligibleSense molecule descriptorMap unit graph node with
  | none => rfl
  | some observed =>
      simp only [Option.map_some]
      cases reference <;> cases observed <;> rfl

theorem retainedReadingEvidence4c_reflect (reference : DescriptorSense) :
    retainedReadingEvidence4c molecule descriptorMap.reflect unit graph reference =
      retainedReadingEvidence4c molecule descriptorMap unit graph reference.mirror := by
  funext node
  simp only [retainedReadingEvidence4c,
    retainedReadingEvidence_reflect molecule descriptorMap unit graph,
    retainedRule4cObservation_reflect molecule descriptorMap unit graph]

theorem retainedNoReferenceEvidence4c_reflect :
    retainedNoReferenceEvidence4c molecule descriptorMap.reflect unit graph =
      retainedNoReferenceEvidence4c molecule descriptorMap unit graph := by
  funext node
  simp only [retainedNoReferenceEvidence4c,
    retainedRankEvidence_reflect molecule descriptorMap unit graph,
    retainedRule4cObservation_reflect molecule descriptorMap unit graph]

theorem retainedRankKey_reflect (node : graph.Node) :
    retainedRankKey molecule descriptorMap.reflect unit graph node =
      retainedRankKey molecule descriptorMap unit graph node := by
  unfold retainedRankKey
  rw [retainedRankEvidence_reflect molecule descriptorMap unit graph]

theorem retainedRankPath_reflect (node : graph.Node) :
    retainedRankPath molecule descriptorMap.reflect unit graph node =
      retainedRankPath molecule descriptorMap unit graph node := by
  unfold retainedRankPath
  apply List.map_congr_left
  intro ancestor _
  exact retainedRankKey_reflect molecule descriptorMap unit graph ancestor

theorem retainedInReferenceClass_reflect (node : graph.Node) :
    RetainedInReferenceClass molecule descriptorMap.reflect unit graph node ↔
      RetainedInReferenceClass molecule descriptorMap unit graph node := by
  unfold RetainedInReferenceClass
  simp only [nearestEligible_reflect,
    retainedRankPath_reflect molecule descriptorMap unit graph]

theorem retainedReferenceClass_reflect :
    retainedReferenceClass molecule descriptorMap.reflect unit graph =
      retainedReferenceClass molecule descriptorMap unit graph := by
  unfold retainedReferenceClass
  ext node
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    retainedInReferenceClass_reflect molecule descriptorMap unit graph]

theorem retainedSeniorCount_reflect :
    retainedSeniorCount molecule descriptorMap.reflect unit graph =
      retainedJuniorCount molecule descriptorMap unit graph := by
  unfold retainedSeniorCount retainedJuniorCount
  rw [retainedReferenceClass_reflect molecule descriptorMap unit graph]
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

theorem retainedJuniorCount_reflect :
    retainedJuniorCount molecule descriptorMap.reflect unit graph =
      retainedSeniorCount molecule descriptorMap unit graph := by
  unfold retainedJuniorCount retainedSeniorCount
  rw [retainedReferenceClass_reflect molecule descriptorMap unit graph]
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

theorem retainedReferenceSelection_reflect :
    retainedReferenceSelection molecule descriptorMap.reflect unit graph =
      (retainedReferenceSelection molecule descriptorMap unit graph).mirror := by
  unfold retainedReferenceSelection
  simp only [eligible_reflect,
    retainedJuniorCount_reflect molecule descriptorMap unit graph,
    retainedSeniorCount_reflect molecule descriptorMap unit graph]
  by_cases hex : ∃ node, Eligible molecule descriptorMap unit graph node
  · simp only [hex, not_true_eq_false, if_false]
    by_cases hlt : retainedSeniorCount molecule descriptorMap unit graph <
        retainedJuniorCount molecule descriptorMap unit graph
    · have hnot := lt_asymm hlt
      simp [hlt, hnot, ReferenceSelection.mirror, DescriptorSense.mirror]
    · by_cases hgt : retainedJuniorCount molecule descriptorMap unit graph <
          retainedSeniorCount molecule descriptorMap unit graph
      · simp [hlt, hgt, ReferenceSelection.mirror, DescriptorSense.mirror]
      · simp [hlt, hgt, ReferenceSelection.mirror]
  · simp [hex, ReferenceSelection.mirror]

theorem retainedCompleteReadingAt_reflect (W D : ℕ) (reference : Option DescriptorSense) :
    retainedCompleteReadingAt molecule descriptorMap.reflect unit graph W D reference =
      retainedCompleteReadingAt molecule descriptorMap unit graph W D
        (reference.map DescriptorSense.mirror) := by
  cases reference with
  | none => simp [retainedCompleteReadingAt, retainedNoReferenceEvidence4c_reflect]
  | some sense =>
      simp [retainedCompleteReadingAt, retainedReadingEvidence_reflect,
        retainedReadingEvidence4c_reflect]

theorem retainedCompleteReadingsAt_reflect (W D : ℕ) :
    retainedCompleteReadingsAt molecule descriptorMap.reflect unit graph W D =
      retainedCompleteReadingsAt molecule descriptorMap unit graph W D := by
  unfold retainedCompleteReadingsAt
  rw [retainedReferenceSelection_reflect molecule descriptorMap unit graph]
  cases retainedReferenceSelection molecule descriptorMap unit graph with
  | empty => simp [retainedCompleteReadingAt_reflect, ReferenceSelection.mirror]
  | one sense =>
      simp [retainedCompleteReadingAt_reflect, ReferenceSelection.mirror,
        DescriptorSense.mirror_mirror]
  | both =>
      simp only [ReferenceSelection.mirror, retainedCompleteReadingAt_reflect,
        Option.map_some, DescriptorSense.mirror]
      rw [max_comm, min_comm]

theorem retainedCompletePriorSignatureAt_reflect (W D : ℕ) :
    retainedCompletePriorSignatureAt molecule descriptorMap.reflect unit graph W D =
      retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D := by
  unfold retainedCompletePriorSignatureAt
  simp only [retainedReferenceSelection_reflect molecule descriptorMap unit graph,
    retainedCompleteReadingsAt_reflect molecule descriptorMap unit graph]
  cases retainedReferenceSelection molecule descriptorMap unit graph <;> rfl

private theorem retainedAbsoluteRule5Label_mirror (own common : DescriptorSense)
    (value : StereoLabel) :
    absoluteRule5Label own.mirror common.mirror value = absoluteRule5Label own common value := by
  cases own <;> cases common <;> rfl

theorem retainedCompleteRule5ReadingAt_reflect (W D : ℕ)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    retainedCompleteRule5ReadingAt molecule descriptorMap.reflect unit graph W D
        (reference.map DescriptorSense.mirror) common.mirror =
      retainedCompleteRule5ReadingAt molecule descriptorMap unit graph W D reference common := by
  cases reference with
  | none =>
      simp only [retainedCompleteRule5ReadingAt]
      exact congrArg (fun key : CompleteReadingKey =>
        mapObservationKey retainedRule5ZeroLabel (ofLex key).2)
        (retainedCompleteReadingAt_reflect molecule descriptorMap unit graph W D none)
  | some own =>
      have reading :
          retainedCompleteReadingAt molecule descriptorMap.reflect unit graph W D
              (some own.mirror) =
            retainedCompleteReadingAt molecule descriptorMap unit graph W D (some own) := by
        simpa using retainedCompleteReadingAt_reflect molecule descriptorMap unit graph W D
          (some own.mirror)
      change mapObservationKey (absoluteRule5Label own.mirror common.mirror)
          (ofLex (retainedCompleteReadingAt molecule descriptorMap.reflect unit graph W D
            (some own.mirror))).1 =
        mapObservationKey (absoluteRule5Label own common)
          (ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some own))).1
      rw [reading]
      congr 1
      funext value
      exact retainedAbsoluteRule5Label_mirror own common value

end Reflection

section Iso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)

local instance retainedIsoLeftNodeFintype : Fintype left.Node := left.nodeFintype
local instance retainedIsoRightNodeFintype : Fintype right.Node := right.nodeFintype

include iso in
theorem retainedRankKey_iso (node : left.Node) :
    retainedRankKey molecule descriptorMap unit right (iso.toEquiv node) =
      retainedRankKey molecule descriptorMap unit left node := by
  unfold retainedRankKey
  rw [width_iso iso, height_iso iso]
  exact ordinaryKeyWithObservations_iso iso
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right unit) left.width left.height
    (fun rule node => retainedContextNodeObservation_iso molecule unit iso rule node)
    (retainedRankEvidence_preserved molecule descriptorMap unit iso) node

include iso in
theorem retainedRankPath_iso (node : left.Node) :
    retainedRankPath molecule descriptorMap unit right (iso.toEquiv node) =
      retainedRankPath molecule descriptorMap unit left node := by
  unfold retainedRankPath
  rw [ancestorChain_iso iso node, List.map_map]
  apply List.map_congr_left
  intro ancestor _
  exact retainedRankKey_iso molecule descriptorMap unit iso ancestor

include iso in
theorem retainedInReferenceClass_iso (node : left.Node) :
    RetainedInReferenceClass molecule descriptorMap unit right (iso.toEquiv node) ↔
      RetainedInReferenceClass molecule descriptorMap unit left node := by
  unfold RetainedInReferenceClass
  constructor
  · rintro ⟨nearest, maximal⟩
    refine ⟨(nearestEligible_iso molecule descriptorMap unit iso node).mpr nearest, ?_⟩
    intro other hother
    have otherRight := (nearestEligible_iso molecule descriptorMap unit iso other).mp hother
    have hle := maximal (iso.toEquiv other) otherRight
    rw [retainedRankPath_iso molecule descriptorMap unit iso other,
      retainedRankPath_iso molecule descriptorMap unit iso node] at hle
    exact hle
  · rintro ⟨nearest, maximal⟩
    refine ⟨(nearestEligible_iso molecule descriptorMap unit iso node).mp nearest, ?_⟩
    intro other hother
    have otherLeft := (nearestEligible_iso molecule descriptorMap unit iso.symm other).mp hother
    have hle := maximal (iso.toEquiv.symm other) otherLeft
    have otherPath :
        retainedRankPath molecule descriptorMap unit right other =
          retainedRankPath molecule descriptorMap unit left (iso.toEquiv.symm other) := by
      simpa using retainedRankPath_iso molecule descriptorMap unit iso (iso.toEquiv.symm other)
    have nodePath :
        retainedRankPath molecule descriptorMap unit right (iso.toEquiv node) =
          retainedRankPath molecule descriptorMap unit left node :=
      retainedRankPath_iso molecule descriptorMap unit iso node
    calc
      retainedRankPath molecule descriptorMap unit right other ≤
          retainedRankPath molecule descriptorMap unit right (iso.toEquiv node) := by
        rw [otherPath, nodePath]
        exact hle

include iso in
theorem retainedSeniorCount_iso :
    retainedSeniorCount molecule descriptorMap unit right =
      retainedSeniorCount molecule descriptorMap unit left := by
  unfold retainedSeniorCount retainedReferenceClass
  symm
  apply Finset.card_equiv iso.toEquiv
  intro node
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [retainedInReferenceClass_iso molecule descriptorMap unit iso node,
    eligibleSense_iso molecule descriptorMap unit iso node]

include iso in
theorem retainedJuniorCount_iso :
    retainedJuniorCount molecule descriptorMap unit right =
      retainedJuniorCount molecule descriptorMap unit left := by
  unfold retainedJuniorCount retainedReferenceClass
  symm
  apply Finset.card_equiv iso.toEquiv
  intro node
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [retainedInReferenceClass_iso molecule descriptorMap unit iso node,
    eligibleSense_iso molecule descriptorMap unit iso node]

include iso in
theorem retainedReferenceSelection_iso :
    retainedReferenceSelection molecule descriptorMap unit right =
      retainedReferenceSelection molecule descriptorMap unit left := by
  unfold retainedReferenceSelection
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
    rw [retainedJuniorCount_iso molecule descriptorMap unit iso,
      retainedSeniorCount_iso molecule descriptorMap unit iso]
  · have hright : ¬ ∃ node, Eligible molecule descriptorMap unit right node := by
      intro h
      exact hleft (existsRight.mp h)
    rw [if_pos hleft, if_pos hright]

private theorem retainedObservedRule4bComponent_iso
    (isomorphism : RootedDigraph.Iso left right) (W D : ℕ) (sense : DescriptorSense) :
    observedRule4bComponent right (retainedContextNodeObservation molecule right unit)
        (retainedReadingEvidence molecule descriptorMap unit right sense) W D right.root =
      observedRule4bComponent left (retainedContextNodeObservation molecule left unit)
        (retainedReadingEvidence molecule descriptorMap unit left sense) W D left.root := by
  unfold observedRule4bComponent
  rw [← isomorphism.map_root]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4bLikeUnlikeDescriptorPairs) [])
    (ordinaryKeyWithObservations_iso isomorphism
      (retainedContextNodeObservation molecule left unit)
      (retainedContextNodeObservation molecule right unit) W D
      (fun rule node => retainedContextNodeObservation_iso molecule unit isomorphism rule node)
      (retainedReadingEvidence_preserved molecule descriptorMap unit isomorphism sense) left.root)

private theorem retainedObservedRule4cComponent_reading_iso
    (isomorphism : RootedDigraph.Iso left right) (W D : ℕ) (sense : DescriptorSense) :
    observedRule4cComponent right (retainedContextNodeObservation molecule right unit)
        (retainedReadingEvidence4c molecule descriptorMap unit right sense) W D right.root =
      observedRule4cComponent left (retainedContextNodeObservation molecule left unit)
        (retainedReadingEvidence4c molecule descriptorMap unit left sense) W D left.root := by
  unfold observedRule4cComponent
  rw [← isomorphism.map_root]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) [])
    (ordinaryKeyWithObservations_iso isomorphism
      (retainedContextNodeObservation molecule left unit)
      (retainedContextNodeObservation molecule right unit) W D
      (fun rule node => retainedContextNodeObservation_iso molecule unit isomorphism rule node)
      (retainedReadingEvidence4c_preserved molecule descriptorMap unit isomorphism sense) left.root)

private theorem retainedObservedRule4cComponent_noReference_iso
    (isomorphism : RootedDigraph.Iso left right) (W D : ℕ) :
    observedRule4cComponent right (retainedContextNodeObservation molecule right unit)
        (retainedNoReferenceEvidence4c molecule descriptorMap unit right) W D right.root =
      observedRule4cComponent left (retainedContextNodeObservation molecule left unit)
        (retainedNoReferenceEvidence4c molecule descriptorMap unit left) W D left.root := by
  unfold observedRule4cComponent
  rw [← isomorphism.map_root]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) [])
    (ordinaryKeyWithObservations_iso isomorphism
      (retainedContextNodeObservation molecule left unit)
      (retainedContextNodeObservation molecule right unit) W D
      (fun rule node => retainedContextNodeObservation_iso molecule unit isomorphism rule node)
      (retainedNoReferenceEvidence4c_preserved molecule descriptorMap unit isomorphism) left.root)

include iso in
theorem retainedCompleteReadingAt_iso (W D : ℕ) (reference : Option DescriptorSense) :
    retainedCompleteReadingAt molecule descriptorMap unit right W D reference =
      retainedCompleteReadingAt molecule descriptorMap unit left W D reference := by
  cases reference with
  | none =>
      exact congrArg (fun key : Key StereoLabel => toLex ([], key))
        (retainedObservedRule4cComponent_noReference_iso molecule descriptorMap unit iso W D)
  | some sense =>
      exact congrArg (fun pair : Key StereoLabel × Key StereoLabel => toLex pair)
        (Prod.ext
          (retainedObservedRule4bComponent_iso molecule descriptorMap unit iso W D sense)
          (retainedObservedRule4cComponent_reading_iso molecule descriptorMap unit iso W D sense))

include iso in
theorem retainedCompleteReadingsAt_iso (W D : ℕ) :
    retainedCompleteReadingsAt molecule descriptorMap unit right W D =
      retainedCompleteReadingsAt molecule descriptorMap unit left W D := by
  unfold retainedCompleteReadingsAt
  rw [retainedReferenceSelection_iso molecule descriptorMap unit iso]
  simp only [retainedCompleteReadingAt_iso molecule descriptorMap unit iso]

include iso in
theorem retainedCompletePriorSignatureAt_iso (W D : ℕ) :
    retainedCompletePriorSignatureAt molecule descriptorMap unit right W D =
      retainedCompletePriorSignatureAt molecule descriptorMap unit left W D := by
  unfold retainedCompletePriorSignatureAt
  rw [retainedReferenceSelection_iso molecule descriptorMap unit iso,
    retainedCompleteReadingsAt_iso molecule descriptorMap unit iso]

include iso in
theorem retainedTaggedAlternativeReferencesAt_iso (W D : ℕ) :
    retainedTaggedAlternativeReferencesAt molecule descriptorMap unit right W D =
      retainedTaggedAlternativeReferencesAt molecule descriptorMap unit left W D := by
  unfold retainedTaggedAlternativeReferencesAt
  rw [retainedReferenceSelection_iso molecule descriptorMap unit iso]
  cases h : retainedReferenceSelection molecule descriptorMap unit left with
  | empty => rfl
  | one sense => rfl
  | both =>
      rw [retainedCompleteReadingAt_iso molecule descriptorMap unit iso W D (some .senior),
        retainedCompleteReadingAt_iso molecule descriptorMap unit iso W D (some .junior)]

include iso in
private theorem retainedCompleteRule5ReadingAt_iso (W D : ℕ)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    retainedCompleteRule5ReadingAt molecule descriptorMap unit right W D reference common =
      retainedCompleteRule5ReadingAt molecule descriptorMap unit left W D reference common := by
  cases reference with
  | none =>
      simp only [retainedCompleteRule5ReadingAt]
      exact congrArg (fun key : CompleteReadingKey =>
        mapObservationKey retainedRule5ZeroLabel (ofLex key).2)
        (retainedCompleteReadingAt_iso molecule descriptorMap unit iso W D none)
  | some own =>
      exact congrArg (fun key : CompleteReadingKey =>
        mapObservationKey (absoluteRule5Label own common) (ofLex key).1)
        (retainedCompleteReadingAt_iso molecule descriptorMap unit iso W D (some own))

include iso in
theorem retainedCompleteRule5ReadingsAt_iso (W D : ℕ) (common : DescriptorSense) :
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D common =
      retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D common := by
  unfold retainedCompleteRule5ReadingsAt
  rw [retainedTaggedAlternativeReferencesAt_iso molecule descriptorMap unit iso W D]
  apply List.map_congr_left
  intro reference _
  exact retainedCompleteRule5ReadingAt_iso molecule descriptorMap unit iso W D reference common

include iso in
theorem retainedMolecularRankPairAt_iso (W D : ℕ) :
    retainedMolecularRankPairAt molecule descriptorMap unit right W D =
      retainedMolecularRankPairAt molecule descriptorMap unit left W D := by
  unfold retainedMolecularRankPairAt observedPairKey observedRule4aComponent
  rw [← iso.map_root]
  have observerEq := fun rule node =>
    retainedContextNodeObservation_iso molecule unit iso rule node
  have keyEq := ordinaryKeyWithObservations_iso iso
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right unit) W D observerEq
    (retainedRankEvidence_preserved molecule descriptorMap unit iso) left.root
  exact congrArg (fun pair : List (Key ℤ) × Key StereoLabel => toLex pair)
    (Prod.ext
      (ruleKeyWithObservations_iso iso
        (retainedContextNodeObservation molecule left unit)
        (retainedContextNodeObservation molecule right unit) W D observerEq left.root)
      (congrArg (fun key =>
        (ofLex key).2.getD (stereoIndex .rule4aStereogenicUnitKind) []) keyEq))

include iso in
theorem retainedCompleteLigandPriorKeyAt_iso (W D : ℕ) :
    retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D := by
  unfold retainedCompleteLigandPriorKeyAt
  exact congrArg (fun pair : MolecularRankPair × CompletePriorSignature => toLex pair)
    (Prod.ext (retainedMolecularRankPairAt_iso molecule descriptorMap unit iso W D)
      (retainedCompletePriorSignatureAt_iso molecule descriptorMap unit iso W D))

include iso in
theorem retainedCompleteLigandRule5KeyAt_iso (W D : ℕ) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D := by
  unfold retainedCompleteLigandRule5KeyAt
  exact congrArg (fun pair : CompleteLigandPriorKey × List (Key StereoLabel) => toLex pair)
    (Prod.ext (retainedCompleteLigandPriorKeyAt_iso molecule descriptorMap unit iso W D)
      (retainedCompleteRule5ReadingsAt_iso molecule descriptorMap unit iso W D .senior))

end Iso

section Agreement

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
  (noDuplicate : ∀ node distance, (graph.label node).provenance ≠ .ringDuplicate distance)
  (observeEq : ∀ rule node, retainedContextNodeObservation molecule graph unit rule node =
    contextualNodeObservation molecule graph unit.1.root rule node)

local instance retainedAgreementNodeFintype : Fintype graph.Node := graph.nodeFintype

include noDuplicate in
theorem retainedRankEvidence_eq_rankEvidence_of_noDuplicate :
    retainedRankEvidence molecule descriptorMap unit graph =
      rankEvidence molecule descriptorMap unit graph := by
  funext node
  exact retainedRankEvidence_eq_rankEvidence_of_not_ringDuplicate molecule descriptorMap unit graph
    node (noDuplicate node)

include noDuplicate in
private theorem retainedReadingEvidence_eq_of_noDuplicate (reference : DescriptorSense) :
    retainedReadingEvidence molecule descriptorMap unit graph reference =
      readingEvidence molecule descriptorMap unit graph reference := by
  funext node
  exact retainedReadingEvidence_eq_readingEvidence_of_not_ringDuplicate molecule descriptorMap unit
    graph reference node (noDuplicate node)

include noDuplicate in
private theorem retainedReadingEvidence4c_eq_of_noDuplicate (reference : DescriptorSense) :
    retainedReadingEvidence4c molecule descriptorMap unit graph reference =
      readingEvidence4c molecule descriptorMap unit graph reference := by
  funext node
  exact retainedReadingEvidence4c_eq_readingEvidence4c_of_not_ringDuplicate molecule descriptorMap
    unit graph reference node (noDuplicate node)

include noDuplicate in
private theorem retainedNoReferenceEvidence4c_eq_of_noDuplicate :
    retainedNoReferenceEvidence4c molecule descriptorMap unit graph =
      noReferenceEvidence4c molecule descriptorMap unit graph := by
  funext node
  exact retainedNoReferenceEvidence4c_eq_noReferenceEvidence4c_of_not_ringDuplicate molecule
    descriptorMap unit graph node (noDuplicate node)

include noDuplicate observeEq in
theorem retainedRankKey_eq_observed_of_noDuplicate (node : graph.Node) :
    retainedRankKey molecule descriptorMap unit graph node =
      observedRankKey molecule descriptorMap unit graph
        (contextualNodeObservation molecule graph unit.1.root) node := by
  unfold retainedRankKey observedRankKey
  rw [retainedRankEvidence_eq_rankEvidence_of_noDuplicate molecule descriptorMap unit graph
    noDuplicate]
  exact ordinaryKeyWithObservations_congr graph
    (retainedContextNodeObservation molecule graph unit)
    (rankEvidence molecule descriptorMap unit graph)
    (contextualNodeObservation molecule graph unit.1.root) observeEq graph.width graph.height node

include noDuplicate observeEq in
theorem retainedRankPath_eq_observed_of_noDuplicate (node : graph.Node) :
    retainedRankPath molecule descriptorMap unit graph node =
      observedRankPath molecule descriptorMap unit graph
        (contextualNodeObservation molecule graph unit.1.root) node := by
  unfold retainedRankPath observedRankPath
  apply List.map_congr_left
  intro ancestor _
  exact retainedRankKey_eq_observed_of_noDuplicate molecule descriptorMap unit graph noDuplicate
    observeEq ancestor

include noDuplicate observeEq in
theorem retainedInReferenceClass_iff_observed_of_noDuplicate (node : graph.Node) :
    RetainedInReferenceClass molecule descriptorMap unit graph node ↔
      ObservedInReferenceClass molecule descriptorMap unit graph
        (contextualNodeObservation molecule graph unit.1.root) node := by
  unfold RetainedInReferenceClass ObservedInReferenceClass
  constructor
  · rintro ⟨nearest, maximal⟩
    refine ⟨nearest, fun candidate hcand => ?_⟩
    simpa [retainedRankPath_eq_observed_of_noDuplicate molecule descriptorMap unit graph noDuplicate
      observeEq candidate,
      retainedRankPath_eq_observed_of_noDuplicate molecule descriptorMap unit graph noDuplicate
        observeEq node] using maximal candidate hcand
  · rintro ⟨nearest, maximal⟩
    refine ⟨nearest, fun candidate hcand => ?_⟩
    simpa [retainedRankPath_eq_observed_of_noDuplicate molecule descriptorMap unit graph noDuplicate
      observeEq candidate,
      retainedRankPath_eq_observed_of_noDuplicate molecule descriptorMap unit graph noDuplicate
        observeEq node] using maximal candidate hcand

include noDuplicate observeEq in
theorem retainedReferenceSelection_eq_contextual_of_noDuplicate :
    retainedReferenceSelection molecule descriptorMap unit graph =
      contextualReferenceSelection molecule descriptorMap unit graph := by
  unfold retainedReferenceSelection contextualReferenceSelection observedReferenceSelection
    retainedSeniorCount observedSeniorCount retainedJuniorCount observedJuniorCount
    retainedReferenceClass observedReferenceClass
  have classes :
      Finset.univ.filter (RetainedInReferenceClass molecule descriptorMap unit graph) =
        Finset.univ.filter (ObservedInReferenceClass molecule descriptorMap unit graph
          (contextualNodeObservation molecule graph unit.1.root)) := by
    congr 1
    funext node
    apply propext
    exact retainedInReferenceClass_iff_observed_of_noDuplicate molecule descriptorMap unit graph
      noDuplicate observeEq node
  rw [classes]

include noDuplicate observeEq in
private theorem retainedRule4bComponent_eq_contextual (W D : ℕ) (sense : DescriptorSense) :
    observedRule4bComponent graph (retainedContextNodeObservation molecule graph unit)
        (retainedReadingEvidence molecule descriptorMap unit graph sense) W D graph.root =
      observedRule4bComponent graph (contextualNodeObservation molecule graph unit.1.root)
        (readingEvidence molecule descriptorMap unit graph sense) W D graph.root := by
  unfold observedRule4bComponent
  rw [retainedReadingEvidence_eq_of_noDuplicate molecule descriptorMap unit graph noDuplicate sense]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4bLikeUnlikeDescriptorPairs) [])
    (ordinaryKeyWithObservations_congr graph
      (retainedContextNodeObservation molecule graph unit)
      (readingEvidence molecule descriptorMap unit graph sense)
      (contextualNodeObservation molecule graph unit.1.root) observeEq W D graph.root)

include noDuplicate observeEq in
private theorem retainedRule4cComponent_eq_contextual (W D : ℕ) (sense : DescriptorSense) :
    observedRule4cComponent graph (retainedContextNodeObservation molecule graph unit)
        (retainedReadingEvidence4c molecule descriptorMap unit graph sense) W D graph.root =
      observedRule4cComponent graph (contextualNodeObservation molecule graph unit.1.root)
        (readingEvidence4c molecule descriptorMap unit graph sense) W D graph.root := by
  unfold observedRule4cComponent
  rw [retainedReadingEvidence4c_eq_of_noDuplicate molecule descriptorMap unit graph noDuplicate
    sense]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) [])
    (ordinaryKeyWithObservations_congr graph
      (retainedContextNodeObservation molecule graph unit)
      (readingEvidence4c molecule descriptorMap unit graph sense)
      (contextualNodeObservation molecule graph unit.1.root) observeEq W D graph.root)

include noDuplicate observeEq in
private theorem retainedNoReferenceComponent_eq_contextual (W D : ℕ) :
    observedRule4cComponent graph (retainedContextNodeObservation molecule graph unit)
        (retainedNoReferenceEvidence4c molecule descriptorMap unit graph) W D graph.root =
      observedRule4cComponent graph (contextualNodeObservation molecule graph unit.1.root)
        (noReferenceEvidence4c molecule descriptorMap unit graph) W D graph.root := by
  unfold observedRule4cComponent
  rw [retainedNoReferenceEvidence4c_eq_of_noDuplicate molecule descriptorMap unit graph noDuplicate]
  exact congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) [])
    (ordinaryKeyWithObservations_congr graph
      (retainedContextNodeObservation molecule graph unit)
      (noReferenceEvidence4c molecule descriptorMap unit graph)
      (contextualNodeObservation molecule graph unit.1.root) observeEq W D graph.root)

include noDuplicate observeEq in
theorem retainedCompleteReadingAt_eq_contextual_of_noDuplicate (W D : ℕ)
    (reference : Option DescriptorSense) :
    retainedCompleteReadingAt molecule descriptorMap unit graph W D reference =
      contextualCompleteReadingAt molecule descriptorMap unit graph W D reference := by
  cases reference with
  | none =>
      unfold retainedCompleteReadingAt contextualCompleteReadingAt
      exact congrArg (fun key : Key StereoLabel => toLex ([], key))
        (retainedNoReferenceComponent_eq_contextual molecule descriptorMap unit graph noDuplicate
          observeEq W D)
  | some sense =>
      unfold retainedCompleteReadingAt contextualCompleteReadingAt
      exact congrArg (fun pair : Key StereoLabel × Key StereoLabel => toLex pair)
        (Prod.ext
          (retainedRule4bComponent_eq_contextual molecule descriptorMap unit graph noDuplicate
            observeEq W D sense)
          (retainedRule4cComponent_eq_contextual molecule descriptorMap unit graph noDuplicate
            observeEq W D sense))

include noDuplicate observeEq in
theorem retainedCompleteReadingsAt_eq_contextual_of_noDuplicate (W D : ℕ) :
    retainedCompleteReadingsAt molecule descriptorMap unit graph W D =
      contextualCompleteReadingsAt molecule descriptorMap unit graph W D := by
  unfold retainedCompleteReadingsAt contextualCompleteReadingsAt
  rw [retainedReferenceSelection_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
    noDuplicate observeEq]
  cases contextualReferenceSelection molecule descriptorMap unit graph with
  | empty =>
      simp [retainedCompleteReadingAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
        noDuplicate observeEq]
  | one sense =>
      simp [retainedCompleteReadingAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
        noDuplicate observeEq]
  | both =>
      simp [retainedCompleteReadingAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
        noDuplicate observeEq]

include noDuplicate observeEq in
theorem retainedCompletePriorSignatureAt_eq_contextual_of_noDuplicate (W D : ℕ) :
    retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D =
      contextualCompletePriorSignatureAt molecule descriptorMap unit graph W D := by
  unfold retainedCompletePriorSignatureAt contextualCompletePriorSignatureAt
  rw [retainedReferenceSelection_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
      noDuplicate observeEq,
    retainedCompleteReadingsAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
      noDuplicate observeEq]

include noDuplicate observeEq in
theorem retainedTaggedAlternativeReferencesAt_eq_contextual_of_noDuplicate (W D : ℕ) :
    retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D =
      contextualTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D := by
  unfold retainedTaggedAlternativeReferencesAt contextualTaggedAlternativeReferencesAt
  rw [retainedReferenceSelection_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
    noDuplicate observeEq]
  cases contextualReferenceSelection molecule descriptorMap unit graph with
  | empty => rfl
  | one sense => rfl
  | both =>
      rw [retainedCompleteReadingAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
          noDuplicate observeEq W D (some .senior),
        retainedCompleteReadingAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
          noDuplicate observeEq W D (some .junior)]

include noDuplicate observeEq in
theorem retainedMolecularRankPairAt_eq_contextual_of_noDuplicate (W D : ℕ) :
    retainedMolecularRankPairAt molecule descriptorMap unit graph W D =
      contextualMolecularRankPairAt molecule descriptorMap unit graph W D := by
  unfold retainedMolecularRankPairAt contextualMolecularRankPairAt observedPairKey
    observedRule4aComponent
  rw [retainedRankEvidence_eq_rankEvidence_of_noDuplicate molecule descriptorMap unit graph
    noDuplicate]
  refine congrArg (fun pair : List (Key ℤ) × Key StereoLabel => toLex pair) (Prod.ext ?_ ?_)
  · exact ruleKeyWithObservations_congr graph W D
      (retainedContextNodeObservation molecule graph unit)
      (contextualNodeObservation molecule graph unit.1.root) observeEq graph.root
  · exact congrArg (fun key => (ofLex key).2.getD (stereoIndex .rule4aStereogenicUnitKind) [])
      (ordinaryKeyWithObservations_congr graph
        (retainedContextNodeObservation molecule graph unit)
        (rankEvidence molecule descriptorMap unit graph)
        (contextualNodeObservation molecule graph unit.1.root) observeEq W D graph.root)

include noDuplicate observeEq in
theorem retainedCompleteLigandPriorKeyAt_eq_contextual_of_noDuplicate (W D : ℕ) :
    retainedCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D =
      contextualCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D := by
  unfold retainedCompleteLigandPriorKeyAt contextualCompleteLigandPriorKeyAt
  exact congrArg (fun pair : MolecularRankPair × CompletePriorSignature => toLex pair)
    (Prod.ext
      (retainedMolecularRankPairAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
        noDuplicate observeEq W D)
      (retainedCompletePriorSignatureAt_eq_contextual_of_noDuplicate molecule descriptorMap unit
        graph noDuplicate observeEq W D))

include noDuplicate observeEq in
theorem retainedCompleteRule5ReadingAt_eq_contextual_of_noDuplicate (W D : ℕ)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    retainedCompleteRule5ReadingAt molecule descriptorMap unit graph W D reference common =
      contextualCompleteRule5ReadingAt molecule descriptorMap unit graph W D reference common := by
  cases reference with
  | none =>
      simp only [retainedCompleteRule5ReadingAt, contextualCompleteRule5ReadingAt]
      rw [retainedCompleteReadingAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
        noDuplicate observeEq W D none]
      rfl
  | some own =>
      simp only [retainedCompleteRule5ReadingAt, contextualCompleteRule5ReadingAt]
      rw [retainedCompleteReadingAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
        noDuplicate observeEq W D (some own)]

include noDuplicate observeEq in
theorem retainedCompleteRule5ReadingsAt_eq_contextual_of_noDuplicate (W D : ℕ)
    (common : DescriptorSense) :
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common =
      contextualCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common := by
  unfold retainedCompleteRule5ReadingsAt contextualCompleteRule5ReadingsAt
  rw [retainedTaggedAlternativeReferencesAt_eq_contextual_of_noDuplicate molecule descriptorMap unit
    graph noDuplicate observeEq W D]
  apply List.map_congr_left
  intro reference _
  exact retainedCompleteRule5ReadingAt_eq_contextual_of_noDuplicate molecule descriptorMap unit
    graph noDuplicate observeEq W D reference common

include noDuplicate observeEq in
theorem retainedCompleteLigandRule5KeyAt_eq_contextual_of_noDuplicate (W D : ℕ) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D =
      contextualCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D := by
  unfold retainedCompleteLigandRule5KeyAt contextualCompleteLigandRule5KeyAt
  exact congrArg (fun pair : CompleteLigandPriorKey × List (Key StereoLabel) => toLex pair)
    (Prod.ext
      (retainedCompleteLigandPriorKeyAt_eq_contextual_of_noDuplicate molecule descriptorMap unit
        graph noDuplicate observeEq W D)
      (retainedCompleteRule5ReadingsAt_eq_contextual_of_noDuplicate molecule descriptorMap unit graph
        noDuplicate observeEq W D .senior))

include noDuplicate in
/-- On a duplicate-free digraph, distance alignment is enough for the retained and contextual
Rule-5 keys to agree. The alignment itself is not established for a cyclic carrier. -/
theorem retainedCompleteLigandRule5KeyAt_eq_contextual_of_noDuplicate_of_distance
    (aligned : ∀ node atom, graph.label node = ⟨some atom, .realAtom⟩ →
      molecule.underlyingSimpleGraph.dist unit.1.root atom =
        match retainedOccurrenceSteps graph node with
        | some steps => (rerootWalk unit.1.root unit.1.path steps).length
        | none => graph.depth node + 1)
    (W D : ℕ) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D =
      contextualCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D := by
  exact retainedCompleteLigandRule5KeyAt_eq_contextual_of_noDuplicate molecule descriptorMap unit
    graph noDuplicate
    (retainedContextNodeObservation_eq_contextualNodeObservation_of_distance molecule graph unit
      unit.1.root aligned) W D

end Agreement

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.eligibleSense_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.not_Eligible_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.not_RetainedInReferenceClass_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteReadingsAt_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompletePriorSignatureAt_count
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompletePriorSignatureAt_empty
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedTaggedAlternativeReferencesAt_projection
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteRule5ReadingsAt_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandPriorKeyAt_rank
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandPriorKeyAt_signature
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandRule5KeyAt_prior
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandRule5KeyAt_rule5
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandPriorKeyAt_compare_eq_then
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandRule5KeyAt_compare_eq_then
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.compare_unmaskedRetainedPriorSignature_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4aObservation_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4cObservation_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankEvidence_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence4c_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedNoReferenceEvidence4c_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankKey_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankPath_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedInReferenceClass_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReferenceClass_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedSeniorCount_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedJuniorCount_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReferenceSelection_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteReadingAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteReadingsAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompletePriorSignatureAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteRule5ReadingAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankKey_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankPath_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedInReferenceClass_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedSeniorCount_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedJuniorCount_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReferenceSelection_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteReadingAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteReadingsAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompletePriorSignatureAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedTaggedAlternativeReferencesAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteRule5ReadingsAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedMolecularRankPairAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandPriorKeyAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandRule5KeyAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankEvidence_eq_rankEvidence_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankKey_eq_observed_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankPath_eq_observed_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedInReferenceClass_iff_observed_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReferenceSelection_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteReadingAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteReadingsAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompletePriorSignatureAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedTaggedAlternativeReferencesAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedMolecularRankPairAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandPriorKeyAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteRule5ReadingAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteRule5ReadingsAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandRule5KeyAt_eq_contextual_of_noDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandRule5KeyAt_eq_contextual_of_noDuplicate_of_distance
