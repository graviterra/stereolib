import TetraStereo.OneCenter.DeclarativeCIPRetainedWindowIndependence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Retained-key window independence at arbitrary parent occurrences.

Deep sibling comparisons occur at ordinary atoms as well as detected tetrahedral centers.
The earlier retained-window theorem unnecessarily required a detected parent. The proofs
below use only its occurrence root and path, and apply without a detected-center hypothesis.
Descriptor reads remain restricted to detected occurrences. This supplies window transport
for molecular-cut deep priors at all internal nodes, including three-coordinate nitrogen.
The earlier API and all its consumers remain unchanged.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence

open DeclarativeCIP
noncomputable section
open scoped Classical
universe u

section Retained

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : OccurrenceUnit Atom) (graph : RootedDigraph Atom)

local instance windowIndependenceRetainedNodeFintype : Fintype graph.Node := graph.nodeFintype

theorem retainedCompleteReadingAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D')
    (reference : Option DescriptorSense) :
    ReadingCorr W D W' D'
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D reference)
      (retainedCompleteReadingAt molecule descriptorMap unit graph W' D' reference) := by
  cases reference with
  | none =>
      exact ⟨Or.inl ⟨rfl, rfl⟩,
        stereoComponent_keyCorr graph (retainedContextNodeObservation molecule graph unit)
          (retainedNoReferenceEvidence4c molecule descriptorMap unit graph)
          .rule4cPseudoasymmetricDescriptor graph.root cover cover'⟩
  | some sense =>
      exact ⟨stereoComponent_keyCorr graph (retainedContextNodeObservation molecule graph unit)
          (retainedReadingEvidence molecule descriptorMap unit graph sense)
          .rule4bLikeUnlikeDescriptorPairs graph.root cover cover',
        stereoComponent_keyCorr graph (retainedContextNodeObservation molecule graph unit)
          (retainedReadingEvidence4c molecule descriptorMap unit graph sense)
          .rule4cPseudoasymmetricDescriptor graph.root cover cover'⟩

theorem retainedCompleteReadingsAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    List.Forall₂ (ReadingCorr W D W' D')
      (retainedCompleteReadingsAt molecule descriptorMap unit graph W D)
      (retainedCompleteReadingsAt molecule descriptorMap unit graph W' D') := by
  have reading := retainedCompleteReadingAt_corr molecule descriptorMap unit graph cover cover'
  unfold retainedCompleteReadingsAt
  cases retainedReferenceSelection molecule descriptorMap unit graph with
  | empty => exact .cons (reading none) .nil
  | one sense => exact .cons (reading (some sense)) .nil
  | both =>
      exact .cons ((readingCorr_faithful W D W' D').max (reading (some .senior))
          (reading (some .junior)))
        (.cons ((readingCorr_faithful W D W' D').min (reading (some .senior))
          (reading (some .junior))) .nil)

theorem retainedCompletePriorSignatureAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    SignatureCorr W D W' D'
      (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D)
      (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W' D') := by
  have readings := retainedCompleteReadingsAt_corr molecule descriptorMap unit graph cover cover'
  refine ⟨rfl, ?_, ?_⟩
  · dsimp only [retainedCompletePriorSignatureAt, ofLex_toLex]
    split_ifs
    · exact .nil
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.Forall₂.imp (fun _ _ h => h.1) readings
  · dsimp only [retainedCompletePriorSignatureAt, ofLex_toLex]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.Forall₂.imp (fun _ _ h => h.2) readings

theorem retainedMolecularRankPairAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    LexCorr (VecCorr 3 W D W' D') (KeyCorr W D W' D')
      (retainedMolecularRankPairAt molecule descriptorMap unit graph W D)
      (retainedMolecularRankPairAt molecule descriptorMap unit graph W' D') :=
  ⟨ruleKey_vecCorr graph (retainedContextNodeObservation molecule graph unit) graph.root
      cover cover',
    stereoComponent_keyCorr graph (retainedContextNodeObservation molecule graph unit)
      (retainedRankEvidence molecule descriptorMap unit graph) .rule4aStereogenicUnitKind
      graph.root cover cover'⟩

/-- **The Rule-5 tagged alternative order is window-free.** The `compare` deciding whether the
junior alternative leads reads complete readings, whose order is window-free. -/
theorem retainedTaggedAlternativeReferencesAt_window {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D =
      retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W' D' := by
  have reading := retainedCompleteReadingAt_corr molecule descriptorMap unit graph cover cover'
  have agree := readingCorr_faithful W D W' D' (reading (some .senior)) (reading (some .junior))
  unfold retainedTaggedAlternativeReferencesAt
  cases retainedReferenceSelection molecule descriptorMap unit graph with
  | empty => rfl
  | one _ => rfl
  | both =>
      dsimp only
      by_cases h : retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior) <
          retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
      · rw [if_pos ((completeReading_compare_lt_iff _ _).2 h),
          if_pos ((completeReading_compare_lt_iff _ _).2 (agree.1.mp h))]
      · rw [if_neg (fun c => h ((completeReading_compare_lt_iff _ _).1 c)),
          if_neg (fun c => h (agree.1.mpr ((completeReading_compare_lt_iff _ _).1 c)))]

theorem retainedCompleteRule5ReadingsAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D')
    (common : DescriptorSense) :
    List.Forall₂ (KeyCorr W D W' D')
      (retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common)
      (retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W' D' common) := by
  have reading := retainedCompleteReadingAt_corr molecule descriptorMap unit graph cover cover'
  unfold retainedCompleteRule5ReadingsAt
  rw [retainedTaggedAlternativeReferencesAt_window molecule descriptorMap unit graph cover cover',
    List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr (fun reference _ => ?_)
  cases reference with
  | none =>
      simp only [retainedCompleteRule5ReadingAt]
      exact keyCorr_map _ (reading none).2
  | some own =>
      simp only [retainedCompleteRule5ReadingAt]
      exact keyCorr_map _ (reading (some own)).1

/-- **The retained complete key corresponds across any two covering windows.** -/
theorem retainedCompleteLigandRule5KeyAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    CompleteKeyCorr W D W' D'
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D)
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit graph W' D') :=
  ⟨⟨retainedMolecularRankPairAt_corr molecule descriptorMap unit graph cover cover',
      retainedCompletePriorSignatureAt_corr molecule descriptorMap unit graph cover cover'⟩,
    retainedCompleteRule5ReadingsAt_corr molecule descriptorMap unit graph cover cover' .senior⟩

end Retained

/-- **Window independence of retained comparisons** between two cut graphs: whole keys (through
Rule 5) and their prior keys (through the count / Rule-4b / Rule-4c signature) compare identically
at any two windows covering both graphs. -/
theorem retainedCompleteLigandRule5KeyAt_orderAgrees_window {Atom : Type u} [Fintype Atom]
    [DecidableEq Atom] (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : OccurrenceUnit Atom) {left right : RootedDigraph Atom} {W D W' D' : ℕ}
    (coverLeft : WindowCovers left W D) (coverLeft' : WindowCovers left W' D')
    (coverRight : WindowCovers right W D) (coverRight' : WindowCovers right W' D') :
    OrderAgrees (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W' D')
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W' D') ∧
    OrderAgrees (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)).1
        (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)).1
      (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W' D')).1
        (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W' D')).1 := by
  have hl := retainedCompleteLigandRule5KeyAt_corr molecule descriptorMap unit left
    coverLeft coverLeft'
  have hr := retainedCompleteLigandRule5KeyAt_corr molecule descriptorMap unit right
    coverRight coverRight'
  exact ⟨completeKeyCorr_faithful W D W' D' hl hr, priorCorr_faithful W D W' D' hl.1 hr.1⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence.retainedCompleteReadingAt_corr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence.retainedCompleteReadingsAt_corr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence.retainedCompletePriorSignatureAt_corr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence.retainedMolecularRankPairAt_corr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence.retainedTaggedAlternativeReferencesAt_window
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence.retainedCompleteRule5ReadingsAt_corr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence.retainedCompleteLigandRule5KeyAt_corr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence.retainedCompleteLigandRule5KeyAt_orderAgrees_window
