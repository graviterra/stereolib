import TetraStereo.UniversalProof.SourceNativePlanarTetrahedralTwoPassClosureProofs.SourceNativePlanarTetrahedralTwoPassClosure
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceReadiness

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativePlanarTetrahedralPriorityClosureProofs.SourceNativePlanarTetrahedralPriorityClosure

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison
  (buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
   buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?_sound
   DeclarativeAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame)
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralTwoPassClosureProofs.SourceNativePlanarTetrahedralTwoPassClosure
  (actual_planar_twoPass_frame_closed)
open TetraStereo.UniversalProof.SourceNativePlanarKeyObservationConservationProofs.SourceNativePlanarKeyObservationConservation
  (HasObservation)
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource
  (target roots firstCursor actual_four_real_roots cisNodeResult)
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralKeyFrameProofs.SourceNativePlanarTetrahedralKeyFrame (roots_valid)

















abbrev source := TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.source
local instance : NeZero source.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

noncomputable def ligandFrame : source.AromaticCanonicalOccurrenceFourLigandFrame 1 :=
  { roots := roots, rootsLength := actual_four_real_roots.1 }

def priority (slot : Fin 4) : Nat :=
  match slot.val with
  | 0 => 6
  | 1 => 9
  | 2 => 35
  | _ => 53

def actualTracked : TrackedLocalizedLigandOrder := ⟨[3, 2, 1, 0], 0⟩

theorem actual_root_atomic_observations (slot : Fin 4) :
    MoleculeGraph.exactOfficialRule1aObservation source.molecule.toLocalizedMoleculeGraph
      (ligandFrame.cursorAt slot).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat (priority slot) := by
  fin_cases slot <;> rfl

theorem priority_injective : Function.Injective priority := by decide +kernel

theorem priority_tracked_sort_computed :
    sortFourLocalizedLigandsTracked (strictRankComparison priority) = some actualTracked := by
  decide +kernel

theorem actual_priority_order_descending :
    actualTracked.highestFirst.Pairwise (fun left right => priority right < priority left) := by
  decide +kernel

private theorem exists_compound_keys
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor 1),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45Key? target view 4) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, computed⟩ := source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
        target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ := exists_compound_keys view cursors
        (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [List.mapM_cons, computed, keysComputed]⟩

/-- Actual four NEW planar records for any view; the seqcis event remains in their Rule-3 frame. -/
theorem actual_planar_key_records (view : source.AromaticCanonicalDependencyView target) :
    ∃ keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1,
      buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
        source target view 4 roots = some keys ∧
      DeclarativeAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame
        source target view 4 roots keys ∧
      ∃ key ∈ keys.rule3Frame.keys, HasObservation source key cisNodeResult := by
  obtain ⟨rule3Frame, rule3Computed, rule3Meaning, _, _, _, observed⟩ :=
    actual_planar_twoPass_frame_closed
  have rule3Length : rule3Frame.keys.length = 4 :=
    (SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison.CanonicalAromaticCanonicalPlanarRule3Frame.keys_length
      source 4 roots rule3Frame rule3Meaning).trans actual_four_real_roots.1
  obtain ⟨rule45Keys, rule45Computed⟩ := exists_compound_keys view roots roots_valid
  have rule45Length : rule45Keys.length = 4 :=
    (mapM_length_eq_of_eq_some
      (source.buildAromaticCanonicalRerootCompoundRule45Key? target view 4)
      roots rule45Keys rule45Computed).trans actual_four_real_roots.1
  let keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1 :=
    { rule3Frame, rule3Length, rule45Keys, rule45Length }
  have computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view 4 roots = some keys := by
    simp [buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?,
      keys, rule3Computed, rule3Length, rule45Computed, rule45Length]
  exact ⟨keys, computed,
    buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?_sound
      source target view 4 roots keys computed, observed⟩

private theorem canonicalList_forall₂
    {input : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {NodeOutcome : OfficialCIPNode input.AromaticCanonicalAtom →
      Option input.AromaticCanonicalRule3SpatialNodeResult → Prop}
    {cursors : List (input.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List input.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : input.CanonicalAromaticCanonicalRule3SpatialKeyWithList
      NodeOutcome fuel cursors keys) :
    List.Forall₂ (input.CanonicalAromaticCanonicalRule3SpatialKeyWith NodeOutcome fuel)
      cursors keys :=
  match derived with
  | .nil _ => .nil
  | .cons head tail => .cons head (canonicalList_forall₂ tail)

private theorem canonical_constitutional_head
    {input : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {NodeOutcome : OfficialCIPNode input.AromaticCanonicalAtom →
      Option input.AromaticCanonicalRule3SpatialNodeResult → Prop}
    {cursor : input.AromaticCanonicalRerootCursor carrierFuel}
    {key : input.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : input.CanonicalAromaticCanonicalRule3SpatialKeyWith NodeOutcome fuel cursor key) :
    key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] := by
  cases derived <;> rfl

theorem actual_key_constitutional_head (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1)
    (computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view 4 roots = some keys) (slot : Fin 4) :
    (keys.keyAt slot).rule3.constitutional.sourceNodes.head? =
      some [([], (ligandFrame.cursorAt slot).occurrence.1.node)] := by
  have meaning := buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?_sound
    source target view 4 roots keys computed
  have pointwise := canonicalList_forall₂ meaning.1.2.2.2
  have derived := pointwise.get (i := slot.val)
    (by rw [actual_four_real_roots.1]; exact slot.isLt)
    (by rw [keys.rule3Length]; exact slot.isLt)
  exact canonical_constitutional_head derived

theorem actual_key_atomic_head (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1)
    (computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view 4 roots = some keys) (slot : Fin 4) :
    (ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
      (keys.keyAt slot).rule3.constitutional.sourceNodes).head? =
      some [([], DeclarativeCIP.ExactAtomicNumber.ofNat (priority slot))] := by
  have head := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph (keys.keyAt slot).rule3.constitutional.sourceNodes
    (ligandFrame.cursorAt slot).occurrence.1.node
    (actual_key_constitutional_head view keys computed slot)
  simpa only [actual_root_atomic_observations] using head

theorem actual_comparison_gt_of_priority (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1)
    (computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view 4 roots = some keys) (left right : Fin 4)
    (higher : priority right < priority left) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right =
      { ordering := .gt, pseudo := false } := by
  have rule1a := ExactOfficialRuleMajorKey.compareSparseExactRule1a_gt_of_heads_gt
    (actual_key_atomic_head view keys computed left)
    (actual_key_atomic_head view keys computed right) higher
  apply source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_gt
  apply source.compareAromaticCanonicalUncancelledRule3SpatialKeys_of_constitutional_gt
  simp [ExactOfficialRuleMajorKey.compare, ExactOfficialRuleMajorKey.compareAddressedSources,
    Ordering.byKey, compareLex, rule1a]

theorem actual_comparison_lt_of_priority (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1)
    (computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view 4 roots = some keys) (left right : Fin 4)
    (lower : priority left < priority right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right =
      { ordering := .lt, pseudo := false } := by
  have rule1a := ExactOfficialRuleMajorKey.compareSparseExactRule1a_lt_of_heads_lt
    (actual_key_atomic_head view keys computed left)
    (actual_key_atomic_head view keys computed right) lower
  have rule3 : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (keys.keyAt left).rule3 (keys.keyAt right).rule3 = .lt := by
    simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, ExactOfficialRuleMajorKey.compare,
      ExactOfficialRuleMajorKey.compareAddressedSources, Ordering.byKey, compareLex, rule1a]
  simp [compareAromaticCanonicalOccurrenceRule3Through5At, rule3]

theorem actual_callback_eq_strictRank_of_ne (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1)
    (computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view 4 roots = some keys) (left right : Fin 4) (different : left ≠ right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys left right =
      strictRankComparison priority left right := by
  have distinct : priority left ≠ priority right := fun equal => different (priority_injective equal)
  rcases Nat.lt_or_gt_of_ne distinct with lower | higher
  · have compared := actual_comparison_lt_of_priority view keys computed left right lower
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
      aromaticCanonicalRule3Through5DescriptorComparison, strictRankComparison,
      compared, Nat.compare_eq_lt.mpr lower]
  · have compared := actual_comparison_gt_of_priority view keys computed left right higher
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
      aromaticCanonicalRule3Through5DescriptorComparison, strictRankComparison,
      compared, Nat.compare_eq_gt.mpr higher]

theorem actual_safe_order_computed (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1)
    (computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view 4 roots = some keys) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some actualTracked := by
  have same := sortLocalizedLigandsTrackedFrom_eq_of_callback_ne
    (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys) (strictRankComparison priority)
    (actual_callback_eq_strictRank_of_ne view keys computed) (List.finRange 4) [] 0
    (List.nodup_finRange 4)
  have rawComputed : source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some actualTracked := by
    change sortLocalizedLigandsTrackedFrom
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys) (List.finRange 4) [] 0 = _
    rw [same]
    exact priority_tracked_sort_computed
  have coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keys actualTracked.highestFirst = true :=
    (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff _ _).mpr
      (actual_priority_order_descending.imp (by
        intro left right higher
        rw [actual_comparison_gt_of_priority view keys computed left right higher]))
  simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawComputed, coherent]

/-- CLOSED actual planar records, independent meaning and safe literal I/Br/F/C order for ANY
dependency view, with zero pseudo history and the real seqcis event retained in the Rule-3 keys. -/
theorem actual_planar_records_and_safe_order
    (view : source.AromaticCanonicalDependencyView target) :
    ∃ keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 1,
      buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
        source target view 4 roots = some keys ∧
      DeclarativeAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame
        source target view 4 roots keys ∧
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some actualTracked ∧
      actualTracked.highestFirst = [3, 2, 1, 0] ∧ actualTracked.pseudoComparisons = 0 ∧
      ∃ key ∈ keys.rule3Frame.keys, HasObservation source key cisNodeResult := by
  obtain ⟨keys, computed, meaning, observed⟩ := actual_planar_key_records view
  exact ⟨keys, computed, meaning, actual_safe_order_computed view keys computed,
    rfl, rfl, observed⟩

end TetraStereo.UniversalProof.SourceNativePlanarTetrahedralPriorityClosureProofs.SourceNativePlanarTetrahedralPriorityClosure
