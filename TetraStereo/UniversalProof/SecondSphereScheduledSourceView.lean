import TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereScheduledSourceView

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering










/-- A successful through-Rule-5 builder actually computed its recorded Rule-3 frame before
consulting any dependency view. -/
theorem computed_rule3_frame (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel cursors = some keys) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors = some keys.rule3Frame := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? at computed
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : cursors.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) with
        | none => simp [rule3Computed, rule45Computed] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length] at computed
              subst keys
              rfl
            · simp [rule3Computed, rule45Computed, rule45Length] at computed
      · simp [rule3Computed, rule3Length] at computed

/-- Two successful actual computations at the same roots and fuel have the same complete
Rule-3 frame, even when their dependency views differ. Rules-4--5 keys may differ. -/
theorem computed_rule3_frame_view_invariant (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (leftView rightView : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (leftKeys rightKeys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (leftComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target leftView fuel cursors = some leftKeys)
    (rightComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target rightView fuel cursors = some rightKeys) :
    leftKeys.rule3Frame = rightKeys.rule3Frame := by
  exact Option.some.inj ((computed_rule3_frame source target leftView fuel cursors leftKeys
    leftComputed).symm.trans (computed_rule3_frame source target rightView fuel cursors rightKeys
      rightComputed))

/-- Equality of frames gives equality of the actual selected Rule-3 keys. The dependent Fin
casts are retained; proof irrelevance is used only after the record fields are identified. -/
theorem keyAt_rule3_eq_of_frame_eq (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (leftKeys rightKeys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (same : leftKeys.rule3Frame = rightKeys.rule3Frame) (slot : Fin 4) :
    (leftKeys.keyAt slot).rule3 = (rightKeys.keyAt slot).rule3 := by
  cases leftKeys with
  | mk leftFrame leftLength left45 left45Length =>
      cases rightKeys with
      | mk rightFrame rightLength right45 right45Length =>
          cases same
          rfl

/-- Actual readiness for any dependency view is reused from returned-root/no-double readiness.
Carrier one is the independently proved adequate topology for this family. -/
theorem family_view_keys_exist (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    ∃ keys, (familySource ps).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) view 4
      (familyFrame ps i 1).roots = some keys := by
  exact actual_source_key_frame_exists (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 1 (familyCenter ps i) (familyRecordDomain ps i)
    (family_four_records ps i) view (family_source_no_double ps)

noncomputable def familyViewKeys (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    (familySource ps).AromaticCanonicalOccurrenceRule3Through5KeyFrame 1 :=
  Classical.choose (family_view_keys_exist ps i view)

theorem family_view_keys_computed (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    (familySource ps).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) view 4
      (familyFrame ps i 1).roots = some (familyViewKeys ps i view) :=
  Classical.choose_spec (family_view_keys_exist ps i view)

theorem family_view_rule3_frame (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    (familyViewKeys ps i view).rule3Frame = (familyKeys ps i 1).rule3Frame :=
  computed_rule3_frame_view_invariant (familySource ps) _ view (constitutionalView ps i 1) 4
    (familyFrame ps i 1).roots (familyViewKeys ps i view) (familyKeys ps i 1)
    (family_view_keys_computed ps i view) (family_keys_computed ps i 1)

theorem family_view_rule3_key (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) (slot : Fin 4) :
    ((familyViewKeys ps i view).keyAt slot).rule3 = ((familyKeys ps i 1).keyAt slot).rule3 :=
  keyAt_rule3_eq_of_frame_eq (familySource ps) _ _ (family_view_rule3_frame ps i view) slot

/-- The actual computed carbon keys preserve their exact second-layer projections under any
independently supplied dependency view. No projection or key-success premise is supplied. -/
theorem family_view_production_projections (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    ExactOfficialRuleMajorKey.exactRule1aLayers (familySource ps).molecule.toLocalizedMoleculeGraph
      ((familyViewKeys ps i view).keyAt (familyRoleSlot ps i 1 2 (by simp))).rule3.constitutional.sourceNodes =
        [carbonRootLayer, bridgeChildLayer] ∧
    ExactOfficialRuleMajorKey.exactRule1aLayers (familySource ps).molecule.toLocalizedMoleculeGraph
      ((familyViewKeys ps i view).keyAt (familyRoleSlot ps i 1 8 (by simp))).rule3.constitutional.sourceNodes =
        [carbonRootLayer, methylChildLayer] := by
  rw [family_view_rule3_key, family_view_rule3_key]
  exact family_one_production_projections ps i

theorem family_view_rule3_carbon_both (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    (familySource ps).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((familyViewKeys ps i view).keyAt (familyRoleSlot ps i 1 2 (by simp))).rule3
      ((familyViewKeys ps i view).keyAt (familyRoleSlot ps i 1 8 (by simp))).rule3 = .gt ∧
    (familySource ps).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((familyViewKeys ps i view).keyAt (familyRoleSlot ps i 1 8 (by simp))).rule3
      ((familyViewKeys ps i view).keyAt (familyRoleSlot ps i 1 2 (by simp))).rule3 = .lt := by
  simp only [family_view_rule3_key]
  exact family_one_rule3_keys_both ps i

theorem family_view_carbon_callback_both (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyViewKeys ps i view)
      (familyRoleSlot ps i 1 2 (by simp)) (familyRoleSlot ps i 1 8 (by simp)) =
        some { ordering := .gt, decisiveRule? := none, pseudo := false } ∧
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyViewKeys ps i view)
      (familyRoleSlot ps i 1 8 (by simp)) (familyRoleSlot ps i 1 2 (by simp)) =
        some { ordering := .lt, decisiveRule? := none, pseudo := false } := by
  have strict := family_view_rule3_carbon_both ps i view
  constructor <;>
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      compareAromaticCanonicalOccurrenceRule3Through5At, strict.1, strict.2]

/-- Unequal physical atomic priorities remain decisive with any view, through the actual
internally constructed key frame. -/
theorem family_view_unequal_role_callback (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)))
    (left right : Nat) (leftMember : left ∈ [2, 6, 7, 8]) (rightMember : right ∈ [2, 6, 7, 8])
    (different : roleAtomicPriority left ≠ roleAtomicPriority right) :
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyViewKeys ps i view)
      (familyRoleSlot ps i 1 left leftMember) (familyRoleSlot ps i 1 right rightMember) =
        some { ordering := (compare (roleAtomicPriority left) (roleAtomicPriority right)), decisiveRule? := none, pseudo := false } := by
  rcases Nat.lt_or_gt_of_ne different with lower | higher
  · have priorities : occurrenceAtomicPriority (familySource ps) (familyFrame ps i 1)
        (familyRoleSlot ps i 1 left leftMember) <
      occurrenceAtomicPriority (familySource ps) (familyFrame ps i 1)
        (familyRoleSlot ps i 1 right rightMember) := by
      rw [family_role_priority, family_role_priority]
      exact lower
    have compared := occurrence_comparison_lt_of_atomic_priority (familySource ps) _ view 4
      (familyFrame ps i 1) (family_roots_real ps i 1) (familyViewKeys ps i view)
      (family_view_keys_computed ps i view) _ _ priorities
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      compared, Nat.compare_eq_lt.mpr lower]
  · have priorities : occurrenceAtomicPriority (familySource ps) (familyFrame ps i 1)
        (familyRoleSlot ps i 1 right rightMember) <
      occurrenceAtomicPriority (familySource ps) (familyFrame ps i 1)
        (familyRoleSlot ps i 1 left leftMember) := by
      rw [family_role_priority, family_role_priority]
      exact higher
    have compared := occurrence_comparison_gt_of_atomic_priority (familySource ps) _ view 4
      (familyFrame ps i 1) (family_roots_real ps i 1) (familyViewKeys ps i view)
      (family_view_keys_computed ps i view) _ _ priorities
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      compared, Nat.compare_eq_gt.mpr higher]

theorem family_view_callback_strictRank (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)))
    (left right : Fin 4) (different : left ≠ right) :
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyViewKeys ps i view) left right =
      strictRankComparison (familyPriorityRank ps i) left right := by
  have ranks := family_priority_rank_roles ps i
  have carbon := family_view_carbon_callback_both ps i view
  rcases family_role_slots_cover ps i left with rfl | rfl | rfl | rfl <;>
    rcases family_role_slots_cover ps i right with rfl | rfl | rfl | rfl
  all_goals simp only [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2]
  all_goals first
    | exact False.elim (different rfl)
    | exact carbon.1
    | exact carbon.2
    | (apply family_view_unequal_role_callback ps i view; decide)

/-- The actual safe source sorter succeeds coherently for every dependency view. -/
theorem family_view_safe_tracked_order (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    ∃ tracked,
      (familySource ps).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
        (familyViewKeys ps i view) = some tracked ∧
      tracked.highestFirst = familyPrioritySlots ps i ∧ tracked.pseudoComparisons = 0 ∧
      (familySource ps).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
        (familyViewKeys ps i view) tracked.highestFirst = true := by
  obtain ⟨tracked, computed, permutation, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne (familyPriorityRank ps i)
      (family_priority_rank_injective ps i)
      ((familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyViewKeys ps i view))
      (family_view_callback_strictRank ps i view)
  have higherOrdering : ∀ left right, familyPriorityRank ps i right < familyPriorityRank ps i left →
      ((familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At
        (familyViewKeys ps i view) left right).ordering = .gt := by
    intro left right higher
    have different : left ≠ right := by intro same; subst right; exact Nat.lt_irrefl _ higher
    have callback := family_view_callback_strictRank ps i view left right different
    have ordering := congrArg (fun result => result.map (fun comparison => comparison.ordering)) callback
    simpa [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      strictRankComparison, Nat.compare_eq_gt.mpr higher] using ordering
  have coherent := ((familySource ps).aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
    (familyViewKeys ps i view) tracked.highestFirst).mpr (descending.imp (fun {left right} higher => higherOrdering left right higher))
  have safe : (familySource ps).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
      (familyViewKeys ps i view) = some tracked := by
    simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?, computed, coherent]
  have exactOrder : tracked.highestFirst = familyPrioritySlots ps i :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ first second => False.elim (Nat.lt_asymm first second))
      descending (family_priority_slots_descending ps i)
      (permutation.trans (family_priority_slots_perm ps i).symm)
  exact ⟨tracked, safe, exactOrder, zero, coherent⟩

/-- The genuine scheduled source model is constructed by the accepted causal scheduler. It
is not supplied by the caller and is not replaced by an expected descriptor environment. -/
noncomputable def familyScheduledState (ps : List TetrahedralInputParity) :
    (familySource ps).AromaticCanonicalAuxiliaryState 1 :=
  constitutionParserRichScheduledState (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps) 1 4

noncomputable def familyScheduledView (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) :=
  (familySource ps).aromaticCanonicalDependencyView (familyScheduledState ps)
    ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))

/-- This is the same internally constructed scheduled model consumed by the production rich
source descriptor function; its assigned parity label is separately derived below. -/
theorem family_scheduled_model (ps : List TetrahedralInputParity) :
    ((familySource ps).aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics (familyRaw ps) (familySource ps)
        (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps) 1 4)).CIPModel
          (familyScheduledState ps) :=
  constitutionParserRichScheduledState_cipModel (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps) 1 4

/-- Actual accepted model evaluation, specialized to the internally chosen family model. No
model/evaluation output is a hypothesis; parity identification is separately derived below. -/
theorem family_scheduled_evaluation (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    constitutionParserRichDescriptor? (familyRaw ps) (familySource ps)
      (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))
      (familyScheduledView ps i) 4 =
        familyScheduledState ps ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) :=
  constitutionParserRichModel_evaluates (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps)
    (familyScheduledState ps) (family_scheduled_model ps)
    ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))

/-- Both exact production second layers for the actual scheduled dependency view. Final
inputs are only the parity list and valid block index. -/
theorem family_scheduled_projections (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ExactOfficialRuleMajorKey.exactRule1aLayers (familySource ps).molecule.toLocalizedMoleculeGraph
      ((familyViewKeys ps i (familyScheduledView ps i)).keyAt
        (familyRoleSlot ps i 1 2 (by simp))).rule3.constitutional.sourceNodes =
          [carbonRootLayer, bridgeChildLayer] ∧
    ExactOfficialRuleMajorKey.exactRule1aLayers (familySource ps).molecule.toLocalizedMoleculeGraph
      ((familyViewKeys ps i (familyScheduledView ps i)).keyAt
        (familyRoleSlot ps i 1 8 (by simp))).rule3.constitutional.sourceNodes =
          [carbonRootLayer, methylChildLayer] :=
  family_view_production_projections ps i (familyScheduledView ps i)

/-- The actual source safe tracked order is coherent at the genuine scheduled view, without
assuming that view equals the independently defined constitutional none-view. -/
theorem family_scheduled_safe_tracked_order (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ∃ tracked,
      (familySource ps).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
        (familyViewKeys ps i (familyScheduledView ps i)) = some tracked ∧
      tracked.highestFirst = familyPrioritySlots ps i ∧ tracked.pseudoComparisons = 0 ∧
      (familySource ps).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
        (familyViewKeys ps i (familyScheduledView ps i)) tracked.highestFirst = true :=
  family_view_safe_tracked_order ps i (familyScheduledView ps i)

noncomputable def familySlotAtomID (ps : List TetrahedralInputParity) (i : Fin ps.length) : Fin 4 → Nat :=
  slotAtomID (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
    1 (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i)

/-- Endpoint identity in an actual returned position. This needs physical row distinctness,
not atomic-number injectivity; the two carbons remain distinct physical endpoints. -/
theorem family_returned_id_at (ps : List TetrahedralInputParity) (i : Fin ps.length) (slot : Fin 4) :
    ((familyFrame ps i 1).roots.map (cursorAtomID (familySource ps)))[slot.val]? =
      some (some (familySlotAtomID ps i slot)) := by
  let frame := familyFrame ps i 1
  have bound : slot.val < frame.roots.length := by rw [frame.rootsLength]; exact slot.isLt
  change (frame.roots.map (cursorAtomID (familySource ps)))[slot.val]? = _
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  obtain ⟨atom, _, current, _, equal⟩ := actual_slot_endpoint (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 1 (familyCenter ps i) (familyRecordDomain ps i)
    (family_four_records ps i) slot
  change some (cursorAtomID (familySource ps) (frame.cursorAt slot)) = _
  change (frame.cursorAt slot).occurrence.1.node.current? = some atom at current
  change familySlotAtomID ps i slot = atom.val at equal
  rw [equal]
  unfold cursorAtomID
  rw [current]
  rfl

/-- Actual finite slot matcher readiness follows from the physical written row and returned
root-ID permutation. No identity alignment or prescribed matcher answer is supplied. -/
theorem family_alignment_exists (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ∃ slots, findSlotAlignment? ((familyRaw ps).writtenNeighbors (familyCenter ps i).1.val)
      ((familyFrame ps i 1).roots.map (cursorAtomID (familySource ps))) = some slots := by
  apply findSlotAlignment?_exists_of_perm
  · rw [family_center_index, familyRaw_tag_written]
    rfl
  · rw [family_center_index, familyRaw_tag_written]
    simp (disch := omega) [List.nodup_cons]
  · rw [family_center_index, familyRaw_tag_written]
    simpa only [List.map_cons, List.map_nil] using family_returned_root_ids ps i 1

noncomputable def familySlots (ps : List TetrahedralInputParity) (i : Fin ps.length) : List Nat :=
  Classical.choose (family_alignment_exists ps i)

theorem family_slots_computed (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    findSlotAlignment? ((familyRaw ps).writtenNeighbors (familyCenter ps i).1.val)
      ((familyFrame ps i 1).roots.map (cursorAtomID (familySource ps))) = some (familySlots ps i) :=
  Classical.choose_spec (family_alignment_exists ps i)

theorem family_slots_matching (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ExactSlotAlignment ((familyRaw ps).writtenNeighbors (familyCenter ps i).1.val)
      ((familyFrame ps i 1).roots.map (cursorAtomID (familySource ps))) (familySlots ps i) :=
  findSlotAlignment?_sound _ _ _ (family_slots_computed ps i)

/-- The actual slot matcher identifies the same physical endpoint in each source slot. -/
theorem family_aligned_written_lookup (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (slot : Fin 4) :
    ((familyRaw ps).writtenNeighbors (familyCenter ps i).1.val)[(familySlots ps i).getD slot.val 0]? =
      some (familySlotAtomID ps i slot) := by
  have matching := family_slots_matching ps i
  have length : (familySlots ps i).length = 4 := matching.2.2.1.length_eq.trans (List.length_range (n := 4))
  have bound : slot.val < (familySlots ps i).length := by rw [length]; exact slot.isLt
  have slotObserved : (familySlots ps i)[slot.val]? = some ((familySlots ps i).getD slot.val 0) := by
    rw [List.getElem?_eq_getElem bound]
    exact congrArg some (List.getElem_eq_getD 0)
  have indexed := congrArg (fun ids : List (Option Nat) => ids[slot.val]?) matching.2.2.2
  dsimp only at indexed
  rw [family_returned_id_at] at indexed
  simp only [List.getElem?_map, slotObserved, Option.map_some] at indexed
  exact Option.some.inj indexed

/-- Actual endpoint lookup and actual alignment agree for every order, including a produced
tracked order. This transports physical identities, without a Z-injectivity assumption. -/
theorem family_aligned_priority_positions (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (order : List (Fin 4)) :
    (order.map (familySlotAtomID ps i)).mapM
      (writtenSlot? ((familyRaw ps).writtenNeighbors (familyCenter ps i).1.val)) =
        some (order.map fun slot => (familySlots ps i).getD slot.val 0) := by
  induction order with
  | nil => rfl
  | cons slot rest ih =>
      have recovered := writtenSlot?_eq_some _ (family_slots_matching ps i).2.1 _ _
        (family_aligned_written_lookup ps i slot)
      simp only [List.map_cons, List.mapM_cons, recovered, ih]
      rfl

/-- The independently computed slot matcher and actual role-priority order give physical
written positions [2,0,3,1]. This result contains no caller alignment premise. -/
theorem family_aligned_role_positions (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyPrioritySlots ps i).map (fun slot => (familySlots ps i).getD slot.val 0) = [2, 0, 3, 1] := by
  have matching := family_aligned_priority_positions ps i (familyPrioritySlots ps i)
  have physical := family_tracked_written_positions ps i
  rw [(family_tracked_properties ps i).2.1] at physical
  have samePhysical : ((familyPrioritySlots ps i).map (familySlotAtomID ps i)).mapM
      (writtenSlot? ((familyRaw ps).writtenNeighbors (familyCenter ps i).1.val)) = some [2, 0, 3, 1] := by
    simpa only [familySlotAtomID, family_center_index] using physical
  exact Option.some.inj (matching.symm.trans samePhysical)

noncomputable def familyViewTracked (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) : TrackedLocalizedLigandOrder :=
  Classical.choose (family_view_safe_tracked_order ps i view)

theorem family_view_tracked_properties (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    (familySource ps).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
      (familyViewKeys ps i view) = some (familyViewTracked ps i view) ∧
    (familyViewTracked ps i view).highestFirst = familyPrioritySlots ps i ∧
    (familyViewTracked ps i view).pseudoComparisons = 0 ∧
    (familySource ps).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      (familyViewKeys ps i view) (familyViewTracked ps i view).highestFirst = true :=
  Classical.choose_spec (family_view_safe_tracked_order ps i view)

theorem family_view_written_descriptor (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    writtenFramePriorityDescriptor (ps.get i) (familySlots ps i)
      (familyViewTracked ps i view).highestFirst = descriptorOfParity (ps.get i) false := by
  have odd : permutationIsEven [2, 0, 3, 1] = false := by decide +kernel
  rw [(family_view_tracked_properties ps i view).2.1]
  unfold writtenFramePriorityDescriptor
  rw [family_aligned_role_positions, odd]

noncomputable def familyViewEvidence (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    ParserRichPriorityEvidence (familySource ps) 1 :=
  { slots := familySlots ps i
    keys := familyViewKeys ps i view
    tracked := familyViewTracked ps i view
    writtenParity := ps.get i
    raw := writtenFramePriorityDescriptor (ps.get i) (familySlots ps i)
      (familyViewTracked ps i view).highestFirst }

/-- Actual rich source priority evidence consumes the real center annotation, returned roots,
finite matcher, actual production keys and actual coherent tracked sorter. -/
theorem family_view_evidence_computed (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    constitutionParserRichPriorityEvidence? (familyRaw ps) (familySource ps)
      (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) view 4 =
        some (familyViewEvidence ps i view) := by
  have observed : (familyRaw ps).atomAt? (familyCenter ps i).1.val =
      some (roleAtom (ps.get i) (roleOfOffset 5)) := by
    rw [family_center_index]
    exact familyRaw_role_atom ps i 5 (by decide)
  have parity : (roleAtom (ps.get i) (roleOfOffset 5)).tetrahedral? = some (ps.get i) := rfl
  have aligned : findSlotAlignment? ((familyRaw ps).writtenNeighbors (familyCenter ps i).1.val)
      (occurrenceRootIDs (familySource ps) (familyFrame ps i 1).roots) = some (familySlots ps i) :=
    family_slots_computed ps i
  simp only [constitutionParserRichPriorityEvidence?, occurrenceTetrahedralCenter?_final,
    Bind.bind, Option.bind, parserIndexViaConversion_val, rawWrittenLigandFrame, observed, parity,
    family_returned_frame, aligned, family_view_keys_computed,
    (family_view_tracked_properties ps i view).1, familyViewEvidence]

/-- Actual production rich descriptor emission for every dependency view. Repeated-carbon
ranking, all slot alignment, input parity and ordinary classification are derived internally. -/
theorem family_view_descriptor_computed (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    constitutionParserRichDescriptor? (familyRaw ps) (familySource ps)
      (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) view 4 =
        some (.chiral (descriptorOfParity (ps.get i) false)) := by
  unfold constitutionParserRichDescriptor?
  rw [family_view_evidence_computed]
  change some (classifyTetrahedralRSPseudo
    (writtenFramePriorityDescriptor (ps.get i) (familySlots ps i)
      (familyViewTracked ps i view).highestFirst)
    (familyViewTracked ps i view).pseudoComparisons) = _
  rw [family_view_written_descriptor, (family_view_tracked_properties ps i view).2.2.1]
  rfl

/-- The internally constructed actual scheduled model assigns the same parity-derived chiral
label. Final inputs are only ps and its valid tag index; no model-output hypothesis. -/
theorem family_scheduled_descriptor (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    familyScheduledState ps ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) =
      some (.chiral (descriptorOfParity (ps.get i) false)) := by
  rw [← family_scheduled_evaluation]
  exact family_view_descriptor_computed ps i (familyScheduledView ps i)

/-- Independent accepted rich descriptor meaning at the actual scheduled view, with physical
record/parser parity, production keys, tracked order and descriptor emission all internal. -/
theorem family_scheduled_descriptor_meaning (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ConstitutionParserRichDescriptorMeaning (familyRaw ps) (familySource ps)
      (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))
      (familyScheduledView ps i) 4 (.chiral (descriptorOfParity (ps.get i) false)) :=
  constitutionParserRichDescriptor?_sound (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps)
    ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))
    (familyScheduledView ps i) 4 (.chiral (descriptorOfParity (ps.get i) false))
    (family_view_descriptor_computed ps i (familyScheduledView ps i))

end TetraStereo.UniversalProof.SecondSphereScheduledSourceView
