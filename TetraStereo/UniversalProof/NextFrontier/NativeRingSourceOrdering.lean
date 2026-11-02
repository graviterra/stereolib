import TetraStereo.UniversalProof.NextFrontier.NativeRingSourceProjection
import TetraStereo.Certificate.ConstitutionalSource

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingSourceOrdering

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.Certificate.Constitutional
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingSourceInput
open TetraStereo.UniversalProof.NativeRingSourceGeometry
open TetraStereo.UniversalProof.NativeRingSourceProjection
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

theorem actual_role_priority (n : Nat) (parity : TetrahedralInputParity)
    (atom : Nat) (member : atom ∈ [n + 5, 1, 2, n + 4]) :
    occurrenceAtomicPriority (ringSource n parity) (ringFrame n parity 1)
      (ringRoleSlot n parity 1 atom member) = (expanded n parity).atomZAt atom := by
  change occurrenceAtomicPriority (ringSource n parity)
    (actualFrame (expanded n parity) (ringSource n parity) (ring_annotation_agreement n parity).1
      1 (ringCenter n parity) (ringRecordDomain n parity 0) (ring_four_records n parity)) _ = _
  rw [actual_priority_eq_raw_Z]
  exact congrArg (expanded n parity).atomZAt (ring_role_slot_index n parity 1 atom member)

theorem actual_unequal_callback (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)))
    (left right leftZ rightZ : Nat) (leftMember : left ∈ [n + 5, 1, 2, n + 4])
    (rightMember : right ∈ [n + 5, 1, 2, n + 4])
    (observedLeft : (expanded n parity).atomZAt left = leftZ)
    (observedRight : (expanded n parity).atomZAt right = rightZ) (different : leftZ ≠ rightZ) :
    (ringSource n parity).compareAromaticCanonicalOccurrenceRule3Through5At? (ringViewKeys n parity 1 view)
      (ringRoleSlot n parity 1 left leftMember) (ringRoleSlot n parity 1 right rightMember) =
        some { ordering := compare leftZ rightZ, decisiveRule? := none, pseudo := false } := by
  exact source_atomic_callback (ringSource n parity) _ view 4 (ringFrame n parity 1)
    (ring_roots_real n parity 1) (ringViewKeys n parity 1 view) (ring_view_keys_computed n parity 1 view) _ _ leftZ rightZ
    ((actual_role_priority n parity left leftMember).trans observedLeft)
    ((actual_role_priority n parity right rightMember).trans observedRight) different


theorem role_slots_ne (n : Nat) (parity : TetrahedralInputParity)
    (left right : Nat) (leftMember : left ∈ [n + 5, 1, 2, n + 4])
    (rightMember : right ∈ [n + 5, 1, 2, n + 4]) (different : left ≠ right) :
    ringRoleSlot n parity 1 left leftMember ≠ ringRoleSlot n parity 1 right rightMember := by
  intro equal
  have indices := congrArg (ringSlotID n parity 1) equal
  rw [ring_role_slot_index, ring_role_slot_index] at indices
  exact different indices

theorem role_slots_nodup (n : Nat) (parity : TetrahedralInputParity) :
    [ringRoleSlot n parity 1 1 (by simp), ringRoleSlot n parity 1 2 (by simp),
      ringRoleSlot n parity 1 (n + 4) (by simp), ringRoleSlot n parity 1 (n + 5) (by simp)].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true]
  repeat' constructor
  all_goals exact role_slots_ne n parity _ _ (by simp) (by simp) (by omega)

noncomputable def roleSlots (n : Nat) (parity : TetrahedralInputParity) : Four (Fin 4) :=
  ⟨ringRoleSlot n parity 1 1 (by simp), ringRoleSlot n parity 1 2 (by simp),
    ringRoleSlot n parity 1 (n + 4) (by simp), ringRoleSlot n parity 1 (n + 5) (by simp)⟩

theorem role_slots_cover (n : Nat) (parity : TetrahedralInputParity) (slot : Fin 4) :
    slot = ringRoleSlot n parity 1 1 (by simp) ∨ slot = ringRoleSlot n parity 1 2 (by simp) ∨
    slot = ringRoleSlot n parity 1 (n + 4) (by simp) ∨ slot = ringRoleSlot n parity 1 (n + 5) (by simp) :=
  four_distinct_cover _ _ _ _ (role_slots_nodup n parity) slot

noncomputable def priorityRank (n : Nat) (parity : TetrahedralInputParity) (slot : Fin 4) : Nat :=
  if slot = ringRoleSlot n parity 1 1 (by simp) then 4
  else if slot = ringRoleSlot n parity 1 2 (by simp) then 3
  else if slot = ringRoleSlot n parity 1 (n + 4) (by simp) then 2 else 1

theorem priority_rank_roles (n : Nat) (parity : TetrahedralInputParity) :
    priorityRank n parity (ringRoleSlot n parity 1 1 (by simp)) = 4 ∧
    priorityRank n parity (ringRoleSlot n parity 1 2 (by simp)) = 3 ∧
    priorityRank n parity (ringRoleSlot n parity 1 (n + 4) (by simp)) = 2 ∧
    priorityRank n parity (ringRoleSlot n parity 1 (n + 5) (by simp)) = 1 :=
  slot_rank_roles (roleSlots n parity) (role_slots_nodup n parity)

theorem priority_rank_injective (n : Nat) (parity : TetrahedralInputParity) :
    Function.Injective (priorityRank n parity) :=
  slot_rank_injective (roleSlots n parity) (role_slots_nodup n parity)

/-- Real source observations, including every immediate child and its multiplicity.
The checker consumes these independently proved projections for every length and parity. -/
theorem source_prefix_realization (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    SourcePrefixRealization (ringSource n parity) (ringFrame n parity 1) (ringViewKeys n parity 1 view)
      (roleSlots n parity) ringObservations := by
  have fZ := expanded_fluorine_z n parity
  have lZ := expanded_left_z n parity
  have rZ := expanded_chain_z n parity n (by omega)
  have hZ := expanded_hydrogen_z n parity (n + 5) (by omega) (by omega)
  have children := actual_child_observations n parity
  have projections := actual_projections n parity view
  refine source_realization_two_spheres (ringSource n parity) (ringFrame n parity 1) (ringViewKeys n parity 1 view)
    (roleSlots n parity) 9 6 6 1 _ _
    ((actual_role_priority n parity 1 (by simp)).trans fZ)
    ((actual_role_priority n parity 2 (by simp)).trans lZ)
    ((actual_role_priority n parity (n + 4) (by simp)).trans rZ)
    ((actual_role_priority n parity (n + 5) (by simp)).trans hZ)
    children.1 children.2 ?_ ?_
  · simpa [roleSlots, rootLayer, childLayer, childLayerFrom,
      TetraStereo.UniversalProof.NativeRingSourceSparseOrdering.carbonRootLayer,
      TetraStereo.UniversalProof.NativeRingSourceSparseOrdering.chlorinatedArmLayer] using projections.1
  · simpa [roleSlots, rootLayer, childLayer, childLayerFrom,
      TetraStereo.UniversalProof.NativeRingSourceSparseOrdering.carbonRootLayer,
      TetraStereo.UniversalProof.NativeRingSourceSparseOrdering.saturatedArmLayer] using projections.2


theorem actual_callback_strictRank (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)))
    (left right : Fin 4) (different : left ≠ right) :
    (ringSource n parity).compareAromaticCanonicalOccurrenceRule3Through5At? (ringViewKeys n parity 1 view)
      left right = strictRankComparison (priorityRank n parity) left right := by
  exact checked_source_callback (ringSource n parity) _ view 4 (ringFrame n parity 1)
    (ring_roots_real n parity 1) (ringViewKeys n parity 1 view) (ring_view_keys_computed n parity 1 view)
    (roleSlots n parity) (role_slots_nodup n parity) ringObservations
    (source_prefix_realization n parity view) ring_checked left right different

noncomputable def prioritySlots (n : Nat) (parity : TetrahedralInputParity) : List (Fin 4) :=
  [ringRoleSlot n parity 1 1 (by simp), ringRoleSlot n parity 1 2 (by simp),
    ringRoleSlot n parity 1 (n + 4) (by simp), ringRoleSlot n parity 1 (n + 5) (by simp)]

theorem priority_slots_perm (n : Nat) (parity : TetrahedralInputParity) :
    (prioritySlots n parity).Perm (List.finRange 4) :=
  (roleSlots n parity).perm_finRange (role_slots_nodup n parity)

theorem priority_slots_descending (n : Nat) (parity : TetrahedralInputParity) :
    (prioritySlots n parity).Pairwise (fun left right => priorityRank n parity right < priorityRank n parity left) :=
  slots_descending (roleSlots n parity) (role_slots_nodup n parity)

/-- The actual source safe sorter succeeds coherently for every dependency view. -/
theorem actual_safe_tracked_order (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    ∃ tracked,
      (ringSource n parity).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
        (ringViewKeys n parity 1 view) = some tracked ∧
      tracked.highestFirst = prioritySlots n parity ∧ tracked.pseudoComparisons = 0 ∧
      (ringSource n parity).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
        (ringViewKeys n parity 1 view) tracked.highestFirst = true := by
  exact checked_source_safe_order (ringSource n parity) _ view 4 (ringFrame n parity 1)
    (ring_roots_real n parity 1) (ringViewKeys n parity 1 view) (ring_view_keys_computed n parity 1 view)
    (roleSlots n parity) (role_slots_nodup n parity) ringObservations
    (source_prefix_realization n parity view) ring_checked

noncomputable def viewTracked (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    TrackedLocalizedLigandOrder := Classical.choose (actual_safe_tracked_order n parity view)

theorem view_tracked_properties (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    (ringSource n parity).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
      (ringViewKeys n parity 1 view) = some (viewTracked n parity view) ∧
    (viewTracked n parity view).highestFirst = prioritySlots n parity ∧
    (viewTracked n parity view).pseudoComparisons = 0 ∧
    (ringSource n parity).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      (ringViewKeys n parity 1 view) (viewTracked n parity view).highestFirst = true :=
  Classical.choose_spec (actual_safe_tracked_order n parity view)

end TetraStereo.UniversalProof.NativeRingSourceOrdering
