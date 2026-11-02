import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceProjection
import TetraStereo.Certificate.ConstitutionalSource

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceOrdering

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.Certificate.Constitutional
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceProjection
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

theorem actual_role_priority (n : Nat) (parity : TetrahedralInputParity)
    (atom : Nat) (member : atom ∈ [n + 7, 1, 2, 4]) :
    occurrenceAtomicPriority (nitrileSource parity n) (nitrileFrame parity n 1)
      (nitrileRoleSlot parity n 1 atom member) = (expanded parity n).atomZAt atom := by
  change occurrenceAtomicPriority (nitrileSource parity n)
    (actualFrame (expanded parity n) (nitrileSource parity n) (expanded_source_annotation_agreement parity n).1
      1 (nitrileCenter parity n) (nitrileRecordDomain parity n) (nitrile_four_records parity n)) _ = _
  rw [actual_priority_eq_raw_Z]
  exact congrArg (expanded parity n).atomZAt (nitrile_role_slot_index parity n 1 atom member)

theorem actual_unequal_callback (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)))
    (left right leftZ rightZ : Nat) (leftMember : left ∈ [n + 7, 1, 2, 4])
    (rightMember : right ∈ [n + 7, 1, 2, 4])
    (observedLeft : (expanded parity n).atomZAt left = leftZ)
    (observedRight : (expanded parity n).atomZAt right = rightZ) (different : leftZ ≠ rightZ) :
    (nitrileSource parity n).compareAromaticCanonicalOccurrenceRule3Through5At? (nitrileViewKeys parity n 1 view)
      (nitrileRoleSlot parity n 1 left leftMember) (nitrileRoleSlot parity n 1 right rightMember) =
        some { ordering := compare leftZ rightZ, decisiveRule? := none, pseudo := false } := by
  exact source_atomic_callback (nitrileSource parity n) _ view 4 (nitrileFrame parity n 1)
    (nitrile_roots_real parity n 1) (nitrileViewKeys parity n 1 view) (nitrile_view_keys_computed parity n 1 view) _ _ leftZ rightZ
    ((actual_role_priority n parity left leftMember).trans observedLeft)
    ((actual_role_priority n parity right rightMember).trans observedRight) different


theorem role_slots_ne (n : Nat) (parity : TetrahedralInputParity)
    (left right : Nat) (leftMember : left ∈ [n + 7, 1, 2, 4])
    (rightMember : right ∈ [n + 7, 1, 2, 4]) (different : left ≠ right) :
    nitrileRoleSlot parity n 1 left leftMember ≠ nitrileRoleSlot parity n 1 right rightMember := by
  intro equal
  have indices := congrArg (nitrileSlotAtom parity n 1) equal
  rw [nitrile_role_slot_index, nitrile_role_slot_index] at indices
  exact different indices

theorem role_slots_nodup (n : Nat) (parity : TetrahedralInputParity) :
    [nitrileRoleSlot parity n 1 1 (by simp), nitrileRoleSlot parity n 1 2 (by simp),
      nitrileRoleSlot parity n 1 (4) (by simp), nitrileRoleSlot parity n 1 (n + 7) (by simp)].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true]
  repeat' constructor
  all_goals exact role_slots_ne n parity _ _ (by simp) (by simp) (by omega)

noncomputable def roleSlots (n : Nat) (parity : TetrahedralInputParity) : Four (Fin 4) :=
  ⟨nitrileRoleSlot parity n 1 1 (by simp), nitrileRoleSlot parity n 1 2 (by simp),
    nitrileRoleSlot parity n 1 4 (by simp), nitrileRoleSlot parity n 1 (n + 7) (by simp)⟩

theorem role_slots_cover (n : Nat) (parity : TetrahedralInputParity) (slot : Fin 4) :
    slot = nitrileRoleSlot parity n 1 1 (by simp) ∨ slot = nitrileRoleSlot parity n 1 2 (by simp) ∨
    slot = nitrileRoleSlot parity n 1 (4) (by simp) ∨ slot = nitrileRoleSlot parity n 1 (n + 7) (by simp) :=
  four_distinct_cover _ _ _ _ (role_slots_nodup n parity) slot

noncomputable def priorityRank (n : Nat) (parity : TetrahedralInputParity) (slot : Fin 4) : Nat :=
  if slot = nitrileRoleSlot parity n 1 1 (by simp) then 4
  else if slot = nitrileRoleSlot parity n 1 2 (by simp) then 3
  else if slot = nitrileRoleSlot parity n 1 4 (by simp) then 2 else 1

theorem priority_rank_roles (n : Nat) (parity : TetrahedralInputParity) :
    priorityRank n parity (nitrileRoleSlot parity n 1 1 (by simp)) = 4 ∧
    priorityRank n parity (nitrileRoleSlot parity n 1 2 (by simp)) = 3 ∧
    priorityRank n parity (nitrileRoleSlot parity n 1 (4) (by simp)) = 2 ∧
    priorityRank n parity (nitrileRoleSlot parity n 1 (n + 7) (by simp)) = 1 :=
  slot_rank_roles (roleSlots n parity) (role_slots_nodup n parity)

theorem priority_rank_injective (n : Nat) (parity : TetrahedralInputParity) :
    Function.Injective (priorityRank n parity) :=
  slot_rank_injective (roleSlots n parity) (role_slots_nodup n parity)

/-- Real source observations, including every immediate child and its multiplicity.
The checker consumes these independently proved projections for every length and parity. -/
theorem source_prefix_realization (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    SourcePrefixRealization (nitrileSource parity n) (nitrileFrame parity n 1) (nitrileViewKeys parity n 1 view)
      (roleSlots n parity) nitrileObservations := by
  rcases expanded_local_atomic_numbers parity n with ⟨_, fZ, lZ, _, rZ, _, _, hZ, _⟩
  have children := actual_source_child_observations parity n
  have projections := actual_projections n parity view
  refine source_realization_two_spheres (nitrileSource parity n) (nitrileFrame parity n 1) (nitrileViewKeys parity n 1 view)
    (roleSlots n parity) 9 6 6 1 _ _
    ((actual_role_priority n parity 1 (by simp)).trans fZ)
    ((actual_role_priority n parity 2 (by simp)).trans lZ)
    ((actual_role_priority n parity 4 (by simp)).trans rZ)
    ((actual_role_priority n parity (n + 7) (by simp)).trans hZ)
    children.1 children.2 ?_ ?_
  · simpa [roleSlots, rootLayer, childLayer, childLayerFrom,
      TetraStereo.UniversalProof.NextFrontier.NativeNitrileSecondSphereOrder.carbonRootLayer,
      TetraStereo.UniversalProof.NextFrontier.NativeNitrileSecondSphereOrder.nitrileChildLayer] using projections.1
  · simpa [roleSlots, rootLayer, childLayer, childLayerFrom,
      TetraStereo.UniversalProof.NextFrontier.NativeNitrileSecondSphereOrder.carbonRootLayer,
      TetraStereo.UniversalProof.NextFrontier.NativeNitrileSecondSphereOrder.aminoalkylChildLayer] using projections.2


theorem actual_callback_strictRank (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)))
    (left right : Fin 4) (different : left ≠ right) :
    (nitrileSource parity n).compareAromaticCanonicalOccurrenceRule3Through5At? (nitrileViewKeys parity n 1 view)
      left right = strictRankComparison (priorityRank n parity) left right := by
  exact checked_source_callback (nitrileSource parity n) _ view 4 (nitrileFrame parity n 1)
    (nitrile_roots_real parity n 1) (nitrileViewKeys parity n 1 view) (nitrile_view_keys_computed parity n 1 view)
    (roleSlots n parity) (role_slots_nodup n parity) nitrileObservations
    (source_prefix_realization n parity view) nitrile_checked left right different

noncomputable def prioritySlots (n : Nat) (parity : TetrahedralInputParity) : List (Fin 4) :=
  [nitrileRoleSlot parity n 1 1 (by simp), nitrileRoleSlot parity n 1 2 (by simp),
    nitrileRoleSlot parity n 1 4 (by simp), nitrileRoleSlot parity n 1 (n + 7) (by simp)]

theorem priority_slots_perm (n : Nat) (parity : TetrahedralInputParity) :
    (prioritySlots n parity).Perm (List.finRange 4) :=
  (roleSlots n parity).perm_finRange (role_slots_nodup n parity)

theorem priority_slots_descending (n : Nat) (parity : TetrahedralInputParity) :
    (prioritySlots n parity).Pairwise (fun left right => priorityRank n parity right < priorityRank n parity left) :=
  slots_descending (roleSlots n parity) (role_slots_nodup n parity)

/-- The actual source safe sorter succeeds coherently for every dependency view. -/
theorem actual_safe_tracked_order (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    ∃ tracked,
      (nitrileSource parity n).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
        (nitrileViewKeys parity n 1 view) = some tracked ∧
      tracked.highestFirst = prioritySlots n parity ∧ tracked.pseudoComparisons = 0 ∧
      (nitrileSource parity n).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
        (nitrileViewKeys parity n 1 view) tracked.highestFirst = true := by
  exact checked_source_safe_order (nitrileSource parity n) _ view 4 (nitrileFrame parity n 1)
    (nitrile_roots_real parity n 1) (nitrileViewKeys parity n 1 view) (nitrile_view_keys_computed parity n 1 view)
    (roleSlots n parity) (role_slots_nodup n parity) nitrileObservations
    (source_prefix_realization n parity view) nitrile_checked

noncomputable def viewTracked (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    TrackedLocalizedLigandOrder := Classical.choose (actual_safe_tracked_order n parity view)

theorem view_tracked_properties (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    (nitrileSource parity n).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
      (nitrileViewKeys parity n 1 view) = some (viewTracked n parity view) ∧
    (viewTracked n parity view).highestFirst = prioritySlots n parity ∧
    (viewTracked n parity view).pseudoComparisons = 0 ∧
    (nitrileSource parity n).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      (nitrileViewKeys parity n 1 view) (viewTracked n parity view).highestFirst = true :=
  Classical.choose_spec (actual_safe_tracked_order n parity view)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceOrdering
