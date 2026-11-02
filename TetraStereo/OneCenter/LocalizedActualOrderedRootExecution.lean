import TetraStereo.OneCenter.LocalizedRerootCompoundOrderedBuilder
import TetraStereo.OneCenter.LocalizedPhysicalRootDescriptorExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000






























namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
  (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target)
  (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
  (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)

/-- The ordered slot keys of a family of production keys. -/
def orderedKeys : Fin 4 → input.LocalizedRerootCompoundRule45Key :=
  fun index => input.outcomeOrdered45 (keys index)

/-- Four production builds at the frame slots. -/
def SlotKeysBuilt : Prop :=
  ∀ index : Fin 4,
    input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
      some (keys index)

variable {input target view frame keys}

/-- **The ordered callback is the compound callback of the ordered keys.** -/
theorem compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_compoundActualCompareAt
    (built : SlotKeysBuilt input target view frame keys) :
    input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame =
      compoundActualCompareAt input (orderedKeys input keys) := by
  funext i j
  rw [input.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built target view frame (built i)
    (built j)]
  rfl

/-- A rank-descending pair of ordered keys is an ordered comparison with ordering `gt`. -/
theorem compareOrderedAt?_exists_ordering_gt_of_rank_lt
    (built : SlotKeysBuilt input target view frame keys)
    (separated : input.CompoundKeyOffDiagonalStrict (orderedKeys input keys))
    {left right : Fin 4}
    (higher : input.compoundKeyRank (orderedKeys input keys) right <
      input.compoundKeyRank (orderedKeys input keys) left) :
    ∃ result,
      input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame left right =
        some result ∧ result.ordering = Ordering.gt := by
  have comparisonEq : input.compareLocalizedRerootCompoundRule45Keys
      (orderedKeys input keys left) (orderedKeys input keys right) =
        compare (input.compoundKeyRank (orderedKeys input keys) left)
          (input.compoundKeyRank (orderedKeys input keys) right) := by
    have h := input.compoundKeyComparison_eq_compare_rank (orderedKeys input keys) separated
      left right
    simpa [compoundKeyComparison, Ordering.byKey] using h
  refine ⟨_, input.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built target view frame
    (built left) (built right), ?_⟩
  show (input.compareLocalizedRerootCompoundThroughRule5 (orderedKeys input keys left)
    (orderedKeys input keys right)).ordering = Ordering.gt
  rw [input.compareLocalizedRerootCompoundThroughRule5_ordering, comparisonEq]
  exact compare_gt_iff_gt.mpr higher

/-- Derived all-pairs coherence of a rank-sorted ordered result. -/
theorem orderCoherentOrdered_eq_true_of_sortedByRank
    (built : SlotKeysBuilt input target view frame keys)
    (separated : input.CompoundKeyOffDiagonalStrict (orderedKeys input keys))
    (tracked : TrackedLocalizedLigandOrder)
    (sorted : SortedByRank (input.compoundKeyRank (orderedKeys input keys))
      tracked.highestFirst.reverse) :
    orderCoherentOf (input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame)
      tracked.highestFirst = true := by
  rw [orderCoherentOf_eq_true_iff]
  exact List.Pairwise.imp
    (fun higher => compareOrderedAt?_exists_ordering_gt_of_rank_lt built separated higher)
    (List.pairwise_reverse.mp sorted)

/-- **The ordered safe order.**  Under the three data-core conditions on the ordered keys, the
ordered safe order succeeds with a permutation of the four slots descending in the computed rank
of the ordered keys and with exactly the number of distinct ordered-prior-tied pairs as its pseudo
count. -/
theorem exists_safeTrackedOrderOrdered_of_data
    (built : SlotKeysBuilt input target view frame keys)
    (separated : input.CompoundKeyOffDiagonalStrict (orderedKeys input keys))
    (maxTwo : input.PriorTieClassAtMostTwo (orderedKeys input keys))
    (mirror : input.PriorTieMirrorReadings (orderedKeys input keys)) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.safeLocalizedOccurrenceRule45TrackedOrderOrdered? target view frame = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      SortedByRank (input.compoundKeyRank (orderedKeys input keys))
        tracked.highestFirst.reverse ∧
      tracked.pseudoComparisons =
        sourceEnantiomorphicPairCount (compoundPriorTieRelation input (orderedKeys input keys)) := by
  obtain ⟨result, computed, permutation, sorted, pseudo⟩ :=
    sortFourLocalizedLigandsTracked_actualCompound_sourcePairFidelity input
      (orderedKeys input keys) separated maxTwo mirror
  refine ⟨result, ?_, by simpa using permutation, sorted, pseudo⟩
  have hsort : sortFourLocalizedLigandsTracked
      (input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame) = some result := by
    rw [compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_compoundActualCompareAt built]
    exact computed
  unfold safeLocalizedOccurrenceRule45TrackedOrderOrdered? safeTrackedOrderOf
  rw [hsort]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (orderCoherentOrdered_eq_true_of_sortedByRank built separated result sorted)]

/-- Cursor-level spatial reads along any slot list. -/
theorem mapM_spatialPoint_eq_some (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index)) :
    ∀ order : List (Fin 4),
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint? (frame.cursorAt index)) =
        some (order.map pointsAt)
  | [] => rfl
  | index :: order => by
      simp [List.mapM_cons, spatial index, mapM_spatialPoint_eq_some pointsAt spatial order]

/-- **Ordered descriptor execution.**  With built slot keys whose ordered keys satisfy the three
data-core conditions, a real centre at the target and nondegenerate coordinates at the frame
slots, the ordered descriptor is the pseudo-aware classification of the oriented-volume reading of
the slot coordinates in the sorted order, with the exact number of distinct ordered-prior-tied
pairs as its count. -/
theorem localizedOccurrenceRule45DescriptorOrdered?_eq_classify_of_actualGeometry
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (built : SlotKeysBuilt input target view frame keys)
    (separated : input.CompoundKeyOffDiagonalStrict (orderedKeys input keys))
    (maxTwo : input.PriorTieClassAtMostTwo (orderedKeys input keys))
    (mirror : input.PriorTieMirrorReadings (orderedKeys input keys))
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS),
      input.safeLocalizedOccurrenceRule45TrackedOrderOrdered? target view frame = some tracked ∧
      input.localizedOccurrenceRule45DescriptorOrdered? target view =
        some (classifyTetrahedralRSPseudo normalizedRS
          (sourceEnantiomorphicPairCount
            (compoundPriorTieRelation input (orderedKeys input keys)))) ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      SortedByRank (input.compoundKeyRank (orderedKeys input keys))
        tracked.highestFirst.reverse ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS := by
  obtain ⟨tracked, safeComputed, perm, sorted, pseudo⟩ :=
    exists_safeTrackedOrderOrdered_of_data built separated maxTwo mirror
  obtain ⟨normalizedRS, rational⟩ :=
    rationalTetrahedralDescriptor_exists_of_permutation pointsAt tracked.highestFirst perm nonzero
  refine ⟨tracked, normalizedRS, safeComputed, ?_, perm, sorted, rational⟩
  have hcenter : input.localizedOccurrenceDescriptorCenter? target = some center :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).2 centerReal
  unfold localizedOccurrenceRule45DescriptorOrdered? localizedOccurrenceRule45SpatialEvidenceOrdered?
  rw [hcenter]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [frameComputed]
  simp only [Option.bind_some]
  rw [safeComputed]
  simp only [Option.bind_some]
  rw [mapM_spatialPoint_eq_some pointsAt spatial]
  simp only [Option.bind_some]
  rw [(descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).2 rational]
  simp only [Option.bind_some, pseudo]

/-- **Lowercase equivalence.**  The executed ordered classification is lowercase exactly when the
number of distinct ordered-prior-tied pairs is one. -/
theorem localizedOccurrenceRule45DescriptorOrdered?_isLowercase_iff
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (built : SlotKeysBuilt input target view frame keys)
    (separated : input.CompoundKeyOffDiagonalStrict (orderedKeys input keys))
    (maxTwo : input.PriorTieClassAtMostTwo (orderedKeys input keys))
    (mirror : input.PriorTieMirrorReadings (orderedKeys input keys))
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      input.localizedOccurrenceRule45DescriptorOrdered? target view = some descriptor ∧
      (descriptor.IsLowercase ↔
        sourceEnantiomorphicPairCount
          (compoundPriorTieRelation input (orderedKeys input keys)) = 1) := by
  obtain ⟨_, normalizedRS, _, descriptorEq, _, _, _⟩ :=
    localizedOccurrenceRule45DescriptorOrdered?_eq_classify_of_actualGeometry frameComputed built
      separated maxTwo mirror center centerReal pointsAt spatial nonzero
  exact ⟨_, descriptorEq, isLowercase_classify_iff normalizedRS _⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_compoundActualCompareAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_safeTrackedOrderOrdered_of_data
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorOrdered?_eq_classify_of_actualGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorOrdered?_isLowercase_iff
