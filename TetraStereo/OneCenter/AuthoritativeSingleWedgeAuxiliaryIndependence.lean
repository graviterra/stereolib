import TetraStereo.OneCenter.AuthoritativeSingleWedgeDescriptorConstruction

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

open CertifiedLocalizedCIPInput

/-!
# Auxiliary-view independence for strictly atomic-separated source drawings

Actual production key fields can depend on the auxiliary view. Their off-diagonal comparison
callbacks nevertheless agree when distinct source-neighbour atomic numbers decide priorities.
The production sorter never compares a slot with itself, so it yields the same complete tracked
history. The alignment and drawing-point lookup are source-only, and the final descriptor agrees.

Carrier zero needs only the local source drawing and independent first-shell atomic separation.
At arbitrary carrier fuel the existing whole-source no-double restriction remains explicit.
No auxiliary view is assumed to be a CIP fixed point or model; this theorem establishes evaluator
independence in the stated strict domain, not model correctness or scientific source approval.
-/

/-- Actual raw tracked sorts agree although the compiled key fields may differ. -/
theorem production_raw_tracked_order_eq_of_auxiliary_views
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (viewA viewB : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (keysA keysB : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computedA : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) viewA ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keysA)
    (computedB : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) viewB ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keysB) :
    source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysA =
      source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysB := by
  have callbacks : ∀ left right, left ≠ right →
      source.compareAromaticCanonicalOccurrenceRule3Through5At? keysA left right =
        source.compareAromaticCanonicalOccurrenceRule3Through5At? keysB left right := by
    intro left right different
    exact (production_callback_eq_strictRank_of_ne source carrierFuel ruleFuel center viewA
      drawing bound separated keysA computedA left right different).trans
      (production_callback_eq_strictRank_of_ne source carrierFuel ruleFuel center viewB
        drawing bound separated keysB computedB left right different).symm
  simpa only [aromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
    sortFourLocalizedLigandsTracked, sortLocalizedLigandsTracked] using
    sortLocalizedLigandsTrackedFrom_eq_of_callback_ne
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keysA)
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keysB)
      callbacks (List.finRange 4) [] 0 (List.nodup_finRange 4)

/-- Both actual safe sorters construct one identical tracked history, with zero pseudo count.
The successful key equations are intermediate premises; source-domain results below derive them. -/
theorem exists_common_production_safe_order_of_auxiliary_views
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (viewA viewB : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (keysA keysB : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computedA : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) viewA ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keysA)
    (computedB : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) viewB ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keysB) :
    ∃ tracked,
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysA = some tracked ∧
        source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysB = some tracked ∧
        tracked.highestFirst.Perm (List.finRange 4) ∧ tracked.pseudoComparisons = 0 := by
  obtain ⟨tracked, rawA, perm, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
      (productionAtomicPriority source carrierFuel center drawing bound)
      (productionAtomicPriority_injective_of_source_separation
        source carrierFuel center drawing bound separated)
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keysA)
      (production_callback_eq_strictRank_of_ne source carrierFuel ruleFuel center viewA
        drawing bound separated keysA computedA)
  have rawA' : source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysA = some tracked :=
    rawA
  have rawB : source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysB = some tracked :=
    (production_raw_tracked_order_eq_of_auxiliary_views source carrierFuel ruleFuel center
      viewA viewB drawing bound separated keysA keysB computedA computedB).symm.trans rawA'
  have coherentA : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keysA tracked.highestFirst = true :=
    (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
      keysA tracked.highestFirst).mpr (descending.imp (by
        intro left right higher
        rw [production_comparison_gt_of_atomic_priority source carrierFuel ruleFuel center
          viewA drawing bound keysA computedA left right higher]))
  have coherentB : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keysB tracked.highestFirst = true :=
    (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
      keysB tracked.highestFirst).mpr (descending.imp (by
        intro left right higher
        rw [production_comparison_gt_of_atomic_priority source carrierFuel ruleFuel center
          viewB drawing bound keysB computedB left right higher]))
  refine ⟨tracked, ?_, ?_, perm, zero⟩
  · simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawA', coherentA]
  · simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawB, coherentB]

theorem production_safe_order_eq_of_auxiliary_views
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (viewA viewB : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (keysA keysB : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computedA : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) viewA ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keysA)
    (computedB : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) viewB ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keysB) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysA =
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysB := by
  obtain ⟨tracked, safeA, safeB, _perm, _zero⟩ :=
    exists_common_production_safe_order_of_auxiliary_views source carrierFuel ruleFuel center
      viewA viewB drawing bound separated keysA keysB computedA computedB
  exact safeA.trans safeB.symm

/-- Descriptor equality follows from the actual common safe order. Alignment and point lookup
are executed identically; equality of the key records themselves is neither assumed nor needed. -/
theorem ordinaryDescriptor?_eq_of_atomic_production_keyFrames
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (viewA viewB : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (keysA keysB : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computedA : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) viewA ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keysA)
    (computedB : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) viewB ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keysB) :
    ordinaryDescriptor? source carrierFuel center viewA ruleFuel =
      ordinaryDescriptor? source carrierFuel center viewB ruleFuel := by
  have safeEqual := production_safe_order_eq_of_auxiliary_views source carrierFuel ruleFuel center
    viewA viewB drawing bound separated keysA keysB computedA computedB
  cases aligned : occurrenceAlignment? source carrierFuel center with
  | none => simp [ordinaryDescriptor?, ordinaryPriorityEvidence?, aligned]
  | some actual =>
      cases trackedComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keysA with
      | none =>
          simp [ordinaryDescriptor?, ordinaryPriorityEvidence?, aligned,
            computedA, computedB, ← safeEqual, trackedComputed]
      | some tracked =>
          cases pointsComputed : tracked.highestFirst.mapM
              (drawingPointForOccurrenceSlot? actual.1 actual.2) with
          | none =>
              simp [ordinaryDescriptor?, ordinaryPriorityEvidence?, aligned,
                computedA, computedB, ← safeEqual, trackedComputed, pointsComputed]
          | some points =>
              simp [ordinaryDescriptor?, ordinaryPriorityEvidence?, aligned,
                computedA, computedB, ← safeEqual, trackedComputed, pointsComputed]

/-- Source-only auxiliary independence at carrier zero/rule two. All intermediate production
keys and the common sorting history are derived, with no global no-double or model hypothesis. -/
theorem ordinaryDescriptor?_auxiliary_independent_zero_carrier
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalTetrahedralCenter)
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (viewA viewB : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ordinaryDescriptor? source 0 center viewA 2 = ordinaryDescriptor? source 0 center viewB 2 := by
  obtain ⟨keysA, computedA⟩ := exists_zero_carrier_production_keyFrame_of_sourceFrame
    source center viewA drawing bound
  obtain ⟨keysB, computedB⟩ := exists_zero_carrier_production_keyFrame_of_sourceFrame
    source center viewB drawing bound
  exact ordinaryDescriptor?_eq_of_atomic_production_keyFrames source 0 2 center viewA viewB
    drawing bound separated keysA keysB computedA computedB

/-- The analogous arbitrary-carrier theorem retains the independent whole-source no-double
restriction used by its key-frame readiness proof. -/
theorem ordinaryDescriptor?_auxiliary_independent_of_noDouble
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (viewA viewB : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ordinaryDescriptor? source carrierFuel center viewA (2 * (carrierFuel + 1)) =
      ordinaryDescriptor? source carrierFuel center viewB (2 * (carrierFuel + 1)) := by
  obtain ⟨keysA, computedA⟩ := exists_production_keyFrame_of_sourceFrame_noDouble
    source carrierFuel center viewA drawing bound noDouble
  obtain ⟨keysB, computedB⟩ := exists_production_keyFrame_of_sourceFrame_noDouble
    source carrierFuel center viewB drawing bound noDouble
  exact ordinaryDescriptor?_eq_of_atomic_production_keyFrames source carrierFuel
    (2 * (carrierFuel + 1)) center viewA viewB drawing bound separated keysA keysB computedA computedB

theorem ordinaryDescriptor?_eq_empty_auxiliary_zero_carrier
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalTetrahedralCenter)
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ordinaryDescriptor? source 0 center view 2 = ordinaryEmptyAuxiliaryDescriptor? source 0 2 center :=
  ordinaryDescriptor?_auxiliary_independent_zero_carrier source center drawing bound separated view
    (source.aromaticCanonicalDependencyView (fun _ => none)
      (source.aromaticCanonicalFinalOccurrence 0 center))

theorem ordinaryDescriptor?_eq_empty_auxiliary_of_noDouble
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ordinaryDescriptor? source carrierFuel center view (2 * (carrierFuel + 1)) =
      ordinaryEmptyAuxiliaryDescriptor? source carrierFuel (2 * (carrierFuel + 1)) center :=
  ordinaryDescriptor?_auxiliary_independent_of_noDouble source carrierFuel center drawing bound
    noDouble separated view
    (source.aromaticCanonicalDependencyView (fun _ => none)
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))

/-- Independence is nonvacuous: one shared uppercase descriptor is constructed for every view. -/
theorem exists_zero_carrier_auxiliary_independent_chiral_descriptor
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalTetrahedralCenter)
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing) :
    ∃ raw, ∀ view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center),
      ordinaryDescriptor? source 0 center view 2 = some (.chiral raw) := by
  obtain ⟨raw, computed⟩ := ordinaryDescriptor?_chiral_exists_of_zero_carrier_source_atomic_separation
    source center
    (source.aromaticCanonicalDependencyView (fun _ => none)
      (source.aromaticCanonicalFinalOccurrence 0 center)) drawing bound separated
  refine ⟨raw, ?_⟩
  intro view
  rw [ordinaryDescriptor?_eq_empty_auxiliary_zero_carrier source center drawing bound separated view]
  exact computed

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeAuxiliaryIndependenceRegression

open AuthoritativeChemicalInput AuthoritativeChemicalInput.SingleWedgeSource
open SingleWedgeOccurrenceAlignmentRegression SingleWedgeAtomicPriorityBridgeRegression

theorem cfclbri_any_auxiliary_view_agrees_empty
    (view : SingleWedgeSourceRegression.source.AromaticCanonicalDependencyView
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter)) :
    ordinaryDescriptor? SingleWedgeSourceRegression.source 0 cfclbriProductionCenter view 2 =
      ordinaryEmptyAuxiliaryDescriptor? SingleWedgeSourceRegression.source 0 2 cfclbriProductionCenter := by
  obtain ⟨aligned, alignedComputed⟩ := cfclbri_constructed_center_alignment 0
  have bound := (occurrenceAlignment?_sound SingleWedgeSourceRegression.source 0
    cfclbriProductionCenter aligned.1 aligned.2 alignedComputed).1
  exact ordinaryDescriptor?_eq_empty_auxiliary_zero_carrier SingleWedgeSourceRegression.source
    cfclbriProductionCenter aligned.1 bound (cfclbri_source_endpoint_atomic_separation aligned.1) view

theorem cfclbri_one_chiral_descriptor_for_every_auxiliary_view :
    ∃ raw, ∀ view : SingleWedgeSourceRegression.source.AromaticCanonicalDependencyView
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter),
      ordinaryDescriptor? SingleWedgeSourceRegression.source 0 cfclbriProductionCenter view 2 =
        some (.chiral raw) := by
  obtain ⟨raw, computed⟩ :=
    SingleWedgeDescriptorConstructionRegression.cfclbri_actual_production_descriptor_exists
  refine ⟨raw, ?_⟩
  intro view
  rw [cfclbri_any_auxiliary_view_agrees_empty view]
  exact computed

/-- A deliberately different all-R state is another evaluator input. This regression makes no
claim that that state, or the empty state, satisfies the global CIP model relation. -/
theorem cfclbri_constant_R_auxiliary_input_agrees_empty :
    ordinaryDescriptor? SingleWedgeSourceRegression.source 0 cfclbriProductionCenter
      (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView
        (fun _ => some (.chiral .R))
        (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter)) 2 =
      ordinaryEmptyAuxiliaryDescriptor? SingleWedgeSourceRegression.source 0 2 cfclbriProductionCenter :=
  cfclbri_any_auxiliary_view_agrees_empty _

end SingleWedgeAuxiliaryIndependenceRegression
end TetraStereo.OneCenter
