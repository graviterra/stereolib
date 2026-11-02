import TetraStereo.OneCenter.AuthoritativeSingleWedgePriorityDescriptor
import TetraStereo.OneCenter.AuthoritativeSingleWedgeAtomicPriorityBridge
import TetraStereo.OneCenter.AuthoritativeSingleWedgeZeroCarrierReadiness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

open CertifiedLocalizedCIPInput RationalTetrahedralPermutation Rule6HandednessSemantics

/-!
Successful source alignment and genuine production key/safe-sort executions cannot subsequently
fail at drawing point lookup or tetrahedral geometry. The key and sort execution premises are
explicit intermediate glue obligations. The final source-domain theorem discharges them for
admitted drawings without ordinary double bonds whose endpoints have distinct atomic numbers.
This module does not establish general chemical admission, auxiliary-state correctness, or
scientific source approval.
At carrier zero, the final theorem permits ordinary double bonds elsewhere in the source;
strict first-shell atomic separation makes deeper tied-priority analysis unnecessary here.

Source profile: the upstream corrected calibration is used throughout.  `R` is the negative
affine determinant and `S` the positive one; the Cartesian written parity is
negative volume ↔ `clockwise`, positive volume ↔ `anticlockwise` (IUPAC P-9, standard
right-handed frame `x` right, `y` up, `z` toward the viewer).  The symbolic
`RawMolecule.descriptorOfParity` is unchanged.
-/

theorem sourceFrame_orientedVolume_ne_zero (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (drawing : Frame)
    (bound : SourceFrame source center.val drawing) :
    CartesianPoint3.orientedVolume drawing.first drawing.second drawing.third drawing.fourth ≠ 0 := by
  have nonempty := extracted_frame_parity_not_none source center drawing
    ((extract?_eq_some_iff source center drawing).mpr bound)
  intro zero
  apply nonempty
  exact (tetrahedralInputParityOfFourPoints?_eq_none_iff_zero
    drawing.first drawing.second drawing.third drawing.fourth).mpr zero

theorem drawing_points_lookup (drawing : Frame) (index : Fin 4) :
    drawing.points[index.val]? =
      some (pointVector drawing.first drawing.second drawing.third drawing.fourth index) := by
  fin_cases index <;> rfl

/-- Every matched occurrence slot has an actual drawing point; the lookup is exactly the
point-vector action of the recovered bijection. -/
theorem drawingPointForOccurrenceSlot?_of_permutation (drawing : Frame) (slots : List Nat)
    (permutation : slots.Perm (List.range 4)) (index : Fin 4) :
    drawingPointForOccurrenceSlot? drawing slots index =
      some (pointVector drawing.first drawing.second drawing.third drawing.fourth
        (finFourEquivOfPermutationList slots permutation index)) := by
  let alignment := finFourEquivOfPermutationList slots permutation
  have slotsEq : finFourPermutationList alignment = slots :=
    finFourPermutationList_equivOfPermutationList slots permutation
  have slotLookup : slots[index.val]? = some (alignment index).val := by
    rw [← slotsEq]
    fin_cases index <;> simp [finFourPermutationList]
  have pointLookup : drawing.points[(alignment index).val]? =
      some (pointVector drawing.first drawing.second drawing.third drawing.fourth
        (alignment index)) := by
    exact drawing_points_lookup drawing (alignment index)
  simp [drawingPointForOccurrenceSlot?, slotLookup, pointLookup, alignment]

/-- A genuine four-slot ordering has an explicit permutation representation. -/
theorem finFour_order_representation (order : List (Fin 4))
    (permutation : order.Perm (List.finRange 4)) :
    ∃ ordering : Equiv.Perm (Fin 4),
      order = [ordering 0, ordering 1, ordering 2, ordering 3] := by
  have ranksPerm : (order.map Fin.val).Perm (List.range 4) := by
    simpa only [List.map_coe_finRange_eq_range] using permutation.map Fin.val
  let ordering := finFourEquivOfPermutationList (order.map Fin.val) ranksPerm
  have encoded := finFourPermutationList_equivOfPermutationList (order.map Fin.val) ranksPerm
  refine ⟨ordering, ?_⟩
  apply List.map_injective_iff.mpr Fin.val_injective
  have mapped : [ordering 0, ordering 1, ordering 2, ordering 3].map Fin.val =
      order.map Fin.val := by
    simpa [finFourPermutationList, ordering] using encoded
  exact mapped.symm

/-- Actual two-stage slot lookup is total and produces one combined `S₄` permutation of the
four written drawing points, rather than an unconstrained four-point witness. -/
theorem drawingPoint_mapM_is_permutedPoints (drawing : Frame) (slots : List Nat)
    (slotsPermutation : slots.Perm (List.range 4)) (order : List (Fin 4))
    (orderPermutation : order.Perm (List.finRange 4)) :
    ∃ ordering : Equiv.Perm (Fin 4),
      order.mapM (drawingPointForOccurrenceSlot? drawing slots) =
        some (permutedPoints drawing.first drawing.second drawing.third drawing.fourth ordering) := by
  obtain ⟨priority, orderEq⟩ := finFour_order_representation order orderPermutation
  let alignment := finFourEquivOfPermutationList slots slotsPermutation
  refine ⟨priority.trans alignment, ?_⟩
  rw [orderEq]
  simp [List.mapM_cons, drawingPointForOccurrenceSlot?_of_permutation drawing slots
    slotsPermutation, permutedPoints, Equiv.trans_apply, alignment]

/-- Every four-slot priority permutation of a recognized source drawing yields a successful
exact rational `R/S` computation. Nondegeneracy comes from the actual source conditions. -/
theorem drawingPoint_mapM_descriptor_exists (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (drawing : Frame)
    (bound : SourceFrame source center.val drawing) (slots : List Nat)
    (slotsPermutation : slots.Perm (List.range 4)) (order : List (Fin 4))
    (orderPermutation : order.Perm (List.finRange 4)) :
    ∃ points raw,
      order.mapM (drawingPointForOccurrenceSlot? drawing slots) = some points ∧
      descriptorOfPriorityOrderedPoints? points = some raw := by
  obtain ⟨ordering, computed⟩ := drawingPoint_mapM_is_permutedPoints drawing slots
    slotsPermutation order orderPermutation
  have nonzero := sourceFrame_orientedVolume_ne_zero source center drawing bound
  rcases lt_trichotomy
      (CartesianPoint3.orientedVolume drawing.first drawing.second drawing.third drawing.fourth)
      0 with negative | zero | positive
  · -- Negative written-order volume is the `clockwise` carrier in the calibrated convention.
    refine ⟨permutedPoints drawing.first drawing.second drawing.third drawing.fourth ordering,
      RawMolecule.descriptorOfParity .clockwise
        (RawMolecule.permutationIsEven (finFourPermutationList ordering)), computed, ?_⟩
    exact (descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).mpr
      (rationalTetrahedralDescriptor_permutedPoints drawing.first drawing.second drawing.third
        drawing.fourth ordering .clockwise negative)
  · exact False.elim (nonzero zero)
  · -- Positive written-order volume is the `anticlockwise` carrier.
    refine ⟨permutedPoints drawing.first drawing.second drawing.third drawing.fourth ordering,
      RawMolecule.descriptorOfParity .anticlockwise
        (RawMolecule.permutationIsEven (finFourPermutationList ordering)), computed, ?_⟩
    exact (descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).mpr
      (rationalTetrahedralDescriptor_permutedPoints drawing.first drawing.second drawing.third
        drawing.fourth ordering .anticlockwise positive)

/-- Actual key construction and safe tracked sorting suffice for the final drawing lookup;
no point-lookup success or nondegenerate output is assumed. -/
theorem ordinaryPriorityEvidence?_exists_of_production_steps
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) (ruleFuel : Nat)
    (drawing : Frame) (slots : List Nat)
    (aligned : occurrenceAlignment? source carrierFuel center = some (drawing, slots))
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (keyComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (tracked : TrackedLocalizedLigandOrder)
    (sortComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some tracked) :
    ∃ evidence, ordinaryPriorityEvidence? source carrierFuel center view ruleFuel = some evidence := by
  have matching := occurrenceAlignment?_sound source carrierFuel center drawing slots aligned
  have ordering := (source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
    keys tracked sortComputed).2.1
  obtain ⟨permutation, pointComputed⟩ := drawingPoint_mapM_is_permutedPoints drawing slots
    matching.2.2.2.1 tracked.highestFirst ordering
  refine ⟨⟨drawing, slots, keys, tracked,
    permutedPoints drawing.first drawing.second drawing.third drawing.fourth permutation⟩, ?_⟩
  simp [ordinaryPriorityEvidence?, aligned, keyComputed, sortComputed, pointComputed]

/-- The complete ordinary drawing descriptor succeeds once the genuine production key/sort
steps succeed. This establishes the geometry completion of those executions. -/
theorem ordinaryDescriptor?_exists_of_production_steps
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) (ruleFuel : Nat)
    (drawing : Frame) (slots : List Nat)
    (aligned : occurrenceAlignment? source carrierFuel center = some (drawing, slots))
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (keyComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (tracked : TrackedLocalizedLigandOrder)
    (sortComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some tracked) :
    ∃ descriptor, ordinaryDescriptor? source carrierFuel center view ruleFuel = some descriptor := by
  have matching := occurrenceAlignment?_sound source carrierFuel center drawing slots aligned
  have ordering := (source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
    keys tracked sortComputed).2.1
  obtain ⟨points, raw, pointComputed, descriptorComputed⟩ :=
    drawingPoint_mapM_descriptor_exists source center.1 drawing matching.1 slots
      matching.2.2.2.1 tracked.highestFirst ordering
  refine ⟨classifyTetrahedralRSPseudo raw tracked.pseudoComparisons, ?_⟩
  simp [ordinaryDescriptor?, ordinaryPriorityEvidence?, aligned, keyComputed,
    sortComputed, pointComputed, descriptorComputed]

/-- Independent source admission suffices to construct the alignment internally. Production
key and sort executions remain explicit and will be discharged by separate priority bridges. -/
theorem ordinaryDescriptor?_exists_of_admitted_production_steps
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) (ruleFuel : Nat)
    (admitted : SourceOccurrenceAdmitted source carrierFuel center)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (keyComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (tracked : TrackedLocalizedLigandOrder)
    (sortComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some tracked) :
    ∃ descriptor, ordinaryDescriptor? source carrierFuel center view ruleFuel = some descriptor := by
  obtain ⟨⟨drawing, slots⟩, aligned⟩ :=
    (occurrenceAlignment?_exists_iff_admitted source carrierFuel center).mpr admitted
  exact ordinaryDescriptor?_exists_of_production_steps source carrierFuel center view ruleFuel
    drawing slots aligned keys keyComputed tracked sortComputed

/-- Zero enantiomorphic comparisons force an uppercase descriptor once the actual key and
safe-sort steps succeed; the raw determinant descriptor is constructed from source geometry. -/
theorem ordinaryDescriptor?_chiral_exists_of_production_steps
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) (ruleFuel : Nat)
    (drawing : Frame) (slots : List Nat)
    (aligned : occurrenceAlignment? source carrierFuel center = some (drawing, slots))
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (keyComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (tracked : TrackedLocalizedLigandOrder)
    (sortComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some tracked) (zero : tracked.pseudoComparisons = 0) :
    ∃ raw, ordinaryDescriptor? source carrierFuel center view ruleFuel = some (.chiral raw) := by
  have matching := occurrenceAlignment?_sound source carrierFuel center drawing slots aligned
  have ordering := (source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
    keys tracked sortComputed).2.1
  obtain ⟨points, raw, pointComputed, descriptorComputed⟩ :=
    drawingPoint_mapM_descriptor_exists source center.1 drawing matching.1 slots
      matching.2.2.2.1 tracked.highestFirst ordering
  refine ⟨raw, ?_⟩
  simp [ordinaryDescriptor?, ordinaryPriorityEvidence?, aligned, keyComputed,
    sortComputed, pointComputed, descriptorComputed, zero]

/-- Source-only completeness for the strict first-shell atomic-separated drawing domain.
All alignment, production-key, safe-sort, point-lookup, and geometry steps are constructed.
The explicit dependency view is arbitrary because Rule 1a decides these distinct endpoints;
this result does not certify that view as a global auxiliary fixed point. -/
theorem ordinaryDescriptor?_chiral_exists_of_source_atomic_separation
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (separated : SourceEndpointAtomicSeparation source drawing) :
    ∃ raw, ordinaryDescriptor? source carrierFuel center view (2 * (carrierFuel + 1)) =
      some (.chiral raw) := by
  obtain ⟨⟨actualDrawing, slots⟩, aligned⟩ :=
    occurrenceAlignment?_exists_of_sourceFrame source carrierFuel center drawing bound
  obtain ⟨keys, tracked, keyComputed, sortComputed, _perm, _descending, zero⟩ :=
    exists_production_keys_and_safe_order_of_source_atomic_separation
      source carrierFuel center view drawing bound noDouble separated
  exact ordinaryDescriptor?_chiral_exists_of_production_steps source carrierFuel center view
    (2 * (carrierFuel + 1)) actualDrawing slots aligned keys keyComputed tracked sortComputed zero

/-- The constructed uppercase descriptor also carries the adapter's independent descriptor
meaning, including source geometry, actual occurrence roots, and production priorities. -/
theorem ordinaryDescriptor?_chiral_meaning_of_source_atomic_separation
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (separated : SourceEndpointAtomicSeparation source drawing) :
    ∃ raw, ordinaryDescriptor? source carrierFuel center view (2 * (carrierFuel + 1)) =
        some (.chiral raw) ∧
      OrdinaryDescriptorMeaning source carrierFuel center view (2 * (carrierFuel + 1))
        (.chiral raw) := by
  obtain ⟨raw, computed⟩ := ordinaryDescriptor?_chiral_exists_of_source_atomic_separation
    source carrierFuel center view drawing bound noDouble separated
  exact ⟨raw, computed, ordinaryDescriptor?_sound source carrierFuel center view
    (2 * (carrierFuel + 1)) (.chiral raw) computed⟩

/-- Carrier-zero completeness needs only the admitted local drawing and strict first-shell
atomic separation. Unrelated ordinary double bonds are permitted in the actual source. -/
theorem ordinaryDescriptor?_chiral_exists_of_zero_carrier_source_atomic_separation
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing) :
    ∃ raw, ordinaryDescriptor? source 0 center view 2 = some (.chiral raw) := by
  obtain ⟨⟨actualDrawing, slots⟩, aligned⟩ :=
    occurrenceAlignment?_exists_of_sourceFrame source 0 center drawing bound
  obtain ⟨keys, tracked, keyComputed, sortComputed, _perm, _descending, zero⟩ :=
    exists_zero_carrier_production_safe_order_of_source_atomic_separation
      source center view drawing bound separated
  exact ordinaryDescriptor?_chiral_exists_of_production_steps source 0 center view 2
    actualDrawing slots aligned keys keyComputed tracked sortComputed zero

theorem ordinaryDescriptor?_chiral_meaning_of_zero_carrier_source_atomic_separation
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing) :
    ∃ raw, ordinaryDescriptor? source 0 center view 2 = some (.chiral raw) ∧
      OrdinaryDescriptorMeaning source 0 center view 2 (.chiral raw) := by
  obtain ⟨raw, computed⟩ := ordinaryDescriptor?_chiral_exists_of_zero_carrier_source_atomic_separation
    source center view drawing bound separated
  exact ⟨raw, computed, ordinaryDescriptor?_sound source 0 center view 2 (.chiral raw) computed⟩

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeDescriptorConstructionRegression

open AuthoritativeChemicalInput AuthoritativeChemicalInput.SingleWedgeSource
open SingleWedgeOccurrenceAlignmentRegression SingleWedgeAtomicPriorityBridgeRegression

/-- The actual CFClBrI drawing, production occurrence keys, and production safe sorter yield
an uppercase descriptor. No guessed `R/S` label or successful pipeline equation is supplied. -/
theorem cfclbri_actual_production_descriptor_exists :
    ∃ raw, ordinaryEmptyAuxiliaryDescriptor? SingleWedgeSourceRegression.source 0 2
      cfclbriProductionCenter = some (.chiral raw) := by
  obtain ⟨aligned, alignedComputed⟩ := cfclbri_constructed_center_alignment 0
  have bound := (occurrenceAlignment?_sound SingleWedgeSourceRegression.source 0
    cfclbriProductionCenter aligned.1 aligned.2 alignedComputed).1
  exact ordinaryDescriptor?_chiral_exists_of_source_atomic_separation
    SingleWedgeSourceRegression.source 0 cfclbriProductionCenter
    (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView (fun _ => none)
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0
        cfclbriProductionCenter)) aligned.1 bound
    SingleWedgeProductionKeyReadinessRegression.cfclbri_no_ordinary_double_bond
    (cfclbri_source_endpoint_atomic_separation aligned.1)

/-- This closed production descriptor has the independent source/priority/geometry meaning;
the empty auxiliary state is an evaluator input, not an asserted fixed point. -/
theorem cfclbri_actual_production_descriptor_meaning :
    ∃ raw, ordinaryEmptyAuxiliaryDescriptor? SingleWedgeSourceRegression.source 0 2
        cfclbriProductionCenter = some (.chiral raw) ∧
      OrdinaryDescriptorMeaning SingleWedgeSourceRegression.source 0 cfclbriProductionCenter
        (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView (fun _ => none)
          (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0
            cfclbriProductionCenter)) 2 (.chiral raw) := by
  obtain ⟨raw, computed⟩ := cfclbri_actual_production_descriptor_exists
  exact ⟨raw, computed, ordinaryEmptyAuxiliaryDescriptor?_sound
    SingleWedgeSourceRegression.source 0 2 cfclbriProductionCenter (.chiral raw) computed⟩

open SingleWedgeZeroCarrierReadinessRegression

private theorem remote_double_source_endpoint_atomic_separation (drawing : SingleWedgeSource.Frame)
    (bound : SourceFrame remoteDoubleSource remoteDoubleProductionCenter.1.val drawing) :
    SourceEndpointAtomicSeparation remoteDoubleSource drawing := by
  have endpoints : drawing.endpoints = [1, 2, 3, 4] := by
    rcases bound with ⟨diagram, positions, observed, positioned, _admitted, drawingEq⟩
    have diagramEq : diagram =
        { atomPositions? := some (SingleWedgeSourceRegression.positions ++ [⟨3, 0⟩, ⟨4, 0⟩]),
          bonds := SingleWedgeSourceRegression.diagram.bonds } := by
      exact Option.some.inj observed.symm
    subst diagram
    rw [drawingEq]
    rfl
  have separated : ∀ left right : remoteDoubleSource.AromaticCanonicalAtom,
      left.val ∈ ([1, 2, 3, 4] : List Nat) →
      right.val ∈ ([1, 2, 3, 4] : List Nat) →
      remoteDoubleSource.molecule.toLocalizedMoleculeGraph.atomZ left =
        remoteDoubleSource.molecule.toLocalizedMoleculeGraph.atomZ right → left = right := by
    intro left right
    fin_cases left <;> fin_cases right <;> decide +kernel
  intro left right leftPresent rightPresent same
  rw [endpoints] at leftPresent rightPresent
  exact separated left right leftPresent rightPresent same

/-- A genuine unrelated source C=C does not prevent the actual drawing-to-production descriptor
pipeline from returning an uppercase label; its exact `R/S` value is not guessed. -/
theorem remote_double_source_actual_production_descriptor_exists :
    ∃ raw, ordinaryEmptyAuxiliaryDescriptor? remoteDoubleSource 0 2
      remoteDoubleProductionCenter = some (.chiral raw) := by
  obtain ⟨drawing, extracted⟩ := Option.isSome_iff_exists.mp remote_double_source_recognized
  have bound : SourceFrame remoteDoubleSource remoteDoubleProductionCenter.1.val drawing :=
    (extract?_eq_some_iff remoteDoubleSource _ drawing).mp extracted
  exact ordinaryDescriptor?_chiral_exists_of_zero_carrier_source_atomic_separation
    remoteDoubleSource remoteDoubleProductionCenter
    (remoteDoubleSource.aromaticCanonicalDependencyView (fun _ => none)
      (remoteDoubleSource.aromaticCanonicalFinalOccurrence 0 remoteDoubleProductionCenter))
    drawing bound (remote_double_source_endpoint_atomic_separation drawing bound)

end SingleWedgeDescriptorConstructionRegression
end TetraStereo.OneCenter
