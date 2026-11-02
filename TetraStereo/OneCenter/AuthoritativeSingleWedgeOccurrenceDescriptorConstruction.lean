import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceReadiness
import TetraStereo.OneCenter.AuthoritativeSingleWedgeBranchOccurrenceSupport

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

open CertifiedLocalizedCIPInput RationalTetrahedralPermutation Rule6HandednessSemantics

/-!
# Drawing descriptors constructed at genuine interior occurrences

Actual source endpoints identify returned reroot cursors without changing their root, address,
history or dependency view. Their real atomic heads give the actual strict priority order, which
is transported to independently ranked drawing slots and exact rational geometry. The final
closed examples assign opposite daughter labels from a source with no 3D coordinates or parser
stereoconfigurations. Global no-double and local atomic separation remain explicit; this is not
coverage of all tied-priority, cyclic auxiliary dependencies, mixed conflicts or source approval.
-/

theorem occurrenceRootIDs_lookup (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) (slot : Fin 4) :
    (frame.roots.map (cursorAtomID source))[slot.val]? =
      some (cursorAtomID source (frame.cursorAt slot)) := by
  have length := frame.rootsLength
  have rootLookup : frame.roots[slot.val]? =
      some (frame.cursorAt slot) := by
    rw [List.getElem?_eq_getElem (by rw [length]; exact slot.isLt)]
    rfl
  simp [List.getElem?_map, rootLookup]

theorem occurrenceAtomicPriority_eq_written_aligned_priority
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (real : OccurrenceRootsReal source frame) (drawing : Frame) (slots : List Nat)
    (matching : ExactSlotAlignment drawing.endpoints
      (frame.roots.map (cursorAtomID source)) slots) (slot : Fin 4) :
    occurrenceAtomicPriority source frame slot =
      writtenAtomicPriority source drawing
        (finFourEquivOfPermutationList slots matching.2.2.1 slot) := by
  let alignment := finFourEquivOfPermutationList slots matching.2.2.1
  have slotsEq := finFourPermutationList_equivOfPermutationList slots matching.2.2.1
  have slotsLookup : slots[slot.val]? = some (alignment slot).val := by
    rw [← slotsEq]
    fin_cases slot <;> simp [finFourPermutationList, alignment]
  have mapped := congrArg (fun ids : List (Option Nat) => ids[slot.val]?) matching.2.2.2
  change (slots.map (fun position => drawing.endpoints[position]?))[slot.val]? =
    (frame.roots.map (cursorAtomID source))[slot.val]? at mapped
  rw [List.getElem?_map, slotsLookup, Option.map_some,
    occurrenceRootIDs_lookup source frame slot] at mapped
  have endpointLookup : drawing.endpoints[(alignment slot).val]? =
      cursorAtomID source (frame.cursorAt slot) :=
    Option.some.inj mapped
  obtain ⟨neighbor, current, _provenance⟩ := real slot
  have ID : cursorAtomID source (frame.cursorAt slot) =
      some neighbor.val := by
    simp [cursorAtomID, current]
  rw [ID] at endpointLookup
  have atomLookup : source.molecule.atoms[neighbor.val]? = some (source.molecule.atoms.get neighbor) :=
    List.getElem?_eq_getElem neighbor.isLt
  simp [occurrenceAtomicPriority, cursorAtomicPriority, current,
    writtenAtomicPriority, endpointLookup, atomLookup, alignment]

/-- Independently strictly sorted written slots uniquely identify the transported actual
original-occurrence priority order. No choice of returned carrier order appears in the conclusion. -/
theorem aligned_occurrence_order_eq_written_order
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (real : OccurrenceRootsReal source frame) (drawing : Frame) (slots : List Nat)
    (matching : ExactSlotAlignment drawing.endpoints
      (frame.roots.map (cursorAtomID source)) slots)
    (order writtenOrder : List (Fin 4)) (orderPerm : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right =>
      occurrenceAtomicPriority source frame right <
        occurrenceAtomicPriority source frame left))
    (writtenPerm : writtenOrder.Perm (List.finRange 4))
    (writtenDescending : writtenOrder.Pairwise (fun left right =>
      writtenAtomicPriority source drawing right < writtenAtomicPriority source drawing left)) :
    order.map (finFourEquivOfPermutationList slots matching.2.2.1) = writtenOrder := by
  let alignment := finFourEquivOfPermutationList slots matching.2.2.1
  have mappedPerm : (order.map alignment).Perm (List.finRange 4) :=
    (orderPerm.map alignment).trans alignment.map_finRange_perm
  have mappedDescending : (order.map alignment).Pairwise (fun left right =>
      writtenAtomicPriority source drawing right < writtenAtomicPriority source drawing left) := by
    apply List.pairwise_map.mpr
    exact descending.imp (by
      intro left right higher
      simpa only [occurrenceAtomicPriority_eq_written_aligned_priority
        source frame real drawing slots matching] using higher)
  exact (mappedPerm.trans writtenPerm.symm).eq_of_pairwise
    (fun _ _ _ _ higher reverse => False.elim (Nat.lt_asymm higher reverse))
    mappedDescending writtenDescending

/-- Construct actual compilation and sorting, then use independent written priority geometry.
All source and carrier support hypotheses are explicit; no descriptor computation is a premise. -/
theorem occurrenceOrdinaryDescriptor?_eq_chiral_of_written_priority
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (centerRecovered : source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (returned : source.aromaticCanonicalOccurrenceLigandFrame? target = some frame.roots)
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (real : OccurrenceRootsReal source frame)
    (sameIDs : (frame.roots.map (cursorAtomID source)).Perm (drawing.endpoints.map some))
    (separated : SourceEndpointAtomicSeparation source drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (writtenOrder : List (Fin 4)) (writtenPerm : writtenOrder.Perm (List.finRange 4))
    (writtenDescending : writtenOrder.Pairwise (fun left right =>
      writtenAtomicPriority source drawing right < writtenAtomicPriority source drawing left))
    (raw : RS)
    (geometry : descriptorOfPriorityOrderedPoints?
      (writtenOrder.map (pointVector drawing.first drawing.second drawing.third drawing.fourth)) =
      some raw) :
    occurrenceOrdinaryDescriptor? source target view (2 * (carrierFuel + 1)) =
      some (.chiral raw) := by
  have drawingComputed := (extract?_eq_some_iff source center.1 drawing).mpr bound
  have drawingBounds := sourceFrame_endpoints_exactly_four_distinct source center.1.val drawing bound
  obtain ⟨slots, slotsComputed⟩ := findSlotAlignment?_exists_of_perm drawing.endpoints
    (frame.roots.map (cursorAtomID source)) drawingBounds.1 drawingBounds.2 sameIDs
  have matching := findSlotAlignment?_sound drawing.endpoints _ slots slotsComputed
  obtain ⟨keys, tracked, keyComputed, sortComputed, perm, descending, zero⟩ :=
    exists_occurrence_production_keys_and_safe_order_of_source_endpoints source target view
      frame returned center.1.val drawing bound real sameIDs separated noDouble
  have orderEq := aligned_occurrence_order_eq_written_order source frame real drawing slots
    matching tracked.highestFirst writtenOrder perm descending writtenPerm writtenDescending
  have pointComputed := drawingPoint_mapM_eq_written_order_points drawing slots matching.2.2.1
    tracked.highestFirst writtenOrder orderEq
  simp [occurrenceOrdinaryDescriptor?, occurrenceOrdinaryPriorityEvidence?, centerRecovered,
    drawingComputed, returned, slotsComputed, keyComputed, sortComputed, pointComputed, geometry, zero]

/-- The same source construction gives the independent sound meaning of its occurrence label,
while preserving the original target and dependency view. -/
theorem occurrenceOrdinaryDescriptor_written_priority_meaning
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (centerRecovered : source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (returned : source.aromaticCanonicalOccurrenceLigandFrame? target = some frame.roots)
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (real : OccurrenceRootsReal source frame)
    (sameIDs : (frame.roots.map (cursorAtomID source)).Perm (drawing.endpoints.map some))
    (separated : SourceEndpointAtomicSeparation source drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (writtenOrder : List (Fin 4)) (writtenPerm : writtenOrder.Perm (List.finRange 4))
    (writtenDescending : writtenOrder.Pairwise (fun left right =>
      writtenAtomicPriority source drawing right < writtenAtomicPriority source drawing left))
    (raw : RS)
    (geometry : descriptorOfPriorityOrderedPoints?
      (writtenOrder.map (pointVector drawing.first drawing.second drawing.third drawing.fourth)) =
      some raw) :
    OccurrenceOrdinaryDescriptorMeaning source target view (2 * (carrierFuel + 1)) (.chiral raw) :=
  occurrenceOrdinaryDescriptor?_sound source target view (2 * (carrierFuel + 1)) (.chiral raw)
    (occurrenceOrdinaryDescriptor?_eq_chiral_of_written_priority source target view center
      centerRecovered frame returned drawing bound real sameIDs separated noDouble
      writtenOrder writtenPerm writtenDescending raw geometry)

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeBranchSourceFixture

open AuthoritativeChemicalInput AuthoritativeChemicalInput.SingleWedgeSource
open CertifiedLocalizedCIPInput

/-! ### Historical-key policy

`left_occurrence_drawing_descriptor_R`, `right_occurrence_drawing_descriptor_S`,
`left_scheduled_drawing_R` and `right_scheduled_drawing_S` are historical API keys pinned by
`AuthoritativeSingleWedgeOccurrenceDescriptorConstructionKernelCertificate`. Their suffixes
predate the corrected negative-`R`/positive-`S` calibration: the left written-priority frame has
positive oriented volume `6` (`S`) and the right frame has negative oriented volume `-6` (`R`).
The historical names are retained with corrected statements, and accurately named siblings state
the same results for new code. -/

/-- Actual daughter nodes have real current atoms; their existing long histories are preserved. -/
theorem left_roots_real : OccurrenceRootsReal source leftBase := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

theorem right_roots_real : OccurrenceRootsReal source rightBase := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

/-- Drawing-only `S` seed at root 1, address [2], for every restricted deeper dependency view.
Historical API key: the suffix `_R` predates the sign correction. -/
theorem left_occurrence_drawing_descriptor_R
    (view : source.AromaticCanonicalDependencyView leftOccurrence) :
    occurrenceOrdinaryDescriptor? source leftOccurrence view 4 = some (.chiral RS.S) := by
  exact occurrenceOrdinaryDescriptor?_eq_chiral_of_written_priority source leftOccurrence view
    leftPerceivedCenter daughter_centers_recovered.1 leftBase actual_ligand_frames.2.1
    leftFrame left_source_frame left_roots_real daughter_root_ids_perm_written_endpoints.1
    left_endpoint_atomic_separation source_no_ordinary_double_bond writtenPriorityOrder
    written_priority_is_actual_atomic_order.1 written_priority_is_actual_atomic_order.2.1
    RS.S actual_sorted_source_geometry.1

/-- Accurate-name sibling of `left_occurrence_drawing_descriptor_R`. -/
theorem left_occurrence_drawing_descriptor_S
    (view : source.AromaticCanonicalDependencyView leftOccurrence) :
    occurrenceOrdinaryDescriptor? source leftOccurrence view 4 = some (.chiral RS.S) :=
  left_occurrence_drawing_descriptor_R view

/-- Drawing-only `R` seed at root 1, address [3], without importing the old spatial label.
Historical API key: the suffix `_S` predates the sign correction. -/
theorem right_occurrence_drawing_descriptor_S
    (view : source.AromaticCanonicalDependencyView rightOccurrence) :
    occurrenceOrdinaryDescriptor? source rightOccurrence view 4 = some (.chiral RS.R) := by
  exact occurrenceOrdinaryDescriptor?_eq_chiral_of_written_priority source rightOccurrence view
    rightPerceivedCenter daughter_centers_recovered.2 rightBase actual_ligand_frames.2.2
    rightFrame right_source_frame right_roots_real daughter_root_ids_perm_written_endpoints.2
    right_endpoint_atomic_separation source_no_ordinary_double_bond writtenPriorityOrder
    written_priority_is_actual_atomic_order.1 written_priority_is_actual_atomic_order.2.2
    RS.R actual_sorted_source_geometry.2

/-- Accurate-name sibling of `right_occurrence_drawing_descriptor_S`. -/
theorem right_occurrence_drawing_descriptor_R
    (view : source.AromaticCanonicalDependencyView rightOccurrence) :
    occurrenceOrdinaryDescriptor? source rightOccurrence view 4 = some (.chiral RS.R) :=
  right_occurrence_drawing_descriptor_S view

noncomputable def drawingScheduledState : source.AromaticCanonicalAuxiliaryState branchCarrierFuel :=
  occurrenceOrdinaryScheduledState source branchCarrierFuel 4

theorem drawingScheduledState_cipModel :
    (source.aromaticCanonicalOccurrenceSystem
      (occurrenceOrdinaryAuxiliarySemantics source branchCarrierFuel 4)).CIPModel drawingScheduledState :=
  occurrenceOrdinaryScheduledState_cipModel source branchCarrierFuel 4

/-- The causal model constructs a nonfinal drawing seed `S`; no auxiliary label is supplied.
Historical API key: the suffix `_R` predates the sign correction. -/
theorem left_scheduled_drawing_R : drawingScheduledState leftOccurrence = some (.chiral RS.S) := by
  have fixed := occurrenceOrdinaryModel_evaluates source drawingScheduledState
    drawingScheduledState_cipModel leftOccurrence
  rw [← fixed]
  exact left_occurrence_drawing_descriptor_R _

/-- Accurate-name sibling of `left_scheduled_drawing_R`. -/
theorem left_scheduled_drawing_S : drawingScheduledState leftOccurrence = some (.chiral RS.S) :=
  left_scheduled_drawing_R

/-- Historical API key: the suffix `_S` predates the sign correction. -/
theorem right_scheduled_drawing_S : drawingScheduledState rightOccurrence = some (.chiral RS.R) := by
  have fixed := occurrenceOrdinaryModel_evaluates source drawingScheduledState
    drawingScheduledState_cipModel rightOccurrence
  rw [← fixed]
  exact right_occurrence_drawing_descriptor_S _

/-- Accurate-name sibling of `right_scheduled_drawing_S`. -/
theorem right_scheduled_drawing_R : drawingScheduledState rightOccurrence = some (.chiral RS.R) :=
  right_scheduled_drawing_S

theorem left_drawing_descriptor_independent_meaning
    (view : source.AromaticCanonicalDependencyView leftOccurrence) :
    OccurrenceOrdinaryDescriptorMeaning source leftOccurrence view 4 (.chiral RS.S) :=
  occurrenceOrdinaryDescriptor?_sound source leftOccurrence view 4 (.chiral RS.S)
    (left_occurrence_drawing_descriptor_R view)

theorem right_drawing_descriptor_independent_meaning
    (view : source.AromaticCanonicalDependencyView rightOccurrence) :
    OccurrenceOrdinaryDescriptorMeaning source rightOccurrence view 4 (.chiral RS.R) :=
  occurrenceOrdinaryDescriptor?_sound source rightOccurrence view 4 (.chiral RS.R)
    (right_occurrence_drawing_descriptor_S view)

/-- An inhabited drawing-only occurrence model with opposite daughter labels and exact source
coordinates. This does not yet prove their decisive downstream Rule-4/5 key comparison. -/
theorem drawing_only_nonfinal_opposite_labels :
    source.spatial? = none ∧ diagram.atomConfigurations = [] ∧
      leftOccurrence.1.root.val = 1 ∧ leftOccurrence.1.address = [2] ∧
      rightOccurrence.1.root.val = 1 ∧ rightOccurrence.1.address = [3] ∧
      drawingScheduledState leftOccurrence = some (.chiral RS.S) ∧
      drawingScheduledState rightOccurrence = some (.chiral RS.R) :=
  ⟨source_has_only_drawing_configuration.1, source_has_only_drawing_configuration.2,
    actual_occurrence_coordinates.2.2.1, actual_occurrence_coordinates.2.2.2.1,
    actual_occurrence_coordinates.2.2.2.2.1, actual_occurrence_coordinates.2.2.2.2.2,
    left_scheduled_drawing_R, right_scheduled_drawing_S⟩

end SingleWedgeBranchSourceFixture
end TetraStereo.OneCenter
