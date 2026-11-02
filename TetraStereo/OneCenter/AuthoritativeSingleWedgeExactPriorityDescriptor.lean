import TetraStereo.OneCenter.AuthoritativeSingleWedgeDescriptorConstruction
import Mathlib.Data.List.Sort

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

open CertifiedLocalizedCIPInput RationalTetrahedralPermutation Rule6HandednessSemantics

/-!
The actual production cursor priority transports through the source-ID alignment. Consequently
its safe atomic-separated ordering selects exactly the independently sorted written drawing
slots. This avoids evaluating the noncomputable carrier or assuming its returned root order.
Scientific approval, tied priorities, and global auxiliary-state correctness remain separate.
-/

def writtenAtomicPriority (source : AuthoritativeChemicalInput) (drawing : Frame)
    (slot : Fin 4) : Nat :=
  ((drawing.endpoints[slot.val]?).bind fun atomID =>
    (source.molecule.atoms[atomID]?).map fun atom => atom.element.atomicNumber).getD 0

theorem finalOccurrenceRootIDs_lookup (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) (slot : Fin 4) :
    (finalOccurrenceRootIDs source fuel center)[slot.val]? =
      some (cursorAtomID source (productionCursorAt source fuel center drawing bound slot)) := by
  have length := finalOccurrenceRoots_length_of_sourceFrame source fuel center drawing bound
  have rootLookup : (finalOccurrenceRoots source fuel center)[slot.val]? =
      some (productionCursorAt source fuel center drawing bound slot) := by
    rw [List.getElem?_eq_getElem (by rw [length]; exact slot.isLt)]
    rfl
  simp [finalOccurrenceRootIDs, List.getElem?_map, rootLookup]

theorem productionAtomicPriority_eq_written_aligned_priority
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) (slots : List Nat)
    (matching : ExactSlotAlignment drawing.endpoints
      (finalOccurrenceRootIDs source fuel center) slots) (slot : Fin 4) :
    productionAtomicPriority source fuel center drawing bound slot =
      writtenAtomicPriority source drawing
        (finFourEquivOfPermutationList slots matching.2.2.1 slot) := by
  let alignment := finFourEquivOfPermutationList slots matching.2.2.1
  have slotsEq := finFourPermutationList_equivOfPermutationList slots matching.2.2.1
  have slotsLookup : slots[slot.val]? = some (alignment slot).val := by
    rw [← slotsEq]
    fin_cases slot <;> simp [finFourPermutationList, alignment]
  have mapped := congrArg (fun ids : List (Option Nat) => ids[slot.val]?) matching.2.2.2
  change (slots.map (fun position => drawing.endpoints[position]?))[slot.val]? =
    (finalOccurrenceRootIDs source fuel center)[slot.val]? at mapped
  rw [List.getElem?_map, slotsLookup, Option.map_some,
    finalOccurrenceRootIDs_lookup source fuel center drawing bound slot] at mapped
  have endpointLookup : drawing.endpoints[(alignment slot).val]? =
      cursorAtomID source (productionCursorAt source fuel center drawing bound slot) :=
    Option.some.inj mapped
  obtain ⟨neighbor, _present, nodeEq⟩ :=
    productionCursorAt_real_root source fuel center drawing bound slot
  have ID : cursorAtomID source (productionCursorAt source fuel center drawing bound slot) =
      some neighbor.val := by
    simp [cursorAtomID, nodeEq, OfficialCIPNode.rootFromEdge]
  rw [ID] at endpointLookup
  have atomLookup : source.molecule.atoms[neighbor.val]? = some (source.molecule.atoms.get neighbor) :=
    List.getElem?_eq_getElem neighbor.isLt
  simp [productionAtomicPriority, cursorAtomicPriority, nodeEq,
    OfficialCIPNode.rootFromEdge, writtenAtomicPriority, endpointLookup, atomLookup, alignment]

/-- Independently strictly sorted written slots uniquely identify the transported actual
production priority order. No choice of returned carrier order appears in the conclusion. -/
theorem aligned_production_order_eq_written_order
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) (slots : List Nat)
    (matching : ExactSlotAlignment drawing.endpoints
      (finalOccurrenceRootIDs source fuel center) slots)
    (order writtenOrder : List (Fin 4)) (orderPerm : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right =>
      productionAtomicPriority source fuel center drawing bound right <
        productionAtomicPriority source fuel center drawing bound left))
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
      simpa only [productionAtomicPriority_eq_written_aligned_priority
        source fuel center drawing bound slots matching] using higher)
  exact (mappedPerm.trans writtenPerm.symm).eq_of_pairwise
    (fun _ _ _ _ higher reverse => False.elim (Nat.lt_asymm higher reverse))
    mappedDescending writtenDescending

theorem drawingPoint_mapM_eq_written_order_points
    (drawing : Frame) (slots : List Nat) (slotsPerm : slots.Perm (List.range 4))
    (order writtenOrder : List (Fin 4))
    (orderEq : order.map (finFourEquivOfPermutationList slots slotsPerm) = writtenOrder) :
    order.mapM (drawingPointForOccurrenceSlot? drawing slots) =
      some (writtenOrder.map (pointVector drawing.first drawing.second drawing.third drawing.fourth)) := by
  have callback : drawingPointForOccurrenceSlot? drawing slots =
      fun index => some (pointVector drawing.first drawing.second drawing.third drawing.fourth
        (finFourEquivOfPermutationList slots slotsPerm index)) :=
    funext (drawingPointForOccurrenceSlot?_of_permutation drawing slots slotsPerm)
  rw [callback]
  have mappedPoints := List.mapM_pure (m := Option) (l := order)
    (f := fun index : Fin 4 => pointVector drawing.first drawing.second drawing.third drawing.fourth
      (finFourEquivOfPermutationList slots slotsPerm index))
  change order.mapM (fun index => some
      (pointVector drawing.first drawing.second drawing.third drawing.fourth
        (finFourEquivOfPermutationList slots slotsPerm index))) =
    some (order.map (fun index => pointVector drawing.first drawing.second drawing.third drawing.fourth
      (finFourEquivOfPermutationList slots slotsPerm index))) at mappedPoints
  rw [mappedPoints]
  have composed : order.map (fun index =>
      pointVector drawing.first drawing.second drawing.third drawing.fourth
        (finFourEquivOfPermutationList slots slotsPerm index)) =
      (order.map (finFourEquivOfPermutationList slots slotsPerm)).map
        (pointVector drawing.first drawing.second drawing.third drawing.fourth) :=
    (List.map_map (l := order) (f := finFourEquivOfPermutationList slots slotsPerm)
      (g := pointVector drawing.first drawing.second drawing.third drawing.fourth)).symm
  rw [composed, orderEq]

/-- Exact uppercase descriptor selected by independently sorted source slots, with all
production key/sort executions constructed from the carrier-zero source domain. -/
theorem ordinaryDescriptor?_eq_chiral_of_zero_carrier_written_priority
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (writtenOrder : List (Fin 4)) (writtenPerm : writtenOrder.Perm (List.finRange 4))
    (writtenDescending : writtenOrder.Pairwise (fun left right =>
      writtenAtomicPriority source drawing right < writtenAtomicPriority source drawing left))
    (raw : RS)
    (geometry : descriptorOfPriorityOrderedPoints?
      (writtenOrder.map (pointVector drawing.first drawing.second drawing.third drawing.fourth)) =
      some raw) :
    ordinaryDescriptor? source 0 center view 2 = some (.chiral raw) := by
  obtain ⟨⟨actualDrawing, slots⟩, aligned⟩ :=
    occurrenceAlignment?_exists_of_sourceFrame source 0 center drawing bound
  have actualBound := (occurrenceAlignment?_sound source 0 center actualDrawing slots aligned).1
  have drawingEq : actualDrawing = drawing := by
    have extracted := (extract?_eq_some_iff source center.1 drawing).mpr bound
    have actualExtracted := (extract?_eq_some_iff source center.1 actualDrawing).mpr actualBound
    exact Option.some.inj (actualExtracted.symm.trans extracted)
  subst actualDrawing
  have matching := (occurrenceAlignment?_sound source 0 center drawing slots aligned).2
  obtain ⟨keys, tracked, keyComputed, sortComputed, perm, descending, zero⟩ :=
    exists_zero_carrier_production_safe_order_of_source_atomic_separation source center view
      drawing bound separated
  have orderEq := aligned_production_order_eq_written_order source 0 center drawing bound slots
    matching tracked.highestFirst writtenOrder perm descending writtenPerm writtenDescending
  have pointComputed := drawingPoint_mapM_eq_written_order_points drawing slots matching.2.2.1
    tracked.highestFirst writtenOrder orderEq
  simp [ordinaryDescriptor?, ordinaryPriorityEvidence?, aligned, keyComputed, sortComputed,
    pointComputed, geometry, zero]

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeExactPriorityDescriptorRegression

open AuthoritativeChemicalInput AuthoritativeChemicalInput.SingleWedgeSource
open SingleWedgeOccurrenceAlignmentRegression SingleWedgeAtomicPriorityBridgeRegression
open CertifiedLocalizedCIPInput RationalTetrahedralPermutation

def writtenFrame (style : DiagramBondStyle) : SingleWedgeSource.Frame :=
  frameOfDiagram 0 (SingleWedgeSourceRegression.diagramWithStyle style)
    SingleWedgeSourceRegression.positions

def hashedProductionCenter :
    (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).AromaticCanonicalTetrahedralCenter :=
  cfclbriProductionCenter

private theorem solid_frame_bound :
    SourceFrame SingleWedgeSourceRegression.source cfclbriProductionCenter.1.val
      (writtenFrame .solidWedge) :=
  ⟨SingleWedgeSourceRegression.diagramWithStyle .solidWedge,
    SingleWedgeSourceRegression.positions, rfl, rfl, by decide +kernel, rfl⟩

private theorem hashed_frame_bound :
    SourceFrame (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
      hashedProductionCenter.1.val (writtenFrame .hashedWedge) :=
  ⟨SingleWedgeSourceRegression.diagramWithStyle .hashedWedge,
    SingleWedgeSourceRegression.positions, rfl, rfl, by decide +kernel, rfl⟩

private theorem descending_slots_perm :
    ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by decide

private theorem solid_written_priorities_descending :
    ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      writtenAtomicPriority SingleWedgeSourceRegression.source (writtenFrame .solidWedge) right <
        writtenAtomicPriority SingleWedgeSourceRegression.source (writtenFrame .solidWedge) left) := by
  decide +kernel

private theorem hashed_written_priorities_descending :
    ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      writtenAtomicPriority (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
        (writtenFrame .hashedWedge) right <
      writtenAtomicPriority (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
        (writtenFrame .hashedWedge) left) := by
  decide +kernel

/-- The solid-wedge written-order determinant is `-3`; the descending written-priority list is an
even (reversal) permutation of the written order, so its exact oriented volume is also negative and
the calibrated descriptor is `R`. -/
private theorem solid_sorted_geometry :
    descriptorOfPriorityOrderedPoints? (([3, 2, 1, 0] : List (Fin 4)).map
      (pointVector (writtenFrame .solidWedge).first (writtenFrame .solidWedge).second
        (writtenFrame .solidWedge).third (writtenFrame .solidWedge).fourth)) = some RS.R := by
  decide +kernel

/-- The hashed-wedge written-order determinant is `+3`; the same even reversal preserves positivity,
so the calibrated descriptor is `S`. -/
private theorem hashed_sorted_geometry :
    descriptorOfPriorityOrderedPoints? (([3, 2, 1, 0] : List (Fin 4)).map
      (pointVector (writtenFrame .hashedWedge).first (writtenFrame .hashedWedge).second
        (writtenFrame .hashedWedge).third (writtenFrame .hashedWedge).fourth)) = some RS.S := by
  decide +kernel

private theorem hashed_source_endpoint_separation (drawing : SingleWedgeSource.Frame) :
    SourceEndpointAtomicSeparation (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
      drawing := by
  intro left right _leftPresent _rightPresent same
  exact cfclbri_source_atomZ_injective same

/-- The full noncomputable production occurrence-key sorter yields exactly uppercase `R`
from the actual solid-wedge CFClBrI source. Returned carrier order is not evaluated or assumed. -/
theorem cfclbri_full_production_solid_descriptor :
    ordinaryEmptyAuxiliaryDescriptor? SingleWedgeSourceRegression.source 0 2
      cfclbriProductionCenter = some (.chiral RS.R) :=
  ordinaryDescriptor?_eq_chiral_of_zero_carrier_written_priority
    SingleWedgeSourceRegression.source cfclbriProductionCenter
    (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView (fun _ => none)
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter))
    (writtenFrame .solidWedge) solid_frame_bound
    (cfclbri_source_endpoint_atomic_separation _) [3, 2, 1, 0] descending_slots_perm
    solid_written_priorities_descending RS.R solid_sorted_geometry

set_option maxHeartbeats 800000 in
/-- The same semantic center with a hashed glyph yields exactly uppercase `S` through the
full production occurrence-key sorter, rather than the separate atomic shortcut. -/
theorem cfclbri_full_production_hashed_descriptor :
    ordinaryEmptyAuxiliaryDescriptor?
      (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge) 0 2 hashedProductionCenter =
      some (.chiral RS.S) :=
  ordinaryDescriptor?_eq_chiral_of_zero_carrier_written_priority
    (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge) hashedProductionCenter
    ((SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).aromaticCanonicalDependencyView
      (fun _ => none) ((SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).aromaticCanonicalFinalOccurrence
        0 hashedProductionCenter))
    (writtenFrame .hashedWedge) hashed_frame_bound
    (hashed_source_endpoint_separation _) [3, 2, 1, 0] descending_slots_perm
    hashed_written_priorities_descending RS.S hashed_sorted_geometry

theorem cfclbri_solid_production_agrees_with_atomic_shortcut :
    ordinaryEmptyAuxiliaryDescriptor? SingleWedgeSourceRegression.source 0 2
      cfclbriProductionCenter =
      (atomicSeparatedDescriptor? SingleWedgeSourceRegression.source cfclbriProductionCenter.1).map
        LocalizedTetrahedralRSPseudoDescriptor.chiral := by
  rw [cfclbri_full_production_solid_descriptor]
  exact (congrArg (Option.map LocalizedTetrahedralRSPseudoDescriptor.chiral)
    SingleWedgePriorityDescriptorRegression.cfclbri_source_solid_descriptor).symm

theorem cfclbri_hashed_production_agrees_with_atomic_shortcut :
    ordinaryEmptyAuxiliaryDescriptor?
      (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge) 0 2 hashedProductionCenter =
      (atomicSeparatedDescriptor? (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
        hashedProductionCenter.1).map LocalizedTetrahedralRSPseudoDescriptor.chiral := by
  rw [cfclbri_full_production_hashed_descriptor]
  exact (congrArg (Option.map LocalizedTetrahedralRSPseudoDescriptor.chiral)
    SingleWedgePriorityDescriptorRegression.cfclbri_source_hashed_descriptor).symm

theorem cfclbri_full_production_solid_meaning :
    OrdinaryDescriptorMeaning SingleWedgeSourceRegression.source 0 cfclbriProductionCenter
      (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView (fun _ => none)
        (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter))
      2 (.chiral RS.R) :=
  ordinaryEmptyAuxiliaryDescriptor?_sound _ 0 2 _ _ cfclbri_full_production_solid_descriptor

theorem cfclbri_full_production_hashed_meaning :
    OrdinaryDescriptorMeaning (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge) 0
      hashedProductionCenter
      ((SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).aromaticCanonicalDependencyView
        (fun _ => none) ((SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).aromaticCanonicalFinalOccurrence
          0 hashedProductionCenter)) 2 (.chiral RS.S) :=
  ordinaryEmptyAuxiliaryDescriptor?_sound _ 0 2 _ _ cfclbri_full_production_hashed_descriptor

end SingleWedgeExactPriorityDescriptorRegression
end TetraStereo.OneCenter
