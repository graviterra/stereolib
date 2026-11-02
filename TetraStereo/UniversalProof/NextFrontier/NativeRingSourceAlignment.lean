import TetraStereo.UniversalProof.NextFrontier.NativeRingSourceOrdering
import TetraStereo.UniversalProof.FamilySourceBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingSourceAlignment

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRingSourceInput
open TetraStereo.UniversalProof.NativeRingSourceGeometry
open TetraStereo.UniversalProof.NativeRingSourceOrdering
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

-- Keep conversion abstract while transporting returned slot identities.
attribute [local irreducible] ringSource

theorem returned_frame (n : Nat) (parity : TetrahedralInputParity) :
    (ringSource n parity).aromaticCanonicalOccurrenceLigandFrame?
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) =
        some (ringFrame n parity 1).roots :=
  (actual_returned_four_roots (expanded n parity) (ringSource n parity) (ring_annotation_agreement n parity).1
    1 (ringCenter n parity) (ringRecordDomain n parity 0) (ring_four_records n parity)).1

theorem returned_root_ids (n : Nat) (parity : TetrahedralInputParity) :
    ((ringFrame n parity 1).roots.map (cursorAtomID (ringSource n parity))).Perm
      [some (n + 5), some 1, some 2, some (n + 4)] := by
  have source := converted_final_root_ids_perm (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 1 (ringCenter n parity) (ringRecordDomain n parity 0)
  exact source.trans ((expanded_root_records n parity).map some)

/-- Endpoint identity in an actual returned position. This needs physical row distinctness,
not atomic-number injectivity; the two carbons remain distinct physical endpoints. -/
theorem returned_id_at (n : Nat) (parity : TetrahedralInputParity) (slot : Fin 4) :
    ((ringFrame n parity 1).roots.map (cursorAtomID (ringSource n parity)))[slot.val]? =
      some (some (ringSlotID n parity 1 slot)) := by
  let frame := ringFrame n parity 1
  have bound : slot.val < frame.roots.length := by rw [frame.rootsLength]; exact slot.isLt
  change (frame.roots.map (cursorAtomID (ringSource n parity)))[slot.val]? = _
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  obtain ⟨atom, _, current, _, equal⟩ := actual_slot_endpoint (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 1 (ringCenter n parity) (ringRecordDomain n parity 0)
    (ring_four_records n parity) slot
  change some (cursorAtomID (ringSource n parity) (frame.cursorAt slot)) = _
  change (frame.cursorAt slot).occurrence.1.node.current? = some atom at current
  change ringSlotID n parity 1 slot = atom.val at equal
  rw [equal]
  unfold cursorAtomID
  rw [current]
  rfl

/-- Actual finite slot matcher readiness follows from the physical written row and returned
root-ID permutation. No identity alignment or prescribed matcher answer is supplied. -/
theorem alignment_exists (n : Nat) (parity : TetrahedralInputParity) :
    ∃ slots, findSlotAlignment? ((expanded n parity).writtenNeighbors (ringCenter n parity).1.val)
      ((ringFrame n parity 1).roots.map (cursorAtomID (ringSource n parity))) = some slots := by
  apply findSlotAlignment?_exists_of_perm
  · rw [ring_center_index, expanded_root_written_row]
    rfl
  · rw [ring_center_index, expanded_root_written_row]
    simp (disch := omega) [List.nodup_cons]
  · rw [ring_center_index, expanded_root_written_row]
    simpa only [List.map_cons, List.map_nil] using returned_root_ids n parity

noncomputable def alignmentSlots (n : Nat) (parity : TetrahedralInputParity) : List Nat :=
  Classical.choose (alignment_exists n parity)

theorem slots_computed (n : Nat) (parity : TetrahedralInputParity) :
    findSlotAlignment? ((expanded n parity).writtenNeighbors (ringCenter n parity).1.val)
      ((ringFrame n parity 1).roots.map (cursorAtomID (ringSource n parity))) = some (alignmentSlots n parity) :=
  Classical.choose_spec (alignment_exists n parity)

theorem slots_matching (n : Nat) (parity : TetrahedralInputParity) :
    ExactSlotAlignment ((expanded n parity).writtenNeighbors (ringCenter n parity).1.val)
      ((ringFrame n parity 1).roots.map (cursorAtomID (ringSource n parity))) (alignmentSlots n parity) :=
  findSlotAlignment?_sound _ _ _ (slots_computed n parity)

/-- The actual slot matcher identifies the same physical endpoint in each source slot. -/
theorem aligned_written_lookup (n : Nat) (parity : TetrahedralInputParity)
    (slot : Fin 4) :
    ((expanded n parity).writtenNeighbors (ringCenter n parity).1.val)[(alignmentSlots n parity).getD slot.val 0]? =
      some (ringSlotID n parity 1 slot) :=
  FamilySourceBridge.aligned_written_lookup _ _ _ (ringSlotID n parity 1)
    (slots_matching n parity) (returned_id_at n parity) slot

/-- Actual endpoint lookup and actual alignment agree for every order, including a produced
tracked order. This transports physical identities, without a Z-injectivity assumption. -/
theorem aligned_priority_positions (n : Nat) (parity : TetrahedralInputParity)
    (order : List (Fin 4)) :
    (order.map (ringSlotID n parity 1)).mapM
      (writtenSlot? ((expanded n parity).writtenNeighbors (ringCenter n parity).1.val)) =
        some (order.map fun slot => (alignmentSlots n parity).getD slot.val 0) :=
  FamilySourceBridge.aligned_priority_positions _ _ _ (ringSlotID n parity 1)
    (slots_matching n parity) (returned_id_at n parity) order


/-- The source's actual finite matcher and physical priority order give the corrected written
positions. No identity slot alignment is assumed. -/
theorem aligned_role_positions (n : Nat) (parity : TetrahedralInputParity) :
    (prioritySlots n parity).map (fun slot => (alignmentSlots n parity).getD slot.val 0) = [1, 2, 3, 0] := by
  have matching := aligned_priority_positions n parity (prioritySlots n parity)
  have written := expanded_root_written_row n parity
  have distinct : ((expanded n parity).writtenNeighbors 0).Nodup := by
    rw [written]
    simp (disch := omega) [List.nodup_cons]
  have p0 := writtenSlot?_eq_some ((expanded n parity).writtenNeighbors 0) distinct 0 (n + 5)
    (by rw [written]; rfl)
  have p1 := writtenSlot?_eq_some ((expanded n parity).writtenNeighbors 0) distinct 1 1
    (by rw [written]; rfl)
  have p2 := writtenSlot?_eq_some ((expanded n parity).writtenNeighbors 0) distinct 2 2
    (by rw [written]; rfl)
  have p3 := writtenSlot?_eq_some ((expanded n parity).writtenNeighbors 0) distinct 3 (n + 4)
    (by rw [written]; rfl)
  have physical : ((prioritySlots n parity).map (ringSlotID n parity 1)).mapM
      (writtenSlot? ((expanded n parity).writtenNeighbors 0)) = some [1, 2, 3, 0] := by
    simp only [prioritySlots, List.map_cons, List.map_nil, ring_role_slot_index]
    simp [List.mapM_cons, p0, p1, p2, p3]
  exact Option.some.inj (matching.symm.trans physical)

end TetraStereo.UniversalProof.NativeRingSourceAlignment
