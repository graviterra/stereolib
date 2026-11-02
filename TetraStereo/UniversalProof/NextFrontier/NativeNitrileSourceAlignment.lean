import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceOrdering
import TetraStereo.UniversalProof.FamilySourceBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceAlignment

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceOrdering
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

-- Keep conversion abstract while transporting returned slot identities.
attribute [local irreducible] nitrileSource

private theorem semantic_conversion (n : Nat) (parity : TetrahedralInputParity) :
    (expanded parity n).toSemanticMolecule? = some (nitrileSource parity n).molecule := by
  simpa only [nitrileSource] using (expanded_source_annotation_agreement parity n).1

theorem returned_frame (n : Nat) (parity : TetrahedralInputParity) :
    (nitrileSource parity n).aromaticCanonicalOccurrenceLigandFrame?
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) =
        some (nitrileFrame parity n 1).roots :=
  (actual_returned_four_roots (expanded parity n) (nitrileSource parity n) (semantic_conversion n parity)
    1 (nitrileCenter parity n) (nitrileRecordDomain parity n) (nitrile_four_records parity n)).1

theorem returned_root_ids (n : Nat) (parity : TetrahedralInputParity) :
    ((nitrileFrame parity n 1).roots.map (cursorAtomID (nitrileSource parity n))).Perm
      [some (n + 7), some 1, some 2, some (4)] := by
  have source := converted_final_root_ids_perm (expanded parity n) (nitrileSource parity n)
    (semantic_conversion n parity) 1 (nitrileCenter parity n) (nitrileRecordDomain parity n)
  exact source.trans ((expanded_center_records parity n).map some)

/-- Endpoint identity in an actual returned position. This needs physical row distinctness,
not atomic-number injectivity; the two carbons remain distinct physical endpoints. -/
theorem returned_id_at (n : Nat) (parity : TetrahedralInputParity) (slot : Fin 4) :
    ((nitrileFrame parity n 1).roots.map (cursorAtomID (nitrileSource parity n)))[slot.val]? =
      some (some (nitrileSlotAtom parity n 1 slot)) := by
  let frame := nitrileFrame parity n 1
  have bound : slot.val < frame.roots.length := by rw [frame.rootsLength]; exact slot.isLt
  change (frame.roots.map (cursorAtomID (nitrileSource parity n)))[slot.val]? = _
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  obtain ⟨atom, _, current, _, equal⟩ := actual_slot_endpoint (expanded parity n) (nitrileSource parity n)
    (semantic_conversion n parity) 1 (nitrileCenter parity n) (nitrileRecordDomain parity n)
    (nitrile_four_records parity n) slot
  change some (cursorAtomID (nitrileSource parity n) (frame.cursorAt slot)) = _
  change (frame.cursorAt slot).occurrence.1.node.current? = some atom at current
  change nitrileSlotAtom parity n 1 slot = atom.val at equal
  rw [equal]
  unfold cursorAtomID
  rw [current]
  rfl

/-- Actual finite slot matcher readiness follows from the physical written row and returned
root-ID permutation. No identity alignment or prescribed matcher answer is supplied. -/
theorem alignment_exists (n : Nat) (parity : TetrahedralInputParity) :
    ∃ slots, findSlotAlignment? ((expanded parity n).writtenNeighbors (nitrileCenter parity n).1.val)
      ((nitrileFrame parity n 1).roots.map (cursorAtomID (nitrileSource parity n))) = some slots := by
  apply findSlotAlignment?_exists_of_perm
  · rw [nitrile_center_index, expanded_center_row]
    rfl
  · rw [nitrile_center_index, expanded_center_row]
    simp (disch := omega) [List.nodup_cons]
  · rw [nitrile_center_index, expanded_center_row]
    simpa only [List.map_cons, List.map_nil] using returned_root_ids n parity

noncomputable def alignmentSlots (n : Nat) (parity : TetrahedralInputParity) : List Nat :=
  Classical.choose (alignment_exists n parity)

theorem slots_computed (n : Nat) (parity : TetrahedralInputParity) :
    findSlotAlignment? ((expanded parity n).writtenNeighbors (nitrileCenter parity n).1.val)
      ((nitrileFrame parity n 1).roots.map (cursorAtomID (nitrileSource parity n))) = some (alignmentSlots n parity) :=
  Classical.choose_spec (alignment_exists n parity)

theorem slots_matching (n : Nat) (parity : TetrahedralInputParity) :
    ExactSlotAlignment ((expanded parity n).writtenNeighbors (nitrileCenter parity n).1.val)
      ((nitrileFrame parity n 1).roots.map (cursorAtomID (nitrileSource parity n))) (alignmentSlots n parity) :=
  findSlotAlignment?_sound _ _ _ (slots_computed n parity)

/-- The actual slot matcher identifies the same physical endpoint in each source slot. -/
theorem aligned_written_lookup (n : Nat) (parity : TetrahedralInputParity)
    (slot : Fin 4) :
    ((expanded parity n).writtenNeighbors (nitrileCenter parity n).1.val)[(alignmentSlots n parity).getD slot.val 0]? =
      some (nitrileSlotAtom parity n 1 slot) :=
  FamilySourceBridge.aligned_written_lookup _ _ _ (nitrileSlotAtom parity n 1)
    (slots_matching n parity) (returned_id_at n parity) slot

/-- Actual endpoint lookup and actual alignment agree for every order, including a produced
tracked order. This transports physical identities, without a Z-injectivity assumption. -/
theorem aligned_priority_positions (n : Nat) (parity : TetrahedralInputParity)
    (order : List (Fin 4)) :
    (order.map (nitrileSlotAtom parity n 1)).mapM
      (writtenSlot? ((expanded parity n).writtenNeighbors (nitrileCenter parity n).1.val)) =
        some (order.map fun slot => (alignmentSlots n parity).getD slot.val 0) :=
  FamilySourceBridge.aligned_priority_positions _ _ _ (nitrileSlotAtom parity n 1)
    (slots_matching n parity) (returned_id_at n parity) order


/-- The source's actual finite matcher and physical priority order give the corrected written
positions. No identity slot alignment is assumed. -/
theorem aligned_role_positions (n : Nat) (parity : TetrahedralInputParity) :
    (prioritySlots n parity).map (fun slot => (alignmentSlots n parity).getD slot.val 0) = [1, 2, 3, 0] := by
  have matching := aligned_priority_positions n parity (prioritySlots n parity)
  have written := expanded_center_row parity n
  have distinct : ((expanded parity n).writtenNeighbors 0).Nodup := by
    rw [written]
    simp (disch := omega) [List.nodup_cons]
  have p0 := writtenSlot?_eq_some ((expanded parity n).writtenNeighbors 0) distinct 0 (n + 7)
    (by rw [written]; rfl)
  have p1 := writtenSlot?_eq_some ((expanded parity n).writtenNeighbors 0) distinct 1 1
    (by rw [written]; rfl)
  have p2 := writtenSlot?_eq_some ((expanded parity n).writtenNeighbors 0) distinct 2 2
    (by rw [written]; rfl)
  have p3 := writtenSlot?_eq_some ((expanded parity n).writtenNeighbors 0) distinct 3 (4)
    (by rw [written]; rfl)
  have physical : ((prioritySlots n parity).map (nitrileSlotAtom parity n 1)).mapM
      (writtenSlot? ((expanded parity n).writtenNeighbors 0)) = some [1, 2, 3, 0] := by
    simp only [prioritySlots, List.map_cons, List.map_nil, nitrile_role_slot_index]
    simp [List.mapM_cons, p0, p1, p2, p3]
  exact Option.some.inj (matching.symm.trans physical)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceAlignment
