import TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000










namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRoles

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource

/-- Physical ID of the atom named by an actual returned central slot. -/
noncomputable def centralSlotID (c l r : TetrahedralInputParity) (slot : Fin 4) : Nat :=
  slotAtomID (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
    1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r) slot

/-- Role labels describe physical neighbors; they do not specify priority. -/
def roleAtomID (role : Fin 4) : Nat :=
  match role.val with
  | 0 => 0
  | 1 => 2
  | 2 => 6
  | _ => 7

def roleOfAtomID (atom : Nat) : Fin 4 :=
  if atom = 0 then 0 else if atom = 2 then 1 else if atom = 6 then 2 else 3

def roleZ (role : Fin 4) : Nat :=
  match role.val with
  | 0 => 1
  | 2 => 35
  | _ => 6

noncomputable def centralRoles (c l r : TetrahedralInputParity) : Fin 4 → Fin 4 :=
  fun slot => roleOfAtomID (centralSlotID c l r slot)

private theorem roleAtomID_roleOfAtomID (atom : Nat) (member : atom ∈ [0, 2, 6, 7]) :
    roleAtomID (roleOfAtomID atom) = atom := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

private theorem roleAtomID_written_lookup (role : Fin 4) :
    ([0, 2, 6, 7] : List Nat)[role.val]? = some (roleAtomID role) := by
  fin_cases role <;> rfl

theorem central_slot_ids_perm (c l r : TetrahedralInputParity) :
    ((List.finRange 4).map (centralSlotID c l r)).Perm [0, 2, 6, 7] := by
  simpa only [centralSlotID, sourceCenter_index, raw_center_record_row] using
    source_slot_ids_perm c l r

theorem central_slot_id_member (c l r : TetrahedralInputParity) (slot : Fin 4) :
    centralSlotID c l r slot ∈ [0, 2, 6, 7] := by
  exact (central_slot_ids_perm c l r).mem_iff.mp
    (List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩)

theorem centralSlotID_injective (c l r : TetrahedralInputParity) :
    Function.Injective (centralSlotID c l r) :=
  actual_slot_ids_injective (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) 1 (sourceCenter c l r) (sourceDomain c l r)
    (source_four c l r)

theorem central_role_id (c l r : TetrahedralInputParity) (slot : Fin 4) :
    roleAtomID (centralRoles c l r slot) = centralSlotID c l r slot :=
  roleAtomID_roleOfAtomID _ (central_slot_id_member c l r slot)

theorem centralRoles_injective (c l r : TetrahedralInputParity) :
    Function.Injective (centralRoles c l r) := by
  intro first second equal
  apply centralSlotID_injective c l r
  have physical := congrArg roleAtomID equal
  simpa only [central_role_id] using physical

theorem central_arm_role (c l r : TetrahedralInputParity) (left : Bool) :
    centralRoles c l r (armSlot c l r left) = if left then 1 else 3 := by
  unfold centralRoles centralSlotID
  rw [arm_slot_index]
  cases left <;> rfl

theorem central_arm_role_iff (c l r : TetrahedralInputParity) (left : Bool)
    (slot : Fin 4) :
    centralRoles c l r slot = (if left then 1 else 3) ↔ slot = armSlot c l r left := by
  constructor
  · intro equal
    apply centralRoles_injective c l r
    exact equal.trans (central_arm_role c l r left).symm
  · rintro rfl
    exact central_arm_role c l r left

theorem raw_center_atomic_numbers (c l r : TetrahedralInputParity) :
    [0, 2, 6, 7].map (raw c l r).atomZAt = [1, 6, 35, 6] := by
  cases c <;> cases l <;> cases r <;> decide +kernel

private theorem raw_center_role_priority (c l r : TetrahedralInputParity) (role : Fin 4) :
    (raw c l r).atomZAt (roleAtomID role) = roleZ role := by
  have entry := congrArg (fun numbers : List Nat => numbers.getD role.val 0)
    (raw_center_atomic_numbers c l r)
  fin_cases role <;> simpa [roleAtomID, roleZ] using entry

/-- Atomic priority comes from the actual source atom at the returned slot. -/
theorem central_role_priority (c l r : TetrahedralInputParity) (slot : Fin 4) :
    occurrenceAtomicPriority (ownSource (raw c l r)) (sourceFrame c l r) slot =
      roleZ (centralRoles c l r slot) := by
  calc
    _ = (raw c l r).atomZAt (centralSlotID c l r slot) := by
      simpa only [centralSlotID] using source_priority_eq_raw_Z c l r slot
    _ = (raw c l r).atomZAt (roleAtomID (centralRoles c l r slot)) :=
      congrArg (raw c l r).atomZAt (central_role_id c l r slot).symm
    _ = _ := raw_center_role_priority c l r (centralRoles c l r slot)

/-- The written center row is read from the actual parsed member. -/
theorem central_written_row (c l r : TetrahedralInputParity) :
    (raw c l r).writtenNeighbors 1 = [0, 2, 6, 7] := by
  cases c <;> cases l <;> cases r <;> decide +kernel

theorem central_frame_real (c l r : TetrahedralInputParity) :
    OccurrenceRootsReal (ownSource (raw c l r)) (sourceFrame c l r) := by
  intro slot
  obtain ⟨atom, _, current, real, _⟩ := source_slot_endpoint c l r slot
  exact ⟨atom, current, real⟩

private theorem frame_returned_id_at (source : AuthoritativeChemicalInput) (fuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame fuel)
    (real : OccurrenceRootsReal source frame) (slot : Fin 4) :
    (frame.roots.map (cursorAtomID source))[slot.val]? =
      some (some ((cursorAtomID source (frame.cursorAt slot)).getD 0)) := by
  have bound : slot.val < frame.roots.length := by rw [frame.rootsLength]; exact slot.isLt
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  obtain ⟨atom, current, _⟩ := real slot
  change some ((frame.cursorAt slot).occurrence.1.node.current?.map Fin.val) =
    some (some (((frame.cursorAt slot).occurrence.1.node.current?.map Fin.val).getD 0))
  rw [current]
  rfl

theorem central_returned_id_at (c l r : TetrahedralInputParity) (slot : Fin 4) :
    ((sourceFrame c l r).roots.map (cursorAtomID (ownSource (raw c l r))))[slot.val]? =
      some (some (centralSlotID c l r slot)) := by
  simpa only [centralSlotID, slotAtomID, sourceFrame] using
    frame_returned_id_at (ownSource (raw c l r)) 1 (sourceFrame c l r)
      (central_frame_real c l r) slot

/-- The production finite matcher succeeds on actual returned central-root IDs. -/
theorem central_alignment_exists (c l r : TetrahedralInputParity) :
    ∃ slots, findSlotAlignment? ((raw c l r).writtenNeighbors 1)
      ((sourceFrame c l r).roots.map (cursorAtomID (ownSource (raw c l r)))) = some slots := by
  apply findSlotAlignment?_exists_of_perm
  · rw [central_written_row]
    rfl
  · rw [central_written_row]
    decide
  · rw [central_written_row, sourceFrame_roots]
    simpa only [finalOccurrenceRootIDs, sourceCenter_index, raw_center_record_row] using
      converted_final_root_ids_perm (raw c l r) (ownSource (raw c l r))
        (raw_semantic_conversion c l r) 1 (sourceCenter c l r) (sourceDomain c l r)

noncomputable def centralSlots (c l r : TetrahedralInputParity) : List Nat :=
  Classical.choose (central_alignment_exists c l r)

theorem central_slots_computed (c l r : TetrahedralInputParity) :
    findSlotAlignment? ((raw c l r).writtenNeighbors 1)
      ((sourceFrame c l r).roots.map (cursorAtomID (ownSource (raw c l r)))) =
        some (centralSlots c l r) := Classical.choose_spec (central_alignment_exists c l r)

theorem central_slots_matching (c l r : TetrahedralInputParity) :
    ExactSlotAlignment ((raw c l r).writtenNeighbors 1)
      ((sourceFrame c l r).roots.map (cursorAtomID (ownSource (raw c l r))))
      (centralSlots c l r) := findSlotAlignment?_sound _ _ _ (central_slots_computed c l r)

theorem central_aligned_written_lookup (c l r : TetrahedralInputParity) (slot : Fin 4) :
    ((raw c l r).writtenNeighbors 1)[(centralSlots c l r).getD slot.val 0]? =
      some (centralSlotID c l r slot) := by
  have matching := central_slots_matching c l r
  have length : (centralSlots c l r).length = 4 :=
    matching.2.2.1.length_eq.trans (List.length_range (n := 4))
  have bound : slot.val < (centralSlots c l r).length := by rw [length]; exact slot.isLt
  have slotObserved : (centralSlots c l r)[slot.val]? =
      some ((centralSlots c l r).getD slot.val 0) := by
    rw [List.getElem?_eq_getElem bound]
    exact congrArg some (List.getElem_eq_getD 0)
  have indexed := congrArg (fun ids : List (Option Nat) => ids[slot.val]?) matching.2.2.2
  dsimp only at indexed
  rw [central_returned_id_at] at indexed
  simp only [List.getElem?_map, slotObserved, Option.map_some] at indexed
  exact Option.some.inj indexed

theorem central_role_written_lookup (c l r : TetrahedralInputParity) (slot : Fin 4) :
    ((raw c l r).writtenNeighbors 1)[(centralRoles c l r slot).val]? =
      some (centralSlotID c l r slot) := by
  rw [central_written_row]
  exact (roleAtomID_written_lookup (centralRoles c l r slot)).trans
    (congrArg some (central_role_id c l r slot))

/-- Matcher output is identified by actual physical lookup, not by equating frame orders. -/
theorem central_aligned_position (c l r : TetrahedralInputParity) (slot : Fin 4) :
    (centralSlots c l r).getD slot.val 0 = (centralRoles c l r slot).val := by
  have actual := writtenSlot?_eq_some _ (central_slots_matching c l r).2.1 _ _
    (central_aligned_written_lookup c l r slot)
  have identified := writtenSlot?_eq_some _ (central_slots_matching c l r).2.1 _ _
    (central_role_written_lookup c l r slot)
  exact Option.some.inj (actual.symm.trans identified)

theorem central_order_written_positions (c l r : TetrahedralInputParity)
    (order : List (Fin 4)) :
    order.map (fun slot => (centralSlots c l r).getD slot.val 0) =
      (order.map (centralRoles c l r)).map Fin.val := by
  simp only [List.map_map, Function.comp_def, central_aligned_position]

/-- Any separately established production role order transports to actual written positions. -/
theorem central_written_positions_of_roles (c l r : TetrahedralInputParity)
    (order expectedRoles : List (Fin 4))
    (roles : order.map (centralRoles c l r) = expectedRoles) :
    order.map (fun slot => (centralSlots c l r).getD slot.val 0) =
      expectedRoles.map Fin.val := by
  rw [central_order_written_positions, roles]

end TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRoles
