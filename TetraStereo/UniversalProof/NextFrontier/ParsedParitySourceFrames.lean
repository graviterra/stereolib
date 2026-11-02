import TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceIntake
import TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000








namespace TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
  (SourceRecordDomain actualFrame slotAtomID actual_slot_endpoint actual_slot_ids_perm
   actual_returned_four_roots actual_priority_eq_raw_Z converted_final_cursor_real_root)

/-! ## 1. Exact written rows, from the actual parser -/

/-- The actual center (atom 1) has written bond records `[0,2,6,7]`. -/
theorem raw_center_record_row (c l r : TetrahedralInputParity) :
    recordNeighbors (raw c l r) 1 = [0, 2, 6, 7] := by
  cases c <;> cases l <;> cases r <;> decide +kernel

/-- The actual left arm (atom 2) has written bond records `[1,3,4,5]`. -/
theorem raw_left_arm_record_row (c l r : TetrahedralInputParity) :
    recordNeighbors (raw c l r) 2 = [1, 3, 4, 5] := by
  cases c <;> cases l <;> cases r <;> decide +kernel

/-- The actual right arm (atom 7) has written bond records `[1,8,9,10]`. -/
theorem raw_right_arm_record_row (c l r : TetrahedralInputParity) :
    recordNeighbors (raw c l r) 7 = [1, 8, 9, 10] := by
  cases c <;> cases l <;> cases r <;> decide +kernel

/-! ## 2. Physical center spec and the actual source center -/

/-- The actual parsed atom-1 spec, read back with the fail-closed shape fallback. -/
def centerSpec (c l r : TetrahedralInputParity) : AtomSpec :=
  ((raw c l r).atomAt? 1).getD { element := .C, explicitHydrogens? := some 0 }

/-- The actual parser returns the center spec at atom 1. -/
theorem centerSpec_observed (c l r : TetrahedralInputParity) :
    (raw c l r).atomAt? 1 = some (centerSpec c l r) := by
  cases observed : (raw c l r).atomAt? 1 with
  | none =>
      have parity := raw_center_parity c l r
      rw [observed] at parity
      simp at parity
  | some spec => simp [centerSpec, observed]

/-- The actual center spec is carbon. -/
theorem centerSpec_element (c l r : TetrahedralInputParity) :
    (centerSpec c l r).element = .C := by
  cases c <;> cases l <;> cases r <;> decide +kernel

/-- The actual center spec carries exactly the chosen center parity. -/
theorem centerSpec_tetrahedral (c l r : TetrahedralInputParity) :
    (centerSpec c l r).tetrahedral? = some c := by
  cases c <;> cases l <;> cases r <;> decide +kernel

/-- The actual center spec is in the connectivity-only tetrahedral element scope. -/
theorem centerSpec_eligible (c l r : TetrahedralInputParity) :
    BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement (centerSpec c l r).element := by
  rw [centerSpec_element]
  decide

/-- The atom-1 index, bounded by the actual parsed atom count. -/
def sourceAtom (c l r : TetrahedralInputParity) : Fin (raw c l r).atomCount :=
  ⟨1, by rw [raw_atom_count c l r]; decide +kernel⟩

/-- The actual source tetrahedral center at atom 1, constructed through the existing
parser-to-source converter. No separately chosen source molecule is used. -/
def sourceCenter (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).AromaticCanonicalTetrahedralCenter :=
  actualCenter (raw c l r) (raw_ordinary_source_input c l r) (sourceAtom c l r)
    (centerSpec c l r) (centerSpec_observed c l r) (centerSpec_eligible c l r)
    ((raw_written_degree c l r).1)

/-- The actual source center sits at physical atom 1. -/
@[simp] theorem sourceCenter_index (c l r : TetrahedralInputParity) :
    (sourceCenter c l r).1.val = 1 := rfl

/-! ## 3. Physical record domain and the exact four-record count -/

theorem raw_center_record_nodup (c l r : TetrahedralInputParity) :
    (recordNeighbors (raw c l r) 1).Nodup := by
  rw [raw_center_record_row]
  decide

/-- The independent source record domain at the actual center: physically well-formed,
row-distinct and single-incident. -/
def sourceDomain (c l r : TetrahedralInputParity) :
    SourceRecordDomain (raw c l r) 1 where
  well := raw_well c l r
  rowDistinct := raw_center_record_nodup c l r
  incidentSingle := fun bond member _ => raw_single c l r bond member

theorem source_four (c l r : TetrahedralInputParity) :
    (recordNeighbors (raw c l r) 1).length = 4 := by
  rw [raw_center_record_row]
  decide

/-! ## 4. The actual successful source frame, root at the center, depth one -/

/-- The parser-to-source semantic conversion at the actual parsed molecule. -/
theorem raw_semantic_conversion (c l r : TetrahedralInputParity) :
    (raw c l r).toSemanticMolecule? = some (ownSource (raw c l r)).molecule :=
  (family_annotation_agreement c l r).1

/-- The actual returned four-ligand source frame at carrier depth one, rooted at the
center. The arms 2 and 7 are occurrences **of this one root**, not separate roots. -/
noncomputable def sourceFrame (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).AromaticCanonicalOccurrenceFourLigandFrame 1 :=
  actualFrame (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
    1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r)

/-! Abstract projection lemmas prevent the concrete parser/converter from being
normalized while elaborating frame projections. No family computation is changed. -/

private theorem actual_frame_roots (rawMol : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : rawMol.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceRecordDomain rawMol center.1.val)
    (four : (recordNeighbors rawMol center.1.val).length = 4) :
    (actualFrame rawMol source converted fuel center domain four).roots =
      finalOccurrenceRoots source fuel center := rfl

private theorem actual_frame_returned (rawMol : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : rawMol.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceRecordDomain rawMol center.1.val)
    (four : (recordNeighbors rawMol center.1.val).length = 4) :
    source.aromaticCanonicalOccurrenceLigandFrame?
        (source.aromaticCanonicalFinalOccurrence fuel center) =
      some (actualFrame rawMol source converted fuel center domain four).roots ∧
    (actualFrame rawMol source converted fuel center domain four).roots.length = 4 := by
  rw [actual_frame_roots]
  exact actual_returned_four_roots rawMol source converted fuel center domain four

private theorem frame_cursor_mem (source : AuthoritativeChemicalInput) (fuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame fuel) (slot : Fin 4) :
    frame.cursorAt slot ∈ frame.roots := List.get_mem _ _

/-- The actual returned source frame is the center-rooted final occurrence's frame, and it
has exactly four roots. -/
theorem source_returned_four_roots (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).aromaticCanonicalOccurrenceLigandFrame?
        ((ownSource (raw c l r)).aromaticCanonicalFinalOccurrence 1 (sourceCenter c l r)) =
      some (sourceFrame c l r).roots ∧
    (sourceFrame c l r).roots.length = 4 := by
  simpa only [sourceFrame] using
    actual_frame_returned (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
      1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r)

/-- The frame roots are exactly the center-rooted returned occurrence roots. -/
theorem sourceFrame_roots (c l r : TetrahedralInputParity) :
    (sourceFrame c l r).roots =
      finalOccurrenceRoots (ownSource (raw c l r)) 1 (sourceCenter c l r) := by
  simpa only [sourceFrame] using
    actual_frame_roots (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
      1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r)

/-! ## 5. Returned source frame IDs, written slot matcher, and root nodes -/

/-- Every one of the four frame slots names a physical written neighbour of the actual
center. This endpoint statement does not assert production priority sorting. -/
theorem source_slot_endpoint (c l r : TetrahedralInputParity) (slot : Fin 4) :
    ∃ atom : (ownSource (raw c l r)).AromaticCanonicalAtom,
      atom.val ∈ recordNeighbors (raw c l r) (sourceCenter c l r).1.val ∧
      ((sourceFrame c l r).cursorAt slot).occurrence.1.node.current? = some atom ∧
      ((sourceFrame c l r).cursorAt slot).occurrence.1.node.provenance = .realAtom ∧
      slotAtomID (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
        1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r) slot = atom.val := by
  simpa only [sourceFrame] using
    actual_slot_endpoint (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
      1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r) slot

/-- The actual returned source frame IDs are a permutation of the physical written
records of the center. -/
theorem source_slot_ids_perm (c l r : TetrahedralInputParity) :
    ((List.finRange 4).map (slotAtomID (raw c l r) (ownSource (raw c l r))
        (raw_semantic_conversion c l r) 1 (sourceCenter c l r) (sourceDomain c l r)
        (source_four c l r))).Perm (recordNeighbors (raw c l r) (sourceCenter c l r).1.val) :=
  actual_slot_ids_perm (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
    1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r)

/-- Every physical written record of the actual center is realised by an actual returned
source frame slot. -/
theorem source_slot_id_exists (c l r : TetrahedralInputParity) (offset : Nat)
    (member : offset ∈ recordNeighbors (raw c l r) (sourceCenter c l r).1.val) :
    ∃ slot : Fin 4, slotAtomID (raw c l r) (ownSource (raw c l r))
        (raw_semantic_conversion c l r) 1 (sourceCenter c l r) (sourceDomain c l r)
        (source_four c l r) slot = offset := by
  have present := (source_slot_ids_perm c l r).mem_iff.mpr member
  obtain ⟨slot, _, equal⟩ := List.mem_map.mp present
  exact ⟨slot, equal⟩

/-- Each arm is realised inside the SAME center-rooted frame, and its returned node is the
center-to-arm `rootFromEdge` node (not a separate arm root). -/
theorem source_slot_root_node (c l r : TetrahedralInputParity) (slot : Fin 4) :
    ∃ neighbor : (ownSource (raw c l r)).AromaticCanonicalAtom,
      neighbor.val ∈ recordNeighbors (raw c l r) (sourceCenter c l r).1.val ∧
      ((sourceFrame c l r).cursorAt slot).occurrence.1.node =
        OfficialCIPNode.rootFromEdge (sourceCenter c l r).1 neighbor := by
  have present := frame_cursor_mem (ownSource (raw c l r)) 1 (sourceFrame c l r) slot
  rw [sourceFrame_roots] at present
  exact converted_final_cursor_real_root (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) 1 (sourceCenter c l r) (sourceDomain c l r)
    ((sourceFrame c l r).cursorAt slot) present

/-! ## 6. Kept-separate arm labels (left arm = atom 2, right arm = atom 7) -/

/-- Every written record of the center is realised by a returned frame slot. -/
noncomputable def sourceRoleSlot (c l r : TetrahedralInputParity) (offset : Nat)
    (member : offset ∈ [2, 7]) : Fin 4 :=
  Classical.choose (source_slot_id_exists c l r offset (by
    rw [sourceCenter_index, raw_center_record_row]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp))

theorem sourceRoleSlot_index (c l r : TetrahedralInputParity) (offset : Nat)
    (member : offset ∈ [2, 7]) :
    slotAtomID (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
      1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r)
      (sourceRoleSlot c l r offset member) = offset :=
  Classical.choose_spec (source_slot_id_exists c l r offset (by
    rw [sourceCenter_index, raw_center_record_row]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp))

/-- The actual returned frame slot of the LEFT arm (physical atom 2). -/
noncomputable def leftArmSlot (c l r : TetrahedralInputParity) : Fin 4 :=
  sourceRoleSlot c l r 2 (by simp)

/-- The actual returned frame slot of the RIGHT arm (physical atom 7). -/
noncomputable def rightArmSlot (c l r : TetrahedralInputParity) : Fin 4 :=
  sourceRoleSlot c l r 7 (by simp)

theorem leftArmSlot_index (c l r : TetrahedralInputParity) :
    slotAtomID (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
      1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r)
      (leftArmSlot c l r) = 2 :=
  sourceRoleSlot_index c l r 2 (by simp)

theorem rightArmSlot_index (c l r : TetrahedralInputParity) :
    slotAtomID (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
      1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r)
      (rightArmSlot c l r) = 7 :=
  sourceRoleSlot_index c l r 7 (by simp)

/-- The two arm slots are distinct, so the left/right view labels cannot be conflated. -/
theorem leftArmSlot_ne_rightArmSlot (c l r : TetrahedralInputParity) :
    leftArmSlot c l r ≠ rightArmSlot c l r := by
  intro equal
  have indices := congrArg (slotAtomID (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) 1 (sourceCenter c l r) (sourceDomain c l r)
    (source_four c l r)) equal
  rw [leftArmSlot_index, rightArmSlot_index] at indices
  exact absurd indices (by decide)

/-! ## 7. Exact computed alignment (priority ↔ physical atomic number) -/

/-- Every frame slot's source atomic priority is the physical atomic number of the atom its
returned ID names. -/
theorem source_priority_eq_raw_Z (c l r : TetrahedralInputParity) (slot : Fin 4) :
    occurrenceAtomicPriority (ownSource (raw c l r)) (sourceFrame c l r) slot =
      (raw c l r).atomZAt (slotAtomID (raw c l r) (ownSource (raw c l r))
        (raw_semantic_conversion c l r) 1 (sourceCenter c l r) (sourceDomain c l r)
        (source_four c l r) slot) :=
  actual_priority_eq_raw_Z (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
    1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r) slot

/-- Left-arm aligned priority. -/
theorem leftArm_priority (c l r : TetrahedralInputParity) :
    occurrenceAtomicPriority (ownSource (raw c l r)) (sourceFrame c l r) (leftArmSlot c l r) =
      (raw c l r).atomZAt 2 := by
  rw [source_priority_eq_raw_Z c l r (leftArmSlot c l r), leftArmSlot_index]

/-- Right-arm aligned priority. -/
theorem rightArm_priority (c l r : TetrahedralInputParity) :
    occurrenceAtomicPriority (ownSource (raw c l r)) (sourceFrame c l r) (rightArmSlot c l r) =
      (raw c l r).atomZAt 7 := by
  rw [source_priority_eq_raw_Z c l r (rightArmSlot c l r), rightArmSlot_index]

end TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
