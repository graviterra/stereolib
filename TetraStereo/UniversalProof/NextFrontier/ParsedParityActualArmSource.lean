import TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceArmCoordinates

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000







namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceArmCoordinates

/-! Abstract frame projection lemmas keep the parsed family opaque during elaboration. -/

private theorem frame_cursor_member (source : AuthoritativeChemicalInput) (fuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame fuel) (slot : Fin 4) :
    frame.cursorAt slot ∈ frame.roots := List.get_mem _ _

private noncomputable def fourFrame (source : AuthoritativeChemicalInput) (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor fuel)) (four : roots.length = 4) :
    source.AromaticCanonicalOccurrenceFourLigandFrame fuel := ⟨roots, four⟩

private theorem fourFrame_roots (source : AuthoritativeChemicalInput) (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor fuel)) (four : roots.length = 4) :
    (fourFrame source fuel roots four).roots = roots := rfl

private theorem frame_real_of_roots (source : AuthoritativeChemicalInput) (fuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame fuel)
    (real : ∀ child ∈ frame.roots, ∃ atom : source.AromaticCanonicalAtom,
      child.occurrence.1.node.current? = some atom ∧
      child.occurrence.1.node.provenance = .realAtom) : OccurrenceRootsReal source frame := by
  intro slot
  exact real (frame.cursorAt slot) (frame_cursor_member source fuel frame slot)

private theorem frame_priority_injective_of_nodup (source : AuthoritativeChemicalInput) (fuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame fuel)
    (distinct : (frame.roots.map (cursorAtomicPriority source)).Nodup) :
    Function.Injective (occurrenceAtomicPriority source frame) := by
  intro first second equal
  have count : (frame.roots.map (cursorAtomicPriority source)).length = 4 := by
    simp only [List.length_map, frame.rootsLength]
  have equalGet : (frame.roots.map (cursorAtomicPriority source)).get (Fin.cast count.symm first) =
      (frame.roots.map (cursorAtomicPriority source)).get (Fin.cast count.symm second) := by
    simpa only [occurrenceAtomicPriority, AromaticCanonicalOccurrenceFourLigandFrame.cursorAt,
      List.get_eq_getElem, List.getElem_map] using equal
  exact Fin.ext (congrArg
    (fun i : Fin (frame.roots.map (cursorAtomicPriority source)).length => i.val)
    (distinct.injective_get equalGet))

private theorem actual_slot_node_of_id (rawMol : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : rawMol.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceRecordDomain rawMol center.1.val)
    (four : (recordNeighbors rawMol center.1.val).length = 4)
    (slot : Fin 4) (endpoint : source.AromaticCanonicalAtom)
    (identifier : slotAtomID rawMol source converted fuel center domain four slot = endpoint.val) :
    ((actualFrame rawMol source converted fuel center domain four).cursorAt slot).occurrence.1.node =
      OfficialCIPNode.rootFromEdge center.1 endpoint := by
  obtain ⟨neighbor, _, node⟩ := converted_final_cursor_real_root rawMol source converted fuel
    center domain ((actualFrame rawMol source converted fuel center domain four).cursorAt slot)
    (List.get_mem _ _)
  have same : neighbor = endpoint := by
    apply Fin.ext
    simpa only [slotAtomID, cursorAtomID, node, OfficialCIPNode.rootFromEdge,
      Option.map_some, Option.getD_some] using identifier
  exact node.trans (congrArg (OfficialCIPNode.rootFromEdge center.1) same)

/-! Reopening a direct child restores the actual parent occurrence. -/

theorem returned_parent_frames (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    source.aromaticCanonicalCarrierParentFrames (fuel := fuel) cursor.occurrence.1 =
      [(source.aromaticCanonicalFinalOccurrence fuel center).1] := by
  classical
  have coordinates := returned_direct_coordinates source fuel center cursor present
  obtain ⟨slot, address⟩ := List.length_eq_one_iff.mp coordinates.2.1
  have rootEq := source.aromaticCanonicalRerootChildren_root_eq
    { occurrence := source.aromaticCanonicalFinalOccurrence fuel center, previous? := none }
    cursor present
  change cursor.occurrence.1.root = center.1 at rootEq
  apply List.perm_singleton.mp
  apply (List.perm_ext_iff_of_nodup
    ((source.aromaticCanonicalOccurrences_nodup fuel).filter _) (by simp)).mpr
  intro candidate
  rw [List.mem_singleton]
  constructor
  · intro member
    rw [List.mem_filter] at member
    have conditions := member.2
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    have addressNil : candidate.address = [] := by
      apply List.eq_nil_of_length_eq_zero
      have one := coordinates.2.1
      omega
    have derived := (source.mem_aromaticCanonicalOccurrences_iff fuel candidate).mp member.1
    have atCenter : source.DeclarativeAromaticCanonicalOccurrenceSubtree
        center.1 [] (fuel + 1) (OfficialCIPNode.root center.1) candidate := by
      simpa [DeclarativeAromaticCanonicalOccurrence,
        DeclarativeAromaticCanonicalOccurrenceAtAtom, conditions.1.1, rootEq] using derived
    exact source.declarativeAromaticCanonicalOccurrenceSubtree_eq_root_of_address_eq
      atCenter addressNil
  · rintro rfl
    rw [List.mem_filter]
    refine ⟨(source.aromaticCanonicalFinalOccurrence fuel center).2, ?_⟩
    simp [rootEq, address, aromaticCanonicalFinalOccurrence]

noncomputable def reopenedRoots (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :=
  source.aromaticCanonicalRerootChildren
    { occurrence := cursor.occurrence, previous? := none }

theorem reopened_roots_returned (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    source.aromaticCanonicalOccurrenceLigandFrame? cursor.occurrence =
      some (reopenedRoots source cursor) := rfl

theorem reopened_nodes_perm (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 1)
    (present : cursor ∈ finalOccurrenceRoots source 1 center)
    (real : cursor.occurrence.1.node.provenance = .realAtom) :
    ((reopenedRoots source cursor).map (fun child => child.occurrence.1.node)).Perm
      (OfficialCIPNode.root center.1 ::
        source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount cursor.occurrence.1.node) := by
  have exactFrames := (source.aromaticCanonicalRerootChildren_sound
    { occurrence := cursor.occurrence, previous? := none }).1
  have frameEq : (reopenedRoots source cursor).map (fun child => child.occurrence.1) =
      (source.aromaticCanonicalFinalOccurrence 1 center).1 ::
        source.aromaticCanonicalCarrierOutwardChildFrames (fuel := 1) cursor.occurrence.1 := by
    simpa [reopenedRoots, intendedAromaticCanonicalRerootChildFrames,
      OfficialCIPNode.isDuplicateLeaf, real, OfficialCIPNodeProvenance.isDuplicateLeaf,
      aromaticCanonicalRerootNeighborFrames, returned_parent_frames source 1 center cursor present]
      using exactFrames
  have outward := (returned_one_outward_frames_perm source center cursor present).map
    (fun frame => frame.node)
  have direct : (directSecondFrames source cursor).map (fun frame => frame.node) =
      source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount cursor.occurrence.1.node := by
    unfold directSecondFrames
    rw [List.map_map]
    exact List.zipIdx_map_fst 0 _
  rw [direct] at outward
  have nodeEq := congrArg (List.map (fun frame => frame.node)) frameEq
  simp only [List.map_map, Function.comp_def] at nodeEq
  rw [nodeEq]
  exact List.Perm.cons _ outward

/-! Physical family instantiation. -/

def armIndex (left : Bool) : Nat := if left then 2 else 7
def armWritten (left : Bool) : List Nat := if left then [1, 3, 4, 5] else [1, 8, 9, 10]

noncomputable def armSlot (c l r : TetrahedralInputParity) (left : Bool) : Fin 4 :=
  if left then leftArmSlot c l r else rightArmSlot c l r

noncomputable def armCursor (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1 :=
  (sourceFrame c l r).cursorAt (armSlot c l r left)

noncomputable def armTarget (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).AromaticCanonicalOccurrence 1 :=
  (armCursor c l r left).occurrence

def armAtom (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).AromaticCanonicalAtom :=
  sourceRoleAtom c l r ⟨armIndex left, by cases left <;> decide⟩

@[simp] theorem armAtom_index (c l r : TetrahedralInputParity) (left : Bool) :
    (armAtom c l r left).val = armIndex left := rfl

theorem arm_slot_index (c l r : TetrahedralInputParity) (left : Bool) :
    slotAtomID (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)
      1 (sourceCenter c l r) (sourceDomain c l r) (source_four c l r)
      (armSlot c l r left) = armIndex left := by
  cases left
  · exact rightArmSlot_index c l r
  · exact leftArmSlot_index c l r

theorem arm_cursor_present (c l r : TetrahedralInputParity) (left : Bool) :
    armCursor c l r left ∈ finalOccurrenceRoots (ownSource (raw c l r)) 1
      (sourceCenter c l r) := by
  have present := frame_cursor_member (ownSource (raw c l r)) 1 (sourceFrame c l r)
    (armSlot c l r left)
  rw [sourceFrame_roots] at present
  exact present

theorem arm_cursor_node (c l r : TetrahedralInputParity) (left : Bool) :
    (armCursor c l r left).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (sourceCenter c l r).1 (armAtom c l r left) := by
  have node := actual_slot_node_of_id (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) 1 (sourceCenter c l r) (sourceDomain c l r)
    (source_four c l r) (armSlot c l r left) (armAtom c l r left)
    (by simpa only [armAtom_index] using arm_slot_index c l r left)
  simpa only [armCursor, sourceFrame] using node

theorem arm_record_row (c l r : TetrahedralInputParity) (left : Bool) :
    recordNeighbors (raw c l r) (armIndex left) = armWritten left := by
  cases left
  · exact raw_right_arm_record_row c l r
  · exact raw_left_arm_record_row c l r

theorem arm_written_row (c l r : TetrahedralInputParity) (left : Bool) :
    (raw c l r).writtenNeighbors (armIndex left) = armWritten left := by
  cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel

def armDomain (c l r : TetrahedralInputParity) (left : Bool) :
    SourceRecordDomain (raw c l r) (armAtom c l r left).val where
  well := raw_well c l r
  rowDistinct := by rw [armAtom_index, arm_record_row]; cases left <;> decide
  incidentSingle := fun bond member _ => raw_single c l r bond member

noncomputable def armRoots (c l r : TetrahedralInputParity) (left : Bool) :
    List ((ownSource (raw c l r)).AromaticCanonicalRerootCursor 1) :=
  reopenedRoots (ownSource (raw c l r)) (armCursor c l r left)

theorem arm_roots_nodes (c l r : TetrahedralInputParity) (left : Bool) :
    ((armRoots c l r left).map (fun child => child.occurrence.1.node)).Perm
      (OfficialCIPNode.root (sourceCenter c l r).1 ::
        (ownSource (raw c l r)).molecule.aromaticCanonicalOfficialCIPChildrenAt
          (ownSource (raw c l r)).molecule.atomCount
          (OfficialCIPNode.rootFromEdge (sourceCenter c l r).1 (armAtom c l r left))) := by
  have nodes := reopened_nodes_perm (ownSource (raw c l r)) (sourceCenter c l r)
    (armCursor c l r left) (arm_cursor_present c l r left)
    (by rw [arm_cursor_node]; rfl)
  simpa only [armRoots, arm_cursor_node] using nodes

theorem arm_roots_ids (c l r : TetrahedralInputParity) (left : Bool) :
    ((armRoots c l r left).map (cursorAtomID (ownSource (raw c l r)))).Perm
      ((armWritten left).map some) := by
  have nodes := (arm_roots_nodes c l r left).map
    (fun node => node.current?.map Fin.val)
  have children := converted_official_edge_ids_perm (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) (armAtom c l r left) (armDomain c l r left)
    (sourceCenter c l r).1
  have joined := nodes.trans (List.Perm.cons (some (sourceCenter c l r).1.val) children)
  have joined' : ((armRoots c l r left).map (cursorAtomID (ownSource (raw c l r)))).Perm
      (some 1 :: (((armWritten left).filter (fun atom => !(atom == 1))).map some)) := by
    simpa only [List.map_map, Function.comp_def, List.map_cons, cursorAtomID, OfficialCIPNode.root,
      Option.map_some, armAtom_index, arm_record_row, sourceCenter_index] using joined
  have row : some 1 :: (((armWritten left).filter (fun atom => !(atom == 1))).map some) =
      (armWritten left).map some := by cases left <;> rfl
  rw [row] at joined'
  exact joined'

theorem arm_root_real (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armRoots c l r left) :
    ∃ atom : (ownSource (raw c l r)).AromaticCanonicalAtom,
      child.occurrence.1.node.current? = some atom ∧
      child.occurrence.1.node.provenance = .realAtom := by
  have member := (arm_roots_nodes c l r left).mem_iff.mp
    (List.mem_map.mpr ⟨child, present, rfl⟩)
  rcases List.mem_cons.mp member with parent | outward
  · exact ⟨(sourceCenter c l r).1, by rw [parent]; rfl, by rw [parent]; rfl⟩
  · rw [converted_official_edge_children (raw c l r) (ownSource (raw c l r))
      (raw_semantic_conversion c l r) (armAtom c l r left) (armDomain c l r left)
      (sourceCenter c l r).1] at outward
    obtain ⟨neighbor, retained, nodeEq⟩ := List.mem_map.mp outward
    have physical : neighbor.val ∈ recordNeighbors (raw c l r) (armAtom c l r left).val :=
      of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp retained).1).2
    have notParent : neighbor ≠ (sourceCenter c l r).1 := by
      simpa using (List.mem_filter.mp retained).2
    have notArm : neighbor ≠ armAtom c l r left := by
      intro same
      exact (converted_neighbor_bound (raw c l r) (ownSource (raw c l r))
        (raw_semantic_conversion c l r) (armAtom c l r left) (armDomain c l r left)
        neighbor.val physical).2 (congrArg Fin.val same)
    refine ⟨neighbor, ?_, ?_⟩
    · rw [← nodeEq]; rfl
    · rw [← nodeEq]
      simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
        OfficialCIPNode.rootFromEdge, notArm, notParent]

theorem arm_roots_length (c l r : TetrahedralInputParity) (left : Bool) :
    (armRoots c l r left).length = 4 := by
  have count := (arm_roots_ids c l r left).length_eq
  simpa only [List.length_map] using count.trans (by cases left <;> rfl)

noncomputable def armFrame (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).AromaticCanonicalOccurrenceFourLigandFrame 1 :=
  fourFrame (ownSource (raw c l r)) 1 (armRoots c l r left) (arm_roots_length c l r left)

theorem armFrame_roots (c l r : TetrahedralInputParity) (left : Bool) :
    (armFrame c l r left).roots = armRoots c l r left := by
  simpa only [armFrame] using fourFrame_roots (ownSource (raw c l r)) 1
    (armRoots c l r left) (arm_roots_length c l r left)

theorem arm_frame_returned (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).aromaticCanonicalOccurrenceLigandFrame? (armTarget c l r left) =
      some (armFrame c l r left).roots := by
  rw [armFrame_roots]
  simpa only [armTarget, armRoots] using
    reopened_roots_returned (ownSource (raw c l r)) (armCursor c l r left)

theorem arm_frame_real (c l r : TetrahedralInputParity) (left : Bool) :
    OccurrenceRootsReal (ownSource (raw c l r)) (armFrame c l r left) := by
  apply frame_real_of_roots (ownSource (raw c l r)) 1 (armFrame c l r left)
  intro child present
  rw [armFrame_roots] at present
  exact arm_root_real c l r left child present

theorem arm_atomic_numbers_distinct (c l r : TetrahedralInputParity) (left : Bool) :
    ((armWritten left).map (raw c l r).atomZAt).Nodup := by
  cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel

theorem arm_priority_injective (c l r : TetrahedralInputParity) (left : Bool) :
    Function.Injective (occurrenceAtomicPriority (ownSource (raw c l r)) (armFrame c l r left)) := by
  let source := ownSource (raw c l r)
  have priorities : (armRoots c l r left).map (cursorAtomicPriority source) =
      ((armRoots c l r left).map (cursorAtomID source)).map
        (fun atom => (raw c l r).atomZAt (atom.getD 0)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro child member
    obtain ⟨atom, current, _⟩ := arm_root_real c l r left child member
    simp only [cursorAtomicPriority, cursorAtomID, current, Option.map_some, Option.getD_some,
      Function.comp_def]
    exact converted_atomic_number (raw c l r) source (raw_semantic_conversion c l r) atom
  have permutation := (arm_roots_ids c l r left).map
    (fun atom => (raw c l r).atomZAt (atom.getD 0))
  rw [← priorities] at permutation
  apply frame_priority_injective_of_nodup source 1 (armFrame c l r left)
  rw [armFrame_roots]
  exact permutation.nodup_iff.mpr (by
    simpa only [List.map_map, Function.comp_def, Option.getD_some] using
      arm_atomic_numbers_distinct c l r left)

/-- The actual finite source matcher succeeds on the actual returned arm-root IDs. -/
theorem arm_alignment_exists (c l r : TetrahedralInputParity) (left : Bool) :
    ∃ slots, findSlotAlignment? ((raw c l r).writtenNeighbors (armIndex left))
      ((armFrame c l r left).roots.map (cursorAtomID (ownSource (raw c l r)))) = some slots := by
  apply findSlotAlignment?_exists_of_perm
  · rw [arm_written_row]; cases left <;> rfl
  · rw [arm_written_row]; cases left <;> decide
  · rw [arm_written_row]
    rw [armFrame_roots]
    exact arm_roots_ids c l r left

/-- For every genuine dependency view, production constructs and safely sorts actual source
keys at rule fuel four. Atomic separation occurs inside each arm, not between the central
carbon arms. No source-key, callback, ranking or desired descriptor premise is supplied. -/
theorem arm_all_views_production (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :
    ∃ keys tracked,
      (ownSource (raw c l r)).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (armTarget c l r left) view 4 (armFrame c l r left).roots = some keys ∧
      (ownSource (raw c l r)).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
        keys = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun first second =>
        occurrenceAtomicPriority (ownSource (raw c l r)) (armFrame c l r left) second <
          occurrenceAtomicPriority (ownSource (raw c l r)) (armFrame c l r left) first) ∧
      tracked.pseudoComparisons = 0 := by
  exact exists_occurrence_production_keys_and_safe_order (ownSource (raw c l r))
    (armTarget c l r left) view (armFrame c l r left) (arm_frame_returned c l r left)
    (arm_frame_real c l r left) (arm_priority_injective c l r left)
    (actual_source_no_double (raw c l r) (raw_ordinary_source_input c l r))

end TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
