import TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Unelaborated successor: actual production sorted IDs, computed written alignment, and
same-root arm labels in the internally constructed source scheduler at carrier/rule fuel 1/4.
No statement here identifies those source fuels with the runtime analysisFuel parameter. -/

namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource

private theorem frame_map_slots {α : Type*} (source : AuthoritativeChemicalInput) (fuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame fuel)
    (read : source.AromaticCanonicalRerootCursor fuel → α) :
    (List.finRange 4).map (fun slot => read (frame.cursorAt slot)) = frame.roots.map read := by
  have casted := List.ofFn_congr frame.rootsLength (fun i => read (frame.roots.get i))
  have enumerated := List.ofFn_comp' frame.roots.get read
  have allRoots := congrArg (List.map read) (List.ofFn_get frame.roots)
  simpa only [List.finRange, List.map_ofFn, AromaticCanonicalOccurrenceFourLigandFrame.cursorAt]
    using casted.symm.trans (enumerated.trans allRoots)

private theorem occurrence_center_of_node (source : AuthoritativeChemicalInput) (fuel : Nat)
    (target : source.AromaticCanonicalOccurrence fuel)
    (center : source.AromaticCanonicalTetrahedralCenter) (parent : source.AromaticCanonicalAtom)
    (node : target.1.node = OfficialCIPNode.rootFromEdge parent center.1) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center := by
  classical
  unfold aromaticCanonicalOccurrenceTetrahedralCenter?
  have real : target.1.node.provenance = .realAtom := by rw [node]; rfl
  have current : target.1.node.current? = some center.1 := by rw [node]; rfl
  rw [dif_pos real, current]
  simp only
  rw [dif_pos center.2]

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

private theorem returned_is_depth_dependency (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    source.AromaticCanonicalDepthDependency cursor.occurrence
      (source.aromaticCanonicalFinalOccurrence fuel center) := by
  have rootEq := source.aromaticCanonicalRerootChildren_root_eq
    { occurrence := source.aromaticCanonicalFinalOccurrence fuel center, previous? := none }
    cursor present
  have coordinates := SecondSphereOwnSourceOrdering.returned_direct_coordinates
    source fuel center cursor present
  refine ⟨rootEq, ?_⟩
  change 0 < cursor.occurrence.1.address.length
  rw [coordinates.2.1]
  decide

private theorem dependency_label_from_state (source : AuthoritativeChemicalInput) (fuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState fuel)
    (target : source.AromaticCanonicalOccurrence fuel)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (below : source.AromaticCanonicalDepthDependency cursor.occurrence target) :
    source.aromaticCanonicalDependencyLabel target (source.aromaticCanonicalDependencyView state target)
      cursor = state cursor.occurrence := by
  unfold aromaticCanonicalDependencyLabel
  rw [dif_pos below]
  rfl

noncomputable def armSlotID (c l r : TetrahedralInputParity) (left : Bool) (slot : Fin 4) : Nat :=
  (cursorAtomID (ownSource (raw c l r)) ((armFrame c l r left).cursorAt slot)).getD 0

theorem arm_slot_priority (c l r : TetrahedralInputParity) (left : Bool) (slot : Fin 4) :
    occurrenceAtomicPriority (ownSource (raw c l r)) (armFrame c l r left) slot =
      (raw c l r).atomZAt (armSlotID c l r left slot) := by
  obtain ⟨atom, current, _⟩ := arm_frame_real c l r left slot
  simp only [occurrenceAtomicPriority, cursorAtomicPriority, armSlotID, cursorAtomID,
    current, Option.map_some, Option.getD_some]
  exact converted_atomic_number (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) atom

theorem arm_slot_ids_perm (c l r : TetrahedralInputParity) (left : Bool) :
    ((List.finRange 4).map (armSlotID c l r left)).Perm (armWritten left) := by
  let read := fun cursor : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1 =>
    (cursorAtomID (ownSource (raw c l r)) cursor).getD 0
  have enumeratedIDs : (List.finRange 4).map (armSlotID c l r left) =
      (armFrame c l r left).roots.map read :=
    frame_map_slots (ownSource (raw c l r)) 1 (armFrame c l r left) read
  rw [enumeratedIDs, armFrame_roots]
  simpa only [List.map_map, Function.comp_def, Option.getD_some, List.map_id'] using
    (arm_roots_ids c l r left).map (fun id => id.getD 0)

def armPriorityIDs (left : Bool) : List Nat := if left then [5, 4, 1, 3] else [10, 9, 1, 8]

theorem arm_priority_ids_perm (left : Bool) :
    (armPriorityIDs left).Perm (armWritten left) := by cases left <;> decide +kernel

theorem arm_priority_ids_descending (c l r : TetrahedralInputParity) (left : Bool) :
    (armPriorityIDs left).Pairwise (fun first second =>
      (raw c l r).atomZAt second < (raw c l r).atomZAt first) := by
  cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel

/-- Actual source sorting determines the physical order uniquely; the numeric list is the
conclusion, and is never supplied as an execution or comparison hypothesis. -/
theorem arm_sorted_physical_ids (c l r : TetrahedralInputParity) (left : Bool)
    (order : List (Fin 4)) (permutation : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun first second =>
      occurrenceAtomicPriority (ownSource (raw c l r)) (armFrame c l r left) second <
        occurrenceAtomicPriority (ownSource (raw c l r)) (armFrame c l r left) first)) :
    order.map (armSlotID c l r left) = armPriorityIDs left := by
  have mappedPermutation := (permutation.map (armSlotID c l r left)).trans
    (arm_slot_ids_perm c l r left)
  have mappedDescending : (order.map (armSlotID c l r left)).Pairwise
      (fun first second => (raw c l r).atomZAt second < (raw c l r).atomZAt first) := by
    rw [List.pairwise_map]
    simpa only [arm_slot_priority] using descending
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ first second => False.elim (Nat.lt_asymm first second))
    mappedDescending (arm_priority_ids_descending c l r left)
    (mappedPermutation.trans (arm_priority_ids_perm left).symm)

noncomputable def armKeys (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :=
  Classical.choose (arm_all_views_production c l r left view)

noncomputable def armTracked (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :=
  Classical.choose (Classical.choose_spec (arm_all_views_production c l r left view))

theorem arm_production_properties (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :
    (ownSource (raw c l r)).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (armTarget c l r left) view 4 (armFrame c l r left).roots = some (armKeys c l r left view) ∧
      (ownSource (raw c l r)).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
        (armKeys c l r left view) = some (armTracked c l r left view) ∧
      (armTracked c l r left view).highestFirst.Perm (List.finRange 4) ∧
      (armTracked c l r left view).highestFirst.Pairwise (fun first second =>
        occurrenceAtomicPriority (ownSource (raw c l r)) (armFrame c l r left) second <
          occurrenceAtomicPriority (ownSource (raw c l r)) (armFrame c l r left) first) ∧
      (armTracked c l r left view).pseudoComparisons = 0 :=
  Classical.choose_spec (Classical.choose_spec (arm_all_views_production c l r left view))

theorem arm_production_physical_ids (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :
    (armTracked c l r left view).highestFirst.map (armSlotID c l r left) = armPriorityIDs left :=
  arm_sorted_physical_ids c l r left _ (arm_production_properties c l r left view).2.2.1
    (arm_production_properties c l r left view).2.2.2.1

noncomputable def armSlots (c l r : TetrahedralInputParity) (left : Bool) : List Nat :=
  Classical.choose (arm_alignment_exists c l r left)

theorem arm_slots_computed (c l r : TetrahedralInputParity) (left : Bool) :
    findSlotAlignment? ((raw c l r).writtenNeighbors (armIndex left))
      ((armFrame c l r left).roots.map (cursorAtomID (ownSource (raw c l r)))) =
        some (armSlots c l r left) := Classical.choose_spec (arm_alignment_exists c l r left)

theorem arm_slots_matching (c l r : TetrahedralInputParity) (left : Bool) :
    ExactSlotAlignment ((raw c l r).writtenNeighbors (armIndex left))
      ((armFrame c l r left).roots.map (cursorAtomID (ownSource (raw c l r))))
      (armSlots c l r left) := findSlotAlignment?_sound _ _ _ (arm_slots_computed c l r left)

theorem arm_returned_id_at (c l r : TetrahedralInputParity) (left : Bool) (slot : Fin 4) :
    ((armFrame c l r left).roots.map (cursorAtomID (ownSource (raw c l r))))[slot.val]? =
      some (some (armSlotID c l r left slot)) := by
  simpa only [armSlotID] using frame_returned_id_at (ownSource (raw c l r)) 1
    (armFrame c l r left) (arm_frame_real c l r left) slot

theorem arm_aligned_written_lookup (c l r : TetrahedralInputParity) (left : Bool) (slot : Fin 4) :
    ((raw c l r).writtenNeighbors (armIndex left))[(armSlots c l r left).getD slot.val 0]? =
      some (armSlotID c l r left slot) := by
  have matching := arm_slots_matching c l r left
  have length : (armSlots c l r left).length = 4 :=
    matching.2.2.1.length_eq.trans (List.length_range (n := 4))
  have bound : slot.val < (armSlots c l r left).length := by rw [length]; exact slot.isLt
  have slotObserved : (armSlots c l r left)[slot.val]? =
      some ((armSlots c l r left).getD slot.val 0) := by
    rw [List.getElem?_eq_getElem bound]
    exact congrArg some (List.getElem_eq_getD 0)
  have indexed := congrArg (fun ids : List (Option Nat) => ids[slot.val]?) matching.2.2.2
  dsimp only at indexed
  rw [arm_returned_id_at] at indexed
  simp only [List.getElem?_map, slotObserved, Option.map_some] at indexed
  exact Option.some.inj indexed

theorem arm_aligned_priority_positions (c l r : TetrahedralInputParity) (left : Bool)
    (order : List (Fin 4)) :
    (order.map (armSlotID c l r left)).mapM
      (writtenSlot? ((raw c l r).writtenNeighbors (armIndex left))) =
        some (order.map fun slot => (armSlots c l r left).getD slot.val 0) := by
  induction order with
  | nil => rfl
  | cons slot rest ih =>
      have recovered := writtenSlot?_eq_some _ (arm_slots_matching c l r left).2.1 _ _
        (arm_aligned_written_lookup c l r left slot)
      simp only [List.map_cons, List.mapM_cons, recovered, ih]
      rfl

theorem arm_production_written_positions (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :
    (armTracked c l r left view).highestFirst.map
      (fun slot => (armSlots c l r left).getD slot.val 0) = [3, 2, 0, 1] := by
  have matching := arm_aligned_priority_positions c l r left (armTracked c l r left view).highestFirst
  rw [arm_production_physical_ids, arm_written_row] at matching
  have lookup : (armPriorityIDs left).mapM (writtenSlot? (armWritten left)) =
      some [3, 2, 0, 1] := by cases left <;> decide +kernel
  exact Option.some.inj (matching.symm.trans lookup)

def armParity (l r : TetrahedralInputParity) (left : Bool) := if left then l else r

theorem arm_production_written_descriptor (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :
    writtenFramePriorityDescriptor (armParity l r left) (armSlots c l r left)
      (armTracked c l r left view).highestFirst = descriptorOfParity (armParity l r left) false := by
  unfold writtenFramePriorityDescriptor
  rw [arm_production_written_positions]
  rfl

def rawArmIndex (c l r : TetrahedralInputParity) (left : Bool) : Fin (raw c l r).atomCount :=
  ⟨armIndex left, by rw [raw_atom_count]; cases left <;> decide⟩

def armSpec (c l r : TetrahedralInputParity) (left : Bool) : AtomSpec :=
  ((raw c l r).atomAt? (armIndex left)).getD { element := .C, explicitHydrogens? := some 0 }

theorem arm_spec_observed (c l r : TetrahedralInputParity) (left : Bool) :
    (raw c l r).atomAt? (armIndex left) = some (armSpec c l r left) := by
  cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel

theorem arm_spec_parity (c l r : TetrahedralInputParity) (left : Bool) :
    (armSpec c l r left).tetrahedral? = some (armParity l r left) := by
  cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel

theorem arm_spec_eligible (c l r : TetrahedralInputParity) (left : Bool) :
    BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement (armSpec c l r left).element := by
  have carbon : (armSpec c l r left).element = .C := by
    cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel
  rw [carbon]
  decide

def armCenter (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).AromaticCanonicalTetrahedralCenter :=
  actualCenter (raw c l r) (raw_ordinary_source_input c l r) (rawArmIndex c l r left)
    (armSpec c l r left) (arm_spec_observed c l r left) (arm_spec_eligible c l r left)
    (by change ((raw c l r).writtenNeighbors (armIndex left)).length = 4
        rw [arm_written_row]; cases left <;> rfl)

@[simp] theorem armCenter_index (c l r : TetrahedralInputParity) (left : Bool) :
    (armCenter c l r left).1.val = armIndex left := rfl

theorem arm_center_computed (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).aromaticCanonicalOccurrenceTetrahedralCenter? (armTarget c l r left) =
      some (armCenter c l r left) := by
  apply occurrence_center_of_node (ownSource (raw c l r)) 1 (armTarget c l r left)
    (armCenter c l r left) (sourceCenter c l r).1
  have same : armAtom c l r left = (armCenter c l r left).1 := Fin.ext rfl
  simpa only [armTarget, same] using arm_cursor_node c l r left

noncomputable def armEvidence (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :
    ParserRichPriorityEvidence (ownSource (raw c l r)) 1 :=
  { slots := armSlots c l r left
    keys := armKeys c l r left view
    tracked := armTracked c l r left view
    writtenParity := armParity l r left
    raw := writtenFramePriorityDescriptor (armParity l r left) (armSlots c l r left)
      (armTracked c l r left view).highestFirst }

theorem arm_evidence_computed (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :
    constitutionParserRichPriorityEvidence? (raw c l r) (ownSource (raw c l r))
      (family_annotation_agreement c l r) (raw_written c l r) (armTarget c l r left) view 4 =
        some (armEvidence c l r left view) := by
  have aligned : findSlotAlignment? ((raw c l r).writtenNeighbors (armIndex left))
      (occurrenceRootIDs (ownSource (raw c l r)) (armFrame c l r left).roots) =
        some (armSlots c l r left) := arm_slots_computed c l r left
  simp only [constitutionParserRichPriorityEvidence?, arm_center_computed,
    Bind.bind, Option.bind, parserIndexViaConversion_val, rawWrittenLigandFrame,
    armCenter_index, arm_spec_observed, arm_spec_parity, arm_frame_returned,
    aligned, (arm_production_properties c l r left view).1,
    (arm_production_properties c l r left view).2.1, armEvidence]

theorem arm_descriptor_all_views (c l r : TetrahedralInputParity) (left : Bool)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView (armTarget c l r left)) :
    constitutionParserRichDescriptor? (raw c l r) (ownSource (raw c l r))
      (family_annotation_agreement c l r) (raw_written c l r) (armTarget c l r left) view 4 =
        some (.chiral (descriptorOfParity (armParity l r left) false)) := by
  unfold constitutionParserRichDescriptor?
  rw [arm_evidence_computed]
  change some (classifyTetrahedralRSPseudo
    (writtenFramePriorityDescriptor (armParity l r left) (armSlots c l r left)
      (armTracked c l r left view).highestFirst)
    (armTracked c l r left view).pseudoComparisons) = _
  rw [arm_production_written_descriptor, (arm_production_properties c l r left view).2.2.2.2]
  rfl

noncomputable def familyScheduledState (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).AromaticCanonicalAuxiliaryState 1 :=
  constitutionParserRichScheduledState (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) 1 4

theorem arm_scheduled_descriptor (c l r : TetrahedralInputParity) (left : Bool) :
    familyScheduledState c l r (armTarget c l r left) =
      some (.chiral (descriptorOfParity (armParity l r left) false)) := by
  have model := constitutionParserRichScheduledState_cipModel (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) 1 4
  have evaluates := constitutionParserRichModel_evaluates (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) (familyScheduledState c l r)
    model (armTarget c l r left)
  exact evaluates.symm.trans (arm_descriptor_all_views c l r left _)

theorem arm_scheduled_meaning (c l r : TetrahedralInputParity) (left : Bool) :
    ConstitutionParserRichDescriptorMeaning (raw c l r) (ownSource (raw c l r))
      (family_annotation_agreement c l r) (raw_written c l r) (armTarget c l r left)
      ((ownSource (raw c l r)).aromaticCanonicalDependencyView
        (familyScheduledState c l r) (armTarget c l r left)) 4
      (.chiral (descriptorOfParity (armParity l r left) false)) :=
  constitutionParserRichDescriptor?_sound (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) (armTarget c l r left) _ 4 _
    (arm_descriptor_all_views c l r left _)

/-- The label consumer and both arm labels belong to one root, with a strict depth edge. -/
theorem arm_is_central_dependency (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).AromaticCanonicalDepthDependency (armTarget c l r left)
      ((ownSource (raw c l r)).aromaticCanonicalFinalOccurrence 1 (sourceCenter c l r)) := by
  simpa only [armTarget] using returned_is_depth_dependency (ownSource (raw c l r)) 1
    (sourceCenter c l r) (armCursor c l r left) (arm_cursor_present c l r left)

/-- The production central dependency view reads the arm's actual scheduled source label. -/
theorem central_scheduled_arm_label (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).aromaticCanonicalDependencyLabel
      ((ownSource (raw c l r)).aromaticCanonicalFinalOccurrence 1 (sourceCenter c l r))
      ((ownSource (raw c l r)).aromaticCanonicalDependencyView (familyScheduledState c l r)
        ((ownSource (raw c l r)).aromaticCanonicalFinalOccurrence 1 (sourceCenter c l r)))
      (armCursor c l r left) =
        some (.chiral (descriptorOfParity (armParity l r left) false)) := by
  have below : (ownSource (raw c l r)).AromaticCanonicalDepthDependency
      (armCursor c l r left).occurrence
      ((ownSource (raw c l r)).aromaticCanonicalFinalOccurrence 1 (sourceCenter c l r)) := by
    simpa only [armTarget] using arm_is_central_dependency c l r left
  rw [dependency_label_from_state (ownSource (raw c l r)) 1 (familyScheduledState c l r)
    _ (armCursor c l r left) below]
  simpa only [armTarget] using arm_scheduled_descriptor c l r left

end TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor
