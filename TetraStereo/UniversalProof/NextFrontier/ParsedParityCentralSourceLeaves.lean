import TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Proposed central-source prerequisites. Every leaf and model label is derived from the
actual parsed family's carrier. This file supplies neither a desired central fact nor a
caller-provided environment. It is not accepted until the bounded gate succeeds. -/

namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceArmCoordinates
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor

private theorem occurrence_center_none_of_ineligible (source : AuthoritativeChemicalInput)
    (fuel : Nat) (target : source.AromaticCanonicalOccurrence fuel)
    (atom : source.AromaticCanonicalAtom)
    (current : target.1.node.current? = some atom)
    (real : target.1.node.provenance = .realAtom)
    (ineligible : ¬ source.ConnectivityOnlyTetrahedralCenterAtom atom) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? target = none := by
  classical
  have notCenter : atom ∉ source.aromaticCanonicalTetrahedralCenterSet := by
    intro detected
    exact ineligible ((source.mem_aromaticCanonicalTetrahedralCenterSet_iff atom).mp detected).1
  unfold aromaticCanonicalOccurrenceTetrahedralCenter?
  rw [dif_pos real, current]
  simp [notCenter]

private theorem dependency_none_of_state_none (source : AuthoritativeChemicalInput) (fuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState fuel)
    (target : source.AromaticCanonicalOccurrence fuel)
    (child : source.AromaticCanonicalRerootCursor fuel)
    (absent : state child.occurrence = none) :
    source.aromaticCanonicalDependencyLabel target (source.aromaticCanonicalDependencyView state target)
      child = none := by
  unfold aromaticCanonicalDependencyLabel
  split
  · exact absent
  · rfl

def terminalIDs (left : Bool) : List Nat := if left then [3, 4, 5] else [8, 9, 10]

noncomputable def armChildren (c l r : TetrahedralInputParity) (left : Bool) :
    List ((ownSource (raw c l r)).AromaticCanonicalRerootCursor 1) :=
  (ownSource (raw c l r)).aromaticCanonicalRerootChildren (armCursor c l r left)

theorem arm_children_nodes (c l r : TetrahedralInputParity) (left : Bool) :
    ((armChildren c l r left).map (fun child => child.occurrence.1.node)).Perm
      ((ownSource (raw c l r)).molecule.aromaticCanonicalOfficialCIPChildrenAt
        (ownSource (raw c l r)).molecule.atomCount
        (OfficialCIPNode.rootFromEdge (sourceCenter c l r).1 (armAtom c l r left))) := by
  have nodes := returned_one_reroot_nodes_perm (ownSource (raw c l r)) (sourceCenter c l r)
    (armCursor c l r left) (arm_cursor_present c l r left) (by rw [arm_cursor_node]; rfl)
  simpa only [armChildren, arm_cursor_node] using nodes

theorem arm_children_ids (c l r : TetrahedralInputParity) (left : Bool) :
    ((armChildren c l r left).map (cursorAtomID (ownSource (raw c l r)))).Perm
      ((terminalIDs left).map some) := by
  have nodes := (arm_children_nodes c l r left).map (fun node => node.current?.map Fin.val)
  have physical := converted_official_edge_ids_perm (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) (armAtom c l r left) (armDomain c l r left)
    (sourceCenter c l r).1
  have result := nodes.trans physical
  have filtered : (armWritten left).filter (fun atom => !(atom == 1)) = terminalIDs left := by
    cases left <;> rfl
  simpa only [List.map_map, Function.comp_def, cursorAtomID, armAtom_index, arm_record_row,
    sourceCenter_index, filtered] using result

theorem arm_child_real (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    ∃ atom : (ownSource (raw c l r)).AromaticCanonicalAtom,
      child.occurrence.1.node.current? = some atom ∧
      child.occurrence.1.node.provenance = .realAtom ∧ atom.val ∈ terminalIDs left := by
  have member := (arm_children_nodes c l r left).mem_iff.mp
    (List.mem_map.mpr ⟨child, present, rfl⟩)
  rw [converted_official_edge_children (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) (armAtom c l r left) (armDomain c l r left)
    (sourceCenter c l r).1] at member
  obtain ⟨neighbor, retained, nodeEq⟩ := List.mem_map.mp member
  have physical : neighbor.val ∈ recordNeighbors (raw c l r) (armAtom c l r left).val :=
    of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp retained).1).2
  have notParent : neighbor ≠ (sourceCenter c l r).1 := by
    simpa using (List.mem_filter.mp retained).2
  have notArm : neighbor ≠ armAtom c l r left := by
    intro same
    exact (converted_neighbor_bound (raw c l r) (ownSource (raw c l r))
      (raw_semantic_conversion c l r) (armAtom c l r left) (armDomain c l r left)
      neighbor.val physical).2 (congrArg Fin.val same)
  have current : child.occurrence.1.node.current? = some neighbor := by rw [← nodeEq]; rfl
  have ids := (arm_children_ids c l r left).mem_iff.mp
    (List.mem_map.mpr ⟨child, present, rfl⟩)
  have terminal : neighbor.val ∈ terminalIDs left := by
    simpa [cursorAtomID, current] using ids
  refine ⟨neighbor, current, ?_, terminal⟩
  rw [← nodeEq]
  simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
    OfficialCIPNode.rootFromEdge, notArm, notParent]

theorem arm_children_length (c l r : TetrahedralInputParity) (left : Bool) :
    (armChildren c l r left).length = 3 := by
  have length := (arm_children_ids c l r left).length_eq
  simpa only [List.length_map] using length.trans (by cases left <;> rfl)

theorem arm_child_terminal (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    (ownSource (raw c l r)).aromaticCanonicalRerootChildren child = [] :=
  returned_one_child_terminal (ownSource (raw c l r)) (sourceCenter c l r)
    (armCursor c l r left) (arm_cursor_present c l r left)
    (by rw [arm_cursor_node]; rfl) child present

theorem terminal_atoms_not_eligible (c l r : TetrahedralInputParity) (left : Bool) :
    ∀ i : Fin 11, i.val ∈ terminalIDs left →
      ¬ (ownSource (raw c l r)).ConnectivityOnlyTetrahedralCenterAtom (sourceRoleAtom c l r i) := by
  have rawIneligible : ∀ i : Fin 11, i.val ∈ terminalIDs left →
      ¬ (raw c l r).atomZAt i.val ∈ [5, 6, 7, 8, 14, 15, 16, 32, 33, 34, 50, 51, 52, 82, 83] := by
    cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel
  intro i member eligible
  change (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.atomZ
    (sourceRoleAtom c l r i) ∈ [5, 6, 7, 8, 14, 15, 16, 32, 33, 34, 50, 51, 52, 82, 83] at eligible
  rw [converted_atomic_number (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r)] at eligible
  exact rawIneligible i member eligible

theorem arm_child_center_none (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    (ownSource (raw c l r)).aromaticCanonicalOccurrenceTetrahedralCenter? child.occurrence = none := by
  classical
  obtain ⟨atom, current, real, member⟩ := arm_child_real c l r left child present
  have bound : atom.val < 11 := by
    cases left <;> simp [terminalIDs] at member <;> omega
  have atomEq : atom = sourceRoleAtom c l r ⟨atom.val, bound⟩ := Fin.ext rfl
  have notEligible := terminal_atoms_not_eligible c l r left ⟨atom.val, bound⟩ member
  rw [← atomEq] at notEligible
  exact occurrence_center_none_of_ineligible (ownSource (raw c l r)) 1 child.occurrence
    atom current real notEligible

theorem arm_child_descriptor_none (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left)
    (view : (ownSource (raw c l r)).AromaticCanonicalDependencyView child.occurrence) :
    constitutionParserRichDescriptor? (raw c l r) (ownSource (raw c l r))
      (family_annotation_agreement c l r) (raw_written c l r) child.occurrence view 4 = none := by
  simp only [constitutionParserRichDescriptor?, constitutionParserRichPriorityEvidence?,
    arm_child_center_none c l r left child present, Bind.bind, Option.bind]

theorem arm_child_scheduled_none (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    familyScheduledState c l r child.occurrence = none := by
  have model := constitutionParserRichScheduledState_cipModel (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) 1 4
  have evaluates := constitutionParserRichModel_evaluates (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) (familyScheduledState c l r)
    model child.occurrence
  exact evaluates.symm.trans (arm_child_descriptor_none c l r left child present _)

noncomputable def centralTarget (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).AromaticCanonicalOccurrence 1 :=
  (ownSource (raw c l r)).aromaticCanonicalFinalOccurrence 1 (sourceCenter c l r)

noncomputable def centralView (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).AromaticCanonicalDependencyView (centralTarget c l r) :=
  (ownSource (raw c l r)).aromaticCanonicalDependencyView (familyScheduledState c l r)
    (centralTarget c l r)

theorem arm_child_dependency_none (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    (ownSource (raw c l r)).aromaticCanonicalDependencyLabel
      (centralTarget c l r) (centralView c l r) child = none := by
  exact dependency_none_of_state_none (ownSource (raw c l r)) 1 (familyScheduledState c l r)
    (centralTarget c l r) child (arm_child_scheduled_none c l r left child present)

theorem central_keys_exist (c l r : TetrahedralInputParity) :
    ∃ keys, (ownSource (raw c l r)).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (centralTarget c l r) (centralView c l r) 4 (sourceFrame c l r).roots = some keys :=
  exists_occurrence_production_keyFrame_of_returned_noDouble (ownSource (raw c l r))
    (centralTarget c l r) (centralView c l r) (sourceFrame c l r)
    (source_returned_four_roots c l r).1
    (actual_source_no_double (raw c l r) (raw_ordinary_source_input c l r))

noncomputable def centralKeys (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).AromaticCanonicalOccurrenceRule3Through5KeyFrame 1 :=
  Classical.choose (central_keys_exist c l r)

theorem central_keys_computed (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (centralTarget c l r) (centralView c l r) 4 (sourceFrame c l r).roots =
        some (centralKeys c l r) := Classical.choose_spec (central_keys_exist c l r)

end TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
