import TetraStereo.UniversalProof.NextFrontier.NativeRingSourceInput

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingSourceGeometry

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingSourceInput
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

-- Keep the actual converted source abstract while specializing the generic frame lemmas.
attribute [local irreducible] ringSource

def ringAtom (n : Nat) (parity : TetrahedralInputParity) (index : Nat)
    (bound : index < (expanded n parity).atomCount) : (ringSource n parity).AromaticCanonicalAtom :=
  (expanded n parity).convertedAtomIndex (ringSource n parity) (ring_annotation_agreement n parity).1
    ⟨index, bound⟩

noncomputable def ringSlotID (n : Nat) (parity : TetrahedralInputParity)
    (carrierFuel : Nat) (slot : Fin 4) : Nat :=
  slotAtomID (expanded n parity) (ringSource n parity) (ring_annotation_agreement n parity).1
    carrierFuel (ringCenter n parity) (ringRecordDomain n parity 0) (ring_four_records n parity) slot

theorem ring_role_slot_exists (n : Nat) (parity : TetrahedralInputParity)
    (carrierFuel atom : Nat) (member : atom ∈ [n + 5, 1, 2, n + 4]) :
    ∃ slot : Fin 4, ringSlotID n parity carrierFuel slot = atom := by
  have permutation := actual_slot_ids_perm (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 carrierFuel (ringCenter n parity)
    (ringRecordDomain n parity 0) (ring_four_records n parity)
  have physical : atom ∈ recordNeighbors (expanded n parity) 0 :=
    (expanded_root_records n parity).mem_iff.mpr member
  obtain ⟨slot, _, equal⟩ := List.mem_map.mp (permutation.mem_iff.mpr physical)
  exact ⟨slot, equal⟩

noncomputable def ringRoleSlot (n : Nat) (parity : TetrahedralInputParity)
    (carrierFuel atom : Nat) (member : atom ∈ [n + 5, 1, 2, n + 4]) : Fin 4 :=
  Classical.choose (ring_role_slot_exists n parity carrierFuel atom member)

theorem ring_role_slot_index (n : Nat) (parity : TetrahedralInputParity)
    (carrierFuel atom : Nat) (member : atom ∈ [n + 5, 1, 2, n + 4]) :
    ringSlotID n parity carrierFuel (ringRoleSlot n parity carrierFuel atom member) = atom :=
  Classical.choose_spec (ring_role_slot_exists n parity carrierFuel atom member)

theorem ring_role_root_node (n : Nat) (parity : TetrahedralInputParity)
    (carrierFuel atom : Nat) (member : atom ∈ [n + 5, 1, 2, n + 4])
    (bound : atom < (expanded n parity).atomCount) :
    ((ringFrame n parity carrierFuel).cursorAt (ringRoleSlot n parity carrierFuel atom member)).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (ringCenter n parity).1 (ringAtom n parity atom bound) := by
  exact actual_slot_root_node (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 carrierFuel (ringCenter n parity)
    (ringRecordDomain n parity 0) (ring_four_records n parity)
    (ringRoleSlot n parity carrierFuel atom member) (ringAtom n parity atom bound)
    (ring_role_slot_index n parity carrierFuel atom member)

noncomputable def leftCursor (n : Nat) (parity : TetrahedralInputParity) :
    (ringSource n parity).AromaticCanonicalRerootCursor 1 :=
  (ringFrame n parity 1).cursorAt (ringRoleSlot n parity 1 2 (by simp))

noncomputable def rightCursor (n : Nat) (parity : TetrahedralInputParity) :
    (ringSource n parity).AromaticCanonicalRerootCursor 1 :=
  (ringFrame n parity 1).cursorAt (ringRoleSlot n parity 1 (n + 4) (by simp))

theorem source_left_child_ids (n : Nat) (parity : TetrahedralInputParity) :
    (((ringSource n parity).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (ringSource n parity).molecule.atomCount (OfficialCIPNode.rootFromEdge
        (ringCenter n parity).1 (ringAtom n parity 2 (by rw [expanded_atom_count]; omega)))).map
          (fun node => node.current?.map Fin.val)).Perm [some 3, some 4, some (n + 6)] := by
  have source := converted_official_edge_ids_perm (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 (ringAtom n parity 2 (by rw [expanded_atom_count]; omega))
    (ringRecordDomain n parity 2) (ringCenter n parity).1
  have physical := ((expanded_left_records n parity).filter (fun atom => !(atom == 0))).map some
  have filtered : (((recordNeighbors (expanded n parity) 2).filter (fun atom => !(atom == 0))).map some).Perm
      [some (n + 6), some 3, some 4] := by simpa using physical
  exact source.trans (filtered.trans (List.perm_append_comm (l₁ := [some (n + 6)]) (l₂ := [some 3, some 4])))

theorem source_right_child_ids (n : Nat) (parity : TetrahedralInputParity) :
    (((ringSource n parity).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (ringSource n parity).molecule.atomCount (OfficialCIPNode.rootFromEdge
        (ringCenter n parity).1 (ringAtom n parity (n + 4) (by rw [expanded_atom_count]; omega)))).map
          (fun node => node.current?.map Fin.val)).Perm
      [some (if n = 0 then 2 else n + 3), some (3 * n + 7), some (3 * n + 8)] := by
  have source := converted_official_edge_ids_perm (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 (ringAtom n parity (n + 4) (by rw [expanded_atom_count]; omega))
    (ringRecordDomain n parity (n + 4)) (ringCenter n parity).1
  have physical := ((expanded_right_records n parity).filter (fun atom => !(atom == 0))).map some
  apply source.trans
  cases n <;> simpa using physical

theorem source_left_observations (n : Nat) (parity : TetrahedralInputParity) :
    (((ringSource n parity).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (ringSource n parity).molecule.atomCount (OfficialCIPNode.rootFromEdge
        (ringCenter n parity).1 (ringAtom n parity 2 (by rw [expanded_atom_count]; omega)))).map
          (ringSource n parity).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation).Perm
      [DeclarativeCIP.ExactAtomicNumber.ofNat 17, .ofNat 6, .ofNat 1] := by
  have permutation := (source_left_child_ids n parity).map (atomIDObservation (expanded n parity))
  rw [← converted_edge_observation_ids (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 (ringAtom n parity 2 (by rw [expanded_atom_count]; omega))
    (ringRecordDomain n parity 2) (ringCenter n parity).1] at permutation
  simpa only [List.map_cons, List.map_nil, atomIDObservation, Option.getD_some,
    expanded_chlorine_z, expanded_chain_z n parity 0 (by omega),
    expanded_hydrogen_z n parity (n + 6) (by omega) (by omega)] using permutation

theorem source_right_observations (n : Nat) (parity : TetrahedralInputParity) :
    (((ringSource n parity).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (ringSource n parity).molecule.atomCount (OfficialCIPNode.rootFromEdge
        (ringCenter n parity).1 (ringAtom n parity (n + 4) (by rw [expanded_atom_count]; omega)))).map
          (ringSource n parity).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation).Perm
      [DeclarativeCIP.ExactAtomicNumber.ofNat 6, .ofNat 1, .ofNat 1] := by
  have permutation := (source_right_child_ids n parity).map (atomIDObservation (expanded n parity))
  rw [← converted_edge_observation_ids (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 (ringAtom n parity (n + 4) (by rw [expanded_atom_count]; omega))
    (ringRecordDomain n parity (n + 4)) (ringCenter n parity).1] at permutation
  simpa only [List.map_cons, List.map_nil, atomIDObservation, Option.getD_some,
    expanded_right_predecessor_z, expanded_hydrogen_z n parity (3 * n + 7) (by omega) (by omega),
    expanded_hydrogen_z n parity (3 * n + 8) (by omega) (by omega)] using permutation

/-- The actual returned source child inventories, derived through the converter and the
carrier's real adjacency, including the minimal triangular ring. -/
theorem actual_child_observations (n : Nat) (parity : TetrahedralInputParity) :
    (((ringSource n parity).aromaticCanonicalRerootChildren (leftCursor n parity)).map (fun child =>
      (ringSource n parity).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm [DeclarativeCIP.ExactAtomicNumber.ofNat 17, .ofNat 6, .ofNat 1] ∧
    (((ringSource n parity).aromaticCanonicalRerootChildren (rightCursor n parity)).map (fun child =>
      (ringSource n parity).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm [DeclarativeCIP.ExactAtomicNumber.ofNat 6, .ofNat 1, .ofNat 1] := by
  have leftNode := ring_role_root_node n parity 1 2 (by simp) (by rw [expanded_atom_count]; omega)
  have rightNode := ring_role_root_node n parity 1 (n + 4) (by simp) (by rw [expanded_atom_count]; omega)
  obtain ⟨_, _, leftReal⟩ := ring_roots_real n parity 1 (ringRoleSlot n parity 1 2 (by simp))
  obtain ⟨_, _, rightReal⟩ := ring_roots_real n parity 1 (ringRoleSlot n parity 1 (n + 4) (by simp))
  have left := returned_one_reroot_nodes_perm (ringSource n parity) (ringCenter n parity)
    (leftCursor n parity) (ring_frame_cursor_mem n parity 1 (ringRoleSlot n parity 1 2 (by simp))) leftReal
  have right := returned_one_reroot_nodes_perm (ringSource n parity) (ringCenter n parity)
    (rightCursor n parity) (ring_frame_cursor_mem n parity 1 (ringRoleSlot n parity 1 (n + 4) (by simp))) rightReal
  change (leftCursor n parity).occurrence.1.node = _ at leftNode
  change (rightCursor n parity).occurrence.1.node = _ at rightNode
  rw [leftNode] at left
  rw [rightNode] at right
  have leftObserved := left.map (ringSource n parity).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
  have rightObserved := right.map (ringSource n parity).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
  simp only [List.map_map] at leftObserved rightObserved
  exact ⟨leftObserved.trans (source_left_observations n parity),
    rightObserved.trans (source_right_observations n parity)⟩

end TetraStereo.UniversalProof.NativeRingSourceGeometry
