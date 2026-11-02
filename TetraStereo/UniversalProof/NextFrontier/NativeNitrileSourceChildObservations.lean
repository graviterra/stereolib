import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceNitrileChildren

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

-- Keep the converted source abstract during projection elaboration.
attribute [local irreducible] expanded

def aminoSourceDomain (parity : TetrahedralInputParity) (n : Nat) :
    SourceRecordDomain (expanded parity n) 4 :=
  ⟨(expanded_admissible parity n).1, expanded_records_nodup parity n 4,
    expanded_incident_single parity n 4 (by decide) (by decide)⟩

def sourceAminoCarbon (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).AromaticCanonicalAtom :=
  nitrileAtom parity n 4 (by rw [expanded_atomCount]; omega)

def sourceAminoRoot (parity : TetrahedralInputParity) (n : Nat) :
    OfficialCIPNode (nitrileSource parity n).AromaticCanonicalAtom :=
  OfficialCIPNode.rootFromEdge (nitrileCenter parity n).1 (sourceAminoCarbon parity n)

theorem source_amino_child_ids (parity : TetrahedralInputParity) (n : Nat) :
    (((nitrileSource parity n).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (nitrileSource parity n).molecule.atomCount (sourceAminoRoot parity n)).map
        (fun node => node.current?.map Fin.val)).Perm [some 5, some 6, some (n + 8)] := by
  have source := converted_official_edge_ids_perm (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n).1 (sourceAminoCarbon parity n)
    (aminoSourceDomain parity n) (nitrileCenter parity n).1
  have physical := ((expanded_amino_records parity n).filter (fun atom => !(atom == 0))).map some
  have filtered : (((recordNeighbors (expanded parity n) 4).filter
      (fun atom => !(atom == 0))).map some).Perm [some (n + 8), some 5, some 6] := by
    simpa using physical
  exact source.trans (filtered.trans (List.perm_append_comm
    (l₁ := [some (n + 8)]) (l₂ := [some 5, some 6])))

theorem source_amino_observations (parity : TetrahedralInputParity) (n : Nat) :
    (((nitrileSource parity n).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (nitrileSource parity n).molecule.atomCount (sourceAminoRoot parity n)).map
        (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation).Perm
      [DeclarativeCIP.ExactAtomicNumber.ofNat 7, .ofNat 6, .ofNat 1] := by
  have permutation := (source_amino_child_ids parity n).map (atomIDObservation (expanded parity n))
  unfold sourceAminoRoot at permutation
  rw [← converted_edge_observation_ids (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n).1 (sourceAminoCarbon parity n)
    (aminoSourceDomain parity n) (nitrileCenter parity n).1] at permutation
  rcases expanded_local_atomic_numbers parity n with
    ⟨_, _, _, _, _, nitrogen, carbon, _, hydrogen⟩
  simpa only [List.map_cons, List.map_nil, atomIDObservation, Option.getD_some,
    nitrogen, carbon, hydrogen] using permutation

/-- Actual returned source-carrier children observe N/N/N versus N/C/H. The nitrile nodes
come from its exact triple-bond constructor, independently of the runtime occurrence lists. -/
theorem actual_source_child_observations (parity : TetrahedralInputParity) (n : Nat) :
    (((nitrileSource parity n).aromaticCanonicalRerootChildren (sourceNitrileCursor parity n)).map
      (fun child => (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm [DeclarativeCIP.ExactAtomicNumber.ofNat 7, .ofNat 7, .ofNat 7] ∧
    (((nitrileSource parity n).aromaticCanonicalRerootChildren (sourceAminoCursor parity n)).map
      (fun child => (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm [DeclarativeCIP.ExactAtomicNumber.ofNat 7, .ofNat 6, .ofNat 1] := by
  have nitrileNode : (sourceNitrileCursor parity n).occurrence.1.node = sourceNitrileRoot parity n :=
    nitrile_role_root_node parity n 1 2 (by simp) (by rw [expanded_atomCount]; omega)
  have aminoNode : (sourceAminoCursor parity n).occurrence.1.node = sourceAminoRoot parity n :=
    nitrile_role_root_node parity n 1 4 (by simp) (by rw [expanded_atomCount]; omega)
  have nitrile := returned_one_reroot_nodes_perm (nitrileSource parity n) (nitrileCenter parity n)
    (sourceNitrileCursor parity n) (nitrile_frame_cursor_mem parity n 1 (nitrileRoleSlot parity n 1 2 (by simp))) (by rw [nitrileNode]; rfl)
  have amino := returned_one_reroot_nodes_perm (nitrileSource parity n) (nitrileCenter parity n)
    (sourceAminoCursor parity n) (nitrile_frame_cursor_mem parity n 1 (nitrileRoleSlot parity n 1 4 (by simp))) (by rw [aminoNode]; rfl)
  rw [nitrileNode] at nitrile
  rw [aminoNode] at amino
  have nitrileObserved := nitrile.map
    (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
  have aminoObserved := amino.map
    (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
  simp only [List.map_map] at nitrileObserved aminoObserved
  rw [source_nitrile_observations] at nitrileObserved
  exact ⟨nitrileObserved, aminoObserved.trans (source_amino_observations parity n)⟩

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
