import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedCursorPhysicalCut
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalTreeConnectivity
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalProfileSuccess
import TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalGenerationCoverage
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeGeneratedCursorPhysicalCut
open TetraStereo.UniversalProof.NativeChronologicalTreeConnectivity
open TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
open TetraStereo.UniversalProof.NativeGeneratedRealNodeInventory
open TetraStereo.UniversalProof.NativeGlobalProfileInventory
open TetraStereo.UniversalProof.NativeChronologicalProfileSuccess
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

/-- Positive physical adjacency exposes an actual raw incident endpoint. -/
theorem rawIncident_of_positive {mol : RawMolecule} {atom neighbor : Nat}
    (positive : 0 < mol.bondOrder atom neighbor) : neighbor ∈ rawIncident mol atom := by
  have different : atom ≠ neighbor := by
    intro same
    rw [same, mol.bondOrder_self] at positive
    exact (Nat.lt_irrefl 0) positive
  obtain ⟨bond, member, connects⟩ := (mol.bondOrder_pos_iff_exists_bond different).mp positive
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
  apply mem_rawIncident.mpr
  refine ⟨bond, member, ?_⟩
  rcases connects with forward | backward
  · exact Or.inl forward
  · exact Or.inr ⟨backward.2, backward.1⟩

/-- Independent raw incidence yields both genuinely oriented cursors, without rediscovery. -/
theorem generated_incident_oriented_edge {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node)
    {atom : Nat} (incident : atom ∈ rawIncident mol node.atom) :
    ∃ neighbor, CanonicalCenterTreeNode mol root neighbor ∧ neighbor.atom = atom ∧
      CanonicalCenterRerootCursor mol root { node := node, previous? := some neighbor } ∧
      CanonicalCenterRerootCursor mol root { node := neighbor, previous? := some node } := by
  have permutation := generated_neighbors_atoms_perm tree rootBound generated
  have mapped : atom ∈ (({ node := node } : CanonicalRerootCursor).neighbors mol).map
      CanonicalBranchNode.atom := permutation.mem_iff.mpr incident
  obtain ⟨neighbor, member, same⟩ := List.mem_map.mp mapped
  rcases generated.neighbor_cases member with ⟨parentGenerated, nodeMember⟩ | childMember
  · exact ⟨neighbor, parentGenerated, same,
      CanonicalCenterRerootCursor.descending parentGenerated nodeMember,
      CanonicalCenterRerootCursor.ascending parentGenerated nodeMember⟩
  · exact ⟨neighbor, CanonicalCenterTreeNode.child generated childMember, same,
      CanonicalCenterRerootCursor.ascending generated childMember,
      CanonicalCenterRerootCursor.descending generated childMember⟩

/-- Physical walks lift to genuine original generation, including parent-side steps. -/
theorem generated_along_physical_walk {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {start finish : Nat} (walk : (physicalGraph mol).Walk start finish)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node)
    (same : node.atom = start) :
    ∃ target, CanonicalCenterTreeNode mol root target ∧ target.atom = finish := by
  induction walk generalizing node with
  | nil => exact ⟨node, generated, same⟩
  | @cons start next finish edge walk ih =>
      have positive : 0 < mol.bondOrder node.atom next := by
        simpa only [same] using edge.2.2
      obtain ⟨neighbor, neighborGenerated, neighborAtom, _forward, _backward⟩ :=
        generated_incident_oriented_edge tree rootBound generated (rawIncident_of_positive positive)
      exact ih neighborGenerated neighborAtom

/-- Every supported physical atom is actually generated from any bounded discovery root.
Connectivity is derived from independent chronological raw inputs rather than supplied. -/
theorem chronological_generated_atom_exists {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root atom : Nat}
    (rootBound : root < mol.atomCount) (atomBound : atom < mol.atomCount) :
    ∃ node, CanonicalCenterTreeNode mol root node ∧ node.atom = atom := by
  obtain ⟨walk⟩ := physical_atoms_reachable tree root atom rootBound atomBound
  exact generated_along_physical_walk tree rootBound walk CanonicalCenterTreeNode.root rfl

/-- Coverage and raw-tree identity give a unique original node, including its retained history. -/
theorem chronological_generated_atom_unique {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root atom : Nat}
    (rootBound : root < mol.atomCount) (atomBound : atom < mol.atomCount) :
    ∃! node, CanonicalCenterTreeNode mol root node ∧ node.atom = atom := by
  obtain ⟨node, generated, same⟩ := chronological_generated_atom_exists tree rootBound atomBound
  refine ⟨node, ⟨generated, same⟩, ?_⟩
  intro other otherFacts
  exact generated_real_node_unique tree rootBound otherFacts.1 generated
    (chronological_generated_all_real tree rootBound otherFacts.1)
    (chronological_generated_all_real tree rootBound generated) (otherFacts.2.trans same.symm)

/-- The executable request is inhabited at every supported atom; no generation or success premise. -/
theorem chronological_generated_profile_exists {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root atom : Nat}
    (rootBound : root < mol.atomCount) (atomBound : atom < mol.atomCount) :
    ∃ node, CanonicalCenterTreeNode mol root node ∧ node.atom = atom ∧
      CanonicalTreeProfile.profile? mol node =
        some ⟨node, ⟨node.history⟩, inventory mol root (mol.atomCount + 1)⟩ := by
  obtain ⟨node, generated, same⟩ := chronological_generated_atom_exists tree rootBound atomBound
  exact ⟨node, generated, same, chronological_profile_success tree rootBound generated⟩

/-- The maintained family internally supplies the domain at every parity list, including []. -/
theorem family_generated_atom_exists (ps : List TetrahedralInputParity) {root atom : Nat}
    (rootBound : root < (familyRaw ps).atomCount) (atomBound : atom < (familyRaw ps).atomCount) :
    ∃ node, CanonicalCenterTreeNode (familyRaw ps) root node ∧ node.atom = atom :=
  chronological_generated_atom_exists (familyRaw_chronologicalPhysicalTree ps) rootBound atomBound

/-- Every written tag is genuinely generated in the retained original discovery tree. -/
theorem family_written_tag_generated (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount) :
    ∃ node, CanonicalCenterTreeNode (familyRaw ps) root node ∧ node.atom = tagIndex i.val := by
  apply family_generated_atom_exists ps rootBound
  rw [familyRaw_atomCount]
  have indexBound := i.isLt
  unfold tagIndex
  omega

/-- Every written tag has an inhabited exact executable profile at any bounded discovery root. -/
theorem family_written_tag_profile_exists (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount) :
    ∃ node, CanonicalCenterTreeNode (familyRaw ps) root node ∧ node.atom = tagIndex i.val ∧
      CanonicalTreeProfile.profile? (familyRaw ps) node =
        some ⟨node, ⟨node.history⟩, inventory (familyRaw ps) root ((familyRaw ps).atomCount + 1)⟩ := by
  obtain ⟨node, generated, same⟩ := family_written_tag_generated ps i rootBound
  exact ⟨node, generated, same,
    chronological_profile_success (familyRaw_chronologicalPhysicalTree ps) rootBound generated⟩

/-- Root0 written-tag requests require no caller-supplied generation, domain or successful output. -/
theorem family_root0_written_tag_profile_exists (ps : List TetrahedralInputParity)
    (i : Fin ps.length) :
    ∃ node, CanonicalCenterTreeNode (familyRaw ps) 0 node ∧ node.atom = tagIndex i.val ∧
      CanonicalTreeProfile.profile? (familyRaw ps) node =
        some ⟨node, ⟨node.history⟩, inventory (familyRaw ps) 0 ((familyRaw ps).atomCount + 1)⟩ :=
  family_written_tag_profile_exists ps i (familyRaw_chronologicalPhysicalTree ps).1

end TetraStereo.UniversalProof.NativeChronologicalGenerationCoverage
