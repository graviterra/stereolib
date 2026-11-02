import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedCursorPhysicalCut
import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedPhysicalFrameMetric
import TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
import TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeFamilyCursorSecondSphereAlignment
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.NativeGeneratedCursorPhysicalCut
open TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
open TetraStereo.UniversalProof.NativeGeneratedPhysicalFrameMetric
open TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic

/-- The two independent raw incident projections are exactly equal for every raw molecule. -/
theorem rawIncident_eq_recordNeighbors (mol : RawMolecule) (atom : Nat) :
    rawIncident mol atom = recordNeighbors mol atom := by
  have lists : ∀ bonds : List RawBond,
      bonds.flatMap (incidentFromBond atom) = bonds.filterMap (recordNeighbor? atom) := by
    intro bonds
    induction bonds with
    | nil => rfl
    | cons bond bonds ih =>
        by_cases source : bond.source = atom
        · simp [incidentFromBond, recordNeighbor?, source, ih]
        · by_cases target : bond.target = atom
          · simp [incidentFromBond, recordNeighbor?, source, target, ih]
          · simp [incidentFromBond, recordNeighbor?, source, target, ih]
  exact lists mol.bonds

/-- Actual bridge cursors, with the tag edge cut, expose C,H,H independent of discovery direction. -/
theorem family_bridge_cursor_child_ids (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {node previous : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root node)
    (previousGenerated : CanonicalCenterTreeNode (familyRaw ps) root previous)
    (nodeAtom : node.atom = 1 + 12 * i.val + 2)
    (previousAtom : previous.atom = 1 + 12 * i.val + 5) :
    ((({ node := node, previous? := some previous } : CanonicalRerootCursor).children (familyRaw ps)).map
      (fun child => child.node.atom)).Perm [1 + 12 * i.val, 1 + 12 * i.val + 3, 1 + 12 * i.val + 4] := by
  have cut := generated_cut_atoms_perm (familyRaw_chronologicalPhysicalTree ps) rootBound
    generated previousGenerated
  rw [nodeAtom, previousAtom, rawIncident_eq_recordNeighbors, familyRaw_bridge_records] at cut
  have zero : 1 + 12 * i.val ≠ 1 + 12 * i.val + 5 := by omega
  have three : 1 + 12 * i.val + 3 ≠ 1 + 12 * i.val + 5 := by omega
  have four : 1 + 12 * i.val + 4 ≠ 1 + 12 * i.val + 5 := by omega
  simpa [zero, three, four] using cut

/-- Actual methyl cursors with the tag edge cut expose H,H,H. -/
theorem family_methyl_cursor_child_ids (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {node previous : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root node)
    (previousGenerated : CanonicalCenterTreeNode (familyRaw ps) root previous)
    (nodeAtom : node.atom = 1 + 12 * i.val + 8)
    (previousAtom : previous.atom = 1 + 12 * i.val + 5) :
    ((({ node := node, previous? := some previous } : CanonicalRerootCursor).children (familyRaw ps)).map
      (fun child => child.node.atom)).Perm
        [1 + 12 * i.val + 9, 1 + 12 * i.val + 10, 1 + 12 * i.val + 11] := by
  have cut := generated_cut_atoms_perm (familyRaw_chronologicalPhysicalTree ps) rootBound
    generated previousGenerated
  rw [nodeAtom, previousAtom, rawIncident_eq_recordNeighbors, familyRaw_methyl_records] at cut
  simpa using cut

/-- The real emitted bridge sphere has exactly the same atomic observation multiset as the source. -/
theorem family_bridge_cursor_source_observations (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {node previous : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root node)
    (previousGenerated : CanonicalCenterTreeNode (familyRaw ps) root previous)
    (nodeAtom : node.atom = 1 + 12 * i.val + 2)
    (previousAtom : previous.atom = 1 + 12 * i.val + 5) :
    ((({ node := node, previous? := some previous } : CanonicalRerootCursor).children (familyRaw ps)).map
      (fun child => DeclarativeCIP.ExactAtomicNumber.ofNat ((familyRaw ps).atomZAt child.node.atom))).Perm
        (((familySource ps).molecule.aromaticCanonicalOfficialCIPChildrenAt
          (familySource ps).molecule.atomCount
          (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
            (familyAtom ps i 2 (by decide)))).map
          (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation) := by
  have ids := family_bridge_cursor_child_ids ps i rootBound generated previousGenerated nodeAtom previousAtom
  have observed := ids.map (fun atom => DeclarativeCIP.ExactAtomicNumber.ofNat ((familyRaw ps).atomZAt atom))
  have z0 := (familyRaw_interior_carbon_Z ps i).1
  have z3 := familyRaw_role_Z ps i 3 (by decide)
  have z4 := familyRaw_role_Z ps i 4 (by decide)
  have physical :
      ((({ node := node, previous? := some previous } : CanonicalRerootCursor).children (familyRaw ps)).map
        (fun child => DeclarativeCIP.ExactAtomicNumber.ofNat ((familyRaw ps).atomZAt child.node.atom))).Perm
          [DeclarativeCIP.ExactAtomicNumber.ofNat 6, .ofNat 1, .ofNat 1] := by
    simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil, z0, z3, z4] using observed
  exact physical.trans (family_source_bridge_observations ps i).symm

/-- The real emitted methyl sphere has the same atomic observation multiset as the actual source. -/
theorem family_methyl_cursor_source_observations (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {node previous : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root node)
    (previousGenerated : CanonicalCenterTreeNode (familyRaw ps) root previous)
    (nodeAtom : node.atom = 1 + 12 * i.val + 8)
    (previousAtom : previous.atom = 1 + 12 * i.val + 5) :
    ((({ node := node, previous? := some previous } : CanonicalRerootCursor).children (familyRaw ps)).map
      (fun child => DeclarativeCIP.ExactAtomicNumber.ofNat ((familyRaw ps).atomZAt child.node.atom))).Perm
        (((familySource ps).molecule.aromaticCanonicalOfficialCIPChildrenAt
          (familySource ps).molecule.atomCount
          (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
            (familyAtom ps i 8 (by decide)))).map
          (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation) := by
  have ids := family_methyl_cursor_child_ids ps i rootBound generated previousGenerated nodeAtom previousAtom
  have observed := ids.map (fun atom => DeclarativeCIP.ExactAtomicNumber.ofNat ((familyRaw ps).atomZAt atom))
  have z9 := familyRaw_role_Z ps i 9 (by decide)
  have z10 := familyRaw_role_Z ps i 10 (by decide)
  have z11 := familyRaw_role_Z ps i 11 (by decide)
  have physical :
      ((({ node := node, previous? := some previous } : CanonicalRerootCursor).children (familyRaw ps)).map
        (fun child => DeclarativeCIP.ExactAtomicNumber.ofNat ((familyRaw ps).atomZAt child.node.atom))).Perm
          [DeclarativeCIP.ExactAtomicNumber.ofNat 1, .ofNat 1, .ofNat 1] := by
    simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil, z9, z10, z11] using observed
  exact physical.trans (family_source_methyl_observations ps i).symm

/-- A genuine oriented cursor retains an actual node from the same original generated tree. -/
theorem genuine_cursor_node_generated {mol : RawMolecule} {root : Nat} {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor) :
    CanonicalCenterTreeNode mol root cursor.node := by
  cases eligible with
  | descending parentGenerated member => exact CanonicalCenterTreeNode.child parentGenerated member
  | ascending nodeGenerated _member => exact nodeGenerated

/-- Every actual first-child cursor is observed in the same physical center-owned metric.
The physical distance is internally derived; no metric output is an input field. -/
theorem genuine_child_fixed_origin_distance {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) {cursor child : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor) (member : child ∈ cursor.children mol) :
    (⟨center.history⟩ : CanonicalComparisonFrame.Frame).realDistance child.node =
      (physicalGraph mol).dist center.atom child.node.atom := by
  have generated := genuine_cursor_node_generated (eligible.child member)
  exact generated_frame_realDistance_eq_physical_distance tree rootBound centerGenerated generated
    (chronological_generated_all_real tree rootBound centerGenerated)
    (chronological_generated_all_real tree rootBound generated)

/-- The decisive bridge sphere has exactly three actual children for every parity-list size. -/
theorem family_bridge_cursor_child_length (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {node previous : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root node)
    (previousGenerated : CanonicalCenterTreeNode (familyRaw ps) root previous)
    (nodeAtom : node.atom = 1 + 12 * i.val + 2)
    (previousAtom : previous.atom = 1 + 12 * i.val + 5) :
    (({ node := node, previous? := some previous } : CanonicalRerootCursor).children (familyRaw ps)).length = 3 := by
  have length := (family_bridge_cursor_child_ids ps i rootBound generated previousGenerated nodeAtom previousAtom).length_eq
  simpa using length

/-- The methyl sphere also has exactly three actual children; no global molecule-size cap is assumed. -/
theorem family_methyl_cursor_child_length (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {node previous : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root node)
    (previousGenerated : CanonicalCenterTreeNode (familyRaw ps) root previous)
    (nodeAtom : node.atom = 1 + 12 * i.val + 8)
    (previousAtom : previous.atom = 1 + 12 * i.val + 5) :
    (({ node := node, previous? := some previous } : CanonicalRerootCursor).children (familyRaw ps)).length = 3 := by
  have length := (family_methyl_cursor_child_ids ps i rootBound generated previousGenerated nodeAtom previousAtom).length_eq
  simpa using length

end TetraStereo.UniversalProof.NativeFamilyCursorSecondSphereAlignment
