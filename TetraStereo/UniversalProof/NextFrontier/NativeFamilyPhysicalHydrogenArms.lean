import TetraStereo.UniversalProof.NextFrontier.NativeFramedCursorObservations
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalGenerationCoverage
import TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
import TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeFamilyPhysicalHydrogenArms
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeFramedCursorObservations
open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeGeneratedCursorPhysicalCut
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.GeneralParserStateBridge (atomSpec)

/-- The independent physical parent role of the five comparison hydrogen roles. -/
def comparisonHydrogenParent (offset : Nat) : Nat := if offset < 8 then 2 else 8

/-- Exact correspondence of the two raw endpoint-list projections, without source ordering imports. -/
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

/-- The actual maintained role table spells all five comparison leaves as default hydrogen. -/
theorem family_comparison_hydrogen_atom (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (hydrogenRole : offset ∈ [3, 4, 9, 10, 11]) :
    (familyRaw ps).atomAt? (1 + 12 * i.val + offset) = some hydrogenSpec := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hydrogenRole
  rcases hydrogenRole with rfl | rfl | rfl | rfl | rfl
  · simpa [roleAtom, roleOfOffset] using familyRaw_role_atom ps i 3 (by decide)
  · simpa [roleAtom, roleOfOffset] using familyRaw_role_atom ps i 4 (by decide)
  · simpa [roleAtom, roleOfOffset] using familyRaw_role_atom ps i 9 (by decide)
  · simpa [roleAtom, roleOfOffset] using familyRaw_role_atom ps i 10 (by decide)
  · simpa [roleAtom, roleOfOffset] using familyRaw_role_atom ps i 11 (by decide)

/-- The actual isotope mass is the source-backed hydrogen picodalton key, not the number one. -/
theorem family_comparison_hydrogen_mass (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (hydrogenRole : offset ∈ [3, 4, 9, 10, 11]) :
    (familyRaw ps).atomMassAt (1 + 12 * i.val + offset) = rule2MassPico .H none := by
  have spelling := family_comparison_hydrogen_atom ps i offset hydrogenRole
  simp [atomMassAt, atomMassAt?, spelling, hydrogenSpec, atomSpec, rule2MassPico]

/-- The actual written bond records give each comparison hydrogen its sole actual carbon parent. -/
theorem family_comparison_hydrogen_incident (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (hydrogenRole : offset ∈ [3, 4, 9, 10, 11]) :
    rawIncident (familyRaw ps) (1 + 12 * i.val + offset) =
      [1 + 12 * i.val + comparisonHydrogenParent offset] := by
  rw [rawIncident_eq_recordNeighbors]
  have records := familyRaw_comparison_leaf_records ps i
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hydrogenRole
  rcases hydrogenRole with rfl | rfl | rfl | rfl | rfl
  · simpa only [comparisonHydrogenParent] using records.1
  · simpa only [comparisonHydrogenParent] using records.2.1
  · simpa only [comparisonHydrogenParent] using records.2.2.1
  · simpa only [comparisonHydrogenParent] using records.2.2.2.1
  · simpa only [comparisonHydrogenParent] using records.2.2.2.2

/-- The actual tag-to-parent-to-hydrogen path is supported, simple and bounded for every block
of every parity list. No tree-path or metric outcome is a supplied premise. -/
theorem family_comparison_hydrogen_path (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (hydrogenRole : offset ∈ [3, 4, 9, 10, 11]) :
    RawSupportedPath (familyRaw ps) (1 + 12 * i.val + 5) (1 + 12 * i.val + offset)
      [1 + 12 * i.val + 5, 1 + 12 * i.val + comparisonHydrogenParent offset,
        1 + 12 * i.val + offset] := by
  have offsetBound : offset < 12 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hydrogenRole
    rcases hydrogenRole with rfl | rfl | rfl | rfl | rfl <;> decide
  have parentBound : comparisonHydrogenParent offset < 12 := by
    unfold comparisonHydrogenParent
    split_ifs <;> decide
  have centerBound := familyRaw_role_bound ps i 5 (by decide)
  have carbonBound := familyRaw_role_bound ps i _ parentBound
  have leafBound := familyRaw_role_bound ps i offset offsetBound
  have parentMember : 1 + 12 * i.val + comparisonHydrogenParent offset ∈
      recordNeighbors (familyRaw ps) (1 + 12 * i.val + 5) := by
    rw [familyRaw_tag_records]
    unfold comparisonHydrogenParent
    split_ifs <;> simp
  have leafMember : 1 + 12 * i.val + offset ∈
      recordNeighbors (familyRaw ps) (1 + 12 * i.val + comparisonHydrogenParent offset) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hydrogenRole
    rcases hydrogenRole with rfl | rfl | rfl | rfl | rfl <;>
      simp [comparisonHydrogenParent, familyRaw_bridge_records, familyRaw_methyl_records]
  have firstEdge : 0 < (familyRaw ps).bondOrder (1 + 12 * i.val + 5)
      (1 + 12 * i.val + comparisonHydrogenParent offset) := by
    rw [familyRaw_incident_order ps _ _ parentMember]
    decide
  have secondEdge : 0 < (familyRaw ps).bondOrder
      (1 + 12 * i.val + comparisonHydrogenParent offset) (1 + 12 * i.val + offset) := by
    rw [familyRaw_incident_order ps _ _ leafMember]
    decide
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hydrogenRole
    rcases hydrogenRole with rfl | rfl | rfl | rfl | rfl <;>
      simp [comparisonHydrogenParent, List.nodup_cons, List.mem_cons]
  · simpa only [RawBondedPath, List.isChain_cons_cons, List.isChain_singleton, and_true] using
      And.intro firstEdge secondEdge
  · intro atom member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact centerBound
    · exact carbonBound
    · exact leafBound

/-- All independent physical hydrogen-arm premises are inhabited by the actual maintained
family constructors, without copying constructor declarations or assuming cursor/comparator outputs. -/
theorem family_comparison_hydrogen_arm (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (hydrogenRole : offset ∈ [3, 4, 9, 10, 11]) :
    PhysicalHydrogenArm (familyRaw ps) (1 + 12 * i.val + 5)
      (1 + 12 * i.val + comparisonHydrogenParent offset) (1 + 12 * i.val + offset) := by
  refine ⟨family_comparison_hydrogen_path ps i offset hydrogenRole,
    family_comparison_hydrogen_incident ps i offset hydrogenRole, ?_,
    family_comparison_hydrogen_mass ps i offset hydrogenRole⟩
  have spelling := family_comparison_hydrogen_atom ps i offset hydrogenRole
  simp [atomZAt, spelling, hydrogenSpec, atomSpec, Element.atomicNumber]



theorem family_comparison_hydrogen_cursor (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (hydrogenRole : offset ∈ [3, 4, 9, 10, 11]) {root : Nat}
    {center node previous : CanonicalBranchNode}
    (eligible : CanonicalCenterRerootCursor (familyRaw ps) root
      { node := node, previous? := some previous })
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (nodeAtom : node.atom = 1 + 12 * i.val + offset)
    (previousAtom : previous.atom = 1 + 12 * i.val + comparisonHydrogenParent offset) :
    PhysicalHydrogenCursor (familyRaw ps) root center
      { node := node, previous? := some previous } := by
  refine ⟨node, previous, rfl, eligible, ?_⟩
  rw [centerAtom, previousAtom, nodeAtom]
  exact family_comparison_hydrogen_arm ps i offset hydrogenRole

/-- Every emitted cursor child remembers exactly the actual current node, independently of
whether the original traversal went upward or downward. -/
theorem actual_child_previous {mol : RawMolecule} {cursor child : CanonicalRerootCursor}
    (member : child ∈ cursor.children mol) : child.previous? = some cursor.node := by
  unfold CanonicalRerootCursor.children at member
  by_cases leaf : cursor.node.forcedLeaf
  · simp [leaf] at member
  · simp only [if_neg leaf] at member
    obtain ⟨neighbor, _neighborMember, output⟩ := List.mem_filterMap.mp member
    cases previous : cursor.previous? with
    | none =>
        simp only [previous, Option.some.injEq] at output
        subst child
        rfl
    | some previousNode =>
        simp only [previous] at output
        by_cases same : neighbor = previousNode
        · simp [same] at output
        · simp only [beq_iff_eq, same, if_false, Option.some.injEq] at output
          subst child
          rfl

/-- Actual child membership and actual role coordinates instantiate physical hydrogen
classification; no child output/permutation/comparator result is a premise. -/
theorem family_actual_hydrogen_child (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (hydrogenRole : offset ∈ [3, 4, 9, 10, 11]) {root : Nat}
    {center : CanonicalBranchNode} {cursor child : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor (familyRaw ps) root cursor)
    (member : child ∈ cursor.children (familyRaw ps))
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (parentAtom : cursor.node.atom = 1 + 12 * i.val + comparisonHydrogenParent offset)
    (childAtom : child.node.atom = 1 + 12 * i.val + offset) :
    PhysicalHydrogenCursor (familyRaw ps) root center child := by
  have previous := actual_child_previous member
  have shape : child = { node := child.node, previous? := some cursor.node } := by
    cases child
    simp_all
  have childEligible := eligible.child member
  rw [shape] at childEligible ⊢
  exact family_comparison_hydrogen_cursor ps i offset hydrogenRole childEligible
    centerAtom childAtom parentAtom

/-- Bridge child IDs are derived directly from actual raw records in this lower physical
context, without importing the old-runtime source-ordering graph. -/
theorem family_bridge_child_ids (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {bridge center : CanonicalBranchNode}
    (bridgeGenerated : CanonicalCenterTreeNode (familyRaw ps) root bridge)
    (centerGenerated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (bridgeAtom : bridge.atom = 1 + 12 * i.val + 2)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    ((({ node := bridge, previous? := some center } : CanonicalRerootCursor).children (familyRaw ps)).map
      (fun child => child.node.atom)).Perm [1 + 12 * i.val, 1 + 12 * i.val + 3, 1 + 12 * i.val + 4] := by
  have cut := generated_cut_atoms_perm (familyRaw_chronologicalPhysicalTree ps) rootBound
    bridgeGenerated centerGenerated
  rw [bridgeAtom, centerAtom, rawIncident_eq_recordNeighbors, familyRaw_bridge_records] at cut
  have zero : 1 + 12 * i.val ≠ 1 + 12 * i.val + 5 := by omega
  have three : 1 + 12 * i.val + 3 ≠ 1 + 12 * i.val + 5 := by omega
  have four : 1 + 12 * i.val + 4 ≠ 1 + 12 * i.val + 5 := by omega
  simpa [zero, three, four] using cut

/-- Actual methyl child IDs are likewise derived from the independent maintained records. -/
theorem family_methyl_child_ids (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {methyl center : CanonicalBranchNode}
    (methylGenerated : CanonicalCenterTreeNode (familyRaw ps) root methyl)
    (centerGenerated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (methylAtom : methyl.atom = 1 + 12 * i.val + 8)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    ((({ node := methyl, previous? := some center } : CanonicalRerootCursor).children (familyRaw ps)).map
      (fun child => child.node.atom)).Perm [1 + 12 * i.val + 9, 1 + 12 * i.val + 10, 1 + 12 * i.val + 11] := by
  have cut := generated_cut_atoms_perm (familyRaw_chronologicalPhysicalTree ps) rootBound
    methylGenerated centerGenerated
  rw [methylAtom, centerAtom, rawIncident_eq_recordNeighbors, familyRaw_methyl_records] at cut
  simpa using cut




theorem family_actual_decisive_child_spheres (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center bridge methyl : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (bridgeEligible : CanonicalCenterRerootCursor (familyRaw ps) root
      { node := bridge, previous? := some center })
    (methylEligible : CanonicalCenterRerootCursor (familyRaw ps) root
      { node := methyl, previous? := some center })
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (bridgeAtom : bridge.atom = 1 + 12 * i.val + 2)
    (methylAtom : methyl.atom = 1 + 12 * i.val + 8)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.compareBranch? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
      authoritative (fuel + 1) stage
      (.actual { node := bridge, previous? := some center })
      (.actual { node := methyl, previous? := some center }) = some .gt := by
  let bridgeCursor : CanonicalRerootCursor := { node := bridge, previous? := some center }
  let methylCursor : CanonicalRerootCursor := { node := methyl, previous? := some center }
  have bridgeGenerated := (genuine_edge_generated bridgeEligible).1
  have methylGenerated := (genuine_edge_generated methylEligible).1
  have bridgeIDs := family_bridge_child_ids ps i rootBound bridgeGenerated centerGenerated bridgeAtom centerAtom
  have methylIDs := family_methyl_child_ids ps i rootBound methylGenerated centerGenerated methylAtom centerAtom
  have bridgeThree : (bridgeCursor.children (familyRaw ps)).length = 3 := by
    simpa only [bridgeCursor, List.length_map, List.length_cons, List.length_nil] using bridgeIDs.length_eq
  have methylThree : (methylCursor.children (familyRaw ps)).length = 3 := by
    simpa only [methylCursor, List.length_map, List.length_cons, List.length_nil] using methylIDs.length_eq
  have carbonMapped : 1 + 12 * i.val ∈
      (bridgeCursor.children (familyRaw ps)).map (fun child => child.node.atom) :=
    bridgeIDs.mem_iff.mpr List.mem_cons_self
  obtain ⟨carbon, carbonMember, carbonAtom⟩ := List.mem_map.mp carbonMapped
  have expectedNodup : [1 + 12 * i.val, 1 + 12 * i.val + 3, 1 + 12 * i.val + 4].Nodup := by
    simp
  have atomNodup := bridgeIDs.nodup_iff.mpr expectedNodup
  have bridgeHydrogens : ∀ child ∈ bridgeCursor.children (familyRaw ps), child ≠ carbon →
      PhysicalHydrogenCursor (familyRaw ps) root center child := by
    intro child member different
    have atomMember : child.node.atom ∈ [1 + 12 * i.val, 1 + 12 * i.val + 3, 1 + 12 * i.val + 4] :=
      bridgeIDs.mem_iff.mp (List.mem_map.mpr ⟨child, member, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at atomMember
    rcases atomMember with zero | three | four
    · exact (different (List.inj_on_of_nodup_map atomNodup member carbonMember (zero.trans carbonAtom.symm))).elim
    · exact family_actual_hydrogen_child ps i 3 (by simp) bridgeEligible member centerAtom
        (by simpa only [bridgeCursor, comparisonHydrogenParent] using bridgeAtom) three
    · exact family_actual_hydrogen_child ps i 4 (by simp) bridgeEligible member centerAtom
        (by simpa only [bridgeCursor, comparisonHydrogenParent] using bridgeAtom) four
  have methylHydrogens : ∀ child ∈ methylCursor.children (familyRaw ps),
      PhysicalHydrogenCursor (familyRaw ps) root center child := by
    intro child member
    have atomMember : child.node.atom ∈ [1 + 12 * i.val + 9, 1 + 12 * i.val + 10, 1 + 12 * i.val + 11] :=
      methylIDs.mem_iff.mp (List.mem_map.mpr ⟨child, member, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at atomMember
    rcases atomMember with nine | ten | eleven
    · exact family_actual_hydrogen_child ps i 9 (by simp) methylEligible member centerAtom
        (by simpa only [methylCursor, comparisonHydrogenParent] using methylAtom) nine
    · exact family_actual_hydrogen_child ps i 10 (by simp) methylEligible member centerAtom
        (by simpa only [methylCursor, comparisonHydrogenParent] using methylAtom) ten
    · exact family_actual_hydrogen_child ps i 11 (by simp) methylEligible member centerAtom
        (by simpa only [methylCursor, comparisonHydrogenParent] using methylAtom) eleven
  have bridgeLabel : (familyRaw ps).atomZAt bridge.atom = 6 := by
    rw [bridgeAtom]
    simpa [roleAtom, roleOfOffset, carbonSpec, atomSpec, Element.atomicNumber] using
      familyRaw_role_Z ps i 2 (by decide)
  have methylLabel : (familyRaw ps).atomZAt methyl.atom = 6 := by
    rw [methylAtom]
    simpa [roleAtom, roleOfOffset, carbonSpec, atomSpec, Element.atomicNumber] using
      familyRaw_role_Z ps i 8 (by decide)
  have carbonLabel : (familyRaw ps).atomZAt carbon.node.atom = 6 := by
    rw [carbonAtom]
    exact (familyRaw_interior_carbon_Z ps i).1
  exact actual_three_child_sphere_decision (familyRaw_chronologicalPhysicalTree ps) rootBound
    centerGenerated bridgeEligible methylEligible bridgeLabel methylLabel bridgeThree methylThree
    carbonMember carbonLabel bridgeHydrogens methylHydrogens authoritative fuel stage




theorem family_written_tag_decisive_comparison (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    ∃ center bridge methyl,
      CanonicalCenterTreeNode (familyRaw ps) root center ∧
      center.atom = 1 + 12 * i.val + 5 ∧
      CanonicalCenterRerootCursor (familyRaw ps) root { node := bridge, previous? := some center } ∧
      CanonicalCenterRerootCursor (familyRaw ps) root { node := methyl, previous? := some center } ∧
      bridge.atom = 1 + 12 * i.val + 2 ∧ methyl.atom = 1 + 12 * i.val + 8 ∧
      FrameRuntime.profile? (familyRaw ps) center = some (generatedProfile (familyRaw ps) root center) ∧
      FrameRuntime.compareBranch? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative (fuel + 1) stage
        (.actual { node := bridge, previous? := some center })
        (.actual { node := methyl, previous? := some center }) = some .gt := by
  obtain ⟨center, centerGenerated, centerAtom⟩ :=
    NativeChronologicalGenerationCoverage.family_generated_atom_exists ps rootBound
      (familyRaw_role_bound ps i 5 (by decide))
  have bridgeIncident : 1 + 12 * i.val + 2 ∈ rawIncident (familyRaw ps) center.atom := by
    rw [centerAtom, rawIncident_eq_recordNeighbors, familyRaw_tag_records]
    simp
  have methylIncident : 1 + 12 * i.val + 8 ∈ rawIncident (familyRaw ps) center.atom := by
    rw [centerAtom, rawIncident_eq_recordNeighbors, familyRaw_tag_records]
    simp
  obtain ⟨bridge, _bridgeGenerated, bridgeAtom, _toTag, bridgeEligible⟩ :=
    NativeChronologicalGenerationCoverage.generated_incident_oriented_edge
      (familyRaw_chronologicalPhysicalTree ps) rootBound centerGenerated bridgeIncident
  obtain ⟨methyl, _methylGenerated, methylAtom, _toTag, methylEligible⟩ :=
    NativeChronologicalGenerationCoverage.generated_incident_oriented_edge
      (familyRaw_chronologicalPhysicalTree ps) rootBound centerGenerated methylIncident
  exact ⟨center, bridge, methyl, centerGenerated, centerAtom, bridgeEligible, methylEligible,
    bridgeAtom, methylAtom, actual_profile_obtained (familyRaw_chronologicalPhysicalTree ps) rootBound centerGenerated,
    family_actual_decisive_child_spheres ps i rootBound centerGenerated bridgeEligible methylEligible
      centerAtom bridgeAtom methylAtom authoritative fuel stage⟩

/-- Unconditional root0 version for every actual written tag of every parity list.
The empty list has no manufactured tag request; its Fin index type is empty. -/
theorem family_root0_written_tag_decisive_comparison (ps : List TetrahedralInputParity)
    (i : Fin ps.length) (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    ∃ center bridge methyl,
      CanonicalCenterTreeNode (familyRaw ps) 0 center ∧
      center.atom = 1 + 12 * i.val + 5 ∧
      CanonicalCenterRerootCursor (familyRaw ps) 0 { node := bridge, previous? := some center } ∧
      CanonicalCenterRerootCursor (familyRaw ps) 0 { node := methyl, previous? := some center } ∧
      bridge.atom = 1 + 12 * i.val + 2 ∧ methyl.atom = 1 + 12 * i.val + 8 ∧
      FrameRuntime.profile? (familyRaw ps) center = some (generatedProfile (familyRaw ps) 0 center) ∧
      FrameRuntime.compareBranch? (familyRaw ps) (generatedProfile (familyRaw ps) 0 center)
        authoritative (fuel + 1) stage
        (.actual { node := bridge, previous? := some center })
        (.actual { node := methyl, previous? := some center }) = some .gt :=
  family_written_tag_decisive_comparison ps i (familyRaw_chronologicalPhysicalTree ps).1
    authoritative fuel stage

end TetraStereo.UniversalProof.NativeFamilyPhysicalHydrogenArms
