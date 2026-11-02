import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedRealNodeInventory
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalTreeConnectivity
import TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalFamilyPathBridge
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeGeneratedRealNodeInventory
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

/-- Every actual second-sphere parity list, including empty, has connected supported raw paths. -/
theorem family_rawPathConnected (ps : List TetrahedralInputParity) : RawPathConnected (familyRaw ps) :=
  NativeChronologicalTreeConnectivity.chronological_rawPathConnected
    (familyRaw_chronologicalPhysicalTree ps)

/-- Every actual family molecule has an acyclic bounded physical graph. -/
theorem family_physicalGraph_acyclic (ps : List TetrahedralInputParity) :
    (NativeChronologicalTreeAcyclic.physicalGraph (familyRaw ps)).IsAcyclic :=
  NativeChronologicalTreeAcyclic.chronological_physicalGraph_acyclic
    (familyRaw_chronologicalPhysicalTree ps)

/-- Global supported simple path uniqueness holds for every actual parity-list molecule. -/
theorem family_uniqueRawSimplePaths (ps : List TetrahedralInputParity) :
    UniqueRawSimplePaths (familyRaw ps) :=
  NativeChronologicalTreeSimplePathUniqueness.chronological_uniqueRawSimplePaths
    (familyRaw_chronologicalPhysicalTree ps)

/-- At any bounded discovery root, genuine real generated occurrences of the same family
atom are the same original node. No root, parity, occurrence or family size is fixed. -/
theorem family_generated_real_nodes_unique (ps : List TetrahedralInputParity)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {left right : CanonicalBranchNode}
    (leftGenerated : CanonicalCenterTreeNode (familyRaw ps) root left)
    (rightGenerated : CanonicalCenterTreeNode (familyRaw ps) root right)
    (leftReal : left.provenance = .realAtom) (rightReal : right.provenance = .realAtom)
    (sameAtom : left.atom = right.atom) : left = right :=
  generated_real_node_unique (familyRaw_chronologicalPhysicalTree ps) rootBound
    leftGenerated rightGenerated leftReal rightReal sameAtom

/-- Actual generated real histories obey the whole-family physical inventory bound. -/
theorem family_generated_real_history_bound (ps : List TetrahedralInputParity)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode (familyRaw ps) root node)
    (real : node.provenance = .realAtom) : node.history.length ≤ (familyRaw ps).atomCount :=
  generated_real_history_length_le_inventory (familyRaw_chronologicalPhysicalTree ps)
    rootBound generated real

end TetraStereo.UniversalProof.NativeChronologicalFamilyPathBridge
