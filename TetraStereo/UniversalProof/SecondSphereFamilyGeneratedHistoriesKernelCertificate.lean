import TetraStereo.UniversalProof.SecondSphereFamilyGeneratedHistories
import TetraStereo.KernelOnly

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyGeneratedHistories

assert_kernel_only canonicalChildCopies_of_single
assert_kernel_only canonical_real_child_mem
assert_kernel_only pathNode_real_child_mem
assert_kernel_only backboneTail_lt
assert_kernel_only backboneTail_nodup
assert_kernel_only backbone_parent_le
assert_kernel_only blocksResult_bond_retained
assert_kernel_only familyRaw_forward_backbone_neighbor
assert_kernel_only familyRaw_backbone_generated
assert_kernel_only familyRaw_bridge_child
assert_kernel_only familyRaw_bridge_generated
assert_kernel_only familyRaw_tag_child
assert_kernel_only familyRaw_tag_generated
assert_kernel_only familyRaw_methyl_child
assert_kernel_only familyRaw_methyl_generated
assert_kernel_only familyRaw_root_carbon
assert_kernel_only familyRaw_root_bound
assert_kernel_only familyRaw_methyl_history_valid
assert_kernel_only familyRaw_tag_history_valid
assert_kernel_only familyRaw_backbone_history_valid
assert_kernel_only familyRaw_bridge_history_valid
assert_kernel_only familyRaw_incoming_bridge_cursor
assert_kernel_only familyRaw_outgoing_methyl_cursor

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterTreeNode (familyRaw ps) 1 (backboneNode i.val) :=
  familyRaw_backbone_generated ps i.val i.isLt

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterTreeNode (familyRaw ps) 1 (methylNode i.val) :=
  familyRaw_methyl_generated ps i

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterRerootCursor (familyRaw ps) 1
      { node := bridgeNode i.val, previous? := some (tagNode i.val) } :=
  familyRaw_incoming_bridge_cursor ps i

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterRerootCursor (familyRaw ps) 1
      { node := methylNode i.val, previous? := some (tagNode i.val) } :=
  familyRaw_outgoing_methyl_cursor ps i
