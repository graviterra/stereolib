import TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereFamilyGeneratedHistories

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery (outgoingNode)

/-! Proposed actual all-block generated histories. No caller supplies a generated
node, cursor, child list, comparison, parser result or source output. Own kernel
validation, downstream discovery coverage and HUMAN/EXTERNAL remain OPEN. -/

def pathNode (atom : Nat) (ancestors : List Nat) : CanonicalBranchNode :=
  { atom := atom, parent := ancestors.headD atom, history := atom :: ancestors,
    provenance := .realAtom }

private theorem canonical_bond_one (raw : RawMolecule) (node : CanonicalBranchNode)
    (other : Nat) (one : raw.bondOrder node.atom other = 1) :
    raw.canonicalBondOrder node other = 1 := by
  cases history : node.history with
  | nil => simpa only [canonicalBondOrder, history] using one
  | cons first tail =>
      cases tail with
      | nil => simpa only [canonicalBondOrder, history] using one
      | cons second tail =>
          cases tail with
          | nil => simp [canonicalBondOrder, history, one]
          | cons third rest => simpa only [canonicalBondOrder, history] using one

private theorem unit_copies (raw : RawMolecule) (node : CanonicalBranchNode)
    (bonds : List RawBond)
    (single : ∀ bond ∈ bonds, ∀ other, recordNeighbor? node.atom bond = some other →
      raw.canonicalBondOrder node other = 1) :
    (bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
      | none => []
      | some other => (List.range (raw.canonicalBondOrder node other)).map
          (fun copy => (other, copy))) =
    (bonds.filterMap (recordNeighbor? node.atom)).map (fun other => (other, 0)) := by
  induction bonds with
  | nil => rfl
  | cons bond bonds ih =>
      have tailSingle : ∀ selected ∈ bonds, ∀ other,
          recordNeighbor? node.atom selected = some other →
            raw.canonicalBondOrder node other = 1 := by
        intro selected member other observed
        exact single selected (List.mem_cons_of_mem bond member) other observed
      simp only [List.flatMap_cons, List.filterMap_cons]
      cases observed : recordNeighbor? node.atom bond with
      | none => simpa only [List.nil_append] using ih tailSingle
      | some other =>
          have one := single bond List.mem_cons_self other observed
          simp only [one, List.range_succ, List.range_zero, List.nil_append,
            List.map_cons, List.map_nil, List.cons_append]
          rw [ih tailSingle]

private theorem erase_map_zero (parent : Nat) (atoms : List Nat) :
    eraseCanonicalParentCopy parent (atoms.map (fun atom => (atom, 0))) =
      (atoms.erase parent).map (fun atom => (atom, 0)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      by_cases equal : atom = parent
      · subst atom
        simp [eraseCanonicalParentCopy]
      · simp [eraseCanonicalParentCopy, equal, ih]

theorem canonicalChildCopies_of_single (raw : RawMolecule) (node : CanonicalBranchNode)
    (single : ∀ other ∈ recordNeighbors raw node.atom, raw.bondOrder node.atom other = 1) :
    raw.canonicalChildCopies node =
      ((recordNeighbors raw node.atom).erase node.parent).map (fun other => (other, 0)) := by
  have seeds := unit_copies raw node raw.bonds (by
    intro bond member other observed
    exact canonical_bond_one raw node other
      (single other (List.mem_filterMap.mpr ⟨bond, member, observed⟩)))
  change eraseCanonicalParentCopy node.parent
    (raw.bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
      | none => []
      | some other => (List.range (raw.canonicalBondOrder node other)).map
          (fun copy => (other, copy))) = _
  rw [seeds, erase_map_zero]
  rfl

/-- A single fresh physical neighbor yields one actual real canonical child.
Other siblings may have duplicate provenance; their freshness is not assumed. -/
theorem canonical_real_child_mem (raw : RawMolecule) (node : CanonicalBranchNode)
    (real : node.provenance = .realAtom)
    (single : ∀ other ∈ recordNeighbors raw node.atom, raw.bondOrder node.atom other = 1)
    (other : Nat) (member : other ∈ recordNeighbors raw node.atom)
    (different : other ≠ node.parent) (fresh : other ∉ node.history) :
    outgoingNode node other ∈ raw.canonicalChildren node := by
  have notLeaf : node.forcedLeaf = false := by
    rw [CanonicalBranchNode.forcedLeaf, real]
  have retained : other ∈ (recordNeighbors raw node.atom).erase node.parent :=
    (List.mem_erase_of_ne different).mpr member
  unfold canonicalChildren
  rw [notLeaf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [canonicalChildCopies_of_single raw node single]
  apply List.mem_map.mpr
  refine ⟨(other, 0), List.mem_map.mpr ⟨other, retained, rfl⟩, ?_⟩
  simp [outgoingNode, fresh]

theorem pathNode_real_child_mem (raw : RawMolecule) (atom : Nat) (ancestors : List Nat)
    (single : ∀ other ∈ recordNeighbors raw atom, raw.bondOrder atom other = 1)
    (other : Nat) (member : other ∈ recordNeighbors raw atom)
    (different : other ≠ ancestors.headD atom) (fresh : other ∉ atom :: ancestors) :
    pathNode other (atom :: ancestors) ∈ raw.canonicalChildren (pathNode atom ancestors) :=
  canonical_real_child_mem raw (pathNode atom ancestors) rfl single other member different fresh

open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation

def backboneIndex (i : Nat) : Nat := 1 + 12 * i

def backboneTail : Nat → List Nat
  | 0 => []
  | i + 1 => backboneIndex i :: backboneTail i

def backboneNode (i : Nat) := pathNode (backboneIndex i) (backboneTail i)
def bridgeNode (i : Nat) := pathNode (backboneIndex i + 2)
  (backboneIndex i :: backboneTail i)
def tagNode (i : Nat) := pathNode (backboneIndex i + 5)
  ((backboneIndex i + 2) :: backboneIndex i :: backboneTail i)
def methylNode (i : Nat) := pathNode (backboneIndex i + 8)
  ((backboneIndex i + 5) :: (backboneIndex i + 2) :: backboneIndex i :: backboneTail i)

theorem backboneTail_lt (i atom : Nat) (member : atom ∈ backboneTail i) :
    atom < backboneIndex i := by
  revert member
  induction i with
  | zero => intro member; simp [backboneTail] at member
  | succ i ih =>
      intro member
      simp only [backboneTail, List.mem_cons] at member
      rcases member with rfl | member
      · unfold backboneIndex; omega
      · have older := ih member
        unfold backboneIndex at older ⊢; omega

theorem backboneTail_nodup (i : Nat) : (backboneTail i).Nodup := by
  induction i with
  | zero => simp [backboneTail]
  | succ i ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih⟩
      intro member
      have impossible := backboneTail_lt i (backboneIndex i) member
      omega

theorem backbone_parent_le (i : Nat) :
    (backboneTail i).headD (backboneIndex i) ≤ backboneIndex i := by
  cases i with
  | zero => simp [backboneTail]
  | succ i => simp only [backboneTail, List.headD_cons]; unfold backboneIndex; omega

private def allocationParent (base parent : Nat) : Nat → Nat
  | 0 => parent
  | i + 1 => base + 12 * i

theorem blocksResult_bond_retained (ps : List TetrahedralInputParity)
    (mol : RawMolecule) (parent : Fin mol.atomCount) (bond : RawBond)
    (member : bond ∈ mol.bonds) : bond ∈ (blocksResult543 ps mol parent).bonds := by
  induction ps generalizing mol parent with
  | nil => exact member
  | cons parity rest ih =>
      apply ih
      rw [blockAppend_bonds_exact]
      exact List.mem_append_left _ member

private theorem blocksResult_backbone_bond (ps : List TetrahedralInputParity)
    (mol : RawMolecule) (parent : Fin mol.atomCount) (i : Nat) (bound : i < ps.length) :
    (⟨allocationParent mol.atomCount parent.val i, mol.atomCount + 12 * i, .single⟩ : RawBond)
      ∈ (blocksResult543 ps mol parent).bonds := by
  induction ps generalizing mol parent i with
  | nil => simp at bound
  | cons parity rest ih =>
      let next := blockAppend mol mol.atomCount rfl parent parity
      let nextParent : Fin next.atomCount := ⟨mol.atomCount, by
        dsimp [next]; rw [blockAppend_atomCount]; omega⟩
      have count : next.atomCount = mol.atomCount + 12 := by
        dsimp [next]; rw [blockAppend_atomCount]
      cases i with
      | zero =>
          change (⟨parent.val, mol.atomCount, .single⟩ : RawBond) ∈
            (blocksResult543 rest next nextParent).bonds
          apply blocksResult_bond_retained
          dsimp [next]
          rw [blockAppend_bonds_exact]
          apply List.mem_append_right
          exact List.mem_cons_self
      | succ i =>
          have selected := ih next nextParent i (by simpa using bound)
          have source : allocationParent next.atomCount nextParent.val i =
              allocationParent mol.atomCount parent.val (i + 1) := by
            cases i <;> simp only [allocationParent, nextParent, count] <;> omega
          have target : next.atomCount + 12 * i = mol.atomCount + 12 * (i + 1) := by
            rw [count]; omega
          change (⟨_, _, .single⟩ : RawBond) ∈ (blocksResult543 rest next nextParent).bonds
          simpa only [source, target] using selected

theorem familyRaw_forward_backbone_neighbor (ps : List TetrahedralInputParity)
    (i : Nat) (bound : i + 1 < ps.length) :
    backboneIndex (i + 1) ∈ recordNeighbors (familyRaw ps) (backboneIndex i) := by
  have selected := blocksResult_backbone_bond ps family543Base baseFin (i + 1) bound
  have bondMember : (⟨backboneIndex i, backboneIndex (i + 1), .single⟩ : RawBond)
      ∈ (familyRaw ps).bonds := by
    unfold familyRaw
    dsimp only
    rw [appendFreshChild_bonds]
    apply List.mem_append_left
    simpa only [allocationParent, family543Base, backboneIndex] using selected
  apply List.mem_filterMap.mpr
  refine ⟨_, bondMember, ?_⟩
  simp [recordNeighbor?]

theorem familyRaw_backbone_generated (ps : List TetrahedralInputParity)
    (i : Nat) (bound : i < ps.length) :
    CanonicalCenterTreeNode (familyRaw ps) 1 (backboneNode i) := by
  revert bound
  induction i with
  | zero => intro bound; exact CanonicalCenterTreeNode.root
  | succ i ih =>
      intro bound
      have generated := ih (by omega)
      have fresh : backboneIndex (i + 1) ∉ backboneIndex i :: backboneTail i := by
        intro member
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · unfold backboneIndex at equal; omega
        · have older := backboneTail_lt i _ member
          unfold backboneIndex at older; omega
      have different : backboneIndex (i + 1) ≠ (backboneTail i).headD (backboneIndex i) := by
        have le := backbone_parent_le i
        unfold backboneIndex at le ⊢; omega
      exact CanonicalCenterTreeNode.child generated
        (pathNode_real_child_mem (familyRaw ps) _ _
          (familyRaw_incident_order ps _) _
          (familyRaw_forward_backbone_neighbor ps i bound) different fresh)

private theorem larger_fresh (i atom : Nat) (larger : backboneIndex i < atom) :
    atom ∉ backboneIndex i :: backboneTail i := by
  intro member
  simp only [List.mem_cons] at member
  rcases member with equal | member
  · omega
  · have older := backboneTail_lt i atom member
    omega

theorem familyRaw_bridge_child (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    bridgeNode i.val ∈ (familyRaw ps).canonicalChildren (backboneNode i.val) := by
  have reverse : backboneIndex i.val ∈ recordNeighbors (familyRaw ps) (backboneIndex i.val + 2) := by
    unfold backboneIndex
    rw [familyRaw_bridge_records ps i]
    exact List.mem_cons_self
  have member := TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery.record_neighbors_symmetric
    (familyRaw ps) (familyRaw_wellFormed ps) reverse
  apply pathNode_real_child_mem (familyRaw ps) _ _ (familyRaw_incident_order ps _) _ member
  · have le := backbone_parent_le i.val; omega
  · exact larger_fresh i.val _ (by omega)

theorem familyRaw_bridge_generated (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterTreeNode (familyRaw ps) 1 (bridgeNode i.val) :=
  .child (familyRaw_backbone_generated ps i.val i.isLt) (familyRaw_bridge_child ps i)

theorem familyRaw_tag_child (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    tagNode i.val ∈ (familyRaw ps).canonicalChildren (bridgeNode i.val) := by
  have member : backboneIndex i.val + 5 ∈ recordNeighbors (familyRaw ps) (backboneIndex i.val + 2) := by
    unfold backboneIndex
    rw [familyRaw_bridge_records ps i]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr True.intro))
  change pathNode (backboneIndex i.val + 5)
    ((backboneIndex i.val + 2) :: backboneIndex i.val :: backboneTail i.val) ∈
    (familyRaw ps).canonicalChildren
      (pathNode (backboneIndex i.val + 2) (backboneIndex i.val :: backboneTail i.val))
  apply pathNode_real_child_mem (familyRaw ps) (backboneIndex i.val + 2)
    (backboneIndex i.val :: backboneTail i.val)
    (familyRaw_incident_order ps _) (backboneIndex i.val + 5) member
  · simp only [List.headD_cons]; omega
  · have fresh := larger_fresh i.val (backboneIndex i.val + 5) (by omega)
    simp only [List.mem_cons, not_or] at fresh ⊢
    exact ⟨by omega, fresh⟩

theorem familyRaw_tag_generated (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterTreeNode (familyRaw ps) 1 (tagNode i.val) :=
  .child (familyRaw_bridge_generated ps i) (familyRaw_tag_child ps i)

theorem familyRaw_methyl_child (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    methylNode i.val ∈ (familyRaw ps).canonicalChildren (tagNode i.val) := by
  have member : backboneIndex i.val + 8 ∈ recordNeighbors (familyRaw ps) (backboneIndex i.val + 5) := by
    unfold backboneIndex
    rw [familyRaw_tag_records ps i]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr True.intro))
  change pathNode (backboneIndex i.val + 8)
    ((backboneIndex i.val + 5) :: (backboneIndex i.val + 2) ::
      backboneIndex i.val :: backboneTail i.val) ∈
    (familyRaw ps).canonicalChildren
      (pathNode (backboneIndex i.val + 5)
        ((backboneIndex i.val + 2) :: backboneIndex i.val :: backboneTail i.val))
  apply pathNode_real_child_mem (familyRaw ps) (backboneIndex i.val + 5)
    ((backboneIndex i.val + 2) :: backboneIndex i.val :: backboneTail i.val)
    (familyRaw_incident_order ps _) (backboneIndex i.val + 8) member
  · simp only [List.headD_cons]; omega
  · have fresh := larger_fresh i.val (backboneIndex i.val + 8) (by omega)
    simp only [List.mem_cons, not_or] at fresh ⊢
    exact ⟨by omega, by omega, fresh⟩

theorem familyRaw_methyl_generated (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterTreeNode (familyRaw ps) 1 (methylNode i.val) :=
  .child (familyRaw_tag_generated ps i) (familyRaw_methyl_child ps i)

theorem familyRaw_root_carbon (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).atomZAt 1 = 6 := by
  have positive : 0 < ps.length := by have bound := i.isLt; omega
  exact (familyRaw_interior_carbon_Z ps ⟨0, positive⟩).1

theorem familyRaw_root_bound (ps : List TetrahedralInputParity) : 1 < (familyRaw ps).atomCount := by
  rw [familyRaw_atomCount]; omega

theorem familyRaw_methyl_history_valid (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (methylNode i.val).history.Nodup ∧
      (∀ atom, atom ∈ (methylNode i.val).history → atom < (familyRaw ps).atomCount) :=
  (familyRaw_methyl_generated ps i).real_history
    (familyRaw_root_bound ps) (familyRaw_wellFormed ps) rfl

theorem familyRaw_tag_history_valid (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (tagNode i.val).history.Nodup ∧
      (∀ atom, atom ∈ (tagNode i.val).history → atom < (familyRaw ps).atomCount) :=
  (familyRaw_tag_generated ps i).real_history
    (familyRaw_root_bound ps) (familyRaw_wellFormed ps) rfl

theorem familyRaw_backbone_history_valid (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (backboneNode i.val).history.Nodup ∧
      (∀ atom, atom ∈ (backboneNode i.val).history → atom < (familyRaw ps).atomCount) :=
  (familyRaw_backbone_generated ps i.val i.isLt).real_history
    (familyRaw_root_bound ps) (familyRaw_wellFormed ps) rfl

theorem familyRaw_bridge_history_valid (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (bridgeNode i.val).history.Nodup ∧
      (∀ atom, atom ∈ (bridgeNode i.val).history → atom < (familyRaw ps).atomCount) :=
  (familyRaw_bridge_generated ps i).real_history
    (familyRaw_root_bound ps) (familyRaw_wellFormed ps) rfl

/-- Genuine incoming-at-tag cursor, produced by ascending its actual bridge-to-tag edge. -/
theorem familyRaw_incoming_bridge_cursor (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterRerootCursor (familyRaw ps) 1
      { node := bridgeNode i.val, previous? := some (tagNode i.val) } :=
  .ascending (familyRaw_bridge_generated ps i) (familyRaw_tag_child ps i)

/-- Genuine outgoing-at-tag cursor, produced by descending its actual tag-to-methyl edge. -/
theorem familyRaw_outgoing_methyl_cursor (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterRerootCursor (familyRaw ps) 1
      { node := methylNode i.val, previous? := some (tagNode i.val) } :=
  .descending (familyRaw_tag_generated ps i) (familyRaw_methyl_child ps i)

end TetraStereo.UniversalProof.SecondSphereFamilyGeneratedHistories
