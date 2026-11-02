import TetraStereo.OneCenter.LocalizedCanonicalAuxiliaryRS
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# First-sphere decisions of the canonical physical priority

The graph-only physical rule-major outcome opens with the first difference of the atomic-number
column, and the hierarchy address `[]` precedes every other address.  Hence whenever the two
current atoms of an incoming-cut pair have different atomic numbers, the canonical physical
outcome is decided at the first sphere by Rule 1a: the heavier atom is senior
(`physicalTreeCanonicalOutcome_gt_of_atomZ_gt`).  At a `DomainPhysicalContext` the canonical
priority between two slots therefore follows from the atomic numbers of their ligand atoms alone
(`DomainPhysicalContext.canonicalPriority_of_atomZ_gt`) — the ingredient needed to exhibit the
canonical highest-first order of a constitutionally rigid centre whose four ligands have distinct
atomic numbers.
-/

namespace TetraStereo.OneCenter

universe u

theorem not_hierarchyAddressBefore_nil (earlier : List ℕ) :
    ¬ DeclarativeCIP.HierarchyAddressBefore earlier [] := by
  intro h
  unfold DeclarativeCIP.HierarchyAddressBefore DeclarativeCIP.HierarchyAddressKey at h
  rw [List.cons_lt_cons_iff] at h
  rcases h with h | ⟨_, h⟩
  · exact Nat.not_lt_zero _ h
  · exact List.not_lt_nil _ h

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem physicalTreeAtomicNumberAt_nil (m : MoleculeGraph V) (tree : PhysicalAtomTree V) :
    physicalTreeAtomicNumberAt m tree [] = m.atomZ tree.root := rfl

/-- Different root atomic numbers decide the physical rule-major outcome at the first sphere. -/
theorem physicalTreeRuleMajorOutcome_gt_of_atomZ_gt (m : MoleculeGraph V) (outerRoot : V)
    {previousLeft previousRight : Option V} {currentLeft currentRight : V}
    {leftTree rightTree : PhysicalAtomTree V}
    (left : PhysicalIncomingCutAdmissible m outerRoot previousLeft currentLeft leftTree)
    (right : PhysicalIncomingCutAdmissible m outerRoot previousRight currentRight rightTree)
    (hZ : m.atomZ currentRight < m.atomZ currentLeft) :
    physicalTreeRuleMajorOutcome m outerRoot leftTree rightTree Ordering.gt := by
  unfold physicalTreeRuleMajorOutcome
  left
  refine ⟨[], ?_, fun earlier h => absurd h (not_hierarchyAddressBefore_nil earlier)⟩
  show DeclarativeCIP.DescendingNatOutcome (physicalTreeAtomicNumberAt m leftTree [])
    (physicalTreeAtomicNumberAt m rightTree []) Ordering.gt
  rw [physicalTreeAtomicNumberAt_nil, physicalTreeAtomicNumberAt_nil,
    PhysicalFullCutTree.root_eq m left.full, PhysicalFullCutTree.root_eq m right.full]
  exact DeclarativeCIP.DescendingNatOutcome.gt hZ

theorem physicalTreeCanonicalOutcome_eq_gt_of_atomZ_gt (m : MoleculeGraph V) (outerRoot : V)
    {previousLeft previousRight : Option V} {currentLeft currentRight : V} {outcome : Ordering}
    (h : PhysicalTreeCanonicalOutcome m outerRoot previousLeft previousRight currentLeft
      currentRight outcome)
    (hZ : m.atomZ currentRight < m.atomZ currentLeft) : outcome = Ordering.gt := by
  obtain ⟨⟨leftTree, left⟩, ⟨rightTree, right⟩, every⟩ := h
  exact physicalTreeRuleMajorOutcome_functional m outerRoot leftTree rightTree
    (every leftTree rightTree left right)
    (physicalTreeRuleMajorOutcome_gt_of_atomZ_gt m outerRoot left right hZ)

theorem physicalTreeCanonicalOutcome_gt_of_atomZ_gt (m : MoleculeGraph V) (outerRoot : V)
    {previousLeft previousRight : Option V} {currentLeft currentRight : V} {outcome : Ordering}
    (h : PhysicalTreeCanonicalOutcome m outerRoot previousLeft previousRight currentLeft
      currentRight outcome)
    (hZ : m.atomZ currentRight < m.atomZ currentLeft) :
    PhysicalTreeCanonicalOutcome m outerRoot previousLeft previousRight currentLeft currentRight
      Ordering.gt := by
  have := physicalTreeCanonicalOutcome_eq_gt_of_atomZ_gt m outerRoot h hZ
  subst this
  exact h

namespace DomainPhysicalContext

open CertifiedLocalizedCIPInput

variable {input : LocalizedUniversalReference.Input}

/-- **Canonical priority from atomic numbers.**  At a physical context, a slot whose ligand atom is
heavier than another slot's ligand atom is canonically senior to it. -/
theorem canonicalPriority_of_atomZ_gt (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) (left right : Fin 4)
    (hZ : input.certified.moleculeGraph.atomZ
        (cursorAtom context.singleBonded context.acyclic ((context.frame branch).cursorAt right)) <
      input.certified.moleculeGraph.atomZ
        (cursorAtom context.singleBonded context.acyclic ((context.frame branch).cursorAt left))) :
    context.canonicalPriority branch left right := by
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    change input.certified.certified.input.molecule.atomCount ≤
      input.certified.certified.input.molecule.atomCount + 1
    omega
  have rootAt (index : Fin 4) :
      ((context.frame branch).cursorAt index).occurrence.1.root = context.target.1.root := by
    have root := frameSlotBranchTree_root input.certified context.target context.view
      (context.frame branch) (context.derived branch) index
    rwa [frameSlotBranchTree_source] at root
  obtain ⟨leftKey, rightKey, _, _, iff⟩ :=
    exists_physicalTreeCanonicalOutcome_iff_actualComparison enough context.singleBonded
      context.acyclic .rule4a context.target context.view context.target.1.root
      ((context.frame branch).cursorAt left) ((context.frame branch).cursorAt right)
      ((context.frame branch).cursorAt_valid input.certified context.target
        (context.derived branch) left)
      ((context.frame branch).cursorAt_valid input.certified context.target
        (context.derived branch) right)
      (rootAt left) (rootAt right)
  have some := (iff (OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional)).1
    rfl
  exact physicalTreeCanonicalOutcome_gt_of_atomZ_gt input.certified.moleculeGraph _ some hZ

end DomainPhysicalContext
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.physicalTreeCanonicalOutcome_gt_of_atomZ_gt
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.canonicalPriority_of_atomZ_gt
