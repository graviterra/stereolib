import TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors
import TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Reached raw occurrences belong to the certified finite carrier

The induction follows actual raw canonical children and transports each edge through the
existing intake agreement. It constructs an official expansion path before invoking the
universal carrier bound. Single bonds exclude the P/S oxido expansion exception; cycles and
their terminal duplicate occurrences are allowed. No descriptor or generated-label meaning
is asserted, and raw child-list positions need not equal official child-list positions.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge

open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open RawLocalizedChildNodeTransport RawLocalizedOxidoPathInvariant

theorem reachedFrom_reachableCanonical (mol : RawMolecule) (center : Nat) (node : Node)
    (reached : ReachedFrom mol center node) :
    ReachableCanonical mol (canonicalCenterRoot center) node := by
  induction reached with
  | refl => exact .refl
  | tail path edge ih => exact .child _ _ ih edge

theorem noOxidoRootEdgeAtRootCopies_of_singleBonded
    (mol : RawMolecule) (single : SingleBonded mol) (root : Node) :
    NoOxidoRootEdgeAtRootCopies mol root := by
  intro copy _ edge
  obtain ⟨_, _, _, _, _, _, order⟩ := edge
  have bound := single root.atom copy.1
  rw [order] at bound
  exact (by decide : ¬ ((2 : Nat) ≤ 1)) bound

private theorem forall₂_mem_right {α β : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β} (aligned : List.Forall₂ relation left right)
    {value : β} (member : value ∈ right) :
    ∃ item ∈ left, relation item value := by
  induction aligned with
  | nil => simp at member
  | @cons headLeft headRight tailLeft tailRight heads tails ih =>
      rcases List.mem_cons.mp member with same | rest
      · subst value
        exact ⟨headLeft, List.mem_cons_self, heads⟩
      · obtain ⟨item, present, related⟩ := ih rest
        exact ⟨item, List.mem_cons_of_mem _ present, related⟩

/-- Every actual reached raw node has a corresponding node on an actual official expansion
path from the same molecular root. The address is constructed, not supplied. -/
theorem reachedFrom_unbounded_corresponds
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (center : Nat) (valid : center < mol.atomCount)
    (node : Node) (reached : ReachedFrom mol center node) :
    ∃ (address : List Nat) (official : OfficialCIPNode input.Atom),
      input.UnboundedOfficialSubtree
        (OfficialCIPNode.root (localizedIndexOf mol input agreement ⟨center, valid⟩))
        address official ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) official node := by
  classical
  induction reached with
  | refl =>
      refine ⟨[], OfficialCIPNode.root (localizedIndexOf mol input agreement ⟨center, valid⟩),
        .refl _, ?_⟩
      exact root_corresponds (fun atom : input.Atom => atom.val)
        (localizedIndexOf mol input agreement ⟨center, valid⟩)
  | @tail parent child path edge ih =>
      obtain ⟨address, official, officialPath, corresponds⟩ := ih
      have parentReach : ReachableCanonical mol (canonicalCenterRoot center) parent :=
        reachedFrom_reachableCanonical mol center parent path
      obtain ⟨aligned, alignment, permutation⟩ :=
        reachableCIPChildren_forall₂_canonicalChildren mol input agreement wellFormed unique
          supported (canonicalCenterRoot center) rfl valid
          (noOxidoRootEdgeAtRootCopies_of_singleBonded mol single _) parent official
          parentReach corresponds
      have member : child ∈ aligned := permutation.mem_iff.mpr edge
      obtain ⟨officialChild, officialMember, childCorresponds⟩ :=
        forall₂_mem_right alignment member
      have slot : (officialChild,
          (input.executableOfficialCIPChildren official).idxOf officialChild) ∈
          (input.executableOfficialCIPChildren official).zipIdx := by
        apply List.mem_zipIdx_iff_getElem?.mpr
        exact List.getElem?_idxOf officialMember
      exact ⟨address ++ [(input.executableOfficialCIPChildren official).idxOf officialChild],
        officialChild, input.unboundedOfficialSubtree_append_last officialPath slot,
        childCorresponds⟩

/-- Actual raw reachability supplies membership in the certified carrier at `atomCount + 1`.
The root and full node correspondence, including history and duplicate provenance, survive. -/
theorem reachedFrom_exists_carrier
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (center : Nat) (valid : center < mol.atomCount)
    (node : Node) (reached : ReachedFrom mol center node) :
    ∃ occurrence : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1),
      occurrence.1.root = localizedIndexOf mol input agreement ⟨center, valid⟩ ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) occurrence.1.node node := by
  obtain ⟨_, _, path, corresponds⟩ := reachedFrom_unbounded_corresponds mol input agreement
    wellFormed unique supported single center valid node reached
  exact ⟨input.localizedUnboundedOccurrenceAtAtom
    (localizedIndexOf mol input agreement ⟨center, valid⟩) path, rfl, corresponds⟩

/-- Root and raw history can be read back from the constructed finite-carrier occurrence.
This is occurrence identity data, not an auxiliary-descriptor interpretation. -/
theorem reachedFrom_exists_carrier_readback
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (center : Nat) (valid : center < mol.atomCount)
    (node : Node) (reached : ReachedFrom mol center node) :
    ∃ occurrence : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1),
      occurrence.1.root.val = center ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) occurrence.1.node node ∧
      occurrence.1.node.history.map (fun atom : input.Atom => atom.val) = node.history := by
  obtain ⟨occurrence, root, corresponds⟩ := reachedFrom_exists_carrier mol input agreement
    wellFormed unique supported single center valid node reached
  refine ⟨occurrence, ?_, corresponds, corresponds.history⟩
  rw [root]
  rfl

end TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge.reachedFrom_reachableCanonical
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge.noOxidoRootEdgeAtRootCopies_of_singleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge.reachedFrom_unbounded_corresponds
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge.reachedFrom_exists_carrier
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge.reachedFrom_exists_carrier_readback
