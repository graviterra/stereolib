import TetraStereo.OneCenter.LocalizedRuleMajorReferenceSelection
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.OneCenter.LocalizedRuleMajorCanonicalBridge
import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingSignature
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
open Certificate.CanonicalSphereKey (Key)
universe u

abbrev MolecularRankPair := Lex (List (Key ℤ) × Key StereoLabel)

def molecularRankPairAt {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (W D : Nat) :
    MolecularRankPair :=
  pairKey molecule graph (rankEvidence molecule descriptorMap unit graph) W D graph.root

theorem molecularRankPairAt_iso {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (W D : Nat) :
    molecularRankPairAt molecule descriptorMap unit right W D =
      molecularRankPairAt molecule descriptorMap unit left W D := by
  unfold molecularRankPairAt pairKey rule4aComponent
  rw [← iso.map_root, ruleKey_iso molecule iso,
    ordinaryKey_iso molecule iso (rankEvidence_preserved molecule descriptorMap unit iso)]

theorem molecularRankPairAt_eq_of_faithful {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (externalParent ligand : Atom)
    {left right : RootedDigraph Atom}
    (faithfulL : left.FaithfulExactExpansion molecule externalParent ligand)
    (faithfulR : right.FaithfulExactExpansion molecule externalParent ligand) (W D : Nat) :
    molecularRankPairAt molecule descriptorMap unit left W D =
      molecularRankPairAt molecule descriptorMap unit right W D := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    molecule externalParent ligand left right faithfulL faithfulR
  exact (molecularRankPairAt_iso molecule descriptorMap unit iso W D).symm

end
end TetraStereo.OneCenter.DeclarativeCIP

namespace TetraStereo.OneCenter.Rule4aTableBridge
open CertifiedLocalizedCIPInput CertifiedLocalizedCIPInput.OriginalRootArm
open LocalizedCumulativeDecoratedTree DeclarativeCIP
noncomputable section

theorem original_ruleMajor_rule4a_key_eq {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (old : input.OriginalRootArm center index .rule4a read)
    (new : input.RuleMajorRootArm center index .rule4a read) :
    old.key = new.key := by
  apply Option.some.inj
  exact old.built.symm.trans
    ((input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized read _ _).symm.trans new.built)

theorem original_rule4a_pair_compare (input : LocalizedUniversalReference.Input)
    {center : input.certified.TetrahedralCenter} {leftIndex rightIndex : Fin 4}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (left : input.certified.OriginalRootArm center leftIndex .rule4a
      (input.certified.molecularReader descriptorMap target))
    (right : input.certified.OriginalRootArm center rightIndex .rule4a
      (input.certified.molecularReader descriptorMap target))
    {W D : Nat} (widthL : (armGraph left).width ≤ W) (depthL : (armGraph left).height ≤ D)
    (widthR : (armGraph right).width ≤ W) (depthR : (armGraph right).height ≤ D) :
    input.certified.compareLocalizedRerootCumulativeRule45Keys left.key right.key =
      compare
        (molecularRankPairAt input.certified.moleculeGraph descriptorMap
          (input.certified.topUnit center) (armGraph left) W D)
        (molecularRankPairAt input.certified.moleculeGraph descriptorMap
          (input.certified.topUnit center) (armGraph right) W D) := by
  have readL := armReadback_of_treeLike_of_tetrahedralMap input descriptorMap tetrahedral
    target targetRoot targetAddress singleBonded acyclic left
  have readR := armReadback_of_treeLike_of_tetrahedralMap input descriptorMap tetrahedral
    target targetRoot targetAddress singleBonded acyclic right
  have repL := (arm_node_bridge4a left readL widthL depthL
    (armGraph left).root left.tree left.key left.trace rfl).2
  have repR := (arm_node_bridge4a right readR widthR depthR
    (armGraph right).root right.tree right.key right.trace rfl).2
  have constitution := arm_compare_eq_compare_vector left right widthL depthL widthR depthR
  change
    (OfficialRuleMajorKey.compare left.key.constitutional right.key.constitutional).then
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.key.descriptor right.key.descriptor) =
    (compare
      (ruleKey input.certified.moleculeGraph (armGraph left) W D (armGraph left).root)
      (ruleKey input.certified.moleculeGraph (armGraph right) W D (armGraph right).root)).then _
  rw [constitution]
  cases h : compare
      (ruleKey input.certified.moleculeGraph (armGraph left) W D (armGraph left).root)
      (ruleKey input.certified.moleculeGraph (armGraph right) W D (armGraph right).root) with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp only [Ordering.eq_then]
      have tied := constitution.trans h
      simp only [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey,
        Ordering.then_eq_eq] at tied
      exact compare_descriptor_eq_compare_key left.tableMatch right.tableMatch
        left.realizes right.realizes tied.1
        (ordinaryKey_stereo_wellShaped input.certified.moleculeGraph (armGraph left) _ W D
          .rule4aStereogenicUnitKind (armGraph left).root)
        (ordinaryKey_stereo_wellShaped input.certified.moleculeGraph (armGraph right) _ W D
          .rule4aStereogenicUnitKind (armGraph right).root) repL repR

/-- The compound's actual Rule-4a comparison equals the independent molecular prefix on
arbitrary tree-like tetrahedral evidence, without a rigid/twin or no-lowercase restriction. -/
theorem ruleMajor_rule4a_pair_compare (input : LocalizedUniversalReference.Input)
    {center : input.certified.TetrahedralCenter} {leftIndex rightIndex : Fin 4}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (left : input.certified.RuleMajorRootArm center leftIndex .rule4a
      (input.certified.molecularReader descriptorMap target))
    (right : input.certified.RuleMajorRootArm center rightIndex .rule4a
      (input.certified.molecularReader descriptorMap target))
    {W D : Nat} (widthL : (ruleMajorArmGraph left).width ≤ W)
    (depthL : (ruleMajorArmGraph left).height ≤ D)
    (widthR : (ruleMajorArmGraph right).width ≤ W)
    (depthR : (ruleMajorArmGraph right).height ≤ D) :
    input.certified.compareLocalizedRerootCumulativeRule45Keys left.key right.key =
      compare
        (molecularRankPairAt input.certified.moleculeGraph descriptorMap
          (input.certified.topUnit center) (ruleMajorArmGraph left) W D)
        (molecularRankPairAt input.certified.moleculeGraph descriptorMap
          (input.certified.topUnit center) (ruleMajorArmGraph right) W D) := by
  obtain ⟨oldL⟩ := input.certified.exists_originalRootArm center leftIndex .rule4a
    (input.certified.molecularReader descriptorMap target)
  obtain ⟨oldR⟩ := input.certified.exists_originalRootArm center rightIndex .rule4a
    (input.certified.molecularReader descriptorMap target)
  have lw := width_eq_of_faithful input.certified.moleculeGraph center.1
    (input.certified.canonicalLigandAtom center leftIndex) oldL.faithful left.faithful
  have ld := height_eq_of_faithful input.certified.moleculeGraph center.1
    (input.certified.canonicalLigandAtom center leftIndex) oldL.faithful left.faithful
  have rw' := width_eq_of_faithful input.certified.moleculeGraph center.1
    (input.certified.canonicalLigandAtom center rightIndex) oldR.faithful right.faithful
  have rd := height_eq_of_faithful input.certified.moleculeGraph center.1
    (input.certified.canonicalLigandAtom center rightIndex) oldR.faithful right.faithful
  have comparison := original_rule4a_pair_compare input descriptorMap tetrahedral target
    targetRoot targetAddress singleBonded acyclic oldL oldR
    (lw.trans_le widthL) (ld.trans_le depthL) (rw'.trans_le widthR) (rd.trans_le depthR)
  rw [original_ruleMajor_rule4a_key_eq oldL left, original_ruleMajor_rule4a_key_eq oldR right,
    molecularRankPairAt_eq_of_faithful input.certified.moleculeGraph descriptorMap
      (input.certified.topUnit center) center.1 (input.certified.canonicalLigandAtom center leftIndex)
      oldL.faithful left.faithful W D,
    molecularRankPairAt_eq_of_faithful input.certified.moleculeGraph descriptorMap
      (input.certified.topUnit center) center.1 (input.certified.canonicalLigandAtom center rightIndex)
      oldR.faithful right.faithful W D] at comparison
  exact comparison

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecularRankPairAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecularRankPairAt_eq_of_faithful
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.original_ruleMajor_rule4a_key_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.original_rule4a_pair_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajor_rule4a_pair_compare
