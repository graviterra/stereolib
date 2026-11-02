import TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Physical root symmetry results for the actual cyclic fixture

This module transports root branch symmetry facts from the canonical `Fin 9` fixture to the
actual certified atom type, molecule, configuration, and detected root exposed by
`LocalizedCyclicPseudoPhysicalDomain`.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs

noncomputable section

open TetraStereo.OneCenter
open RootedTetrahedralBranchSymmetry
open LocalizedCyclicPseudoInputWitness
open LocalizedCyclicPseudoSpatialWitness
open LocalizedCyclicPseudoPhysicalDomain

private theorem actualAdj (i j : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.Adj (atomEquiv i) (atomEquiv j) ↔ graph.Adj i j := by
  exact LocalizedCyclicPseudoPhysicalDomain.actualAdj i j

private theorem actualNeighborFinset (i : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.neighborFinset (atomEquiv i) =
      Finset.map atomEquiv.toEmbedding (graph.neighborFinset i) := by
  ext a
  constructor
  · intro ha
    let j := atomEquiv.symm a
    refine Finset.mem_map.mpr ⟨j, ?_, atomEquiv.apply_symm_apply a⟩
    exact (MoleculeGraph.mem_neighborFinset _ _ _).mpr
      ((actualAdj i j).mp ((MoleculeGraph.mem_neighborFinset _ _ _).mp ha))
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨j, hj, hja⟩
    subst a
    exact (MoleculeGraph.mem_neighborFinset _ _ _).mpr
      ((actualAdj i j).mpr ((MoleculeGraph.mem_neighborFinset _ _ _).mp hj))

private theorem inputCenter_iff_graph (i : Fin 9) :
    atomEquiv i ∈ pseudoSpatialCertified.tetrahedralCenterSet ↔
      i ∈ graph.tetrahedralCenterSet := by
  rw [CertifiedLocalizedCIPInput.tetrahedralCenterSet,
    MoleculeGraph.mem_tetrahedralCenterSet, MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card,
    MoleculeGraph.mem_tetrahedralCenterSet, MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card,
    actualNeighborFinset, Finset.card_map]

private theorem actualCenter_iff (i : Fin 9) :
    atomEquiv i ∈ physicalMolecule.centers ↔ i ∈ canon.centers := by
  calc
    atomEquiv i ∈ physicalMolecule.centers ↔ i ∈ graph.tetrahedralCenterSet := by
      rw [actual_detected_center_inventory, CertifiedLocalizedCIPInput.tetrahedralCenterSet]
      exact inputCenter_iff_graph i
    _ ↔ i ∈ canon.centers := by rw [LocalizedCyclicPseudoSpatialWitness.canon_centers]

private noncomputable def centerEquiv : physicalMolecule.Center ≃ canon.Center where
  toFun c := ⟨atomEquiv.symm c.1, by
    have hc : atomEquiv (atomEquiv.symm c.1) ∈ physicalMolecule.centers := by
      rw [atomEquiv.apply_symm_apply]
      exact c.2
    exact (actualCenter_iff (atomEquiv.symm c.1)).mp hc⟩
  invFun c := ⟨atomEquiv c.1, (actualCenter_iff c.1).mpr (by
    have hc : c.1 ∈ graph.tetrahedralCenterSet := by
      simpa only [LocalizedCyclicPseudoSpatialWitness.canon_centers] using c.2
    exact hc)⟩
  left_inv := by intro c; apply Subtype.ext; simp
  right_inv := by intro c; apply Subtype.ext; simp

private def actualToCanonHom :
    physicalMolecule.mol.underlyingSimpleGraph →g canon.mol.underlyingSimpleGraph where
  toFun := atomEquiv.symm
  map_rel' := by
    intro a b hab
    apply (MoleculeGraph.underlyingSimpleGraph_adj canon.mol _ _).2
    apply (actualAdj (atomEquiv.symm a) (atomEquiv.symm b)).mp
    exact (MoleculeGraph.underlyingSimpleGraph_adj physicalMolecule.mol _ _).mp hab

private theorem actualReach_to_canon (i : Fin 4) (d : physicalMolecule.Center) :
    LigandBranchReaches physicalMolecule LocalizedCyclicPseudoPhysicalDomain.rootCenter i d.1 →
      LigandBranchReaches canon LocalizedCyclicPseudoSpatialWitness.rootCenter i
        (centerToCanon d).1 := by
  rintro ⟨p, avoid⟩
  have start : actualToCanonHom (physicalMolecule.ligandAtomAt
      LocalizedCyclicPseudoPhysicalDomain.rootCenter i) =
      canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter i := by
    change atomEquiv.symm (physicalMolecule.ligandAtomAt
      (centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter) i) = _
    rw [physical_ligandAt]
    simp
  have finish : actualToCanonHom d.1 = (centerToCanon d).1 := rfl
  refine ⟨(p.map actualToCanonHom).copy start finish, ?_⟩
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
  intro hmem
  rcases List.mem_map.mp hmem with ⟨x, hx, hxroot⟩
  apply avoid
  have hxactual : x = LocalizedCyclicPseudoPhysicalDomain.rootCenter.1 := by
    change atomEquiv.symm x = LocalizedCyclicPseudoSpatialWitness.rootCenter.1
      at hxroot
    simpa [LocalizedCyclicPseudoPhysicalDomain.rootCenter,
      LocalizedCyclicPseudoSpatialWitness.rootCenter] using congrArg atomEquiv hxroot
  simpa [hxactual] using hx

theorem actual_mirror_transport :
    MirrorTransport physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter 1 2 := by
  rcases LocalizedCyclicPseudoSpatialWitness.mirror_transport
      with ⟨e0, hc0, hi0, hs0⟩
  let e := pushforwardAut e0
  have hc : physicalMolecule.centerPerm e LocalizedCyclicPseudoPhysicalDomain.rootCenter =
      LocalizedCyclicPseudoPhysicalDomain.rootCenter := by
    change physicalMolecule.centerPerm e
        (centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter) = _
    rw [centerPerm_pushforward, hc0]
    change centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter =
      centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter
    rfl
  have hi : physicalMolecule.ligandPermAt e
      LocalizedCyclicPseudoPhysicalDomain.rootCenter 1 = 2 := by
    rw [show LocalizedCyclicPseudoPhysicalDomain.rootCenter =
      centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter by rfl,
      ligandPermAt_pushforward]
    exact hi0
  refine ⟨e, hc, hi, ?_⟩
  intro d hd
  let d0 := centerToCanon d
  have dEq : d = centerFromCanon d0 := (centerFromCanon_toCanon d).symm
  rw [dEq]
  have hd0 := actualReach_to_canon 1 (centerFromCanon d0) (by simpa using hd)
  have hcanon := hs0 d0 hd0
  dsimp only [e]
  rw [configurationSign_physicalCfg d0]
  rw [ligandPermAt_pushforward_eq e0 d0]
  rw [centerPerm_pushforward e0 d0, configurationSign_physicalCfg]
  exact hcanon

private theorem actual_reach_arm :
    LigandBranchReaches physicalMolecule LocalizedCyclicPseudoPhysicalDomain.rootCenter 1
      (centerFromCanon LocalizedCyclicPseudoSpatialWitness.armCenter).1 := by
  have start : physicalMolecule.ligandAtomAt
      LocalizedCyclicPseudoPhysicalDomain.rootCenter 1 =
      (centerFromCanon LocalizedCyclicPseudoSpatialWitness.armCenter).1 := by
    change atomEquiv (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter 1) = _
    exact congrArg atomEquiv LocalizedCyclicPseudoSpatialWitness.root_ligands.2.1
  simpa [start] using ligandBranchReaches_self physicalMolecule
    LocalizedCyclicPseudoPhysicalDomain.rootCenter 1

theorem actual_not_proper_transport :
    ¬ ProperTransport physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter 1 2 := by
  intro htransport
  rcases htransport with ⟨eA, hcA, hiA, hsA⟩
  let e0 := pullbackAut eA
  have eAeq : eA = pushforwardAut e0 := (pushforward_pullbackAut eA).symm
  rw [eAeq] at hcA hiA hsA
  have hcLift : centerFromCanon
      (canon.centerPerm e0 LocalizedCyclicPseudoSpatialWitness.rootCenter) =
      centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter := by
    simpa only [centerPerm_pushforward] using hcA
  have hc0 : canon.centerPerm e0 LocalizedCyclicPseudoSpatialWitness.rootCenter =
      LocalizedCyclicPseudoSpatialWitness.rootCenter := by
    have h := congrArg centerToCanon hcLift
    simpa only [centerToCanon_fromCanon] using h
  have hi0 : canon.ligandPermAt e0 LocalizedCyclicPseudoSpatialWitness.rootCenter 1 = 2 := by
    simpa only [ligandPermAt_pushforward] using hiA
  rcases LocalizedCyclicPseudoSpatialWitness.canon_automorphism_dichotomy e0 with hid | hmirror
  · rw [hid] at hi0
    simp [canon.ligandPermAt_one] at hi0
  · have hsArm := hsA (centerFromCanon LocalizedCyclicPseudoSpatialWitness.armCenter)
      actual_reach_arm
    rw [hmirror, configurationSign_physicalCfg, ligandPermAt_pushforward_eq,
      centerPerm_pushforward, configurationSign_physicalCfg,
      LocalizedCyclicPseudoSpatialWitness.mirror_handedness_arm] at hsArm
    have armImage : canon.centerPerm LocalizedCyclicPseudoSpatialWitness.canonMirror
        LocalizedCyclicPseudoSpatialWitness.armCenter =
        LocalizedCyclicPseudoSpatialWitness.closingCenter := by
      apply Subtype.ext
      change (LocalizedCyclicPseudoSpatialWitness.canonMirror : Equiv.Perm (Fin 9))
        LocalizedCyclicPseudoSpatialWitness.armCenter.1 =
        LocalizedCyclicPseudoSpatialWitness.closingCenter.1
      rfl
    rw [armImage, LocalizedCyclicPseudoSpatialWitness.arm_configurationSign,
      LocalizedCyclicPseudoSpatialWitness.closing_configurationSign] at hsArm
    norm_num at hsArm

private theorem actualRootSlotZ (i : Fin 4) :
    physicalMolecule.mol.atomZ
        (physicalMolecule.ligandAtomAt LocalizedCyclicPseudoPhysicalDomain.rootCenter i) =
      graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter i) := by
  change pseudoSpatialCertified.moleculeGraph.atomZ
      (physicalMolecule.ligandAtomAt LocalizedCyclicPseudoPhysicalDomain.rootCenter i) = _
  rw [show LocalizedCyclicPseudoPhysicalDomain.rootCenter =
    centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter by rfl,
    physical_ligandAt]
  exact actualZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter i)

private theorem rootSlotZ_eq_implies (i j : Fin 4)
    (hz : graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter i) =
      graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter j)) :
    i = j ∨ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) := by
  have zslot (k : Fin 4) :
      graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter k) =
        if k = 0 then 9 else if k = 1 then 6 else if k = 2 then 6 else 1 := by
    fin_cases k
    · change graph.atomZ (canon.ligandAtomAt
        LocalizedCyclicPseudoSpatialWitness.rootCenter 0) = 9
      rw [LocalizedCyclicPseudoSpatialWitness.root_ligands.1]
      exact (LocalizedCyclicPseudoInputWitness.z_fluorine 1).mpr rfl
    · change graph.atomZ (canon.ligandAtomAt
        LocalizedCyclicPseudoSpatialWitness.rootCenter 1) = 6
      rw [LocalizedCyclicPseudoSpatialWitness.root_ligands.2.1]
      exact (LocalizedCyclicPseudoInputWitness.z_carbon 2).mpr (Or.inr (Or.inl rfl))
    · change graph.atomZ (canon.ligandAtomAt
        LocalizedCyclicPseudoSpatialWitness.rootCenter 2) = 6
      rw [LocalizedCyclicPseudoSpatialWitness.root_ligands.2.2.1]
      exact (LocalizedCyclicPseudoInputWitness.z_carbon 4).mpr (Or.inr (Or.inr rfl))
    · change graph.atomZ (canon.ligandAtomAt
        LocalizedCyclicPseudoSpatialWitness.rootCenter 3) = 1
      rw [LocalizedCyclicPseudoSpatialWitness.root_ligands.2.2.2]
      exact (LocalizedCyclicPseudoInputWitness.z_hydrogen 5).mpr (Or.inl rfl)
  have hz' : (if i = 0 then 9 else if i = 1 then 6 else if i = 2 then 6 else 1) =
      (if j = 0 then 9 else if j = 1 then 6 else if j = 2 then 6 else 1) := by
    rw [← zslot i, ← zslot j]
    exact hz
  fin_cases i <;> fin_cases j
  all_goals norm_num [Fin.ext_iff] at hz'
  all_goals norm_num [Fin.ext_iff]

private theorem actual_root_ligand_z_invariant (e : physicalMolecule.Aut)
    (fixed : physicalMolecule.centerPerm e LocalizedCyclicPseudoPhysicalDomain.rootCenter =
      LocalizedCyclicPseudoPhysicalDomain.rootCenter) (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter
        (physicalMolecule.ligandPermAt e LocalizedCyclicPseudoPhysicalDomain.rootCenter i)) =
      graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter i) := by
  have action := physicalMolecule.ligandAtomAt_ligandPermAt e
    LocalizedCyclicPseudoPhysicalDomain.rootCenter i
  rw [fixed] at action
  let eMol : physicalMolecule.mol.Aut :=
    ⟨(e : Equiv.Perm pseudoSpatialCertified.Atom),
      MultiCenterMolecule.Aut.mem_molAut (m := physicalMolecule) e⟩
  have zpres := MoleculeGraph.Aut.atomZ_eq (m := physicalMolecule.mol) eMol
    (physicalMolecule.ligandAtomAt LocalizedCyclicPseudoPhysicalDomain.rootCenter i)
  calc
    graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter
        (physicalMolecule.ligandPermAt e LocalizedCyclicPseudoPhysicalDomain.rootCenter i)) =
        physicalMolecule.mol.atomZ
          (physicalMolecule.ligandAtomAt LocalizedCyclicPseudoPhysicalDomain.rootCenter
            (physicalMolecule.ligandPermAt e LocalizedCyclicPseudoPhysicalDomain.rootCenter i)) :=
      (actualRootSlotZ _).symm
    _ = physicalMolecule.mol.atomZ
          ((e : Equiv.Perm pseudoSpatialCertified.Atom)
            (physicalMolecule.ligandAtomAt LocalizedCyclicPseudoPhysicalDomain.rootCenter i)) :=
      congrArg physicalMolecule.mol.atomZ action
    _ = physicalMolecule.mol.atomZ
          (physicalMolecule.ligandAtomAt LocalizedCyclicPseudoPhysicalDomain.rootCenter i) := zpres
    _ = graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter i) :=
      actualRootSlotZ i

theorem actual_enantiomorphic_ring_carbons :
    Enantiomorphic physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter 1 2 := by
  exact ⟨by decide, actual_mirror_transport, actual_not_proper_transport⟩

theorem actual_root_enantiomorphic_iff (i j : Fin 4) :
    Enantiomorphic physicalMolecule physicalCfg LocalizedCyclicPseudoPhysicalDomain.rootCenter i j ↔
      ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) := by
  constructor
  · intro h
    rcases h with ⟨hij, ⟨e, fixed, sends, _⟩, _⟩
    have hZ := actual_root_ligand_z_invariant e fixed i
    have hZ' : graph.atomZ (canon.ligandAtomAt
        LocalizedCyclicPseudoSpatialWitness.rootCenter j) =
        graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter i) := by
      simpa [sends] using hZ
    rcases rootSlotZ_eq_implies j i hZ' with heq | hpair
    · exact False.elim (hij (heq.symm))
    · rcases hpair with ⟨hj, hi⟩ | ⟨hj, hi⟩
      · exact Or.inr ⟨hi, hj⟩
      · exact Or.inl ⟨hi, hj⟩
  · intro h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst i; subst j
      exact actual_enantiomorphic_ring_carbons
    · subst i; subst j
      exact enantiomorphic_symm physicalMolecule physicalCfg
        LocalizedCyclicPseudoPhysicalDomain.rootCenter actual_enantiomorphic_ring_carbons

theorem actual_root_physical_pair_count :
    physicalEnantiomorphicPairCount physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter = 1 := by
  rw [physicalEnantiomorphicPairCount_eq_one_iff]
  refine ⟨1, 2, by decide, actual_enantiomorphic_ring_carbons, ?_⟩
  intro otherFirst otherSecond _different enantiomorphic
  exact (actual_root_enantiomorphic_iff otherFirst otherSecond).mp enantiomorphic

private theorem proper_transport_root_z (i j : Fin 4)
    (hproper : ProperTransport physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter i j) :
    graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter j) =
      graph.atomZ (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.rootCenter i) := by
  rcases hproper with ⟨e, fixed, sends, _⟩
  have hz := actual_root_ligand_z_invariant e fixed i
  simpa [sends] using hz

/-- Every pair of distinct branches at the actual detected root is properly
distinguishable on the calibrated physical configuration. -/
theorem actual_pairwise_proper_distinguishable :
    MultiCenterMolecule.PairwiseProperDistinguishable physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter := by
  intro i j hij hproper
  have hz' := proper_transport_root_z i j hproper
  rcases rootSlotZ_eq_implies j i hz' with heq | hpair
  · exact hij heq.symm
  · rcases hpair with ⟨hj, hi⟩ | ⟨hj, hi⟩
    · subst j; subst i
      have hreverse :
          ProperTransport physicalMolecule physicalCfg
            LocalizedCyclicPseudoPhysicalDomain.rootCenter 1 2 :=
        branchTransport_inverse physicalMolecule physicalCfg
          LocalizedCyclicPseudoPhysicalDomain.rootCenter hproper
      exact actual_not_proper_transport hreverse
    · subst j; subst i
      exact actual_not_proper_transport hproper

end
end TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs.actual_mirror_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs.actual_not_proper_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs.actual_enantiomorphic_ring_carbons
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs.actual_root_enantiomorphic_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs.actual_root_physical_pair_count
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs.actual_pairwise_proper_distinguishable
