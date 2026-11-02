import TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader
import TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.LocalizedPhysicalDomainReindexing
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# General physical-root assembly for the cyclic pseudo fixture

This module connects the actual nine-atom fixture to the general cyclic final-root theorem. The
fixture's geometric molecule uses canonical sorted-neighbor slots; the theorem's input uses the
automatically detected molecule's independent finite enumeration. The bridge is explicit and
accounts for the per-center ligand reindexing and its orientation sign.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoGeneralTheorem

open TetraStereo.OneCenter
open CertifiedLocalizedCIPInput
open LocalizedRuleMajorReference
open LocalizedCyclicPseudoPhysicalDomain
open LocalizedCyclicPseudoSpatialWitness
open LocalizedCyclicPseudoActualEvaluation
open LocalizedCyclicPseudoActualRootLetter
open LocalizedCyclicPseudoComputableReader
open LocalizedCyclicRootPhysicalSetup
open LocalizedCyclicRootIndependentJudgment
open RootedTetrahedralBranchSymmetry

noncomputable section

private theorem molecule_ext {V : Type*} [Fintype V] [DecidableEq V]
    {m n : MultiCenterMolecule V}
    (hmol : m.mol = n.mol) (hcenters : m.centers = n.centers)
    (hl : ∀ c (hc : c ∈ m.centers) i,
      m.ligandAtom c hc i = n.ligandAtom c (hcenters ▸ hc) i) : m = n := by
  cases m with
  | mk mm mc ml ma mi ms =>
    cases n with
    | mk nm nc nl na ni ns =>
      dsimp at hmol hcenters hl
      subst nm
      subst nc
      have hfun : ml = nl := by
        funext c
        funext hc
        funext i
        exact hl c hc i
      subst nl
      rfl

/-- The fixture's physical molecule is the certified input's canonical detected molecule.
Its atom carrier is already the certified carrier; only the center-finset presentation differs. -/
theorem physicalMolecule_eq_canonicalDetected :
    physicalMolecule = canonicalDetectedMultiCenterMolecule pseudoSpatialCertified := by
  have hc : physicalMolecule.centers =
      (canonicalDetectedMultiCenterMolecule pseudoSpatialCertified).centers := by
    ext atom
    exact actual_detected_center_inventory (atomEquiv.symm atom)
  cases hc
  simp only [physicalMolecule, canonicalDetectedMultiCenterMolecule]
  apply molecule_ext rfl rfl
  intro c hc i
  rfl

private abbrev detectedMolecule := pseudoSpatialCertified.detectedMultiCenterMolecule

private noncomputable def rootFrameReindex (c : detectedMolecule.Center) :
    Equiv.Perm (Fin 4) :=
  pseudoSpatialCertified.canonicalLigandReindex c

/-- The detected molecule is the fixture's canonical molecule reindexed by the adapter's
per-center detected-to-canonical ligand permutation. -/
theorem detectedMolecule_eq_reindexedCanonical :
    detectedMolecule =
      (canonicalDetectedMultiCenterMolecule pseudoSpatialCertified).reindexFrames
        rootFrameReindex := by
  apply molecule_ext (m := detectedMolecule)
    (n := (canonicalDetectedMultiCenterMolecule pseudoSpatialCertified).reindexFrames
      rootFrameReindex) rfl rfl
  intro c hc i
  let cc : detectedMolecule.Center := ⟨c, hc⟩
  change detectedMolecule.ligandAtomAt cc i =
    (canonicalDetectedMultiCenterMolecule pseudoSpatialCertified).ligandAtomAt cc
      (rootFrameReindex cc i)
  rw [canonicalDetectedMultiCenterMolecule_ligandAtomAt]
  exact pseudoSpatialCertified.canonicalLigandReindex_spec cc i

private def canonicalRootPoints : Fin 4 → CartesianPoint3
  | 0 => P1
  | 1 => P2
  | 2 => P4
  | 3 => P5

private theorem sourcePointAt (i : Fin 9) :
    pseudoSpatialCertified.spatialPointAt? (atomEquiv i) =
      some (positions[i.val]'(by simp [positions])) := by
  rw [spatialPointAt?_eq_some_iff]
  refine ⟨⟨positions⟩, rfl, ?_⟩
  change positions[(atomEquiv i).val]? = some _
  rw [show (atomEquiv i).val = i.val by rfl]
  exact List.getElem?_eq_getElem (by simp [positions])

/-- The nine-atom cyclic fixture supplies physical root geometry in its canonical enumeration. -/
private theorem fixture_root_geometry :
    RootPhysicalGeometry pseudoSpatialCertified physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter := by
  refine ⟨canonicalRootPoints, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change pseudoSpatialCertified.spatialPointAt?
        (physicalMolecule.ligandAtomAt
          (centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter) 0) = some P1
      rw [physical_ligandAt, LocalizedCyclicPseudoSpatialWitness.root_ligands.1]
      exact sourcePointAt 1
    · change pseudoSpatialCertified.spatialPointAt?
        (physicalMolecule.ligandAtomAt
          (centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter) 1) = some P2
      rw [physical_ligandAt, LocalizedCyclicPseudoSpatialWitness.root_ligands.2.1]
      exact sourcePointAt 2
    · change pseudoSpatialCertified.spatialPointAt?
        (physicalMolecule.ligandAtomAt
          (centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter) 2) = some P4
      rw [physical_ligandAt, LocalizedCyclicPseudoSpatialWitness.root_ligands.2.2.1]
      exact sourcePointAt 4
    · change pseudoSpatialCertified.spatialPointAt?
        (physicalMolecule.ligandAtomAt
          (centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter) 3) = some P5
      rw [physical_ligandAt, LocalizedCyclicPseudoSpatialWitness.root_ligands.2.2.2]
      exact sourcePointAt 5
  · simp only [canonicalRootPoints]
    rw [LocalizedCyclicPseudoSpatialWitness.root_volume]
    norm_num
  · simp only [canonicalRootPoints]
    rw [LocalizedCyclicPseudoSpatialWitness.root_volume,
      actual_root_configuration_sign]
    norm_num [rationalVolumeSign]

/-- Root geometry follows the same per-center frame reindexing as the physical domain. -/
private theorem rootGeometry_reindexFrames
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    {cfg : m.Configuration} {root : m.Center}
    (geometry : RootPhysicalGeometry input m cfg root)
    (tau : m.Center → Equiv.Perm (Fin 4)) :
    RootPhysicalGeometry input (m.reindexFrames tau)
      (m.reindexConfiguration tau cfg) root := by
  obtain ⟨points, observed, nonzero, sign⟩ := geometry
  refine ⟨fun i => points (tau root i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact observed (tau root i)
  · exact cartesianOrientedVolume_perm_ne_zero points (tau root) nonzero
  · have hvec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector
          (points 0) (points 1) (points 2) (points 3) k = points k := by
      intro k
      fin_cases k <;> rfl
    have hperm : RationalTetrahedralPermutation.permutedOrientedVolume
        (points 0) (points 1) (points 2) (points 3) (tau root) =
      CartesianPoint3.orientedVolume
        (points (tau root 0)) (points (tau root 1))
          (points (tau root 2)) (points (tau root 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
    rw [← hperm, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

private theorem physicalDomain_congr_molecule
    {input : CertifiedLocalizedCIPInput} {m n : MultiCenterMolecule input.Atom}
    (h : m = n) (cfg : m.Configuration) (root : m.Center)
    (domain : ActualGeneralRigidPhysicalDomain input m cfg root) :
    ActualGeneralRigidPhysicalDomain input n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) root) := by
  cases h
  exact domain

private theorem pairwise_congr_molecule
    {m n : MultiCenterMolecule pseudoSpatialCertified.Atom} (h : m = n)
    (cfg : m.Configuration) (root : m.Center)
    (proper : MultiCenterMolecule.PairwiseProperDistinguishable m cfg root) :
    MultiCenterMolecule.PairwiseProperDistinguishable n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) root) := by
  cases h
  exact proper

private theorem geometry_congr_molecule
    {m n : MultiCenterMolecule pseudoSpatialCertified.Atom} (h : m = n)
    (cfg : m.Configuration) (root : m.Center)
    (geometry : RootPhysicalGeometry pseudoSpatialCertified m cfg root) :
    RootPhysicalGeometry pseudoSpatialCertified n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) root) := by
  cases h
  exact geometry

/-- All fixture atoms have formal charge zero. -/
private theorem fixture_constant_charge :
    AcyclicCutBranchAutomorphism.ConstantFormalCharge pseudoSpatialCertified.moleculeGraph := by
  refine ⟨0, ?_⟩
  intro atom
  obtain ⟨i, rfl⟩ := atomEquiv.surjective atom
  rw [actualCharge]
  fin_cases i <;> decide +kernel

/-- A concrete inhabitant of the general cyclic physical domain at the evaluator's own root.
The configuration is the fixture's calibrated configuration transported through the exact
detected-to-physical ligand reindexing. -/
theorem actual_cyclic_pseudo_physical_setup :
    ∃ cfg : detectedMolecule.Configuration,
      CyclicRootPhysicalDomain pseudoReference rootTetra cfg := by
  have hcenters : physicalMolecule.centers =
      pseudoSpatialCertified.tetrahedralCenterSet := by
    rw [physicalMolecule_eq_canonicalDetected,
      canonicalDetectedMultiCenterMolecule_centers]
  obtain ⟨tau, htau⟩ :=
    pseudoSpatialCertified.exists_reindexFrames_detectedMultiCenterMolecule
      (by rfl) hcenters
  have hroot_mem : rootTetra.1 ∈ physicalMolecule.centers := by
    rw [hcenters]
    exact rootTetra.2
  let rootPhysical : physicalMolecule.Center := ⟨rootTetra.1, hroot_mem⟩
  have hroot : rootPhysical = LocalizedCyclicPseudoPhysicalDomain.rootCenter := by
    apply Subtype.ext
    rfl
  let cfgReindexed := physicalMolecule.reindexConfiguration tau physicalCfg
  let cfgDetected : detectedMolecule.Configuration :=
    Eq.mp (congrArg MultiCenterMolecule.Configuration htau) cfgReindexed
  let rootDetected : detectedMolecule.Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center htau) rootPhysical
  have hrootDetected : rootDetected = rootTetra := by
    apply Subtype.ext
    rfl
  have domainReindexed := actualGeneralRigidPhysicalDomain_reindexFrames
    pseudoSpatialCertified physicalMolecule physicalCfg rootPhysical tau
    actual_physical_domain
  have domainDetected :
      ActualGeneralRigidPhysicalDomain pseudoSpatialCertified detectedMolecule
        cfgDetected rootTetra := by
    simpa [cfgDetected, rootDetected, hrootDetected] using
      physicalDomain_congr_molecule htau cfgReindexed rootPhysical domainReindexed
  have properReindexed :
      MultiCenterMolecule.PairwiseProperDistinguishable
        (physicalMolecule.reindexFrames tau) cfgReindexed rootPhysical := by
    exact (MultiCenterMolecule.pairwiseProperDistinguishable_reindexFrames_iff
      physicalMolecule tau physicalCfg
        LocalizedCyclicPseudoPhysicalDomain.rootCenter).2
        (by simpa [hroot] using
          LocalizedCyclicPseudoActualRootLetter.actual_root_pairwise_proper_distinguishable)
  have properDetected :
      MultiCenterMolecule.PairwiseProperDistinguishable detectedMolecule cfgDetected rootTetra := by
    simpa [cfgDetected, rootDetected, hrootDetected] using
      pairwise_congr_molecule htau cfgReindexed rootPhysical properReindexed
  have geometryReindexed :
      RootPhysicalGeometry pseudoSpatialCertified
        (physicalMolecule.reindexFrames tau) cfgReindexed rootPhysical := by
    simpa [hroot] using rootGeometry_reindexFrames fixture_root_geometry tau
  have geometryDetected :
      RootPhysicalGeometry pseudoSpatialCertified detectedMolecule cfgDetected rootTetra := by
    simpa [cfgDetected, rootDetected, hrootDetected] using
      geometry_congr_molecule htau cfgReindexed rootPhysical geometryReindexed
  exact ⟨cfgDetected, ⟨spatial_simpleBonded, fixture_constant_charge,
    domainDetected, properDetected, geometryDetected⟩⟩

/-- Instantiate the general final-root theorem on the actual nine-atom cyclic pseudo fixture.
The fixture setup, current root state, and physical lowercase count are all derived from its
certified input, spatial data, and the now-unconditional general physical theorem. -/
theorem actual_cyclic_pseudo_final_root_endpoint :
    ∃ cfg : detectedMolecule.Configuration,
      CyclicRootPhysicalDomain pseudoReference rootTetra cfg ∧
      referenceState pseudoReference rootTarget =
        some (.pseudoasymmetric PseudoRS.s : LocalizedAuxiliaryLabel) ∧
      physicalEnantiomorphicPairCount detectedMolecule cfg rootTetra = 1 := by
  obtain ⟨cfg, setup⟩ := actual_cyclic_pseudo_physical_setup
  obtain ⟨descriptor, returned, analyzed, executed, retained, lowercase, reading⟩ :=
    finalRoot_physical_descriptor setup
  have stateEq : descriptor =
      (.pseudoasymmetric PseudoRS.s : LocalizedAuxiliaryLabel) := by
    have h := returned.symm.trans actual_root_referenceState
    exact Option.some.inj h
  have descriptorLowercase : descriptor.IsLowercase := by
    rw [stateEq]
    trivial
  have physicalCount := lowercase.mp descriptorLowercase
  exact ⟨cfg, setup, actual_root_referenceState, physicalCount⟩


end

end TetraStereo.OneCenter.LocalizedCyclicPseudoGeneralTheorem

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoGeneralTheorem.physicalMolecule_eq_canonicalDetected
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoGeneralTheorem.detectedMolecule_eq_reindexedCanonical
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoGeneralTheorem.actual_cyclic_pseudo_physical_setup
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoGeneralTheorem.actual_cyclic_pseudo_final_root_endpoint
