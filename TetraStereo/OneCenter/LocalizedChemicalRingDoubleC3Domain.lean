import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The opposite-coordinate double-C3 fixture in the accepted detected-center frames.
The configuration is constructed from the actual spatial table and transported by the
derived frame correspondence. The recursive physical domain, root calibration, proper
branch distinction and physical pair count are inhabited independently of runtime labels
or evaluation success. This is the cyclic recursive domain, not the acyclic rigid domain. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain

open LocalizedChemicalRingDoubleC3Input LocalizedChemicalRingDoubleC3Physical
open LocalizedChemicalRingDoubleC3Geometry LocalizedActualPhysicalBranchDecision
open LocalizedRecursiveAuxiliaryPhysicalDomain RootedTetrahedralBranchSymmetry
open CertifiedLocalizedCIPInput CartesianPoint3

noncomputable section

abbrev input := certified true
abbrev detected := input.detectedMultiCenterMolecule

theorem detectedFrameReindex :
    ∃ tau : canon.Center → Equiv.Perm (Fin 4), canon.reindexFrames tau = detected :=
  input.exists_reindexFrames_detectedMultiCenterMolecule (m := canon) rfl rfl

def frameChange : canon.Center → Equiv.Perm (Fin 4) := Classical.choose detectedFrameReindex
theorem frameChange_spec : canon.reindexFrames frameChange = detected :=
  Classical.choose_spec detectedFrameReindex

def cfg : detected.Configuration :=
  Eq.mp (congrArg MultiCenterMolecule.Configuration frameChange_spec)
    (canon.reindexConfiguration frameChange (canonicalCfg true))

def detectedRoot : detected.Center := ⟨(0 : Fin 25), by
  change (0 : Fin 25) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

private theorem center_val_congr {m n : MultiCenterMolecule input.Atom}
    (h : m = n) (c : m.Center) :
    (Eq.mp (congrArg MultiCenterMolecule.Center h) c).1 = c.1 := by
  cases h
  rfl

theorem root_transfer :
    Eq.mp (congrArg MultiCenterMolecule.Center frameChange_spec) center0 = detectedRoot := by
  apply Subtype.ext
  exact center_val_congr frameChange_spec center0

private theorem calibration_reindexed (c : canon.Center) :
    ActualPhysicalCalibratedCoordinates input (canon.reindexFrames frameChange)
      (canon.reindexConfiguration frameChange (canonicalCfg true)) c := by
  obtain ⟨points, observed, nonzero, sign⟩ := canonical_calibrated true c
  refine ⟨fun i => points (frameChange c i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact observed _
  · exact cartesianOrientedVolume_perm_ne_zero points (frameChange c) nonzero
  · have vec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector (points 0) (points 1) (points 2) (points 3) k =
          points k := by intro k; fin_cases k <;> rfl
    have volume : RationalTetrahedralPermutation.permutedOrientedVolume
        (points 0) (points 1) (points 2) (points 3) (frameChange c) =
        orientedVolume (points (frameChange c 0)) (points (frameChange c 1))
          (points (frameChange c 2)) (points (frameChange c 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, vec]
    rw [← volume, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

theorem calibrated (c : detected.Center) :
    ActualPhysicalCalibratedCoordinates input detected cfg c := by
  let c' : (canon.reindexFrames frameChange).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center frameChange_spec.symm) c
  have transferred := calibration_reindexed c'
  have congruence {m n : MultiCenterMolecule input.Atom} (h : m = n)
      (configuration : m.Configuration) (d : m.Center)
      (proof : ActualPhysicalCalibratedCoordinates input m configuration d) :
      ActualPhysicalCalibratedCoordinates input n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) configuration)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) d) := by
    cases h
    exact proof
  simpa [cfg, c'] using congruence frameChange_spec
    (canon.reindexConfiguration frameChange (canonicalCfg true)) c' transferred

theorem domain (root : detected.Center) : RecursiveAuxiliaryPhysicalDomain input cfg root :=
  ⟨fun c _ => Or.inr (calibrated c)⟩

theorem root_calibrated : ActualPhysicalCalibratedCoordinates input detected cfg detectedRoot :=
  calibrated detectedRoot

theorem proper_distinct : detected.PairwiseProperDistinguishable cfg detectedRoot := by
  have congruence {m n : MultiCenterMolecule input.Atom} (h : m = n)
      (configuration : m.Configuration) (d : m.Center)
      (proof : m.PairwiseProperDistinguishable configuration d) :
      n.PairwiseProperDistinguishable
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) configuration)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) d) := by
    cases h
    exact proof
  have reindexed := (MultiCenterMolecule.pairwiseProperDistinguishable_reindexFrames_iff
    canon frameChange (canonicalCfg true) center0).mpr opposite_proper_distinct
  have transferred := congruence frameChange_spec
    (canon.reindexConfiguration frameChange (canonicalCfg true)) center0 reindexed
  rw [root_transfer] at transferred
  exact transferred

theorem mirror_pair_count : physicalEnantiomorphicPairCount detected cfg detectedRoot = 1 := by
  have transferred := LocalizedActualPhysicalBranchDecision.physicalPairCount_congr
    frameChange_spec (canon.reindexConfiguration frameChange (canonicalCfg true)) center0
  rw [root_transfer] at transferred
  exact transferred.trans ((physicalEnantiomorphicPairCount_reindexFrames
    canon frameChange (canonicalCfg true) center0).trans opposite_pair_count)

/-- The original source input and its detected root inhabit all the stated cyclic physical
conditions. No statement about the evaluator is included in this witness. -/
theorem actual_domain_witness :
    ∃ (configuration : detected.Configuration) (root : detected.Center),
      root.1 = (0 : Fin 25) ∧ RecursiveAuxiliaryPhysicalDomain input configuration root ∧
      ActualPhysicalCalibratedCoordinates input detected configuration root ∧
      detected.PairwiseProperDistinguishable configuration root ∧
      physicalEnantiomorphicPairCount detected configuration root = 1 :=
  ⟨cfg, detectedRoot, rfl, domain detectedRoot, root_calibrated, proper_distinct, mirror_pair_count⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.detectedFrameReindex
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.frameChange_spec
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.root_transfer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.domain
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.root_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.proper_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.mirror_pair_count
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain.actual_domain_witness
