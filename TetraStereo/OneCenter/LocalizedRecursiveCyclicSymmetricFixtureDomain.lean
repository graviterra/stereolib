import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
import TetraStereo.OneCenter.LocalizedPhysicalDomainReindexing
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Detected-frame physical domain for the symmetric cyclic fixture

This module transports the explicit canonical-frame geometry and physical branch facts for the
nine-atom triangle to the certified input's actual detected molecule in one per-center ligand
reindexing. It inhabits the new recursive auxiliary physical domain at every detected root. It
makes no claim about production auxiliary labels or whole-report execution.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.CartesianPoint3
open CertifiedLocalizedCIPInput
open scoped Classical

noncomputable section

private theorem sourcePointAt (atom : Fin 9) :
    symmetricCertified.spatialPointAt? atom =
      some (positions[atom.val]'(by simp [positions])) := by
  rw [symmetricCertified.spatialPointAt?_eq_some_iff]
  refine ⟨⟨positions⟩, rfl, ?_⟩
  change positions[atom.val]? = some _
  exact List.getElem?_eq_getElem (by simp [positions])

private theorem canonicalCoordinates0 :
    ActualPhysicalCalibratedCoordinates symmetricCertified canon calibratedCfg center0 := by
  refine ⟨![P1, P2, P4, P5], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center0 0) = some P1
      rw [ligands0.1]
      exact sourcePointAt 1
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center0 1) = some P2
      rw [ligands0.2.1]
      exact sourcePointAt 2
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center0 2) = some P4
      rw [ligands0.2.2.1]
      exact sourcePointAt 4
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center0 3) = some P5
      rw [ligands0.2.2.2]
      exact sourcePointAt 5
  · change orientedVolume P1 P2 P4 P5 ≠ 0
    rw [volume0]
    norm_num
  · change rationalVolumeSign (orientedVolume P1 P2 P4 P5) =
      canon.configurationSign calibratedCfg center0
    rw [volume0, cfgSign0]
    norm_num [rationalVolumeSign]

private theorem canonicalCoordinates2 :
    ActualPhysicalCalibratedCoordinates symmetricCertified canon calibratedCfg center2 := by
  refine ⟨![P0, P3, P4, P6], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center2 0) = some P0
      rw [ligands2.1]
      exact sourcePointAt 0
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center2 1) = some P3
      rw [ligands2.2.1]
      exact sourcePointAt 3
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center2 2) = some P4
      rw [ligands2.2.2.1]
      exact sourcePointAt 4
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center2 3) = some P6
      rw [ligands2.2.2.2]
      exact sourcePointAt 6
  · change orientedVolume P0 P3 P4 P6 ≠ 0
    rw [volume2]
    norm_num
  · change rationalVolumeSign (orientedVolume P0 P3 P4 P6) =
      canon.configurationSign calibratedCfg center2
    rw [volume2, cfgSign2]
    norm_num [rationalVolumeSign]

private theorem canonicalCoordinates4 :
    ActualPhysicalCalibratedCoordinates symmetricCertified canon calibratedCfg center4 := by
  refine ⟨![P0, P2, P7, P8], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center4 0) = some P0
      rw [ligands4.1]
      exact sourcePointAt 0
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center4 1) = some P2
      rw [ligands4.2.1]
      exact sourcePointAt 2
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center4 2) = some P7
      rw [ligands4.2.2.1]
      exact sourcePointAt 7
    · change symmetricCertified.spatialPointAt? (canon.ligandAtomAt center4 3) = some P8
      rw [ligands4.2.2.2]
      exact sourcePointAt 8
  · change orientedVolume P0 P2 P7 P8 ≠ 0
    rw [volume4]
    norm_num
  · change rationalVolumeSign (orientedVolume P0 P2 P7 P8) =
      canon.configurationSign calibratedCfg center4
    rw [volume4, cfgSign4]
    norm_num [rationalVolumeSign]

private theorem canonicalCoordinates (center : canon.Center) :
    ActualPhysicalCalibratedCoordinates symmetricCertified canon calibratedCfg center := by
  have hc : center.1 = 0 ∨ center.1 = 2 ∨ center.1 = 4 := by
    have h : center.1 ∈ graph.tetrahedralCenterSet := by
      change center.1 ∈ canon.centers
      exact center.2
    exact (degree_four_iff center.1).mp h
  rcases hc with h0 | h2 | h4
  · have heq : center = center0 := Subtype.ext h0
    subst center
    exact canonicalCoordinates0
  · have heq : center = center2 := Subtype.ext h2
    subst center
    exact canonicalCoordinates2
  · have heq : center = center4 := Subtype.ext h4
    subst center
    exact canonicalCoordinates4

private theorem calibratedCoordinates_reindexFrames
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    {cfg : m.Configuration} (tau : m.Center → Equiv.Perm (Fin 4)) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input (m.reindexFrames tau)
      (m.reindexConfiguration tau cfg) center := by
  obtain ⟨pointAt, observed, nonzero, sign⟩ := coordinates
  refine ⟨fun i => pointAt (tau center i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact observed (tau center i)
  · exact cartesianOrientedVolume_perm_ne_zero pointAt (tau center) nonzero
  · have hvec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) k = pointAt k := by
      intro k
      fin_cases k <;> rfl
    have hperm : RationalTetrahedralPermutation.permutedOrientedVolume
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) (tau center) =
        CartesianPoint3.orientedVolume
          (pointAt (tau center 0)) (pointAt (tau center 1))
            (pointAt (tau center 2)) (pointAt (tau center 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
    rw [← hperm, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

private theorem calibratedCoordinates_congr
    {input : CertifiedLocalizedCIPInput} {m n : MultiCenterMolecule input.Atom}
    (h : m = n) (cfg : m.Configuration) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) center) := by
  cases h
  exact coordinates

private theorem pairwiseProper_congr
    {m n : MultiCenterMolecule (Fin 9)} (h : m = n) (cfg : m.Configuration)
    (center : m.Center)
    (proper : MultiCenterMolecule.PairwiseProperDistinguishable m cfg center) :
    MultiCenterMolecule.PairwiseProperDistinguishable n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) center) := by
  cases h
  exact proper

private theorem physicalPairCount_congr
    {m n : MultiCenterMolecule (Fin 9)} (h : m = n) (cfg : m.Configuration)
    (center : m.Center) :
    physicalEnantiomorphicPairCount n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) center) =
      physicalEnantiomorphicPairCount m cfg center := by
  cases h
  rfl


/-- Canonical and detected molecules differ only by one per-center ligand-frame reindexing. -/
theorem detectedFrameReindex :
    ∃ tau : canon.Center → Equiv.Perm (Fin 4),
      canon.reindexFrames tau = symmetricCertified.detectedMultiCenterMolecule := by
  apply symmetricCertified.exists_reindexFrames_detectedMultiCenterMolecule (m := canon)
  · rfl
  · rfl

noncomputable def fixtureTau : canon.Center → Equiv.Perm (Fin 4) :=
  Classical.choose detectedFrameReindex

theorem fixtureTau_spec :
    canon.reindexFrames fixtureTau = symmetricCertified.detectedMultiCenterMolecule :=
  Classical.choose_spec detectedFrameReindex

noncomputable def detectedCfg :
    symmetricCertified.detectedMultiCenterMolecule.Configuration :=
  Eq.mp (congrArg MultiCenterMolecule.Configuration fixtureTau_spec)
    (canon.reindexConfiguration fixtureTau calibratedCfg)


private theorem detectedCoordinates
    (center : symmetricCertified.detectedMultiCenterMolecule.Center) :
    ActualPhysicalCalibratedCoordinates symmetricCertified
      symmetricCertified.detectedMultiCenterMolecule detectedCfg center := by
  let center' : (canon.reindexFrames fixtureTau).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center fixtureTau_spec.symm) center
  have coordinates' := calibratedCoordinates_reindexFrames
    (input := symmetricCertified) (m := canon) (cfg := calibratedCfg)
    fixtureTau center' (canonicalCoordinates center')
  simpa [detectedCfg] using
    calibratedCoordinates_congr (input := symmetricCertified)
      (m := canon.reindexFrames fixtureTau)
      (n := symmetricCertified.detectedMultiCenterMolecule) fixtureTau_spec
      (canon.reindexConfiguration fixtureTau calibratedCfg) center' coordinates'

/-- Public projection of the coordinate branch used to inhabit the recursive auxiliary domain. -/
theorem detectedCoordinates_at
    (center : symmetricCertified.detectedMultiCenterMolecule.Center) :
    ActualPhysicalCalibratedCoordinates symmetricCertified
      symmetricCertified.detectedMultiCenterMolecule detectedCfg center :=
  detectedCoordinates center

private theorem canonicalPairwiseAt (center : canon.Center) :
    MultiCenterMolecule.PairwiseProperDistinguishable canon calibratedCfg center := by
  have hc : center.1 = 0 ∨ center.1 = 2 ∨ center.1 = 4 :=
    (degree_four_iff center.1).mp center.2
  rcases hc with h0 | h2 | h4
  · have heq : center = center0 := Subtype.ext h0
    subst center
    exact pairwiseProperAt0
  · have heq : center = center2 := Subtype.ext h2
    subst center
    exact pairwiseProperAt2
  · have heq : center = center4 := Subtype.ext h4
    subst center
    exact pairwiseProperAt4

private theorem canonicalPairCountAt (center : canon.Center) :
    physicalEnantiomorphicPairCount canon calibratedCfg center = 1 := by
  have hc : center.1 = 0 ∨ center.1 = 2 ∨ center.1 = 4 :=
    (degree_four_iff center.1).mp center.2
  rcases hc with h0 | h2 | h4
  · have heq : center = center0 := Subtype.ext h0
    subst center
    exact physicalPairCountAt0
  · have heq : center = center2 := Subtype.ext h2
    subst center
    exact physicalPairCountAt2
  · have heq : center = center4 := Subtype.ext h4
    subst center
    exact physicalPairCountAt4

/-- Every detected ring center inhabits the new recursive auxiliary domain. All three molecular
centers have calibrated coordinates, so the non-root case is witnessed directly without imposing
constitutional rigidity. -/
theorem detectedDomainAtEveryRoot :
    ∀ root : symmetricCertified.detectedMultiCenterMolecule.Center,
      RecursiveAuxiliaryPhysicalDomain symmetricCertified detectedCfg root := by
  intro root
  refine ⟨?_⟩
  intro center _
  exact Or.inr (detectedCoordinates center)

theorem detectedPairwiseProperAtEveryRoot :
    ∀ root : symmetricCertified.detectedMultiCenterMolecule.Center,
      MultiCenterMolecule.PairwiseProperDistinguishable
        symmetricCertified.detectedMultiCenterMolecule detectedCfg root := by
  intro root
  let root' : (canon.reindexFrames fixtureTau).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center fixtureTau_spec.symm) root
  have hpair := (MultiCenterMolecule.pairwiseProperDistinguishable_reindexFrames_iff
    canon fixtureTau calibratedCfg root').2 (canonicalPairwiseAt root')
  simpa [detectedCfg] using
    pairwiseProper_congr fixtureTau_spec
      (canon.reindexConfiguration fixtureTau calibratedCfg) root' hpair

theorem detectedPairCountAtEveryRoot :
    ∀ root : symmetricCertified.detectedMultiCenterMolecule.Center,
      physicalEnantiomorphicPairCount
        symmetricCertified.detectedMultiCenterMolecule detectedCfg root = 1 := by
  intro root
  let root' : (canon.reindexFrames fixtureTau).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center fixtureTau_spec.symm) root
  have hcount := physicalEnantiomorphicPairCount_reindexFrames
    canon fixtureTau calibratedCfg root'
  have hcanonical := canonicalPairCountAt root'
  calc
    physicalEnantiomorphicPairCount
        symmetricCertified.detectedMultiCenterMolecule detectedCfg root =
      physicalEnantiomorphicPairCount
        (canon.reindexFrames fixtureTau) (canon.reindexConfiguration fixtureTau calibratedCfg) root' := by
          simpa [detectedCfg] using physicalPairCount_congr fixtureTau_spec
            (canon.reindexConfiguration fixtureTau calibratedCfg) root'
    _ = 1 := hcount.trans hcanonical

end
end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedFrameReindex
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain.fixtureTau_spec
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedDomainAtEveryRoot
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCoordinates_at
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedPairwiseProperAtEveryRoot
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedPairCountAtEveryRoot
