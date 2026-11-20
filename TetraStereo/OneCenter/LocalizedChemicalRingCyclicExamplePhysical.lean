import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput
import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Physical data for the actual retained-evaluator ring input. The diagram channel added by
the raw adapter leaves the certified graph and coordinates unchanged. All detected centers
have calibrated geometry, distinct proper branches, and one physical mirror pair. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical

noncomputable section

open LocalizedChemicalRingCyclicExampleInput
open LocalizedRecursiveCyclicSymmetricFixture
open LocalizedRecursiveCyclicSymmetricFixtureDomain
open LocalizedRecursiveAuxiliaryPhysicalDomain
open RootedTetrahedralBranchSymmetry

abbrev physical := certified.detectedMultiCenterMolecule

def cfg : physical.Configuration := detectedCfg

theorem cyclic : ¬ certified.moleculeGraph.Acyclic :=
  LocalizedCyclicPseudoInputWitness.not_acyclic

theorem calibrated (center : physical.Center) :
    ActualPhysicalCalibratedCoordinates certified physical cfg center :=
  detectedCoordinates_at center

theorem domain (center : physical.Center) :
    RecursiveAuxiliaryPhysicalDomain certified cfg center :=
  ⟨fun other _ => Or.inr (calibrated other)⟩

theorem proper_distinct (center : physical.Center) :
    physical.PairwiseProperDistinguishable cfg center :=
  detectedPairwiseProperAtEveryRoot center

theorem mirror_pair_count (center : physical.Center) :
    physicalEnantiomorphicPairCount physical cfg center = 1 :=
  detectedPairCountAtEveryRoot center

private theorem rigid_of_reindexed_rigid {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (tau : m.Center → Equiv.Perm (Fin 4)) (c : m.Center)
    (rigid : ConstitutionallyRigid (m.reindexFrames tau) c) : ConstitutionallyRigid m c := by
  intro e fixed
  have reindexed := rigid (m.autReindex tau e) (by
    rw [MultiCenterMolecule.reindexFrames_centerPerm]
    exact fixed)
  rw [MultiCenterMolecule.reindexFrames_ligandPermAt,
    MultiCenterMolecule.reindexFrames_centerPerm, fixed] at reindexed
  have canceled := congrArg (fun p : Equiv.Perm (Fin 4) => tau c * p * (tau c)⁻¹) reindexed
  simpa [mul_assoc] using canceled

theorem no_constitutionally_rigid_center (center : physical.Center) :
    ¬ ConstitutionallyRigid physical center := by
  have canonical : ∀ c : canon.Center, ¬ ConstitutionallyRigid canon c := by
    intro c
    have cases := (degree_four_iff c.1).mp c.2
    rcases cases with h | h | h
    · have same : c = center0 := Subtype.ext h
      simpa only [same] using center0_not_constitutionallyRigid
    · have same : c = center2 := Subtype.ext h
      simpa only [same] using center2_not_constitutionallyRigid
    · have same : c = center4 := Subtype.ext h
      simpa only [same] using center4_not_constitutionallyRigid
  have every : ∀ c : (canon.reindexFrames fixtureTau).Center,
      ¬ ConstitutionallyRigid (canon.reindexFrames fixtureTau) c := by
    intro c rigid
    exact canonical c (rigid_of_reindexed_rigid canon fixtureTau c rigid)
  rw [fixtureTau_spec] at every
  exact every center

end
end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical.calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical.cyclic
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical.domain
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical.proper_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical.mirror_pair_count
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical.no_constitutionally_rigid_center
