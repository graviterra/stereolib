import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Root symmetry hypothesis for the detected symmetric cyclic fixture

This module transports the fixture's explicitly proved molecular symmetries to the actual
detected ligand frames. It does not assume a production label or descriptor.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureRootSymmetry

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.MultiCenterMolecule
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
open scoped Classical

private theorem rootSlotZ0 (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt center0 i) = ![17, 6, 6, 1] i := by
  fin_cases i
  · simpa [ligands0.1] using (atomZ_cases 1).2.1.mpr (by simp)
  · simpa [ligands0.2.1] using (atomZ_cases 2).1.mpr (Or.inr (Or.inl rfl))
  · simpa [ligands0.2.2.1] using (atomZ_cases 4).1.mpr (Or.inr (Or.inr rfl))
  · simpa [ligands0.2.2.2] using (atomZ_cases 5).2.2.mpr (by simp)

private theorem rootSlotZ2 (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt center2 i) = ![6, 17, 6, 1] i := by
  fin_cases i
  · simpa [ligands2.1] using (atomZ_cases 0).1.mpr (Or.inl rfl)
  · simpa [ligands2.2.1] using (atomZ_cases 3).2.1.mpr (Or.inr (Or.inl rfl))
  · simpa [ligands2.2.2.1] using (atomZ_cases 4).1.mpr (Or.inr (Or.inr rfl))
  · simpa [ligands2.2.2.2] using (atomZ_cases 6).2.2.mpr (Or.inr (Or.inl rfl))

private theorem rootSlotZ4 (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt center4 i) = ![6, 6, 1, 17] i := by
  fin_cases i
  · simpa [ligands4.1] using (atomZ_cases 0).1.mpr (Or.inl rfl)
  · simpa [ligands4.2.1] using (atomZ_cases 2).1.mpr (Or.inr (Or.inl rfl))
  · simpa [ligands4.2.2.1] using (atomZ_cases 7).2.2.mpr (Or.inr (Or.inr rfl))
  · simpa [ligands4.2.2.2] using (atomZ_cases 8).2.1.mpr (Or.inr (Or.inr rfl))

private theorem invariantZ (c : canon.Center) (e : canon.Aut)
    (fixed : canon.centerPerm e c = c) (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt c (canon.ligandPermAt e c i)) =
      graph.atomZ (canon.ligandAtomAt c i) := by
  have action := canon.ligandAtomAt_ligandPermAt (e := e) (c := c) i
  rw [fixed] at action
  rw [action]
  exact MoleculeGraph.Aut.atomZ_eq (m := graph) ⟨e.val, e.property.1⟩ _

private theorem tied0 (i j : Fin 4)
    (h : graph.atomZ (canon.ligandAtomAt center0 i) =
      graph.atomZ (canon.ligandAtomAt center0 j)) :
    i = j ∨ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) := by
  rw [rootSlotZ0 i, rootSlotZ0 j] at h
  fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]

private theorem tied2 (i j : Fin 4)
    (h : graph.atomZ (canon.ligandAtomAt center2 i) =
      graph.atomZ (canon.ligandAtomAt center2 j)) :
    i = j ∨ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) := by
  rw [rootSlotZ2 i, rootSlotZ2 j] at h
  fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]

private theorem tied4 (i j : Fin 4)
    (h : graph.atomZ (canon.ligandAtomAt center4 i) =
      graph.atomZ (canon.ligandAtomAt center4 j)) :
    i = j ∨ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
  rw [rootSlotZ4 i, rootSlotZ4 j] at h
  fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]

private theorem canonicalPairs0 :
    ConstitutionalPairsEnantiomorphic canon calibratedCfg center0 := by
  intro e fixed i j distinct sends
  have hz := invariantZ center0 e fixed i
  have tied := tied0 i j (by simpa [sends] using hz.symm)
  rcases tied with same | pair
  · exact (distinct same).elim
  · rcases pair with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst i; subst j
      exact ⟨by decide, mirrorTransportAt0, notProperAt0⟩
    · subst i; subst j
      exact enantiomorphic_symm canon calibratedCfg center0
        ⟨by decide, mirrorTransportAt0, notProperAt0⟩

private theorem canonicalPairs2 :
    ConstitutionalPairsEnantiomorphic canon calibratedCfg center2 := by
  intro e fixed i j distinct sends
  have hz := invariantZ center2 e fixed i
  have tied := tied2 i j (by simpa [sends] using hz.symm)
  rcases tied with same | pair
  · exact (distinct same).elim
  · rcases pair with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst i; subst j
      exact ⟨by decide, mirrorTransportAt2, notProperAt2⟩
    · subst i; subst j
      exact enantiomorphic_symm canon calibratedCfg center2
        ⟨by decide, mirrorTransportAt2, notProperAt2⟩

private theorem canonicalPairs4 :
    ConstitutionalPairsEnantiomorphic canon calibratedCfg center4 := by
  intro e fixed i j distinct sends
  have hz := invariantZ center4 e fixed i
  have tied := tied4 i j (by simpa [sends] using hz.symm)
  rcases tied with same | pair
  · exact (distinct same).elim
  · rcases pair with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst i; subst j
      exact ⟨by decide, mirrorTransportAt4, notProperAt4⟩
    · subst i; subst j
      exact enantiomorphic_symm canon calibratedCfg center4
        ⟨by decide, mirrorTransportAt4, notProperAt4⟩

private theorem canonicalPairsAt (c : canon.Center) :
    ConstitutionalPairsEnantiomorphic canon calibratedCfg c := by
  have hc : c.1 = 0 ∨ c.1 = 2 ∨ c.1 = 4 := (degree_four_iff c.1).mp c.2
  rcases hc with h0 | h2 | h4
  · have heq : c = center0 := Subtype.ext h0
    subst c
    exact canonicalPairs0
  · have heq : c = center2 := Subtype.ext h2
    subst c
    exact canonicalPairs2
  · have heq : c = center4 := Subtype.ext h4
    subst c
    exact canonicalPairs4

private theorem constitutionalPairs_reindex
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (tau : m.Center → Equiv.Perm (Fin 4))
    (cfg : m.Configuration) (c : m.Center)
    (pairs : ConstitutionalPairsEnantiomorphic m cfg c) :
    ConstitutionalPairsEnantiomorphic (m.reindexFrames tau)
      (m.reindexConfiguration tau cfg) c := by
  intro e fixed i j distinct sends
  let e' : m.Aut := m.autUnreindex tau e
  have fixedR : (m.reindexFrames tau).centerPerm
      (m.autReindex tau e') c = c := by
    simpa [e'] using fixed
  have fixed' : m.centerPerm e' c = c := by
    exact (reindexFrames_centerPerm m tau e' c).symm.trans fixedR
  have sendsR : (m.reindexFrames tau).ligandPermAt
      (m.autReindex tau e') c i = j := by
    simpa [e'] using sends
  have sends' : m.ligandPermAt e' c (tau c i) = tau c j := by
    have h := (reindexFrames_ligandPermAt_apply_iff m tau e' c i j).1 sendsR
    simpa [reindexFrames_centerPerm, fixed'] using h
  have pair := pairs e' fixed' (tau c i) (tau c j)
    (fun h => distinct ((tau c).injective h)) sends'
  exact (enantiomorphic_reindexFrames_iff m tau cfg c i j).2 pair

private theorem constitutionalPairs_congr
    {V : Type*} [Fintype V] [DecidableEq V]
    {m n : MultiCenterMolecule V} (h : m = n) (cfg : m.Configuration)
    (c : m.Center) (pairs : ConstitutionalPairsEnantiomorphic m cfg c) :
    ConstitutionalPairsEnantiomorphic n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) c) := by
  cases h
  exact pairs

/-- At each actual detected center, every root-fixing molecular automorphism that exchanges two
distinct ligand slots exhibits a physical enantiomorphic pair. -/
theorem detectedConstitutionalPairsEnantiomorphic :
    ∀ root : symmetricCertified.detectedMultiCenterMolecule.Center,
      ConstitutionalPairsEnantiomorphic
        symmetricCertified.detectedMultiCenterMolecule detectedCfg root := by
  intro root
  let root' : (canon.reindexFrames fixtureTau).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center fixtureTau_spec.symm) root
  have canonical := canonicalPairsAt root'
  have reindexed := constitutionalPairs_reindex canon fixtureTau calibratedCfg root' canonical
  simpa [detectedCfg] using constitutionalPairs_congr fixtureTau_spec
    (canon.reindexConfiguration fixtureTau calibratedCfg) root' reindexed

end
end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureRootSymmetry

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureRootSymmetry.detectedConstitutionalPairsEnantiomorphic
