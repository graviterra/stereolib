import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation
import TetraStereo.OneCenter.LocalizedRecursiveGlobalPhysicalCovariance
import TetraStereo.OneCenter.LocalizedRecursiveAllOccurrenceCovariance
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie
import TetraStereo.OneCenter.LocalizedRetainedOccurrenceTransport
import TetraStereo.OneCenter.LocalizedRetainedPhysicalConfigurationTransport
import TetraStereo.OneCenter.LocalizedRetainedContextGeneratedDescriptor
import TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Whole detected-center report for the cyclic fixture

This module develops the root-changing covariance needed to move the proved root report to the
other detected roots. The all-occurrence covariance supplies the actual root-cut reader agreement,
so every detected center is shown to occur in the actual report with a lowercase descriptor.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureWholeReport

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.LocalizedRecursiveGlobalPhysicalCovariance
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
open TetraStereo.OneCenter.LocalizedRecursiveAllOccurrenceCovariance
open TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
open TetraStereo.OneCenter
open scoped Classical

def canonicalRotation : canon.Aut := auto04 * auto02

private theorem canonicalRotation_center0 :
    canon.centerPerm canonicalRotation center0 = center2 := by
  rw [show canonicalRotation = auto04 * auto02 by rfl, centerPerm_mul_apply]
  rw [auto02_center0, auto04_center2]

private theorem canonicalRotation_center2 :
    canon.centerPerm canonicalRotation center2 = center4 := by
  rw [show canonicalRotation = auto04 * auto02 by rfl, centerPerm_mul_apply]
  rw [auto02_center2, auto04_center0]

private theorem canonicalRotation_center4 :
    canon.centerPerm canonicalRotation center4 = center0 := by
  rw [show canonicalRotation = auto04 * auto02 by rfl, centerPerm_mul_apply]
  rw [auto02_center4, auto04_center4]

private theorem canonicalRotation_parity0 :
    permHandedness (canon.ligandPermAt canonicalRotation center0) = 1 := by
  rw [show canonicalRotation = auto04 * auto02 by rfl,
    MultiCenterMolecule.ligandPermAt_mul, auto02_center0]
  have h04 : canon.ligandPermAt auto04 center2 = Equiv.swap 0 2 := by
    ext i
    rw [slotMap04at2]
    fin_cases i <;> rfl
  have h02 : canon.ligandPermAt auto02 center0 = Equiv.swap 0 1 := by
    ext i
    rw [slotMap02at0]
    fin_cases i <;> rfl
  rw [h04, h02, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]

private theorem canonicalRotation_parity2 :
    permHandedness (canon.ligandPermAt canonicalRotation center2) = -1 := by
  rw [show canonicalRotation = auto04 * auto02 by rfl,
    MultiCenterMolecule.ligandPermAt_mul, auto02_center2]
  have h04 : canon.ligandPermAt auto04 center0 = Equiv.swap 0 2 * Equiv.swap 0 3 := by
    ext i
    rw [slotMap04at0]
    fin_cases i <;> rfl
  have h02 : canon.ligandPermAt auto02 center2 = Equiv.swap 0 1 := by
    ext i
    rw [slotMap02at2]
    fin_cases i <;> rfl
  rw [h04, h02, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]

private theorem canonicalRotation_parity4 :
    permHandedness (canon.ligandPermAt canonicalRotation center4) = -1 := by
  rw [show canonicalRotation = auto04 * auto02 by rfl,
    MultiCenterMolecule.ligandPermAt_mul, auto02_center4]
  have h04 : canon.ligandPermAt auto04 center4 = Equiv.swap 0 3 * Equiv.swap 0 2 := by
    ext i
    rw [slotMap04at4]
    fin_cases i <;> rfl
  have h02 : canon.ligandPermAt auto02 center4 = Equiv.swap 0 1 := by
    ext i
    rw [slotMap02at4]
    fin_cases i <;> rfl
  rw [h04, h02, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]

/-- The explicit cyclic rotation is proper at every center for the fixture's actual configuration.
This is a global physical sign law, rather than a root-fixing branch symmetry. -/
theorem canonicalRotation_proper_everywhere (center : canon.Center) :
    canon.configurationSign calibratedCfg center *
        permHandedness (canon.ligandPermAt canonicalRotation center) =
      canon.configurationSign calibratedCfg (canon.centerPerm canonicalRotation center) := by
  have hc : center.1 = 0 ∨ center.1 = 2 ∨ center.1 = 4 :=
    (degree_four_iff center.1).mp center.2
  rcases hc with h0 | h2 | h4
  · have heq : center = center0 := Subtype.ext h0
    subst center
    rw [cfgSign0, canonicalRotation_center0, cfgSign2, canonicalRotation_parity0]
    norm_num
  · have heq : center = center2 := Subtype.ext h2
    subst center
    rw [cfgSign2, canonicalRotation_center2, cfgSign4, canonicalRotation_parity2]
    norm_num
  · have heq : center = center4 := Subtype.ext h4
    subst center
    rw [cfgSign4, canonicalRotation_center4, cfgSign0, canonicalRotation_parity4]
    norm_num

noncomputable def reindexedRotation : (canon.reindexFrames fixtureTau).Aut :=
  canon.autReindex fixtureTau canonicalRotation

theorem reindexedRotation_proper_everywhere
    (center : (canon.reindexFrames fixtureTau).Center) :
    (canon.reindexFrames fixtureTau).configurationSign
        (canon.reindexConfiguration fixtureTau calibratedCfg) center *
      permHandedness ((canon.reindexFrames fixtureTau).ligandPermAt reindexedRotation center) =
    (canon.reindexFrames fixtureTau).configurationSign
      (canon.reindexConfiguration fixtureTau calibratedCfg)
      ((canon.reindexFrames fixtureTau).centerPerm reindexedRotation center) := by
  have hcanon : canon.configurationSign calibratedCfg center *
      permHandedness (canon.ligandPermAt canonicalRotation center) =
      (if false = true then -1 else 1) *
        canon.configurationSign calibratedCfg (canon.centerPerm canonicalRotation center) := by
    simpa using canonicalRotation_proper_everywhere center
  simpa [reindexedRotation] using
    (MultiCenterMolecule.branchTransportSign_reindexFrames_iff
      canon fixtureTau calibratedCfg canonicalRotation center false).2 hcanon

private theorem properSign_congr
    {m n : MultiCenterMolecule (Fin 9)} (h : m = n) (cfg : m.Configuration)
    (e : m.Aut) (center : m.Center)
    (law : m.configurationSign cfg center * permHandedness (m.ligandPermAt e center) =
      m.configurationSign cfg (m.centerPerm e center)) :
    n.configurationSign (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) center) *
      permHandedness (n.ligandPermAt
        (Eq.mp (congrArg (fun m : MultiCenterMolecule (Fin 9) => (m.Aut : Type _)) h) e)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) center)) =
    n.configurationSign (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (n.centerPerm
        (Eq.mp (congrArg (fun m : MultiCenterMolecule (Fin 9) => (m.Aut : Type _)) h) e)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) center)) := by
  cases h
  exact law

noncomputable def detectedRotation :
    symmetricCertified.detectedMultiCenterMolecule.Aut :=
  Eq.mp (congrArg (fun m : MultiCenterMolecule (Fin 9) => (m.Aut : Type _)) fixtureTau_spec)
    reindexedRotation

theorem detectedRotation_proper_everywhere
    (center : symmetricCertified.detectedMultiCenterMolecule.Center) :
    symmetricCertified.detectedMultiCenterMolecule.configurationSign detectedCfg center *
      permHandedness (symmetricCertified.detectedMultiCenterMolecule.ligandPermAt
        detectedRotation center) =
    symmetricCertified.detectedMultiCenterMolecule.configurationSign detectedCfg
      (symmetricCertified.detectedMultiCenterMolecule.centerPerm detectedRotation center) := by
  let center' : (canon.reindexFrames fixtureTau).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center fixtureTau_spec.symm) center
  simpa [detectedCfg, detectedRotation] using properSign_congr fixtureTau_spec
    (canon.reindexConfiguration fixtureTau calibratedCfg) reindexedRotation center'
    (reindexedRotation_proper_everywhere center')

noncomputable def rotationGraphAut : symmetricCertified.moleculeGraph.Aut :=
  detectedGraphAut symmetricCertified detectedRotation

private theorem rotationGraphAut_eq_canonical :
    (rotationGraphAut : Equiv.Perm symmetricCertified.Atom) =
      (canonicalRotation : Equiv.Perm (Fin 9)) := by
  change (detectedRotation : Equiv.Perm symmetricCertified.Atom) =
    (canonicalRotation : Equiv.Perm (Fin 9))
  change (reindexedRotation : Equiv.Perm (Fin 9)) =
    (canonicalRotation : Equiv.Perm (Fin 9))
  rfl

private theorem rootTetra_atom_eq_zero : rootTetra.1 = ⟨0, by decide⟩ := by
  apply Fin.ext
  rfl

private theorem certifiedAtomCount :
    symmetricCertified.certified.input.molecule.atomCount = 9 := rfl

private theorem canonicalRotation_apply0 :
    (canonicalRotation : Equiv.Perm (Fin 9)) 0 = 2 := by
  simpa [MultiCenterMolecule.centerPerm, center0, center2] using
    congrArg Subtype.val canonicalRotation_center0

private theorem canonicalRotation_apply2 :
    (canonicalRotation : Equiv.Perm (Fin 9)) 2 = 4 := by
  simpa [MultiCenterMolecule.centerPerm, center2, center4] using
    congrArg Subtype.val canonicalRotation_center2

private theorem fixtureSimpleBonded : symmetricCertified.moleculeGraph.SimpleBonded := by
  change graph.SimpleBonded
  exact simple_bonded

private theorem rotationGraphAut_signLaw :
    ∀ center : symmetricCertified.detectedMultiCenterMolecule.Center,
      symmetricCertified.detectedMultiCenterMolecule.configurationSign detectedCfg center *
        permHandedness (symmetricCertified.detectedMultiCenterMolecule.ligandPermAt
          (symmetricCertified.physicalDetectedAut rotationGraphAut) center) =
        symmetricCertified.detectedMultiCenterMolecule.configurationSign detectedCfg
          (symmetricCertified.detectedMultiCenterMolecule.centerPerm
            (symmetricCertified.physicalDetectedAut rotationGraphAut) center) := by
  intro center
  simpa [rotationGraphAut, physicalDetectedAut_detectedGraphAut] using
    detectedRotation_proper_everywhere center

private theorem transportRootUnit_eq_final
    (center : symmetricCertified.TetrahedralCenter)
    (target : Occurrence fixtureReference)
    (targetUnit : symmetricCertified.molecularFrameUnit target.1 =
      (finalCenterUnit fixtureReference center).1) :
    symmetricCertified.molecularFrameUnit
        (symmetricCertified.transportOccurrence fixtureSimpleBonded rotationGraphAut target).1 =
      (finalCenterUnit fixtureReference
        (symmetricCertified.transportTetrahedralCenter rotationGraphAut center)).1 := by
  rw [symmetricCertified.molecularFrameUnit_transport fixtureSimpleBonded rotationGraphAut target,
    targetUnit]
  rfl

private theorem report_has_lowercase_at_center
    (center : symmetricCertified.TetrahedralCenter)
    (target : Occurrence fixtureReference)
    (targetUnit : symmetricCertified.molecularFrameUnit target.1 =
      (finalCenterUnit fixtureReference center).1)
    {descriptor : LocalizedAuxiliaryLabel}
    (state : referenceState fixtureReference target = some descriptor)
    (lowercase : descriptor.IsLowercase) :
    (center.1.val, some descriptor) ∈ analyze fixtureReference ∧ descriptor.IsLowercase := by
  refine ⟨?_, lowercase⟩
  rw [LocalizedRuleMajorReference.analyze_eq_referenceReport fixtureReference]
  apply List.mem_map.mpr
  refine ⟨center, ?_, ?_⟩
  · exact (fixtureReference.certified.mem_canonicalTetrahedralCenters_iff center).mpr center.2
  · apply Prod.ext
    · rfl
    · have chosenTarget :=
        (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded fixtureReference
          fixtureSimpleBonded (finalCenterUnit fixtureReference center).1 target).2 targetUnit
      have chosenFinal :=
        (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded fixtureReference
          fixtureSimpleBonded (finalCenterUnit fixtureReference center).1
          (symmetricCertified.localizedFinalOccurrenceExecutable
            (carrierFuel fixtureReference) center)).2
          (finalOccurrence_molecularFrameUnit fixtureReference center)
      have targetEq : target =
          symmetricCertified.localizedFinalOccurrenceExecutable
            (carrierFuel fixtureReference) center :=
        Option.some.inj (chosenTarget.symm.trans chosenFinal)
      simpa [targetEq] using state

/-- One lowercase descriptor occurs in the actual report at every detected center. The proof
transports the production root state around the proper cyclic molecular symmetry and then connects
each transported occurrence to the final occurrence selected by `analyze`. -/
theorem every_detected_root_reported_lowercase_shared :
    ∃ descriptor : LocalizedAuxiliaryLabel, descriptor.IsLowercase ∧
      ∀ center : symmetricCertified.TetrahedralCenter,
        (center.1.val, some descriptor) ∈ analyze fixtureReference := by
  obtain ⟨descriptor, rootState, lowercase⟩ := root0_actualState_isLowercase
  refine ⟨descriptor, lowercase, ?_⟩
  intro center
  have root0Report := report_has_lowercase_at_center rootTetra rootTarget
    (finalOccurrence_molecularFrameUnit fixtureReference rootTetra) rootState lowercase
  let e := rotationGraphAut
  let center1 := symmetricCertified.transportTetrahedralCenter e rootTetra
  let target1 := symmetricCertified.transportOccurrence fixtureSimpleBonded e rootTarget
  have target0Unit : symmetricCertified.molecularFrameUnit rootTarget.1 =
      (finalCenterUnit fixtureReference rootTetra).1 :=
    finalOccurrence_molecularFrameUnit fixtureReference rootTetra
  have target1Unit := transportRootUnit_eq_final rootTetra rootTarget target0Unit
  have law1 := referenceState_transport_allOccurrences (input := fixtureReference)
    fixtureSimpleBonded detectedCfg detectedCoordinates_at e false
    (by simpa [physicalMirrorFactor] using rotationGraphAut_signLaw) rootTarget
  have state1 : referenceState fixtureReference target1 = some descriptor := by
    simpa [Law, target1, e, rootState, retainedPhysicalLetter] using law1
  have report1 := report_has_lowercase_at_center center1 target1 target1Unit state1 lowercase
  let center2 := symmetricCertified.transportTetrahedralCenter e center1
  let target2 := symmetricCertified.transportOccurrence fixtureSimpleBonded e target1
  have target2Unit := transportRootUnit_eq_final center1 target1 target1Unit
  have law2 := referenceState_transport_allOccurrences (input := fixtureReference)
    fixtureSimpleBonded detectedCfg detectedCoordinates_at e false
    (by simpa [physicalMirrorFactor] using rotationGraphAut_signLaw) target1
  have state2 : referenceState fixtureReference target2 = some descriptor := by
    simpa [Law, target2, e, state1, retainedPhysicalLetter] using law2
  have report2 := report_has_lowercase_at_center center2 target2 target2Unit state2 lowercase
  have atom1 : center1.1 = ⟨2, by decide⟩ := by
    apply Fin.ext
    change ((rotationGraphAut : Equiv.Perm symmetricCertified.Atom) rootTetra.1).val = 2
    rw [rotationGraphAut_eq_canonical]
    rw [rootTetra_atom_eq_zero]
    change ((canonicalRotation : Equiv.Perm (Fin 9)) 0).val = 2
    exact congrArg Fin.val canonicalRotation_apply0
  have atom2 : center2.1 = ⟨4, by decide⟩ := by
    apply Fin.ext
    change ((rotationGraphAut : Equiv.Perm symmetricCertified.Atom)
      ((rotationGraphAut : Equiv.Perm symmetricCertified.Atom) rootTetra.1)).val = 4
    rw [rotationGraphAut_eq_canonical]
    rw [rootTetra_atom_eq_zero]
    change ((canonicalRotation : Equiv.Perm (Fin 9))
      ((canonicalRotation : Equiv.Perm (Fin 9)) 0)).val = 4
    rw [canonicalRotation_apply0]
    exact congrArg Fin.val canonicalRotation_apply2
  have inventory : center = rootTetra ∨ center = center1 ∨ center = center2 := by
    have atomCases : center.1.val = 0 ∨ center.1.val = 2 ∨ center.1.val = 4 := by
      let idx : Fin 9 := ⟨center.1.val, by
        have hbound := center.1.isLt
        exact Nat.lt_of_lt_of_eq hbound certifiedAtomCount⟩
      have idxEq : idx = center.1 := by
        change idx = center.1
        apply Fin.ext
        rfl
      have member : idx ∈ graph.tetrahedralCenterSet := by
        change idx ∈ symmetricCertified.tetrahedralCenterSet
        rw [idxEq]
        exact center.2
      have cases := (degree_four_iff idx).mp member
      rcases cases with h0 | h2 | h4
      · exact Or.inl (congrArg Fin.val (by simpa [idx] using h0))
      · exact Or.inr (Or.inl (congrArg Fin.val (by simpa [idx] using h2)))
      · exact Or.inr (Or.inr (congrArg Fin.val (by simpa [idx] using h4)))
    rcases atomCases with h0 | h2 | h4
    · left
      apply Subtype.ext
      apply Fin.ext
      simpa [rootTetra_atom_eq_zero] using h0
    · right
      left
      apply Subtype.ext
      apply Fin.ext
      have hval : center1.1.val = 2 := congrArg Fin.val atom1
      omega
    · right
      right
      apply Subtype.ext
      apply Fin.ext
      have hval : center2.1.val = 4 := congrArg Fin.val atom2
      omega
  rcases inventory with h0 | h1 | h2
  · subst center
    exact root0Report.1
  · subst center
    exact report1.1
  · subst center
    exact report2.1

/-- At each detected center, the actual report contains a lowercase descriptor. The shared-witness
theorem above shows that the same descriptor works for all centers. -/
theorem every_detected_root_reported_lowercase :
    ∀ center : symmetricCertified.TetrahedralCenter,
      ∃ descriptor : LocalizedAuxiliaryLabel,
        (center.1.val, some descriptor) ∈ analyze fixtureReference ∧ descriptor.IsLowercase := by
  obtain ⟨descriptor, lowercase, allCenters⟩ :=
    every_detected_root_reported_lowercase_shared
  intro center
  exact ⟨descriptor, allCenters center, lowercase⟩

end
end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureWholeReport

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureWholeReport.canonicalRotation_proper_everywhere
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureWholeReport.detectedRotation_proper_everywhere
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureWholeReport.every_detected_root_reported_lowercase_shared
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureWholeReport.every_detected_root_reported_lowercase
