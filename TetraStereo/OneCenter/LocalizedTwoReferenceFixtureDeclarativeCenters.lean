import TetraStereo.OneCenter.DeclarativeCIPFinalTetrahedralAssignment
import TetraStereo.OneCenter.DeclarativeCIPMultiReferenceFirstSphere
import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.OneCenter.LocalizedActualOrderedRootEightRuleConnection
import TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Independent declarative assignments at the eight non-root fixture centers

Each non-root center has four distinct ligand atomic numbers.  The generic first-sphere bridge
therefore supplies its unique ranking, and the accepted canonical coordinates supply its
geometric R/S letter.  Every pair is decided before Rule 5, so the independent final count is
zero.  Expansion existence is obtained from an arbitrary-reader original-root arm; no whole
33-atom carrier state is evaluated here.
-/

namespace TetraStereo.OneCenter
namespace LocalizedTwoReferenceFixtureDeclarativeCenters

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixturePhysicalInstance
open FixtureInventory
open FixtureCalibration

noncomputable section
open scoped Classical

abbrev fixtureProblem :=
  DeclarativeCIP.multiReferenceProblem input.certified.moleculeGraph
    input.certified.localizedDetectedFrame input.certified.geometricOrientation

abbrev fixtureMap := actualReferenceDescriptorMap input

/-- The canonical permutation for ascending-index atomic numbers `[7, 1, 9, 6]`: the
descending-Z ligand order is `[2, 0, 3, 1]`. -/
def rankingA : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

/-- The canonical permutation for ascending-index atomic numbers `[6, 1, 17, 35]`: the
descending-Z ligand order is `[3, 2, 0, 1]`. -/
def rankingB : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private theorem zA_injective : Function.Injective zA := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [zA]

private theorem zB_injective : Function.Injective zB := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [zB]

private theorem rankingA_descending : ∀ i j, i < j → zA (rankingA j) < zA (rankingA i) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [rankingA, zA]

private theorem rankingB_descending : ∀ i j, i < j → zB (rankingB j) < zB (rankingB i) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [rankingB, zB]

/-- One arbitrary-reader original-root arm supplies a faithful expansion at every ligand of a
detected top unit. -/
theorem originalRootExpansion_exists (center : input.certified.TetrahedralCenter) (i : Fin 4) :
    ∃ graph, fixtureProblem.admissibleExpansion (input.certified.topUnit center) i graph := by
  let arm := Classical.choice (input.certified.exists_originalRootArm center i .rule4a
    (fun _ => none))
  refine ⟨(LocalizedCumulativeDecoratedTree.toOfficialSourceTree arm.tree).toDeclarativeDigraph,
    ?_⟩
  change RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph center.1
    (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center) i)
    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree arm.tree).toDeclarativeDigraph
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact arm.faithful

/-- The direct declarative result expected at a non-root center: its geometric descriptor is
unique, its Rule-5 tie count is zero, and the final assignment is uniquely chiral. -/
def CenterAssignment (unit : DetectedOccurrence input.certified.moleculeGraph) (rs : RS) : Prop :=
  fixtureProblem.DescriptorJudgment fixtureMap unit (rsDescriptor rs) ∧
    (∀ descriptor, fixtureProblem.DescriptorJudgment fixtureMap unit descriptor →
      descriptor = rsDescriptor rs) ∧
    finalRule5PairCount fixtureProblem fixtureMap unit = 0 ∧
    FinalTetrahedralAssignment fixtureProblem fixtureMap unit (.chiral rs) ∧
    ∃! label, FinalTetrahedralAssignment fixtureProblem fixtureMap unit label

/-- Generic declarative center theorem.  A strict atomic-number order gives a complete unique
ranking in the independent multireference problem; the observed canonical points determine its
descriptor.  Distinct atomic numbers also rule out every pre-Rule-5 tie. -/
theorem actualTopUnit_assignment_of_canonicalData
    (center : input.certified.TetrahedralCenter)
    (z : Fin 4 → ℕ) (points : Fin 4 → CartesianPoint3)
    (observed : ∀ i, input.certified.spatialPointAt?
      (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center) i) =
        some (points i))
    (zReadback : ∀ i, input.certified.moleculeGraph.atomZ
      (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center) i) = z i)
    (zInjective : Function.Injective z)
    (ranking : Equiv.Perm (Fin 4))
    (descending : ∀ i j, i < j → z (ranking j) < z (ranking i))
    (rs : RS)
    (geometry : RationalTetrahedralDescriptor
      ((List.finRange 4).map fun k => points (ranking k)) rs) :
    CenterAssignment (input.certified.topUnit center) rs := by
  let problem := fixtureProblem
  have expansions : ∀ i, ∃ graph, problem.admissibleExpansion
      (input.certified.topUnit center) i graph :=
    fun i => originalRootExpansion_exists center i
  have higher_iff (i j : Fin 4)
      (hne : input.certified.moleculeGraph.atomZ
        (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center) i) ≠
        input.certified.moleculeGraph.atomZ
          (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center) j)) :
      problem.Higher fixtureMap (input.certified.topUnit center) i j ↔
        input.certified.moleculeGraph.atomZ
          (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center) j) <
        input.certified.moleculeGraph.atomZ
          (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center) i) := by
    exact multiReferenceHigher_iff_atomicNumber_gt_of_ne input.certified.moleculeGraph
      input.certified.localizedDetectedFrame input.certified.geometricOrientation fixtureMap
      (input.certified.topUnit center) i j (expansions i) (expansions j) hne
  have ranks : problem.Ranks fixtureMap (input.certified.topUnit center) ranking := by
    intro i j hij
    have hneqZ : input.certified.moleculeGraph.atomZ
        (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center)
          (ranking i)) ≠
      input.certified.moleculeGraph.atomZ
        (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center)
          (ranking j)) := by
      intro heq
      apply (ne_of_lt hij)
      apply ranking.injective
      apply zInjective
      rw [← zReadback (ranking i), ← zReadback (ranking j)]
      exact heq
    exact (higher_iff (ranking i) (ranking j) hneqZ).2 (by
      rw [zReadback (ranking j), zReadback (ranking i)]
      exact descending i j hij)
  have orientation : input.certified.geometricOrientation
      (input.certified.topUnit center) ranking (rsDescriptor rs) := by
    exact ⟨points, rs, observed, geometry, rfl⟩
  have judgment : problem.DescriptorJudgment fixtureMap
      (input.certified.topUnit center) (rsDescriptor rs) :=
    ⟨ranking, ranks, orientation⟩
  have noEarlierTie : ∀ i j : Fin 4, i ≠ j →
      ¬ problem.EarlierRulesTie fixtureMap .rule5EnantiomorphicDescriptor
        (input.certified.topUnit center) i j := by
    intro i j hij
    apply multiReferenceEarlierRulesTie5_false_of_atomicNumber_ne
      input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation fixtureMap (input.certified.topUnit center) i j
      (expansions i) (expansions j)
    intro heq
    apply hij
    apply zInjective
    rw [← zReadback i, ← zReadback j]
    exact heq
  have countZero : finalRule5PairCount problem fixtureMap
      (input.certified.topUnit center) = 0 :=
    finalRule5PairCount_eq_zero_of_noEarlierTie problem fixtureMap
      (input.certified.topUnit center) noEarlierTie
  have uniqueDescriptor : ∀ descriptor,
      problem.DescriptorJudgment fixtureMap (input.certified.topUnit center) descriptor →
        descriptor = rsDescriptor rs := by
    intro descriptor hdescriptor
    obtain ⟨otherRanking, otherRanks, otherOrientation⟩ := hdescriptor
    have compositionStrict : ∀ a b, a < b →
        otherRanking.symm (ranking a) < otherRanking.symm (ranking b) := by
      intro a b hab
      have distinctPositions : otherRanking.symm (ranking a) ≠
          otherRanking.symm (ranking b) := by
        intro heq
        have hmap : ranking a = ranking b := by
          have := congrArg otherRanking heq
          simpa using this
        exact (ne_of_lt hab) (ranking.injective hmap)
      by_contra hnot
      have reverse : otherRanking.symm (ranking b) < otherRanking.symm (ranking a) :=
        lt_of_le_of_ne (not_lt.1 hnot) (Ne.symm distinctPositions)
      have reverseHigher := otherRanks _ _ reverse
      have distinctZ : input.certified.moleculeGraph.atomZ
            (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center)
              (otherRanking (otherRanking.symm (ranking b)))) ≠
          input.certified.moleculeGraph.atomZ
            (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center)
              (otherRanking (otherRanking.symm (ranking a)))) := by
        intro hEq
        apply distinctPositions
        have hAtomEq : input.certified.moleculeGraph.atomZ
            (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center)
              (ranking b)) =
            input.certified.moleculeGraph.atomZ
              (input.certified.localizedDetectedFrame.ligand (input.certified.topUnit center)
                (ranking a)) := by
          simpa only [Equiv.apply_symm_apply] using hEq
        have hZEQ : z (ranking b) = z (ranking a) := by
          rw [← zReadback (ranking b), ← zReadback (ranking a)]
          exact hAtomEq
        have hRank : ranking b = ranking a := zInjective hZEQ
        have hidx := congrArg otherRanking.symm hRank
        exact hidx.symm
      have reverseByZ := (higher_iff _ _ distinctZ).1 reverseHigher
      have contrad : z (ranking a) < z (ranking b) := by
        rw [← zReadback (ranking a), ← zReadback (ranking b)]
        simpa using reverseByZ
      exact (Nat.lt_asymm (descending a b hab) contrad).elim
    have rankingEq : otherRanking = ranking := by
      apply Equiv.ext
      intro a
      have identity := TetraStereo.OneCenter.strictMono_fin4_eq
        (fun k => otherRanking.symm (ranking k)) compositionStrict a
      have mapped := congrArg otherRanking identity
      simpa using mapped.symm
    subst otherRanking
    exact input.certified.geometricOrientation_functional otherOrientation orientation
  have chiralAssignment : FinalTetrahedralAssignment problem fixtureMap
      (input.certified.topUnit center) (.chiral rs) :=
    finalTetrahedralAssignment_chiral_of_count_zero problem fixtureMap
      (input.certified.topUnit center) rs judgment countZero
  have uniqueAssignment := finalTetrahedralAssignment_existsUnique problem fixtureMap
    (input.certified.topUnit center) rs judgment uniqueDescriptor
  exact ⟨judgment, uniqueDescriptor, countZero, chiralAssignment, uniqueAssignment⟩

private theorem points4 : ∀ i, input.certified.spatialPointAt?
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center4) i) =
      some (FixtureCalibration.canonicalPoint4 i) := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact FixtureCalibration.canonicalObserved4 i

private theorem points7 : ∀ i, input.certified.spatialPointAt?
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center7) i) =
      some (FixtureCalibration.canonicalPoint7 i) := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact FixtureCalibration.canonicalObserved7 i

private theorem points11 : ∀ i, input.certified.spatialPointAt?
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center11) i) =
      some (FixtureCalibration.canonicalPoint11 i) := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact FixtureCalibration.canonicalObserved11 i

private theorem points14 : ∀ i, input.certified.spatialPointAt?
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center14) i) =
      some (FixtureCalibration.canonicalPoint14 i) := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact FixtureCalibration.canonicalObserved14 i

private theorem points19 : ∀ i, input.certified.spatialPointAt?
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center19) i) =
      some (FixtureCalibration.canonicalPoint19 i) := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact FixtureCalibration.canonicalObserved19 i

private theorem points22 : ∀ i, input.certified.spatialPointAt?
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center22) i) =
      some (FixtureCalibration.canonicalPoint22 i) := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact FixtureCalibration.canonicalObserved22 i

private theorem points26 : ∀ i, input.certified.spatialPointAt?
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center26) i) =
      some (FixtureCalibration.canonicalPoint26 i) := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact FixtureCalibration.canonicalObserved26 i

private theorem points29 : ∀ i, input.certified.spatialPointAt?
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center29) i) =
      some (FixtureCalibration.canonicalPoint29 i) := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact FixtureCalibration.canonicalObserved29 i

private theorem zReadback4 : ∀ i, input.certified.moleculeGraph.atomZ
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center4) i) = zA i := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact atomZ4 i

private theorem zReadback7 : ∀ i, input.certified.moleculeGraph.atomZ
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center7) i) = zB i := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact atomZ7 i

private theorem zReadback11 : ∀ i, input.certified.moleculeGraph.atomZ
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center11) i) = zA i := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact atomZ11 i

private theorem zReadback14 : ∀ i, input.certified.moleculeGraph.atomZ
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center14) i) = zB i := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact atomZ14 i

private theorem zReadback19 : ∀ i, input.certified.moleculeGraph.atomZ
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center19) i) = zA i := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact atomZ19 i

private theorem zReadback22 : ∀ i, input.certified.moleculeGraph.atomZ
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center22) i) = zB i := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact atomZ22 i

private theorem zReadback26 : ∀ i, input.certified.moleculeGraph.atomZ
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center26) i) = zA i := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact atomZ26 i

private theorem zReadback29 : ∀ i, input.certified.moleculeGraph.atomZ
    (input.certified.localizedDetectedFrame.ligand
      (input.certified.topUnit FixtureInventory.center29) i) = zB i := by
  intro i
  rw [CertifiedLocalizedCIPInput.localizedDetectedFrame_ligand_topUnit]
  exact atomZ29 i

private theorem geometryA4 : RationalTetrahedralDescriptor
    ((List.finRange 4).map fun k => FixtureCalibration.canonicalPoint4 (rankingA k)) RS.R := by
  simpa [rankingA] using LocalizedTwoReferenceFixturePhysicalInstance.geometry4

private theorem geometryA11 : RationalTetrahedralDescriptor
    ((List.finRange 4).map fun k => FixtureCalibration.canonicalPoint11 (rankingA k)) RS.S := by
  simpa [rankingA] using LocalizedTwoReferenceFixturePhysicalInstance.geometry11

private theorem geometryA19 : RationalTetrahedralDescriptor
    ((List.finRange 4).map fun k => FixtureCalibration.canonicalPoint19 (rankingA k)) RS.S := by
  simpa [rankingA] using LocalizedTwoReferenceFixturePhysicalInstance.geometry19

private theorem geometryA26 : RationalTetrahedralDescriptor
    ((List.finRange 4).map fun k => FixtureCalibration.canonicalPoint26 (rankingA k)) RS.R := by
  simpa [rankingA] using LocalizedTwoReferenceFixturePhysicalInstance.geometry26

private theorem geometryB7 : RationalTetrahedralDescriptor
    ((List.finRange 4).map fun k => FixtureCalibration.canonicalPoint7 (rankingB k)) RS.R := by
  simpa [rankingB] using LocalizedTwoReferenceFixturePhysicalInstance.geometry7

private theorem geometryB14 : RationalTetrahedralDescriptor
    ((List.finRange 4).map fun k => FixtureCalibration.canonicalPoint14 (rankingB k)) RS.R := by
  simpa [rankingB] using LocalizedTwoReferenceFixturePhysicalInstance.geometry14

private theorem geometryB22 : RationalTetrahedralDescriptor
    ((List.finRange 4).map fun k => FixtureCalibration.canonicalPoint22 (rankingB k)) RS.S := by
  simpa [rankingB] using LocalizedTwoReferenceFixturePhysicalInstance.geometry22

private theorem geometryB29 : RationalTetrahedralDescriptor
    ((List.finRange 4).map fun k => FixtureCalibration.canonicalPoint29 (rankingB k)) RS.S := by
  simpa [rankingB] using LocalizedTwoReferenceFixturePhysicalInstance.geometry29

theorem center4_judgment : CenterAssignment
    (input.certified.topUnit FixtureInventory.center4) RS.R :=
  actualTopUnit_assignment_of_canonicalData FixtureInventory.center4 zA
    FixtureCalibration.canonicalPoint4 points4 zReadback4 zA_injective rankingA
    rankingA_descending RS.R geometryA4

theorem center7_judgment : CenterAssignment
    (input.certified.topUnit FixtureInventory.center7) RS.R :=
  actualTopUnit_assignment_of_canonicalData FixtureInventory.center7 zB
    FixtureCalibration.canonicalPoint7 points7 zReadback7 zB_injective rankingB
    rankingB_descending RS.R geometryB7

theorem center11_judgment : CenterAssignment
    (input.certified.topUnit FixtureInventory.center11) RS.S :=
  actualTopUnit_assignment_of_canonicalData FixtureInventory.center11 zA
    FixtureCalibration.canonicalPoint11 points11 zReadback11 zA_injective rankingA
    rankingA_descending RS.S geometryA11

theorem center14_judgment : CenterAssignment
    (input.certified.topUnit FixtureInventory.center14) RS.R :=
  actualTopUnit_assignment_of_canonicalData FixtureInventory.center14 zB
    FixtureCalibration.canonicalPoint14 points14 zReadback14 zB_injective rankingB
    rankingB_descending RS.R geometryB14

theorem center19_judgment : CenterAssignment
    (input.certified.topUnit FixtureInventory.center19) RS.S :=
  actualTopUnit_assignment_of_canonicalData FixtureInventory.center19 zA
    FixtureCalibration.canonicalPoint19 points19 zReadback19 zA_injective rankingA
    rankingA_descending RS.S geometryA19

theorem center22_judgment : CenterAssignment
    (input.certified.topUnit FixtureInventory.center22) RS.S :=
  actualTopUnit_assignment_of_canonicalData FixtureInventory.center22 zB
    FixtureCalibration.canonicalPoint22 points22 zReadback22 zB_injective rankingB
    rankingB_descending RS.S geometryB22

theorem center26_judgment : CenterAssignment
    (input.certified.topUnit FixtureInventory.center26) RS.R :=
  actualTopUnit_assignment_of_canonicalData FixtureInventory.center26 zA
    FixtureCalibration.canonicalPoint26 points26 zReadback26 zA_injective rankingA
    rankingA_descending RS.R geometryA26

theorem center29_judgment : CenterAssignment
    (input.certified.topUnit FixtureInventory.center29) RS.S :=
  actualTopUnit_assignment_of_canonicalData FixtureInventory.center29 zB
    FixtureCalibration.canonicalPoint29 points29 zReadback29 zB_injective rankingB
    rankingB_descending RS.S geometryB29

end

end LocalizedTwoReferenceFixtureDeclarativeCenters
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.originalRootExpansion_exists
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.actualTopUnit_assignment_of_canonicalData
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.center4_judgment
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.center7_judgment
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.center11_judgment
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.center14_judgment
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.center19_judgment
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.center22_judgment
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.center26_judgment
assert_kernel_only
  TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters.center29_judgment
