import TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# End-to-end uncapped recursive assignment on the dependent-center cage family

The actual uncapped evaluator generates the same far facts, near facts, root snapshot and
mirror-derived final descriptor as the accepted constructor. No temporary labels, reference
choices, schedule, ranking success or desired output are hypotheses. Geometry is arbitrary
within the explicit nondegenerate 15-atom family.

This establishes the cyclic dependent-center family endpoint for the new instance. It is not
general chemical completeness, nor a theorem about every center's report.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedCageCorrectness

open LocalizedMarkedOperationEvaluator LocalizedMarkedOperationSimulation
open LocalizedMarkedUncappedCageFarSimulation LocalizedMarkedUncappedCageNearSimulation
open LocalizedHiddenParityMarkedProbe LocalizedHiddenParityPromotedReadback
open LocalizedHiddenParityPromotedReflection LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedGenericMarkedRecalculationCage (geomOf geomOf_mirror gFrame_eq)
open LocalizedGenericMarkedRecalculation (frameAtoms? eligibleOf flatMap_congr_mem)

theorem root_tiedChildren_eq :
    tiedChildren cageRaw uncapped [] root0 =
      LocalizedGenericMarkedRecalculation.tiedChildren cageRaw 16 [] root0 := by
  unfold tiedChildren LocalizedGenericMarkedRecalculation.tiedChildren
  change (match frameAtoms? cageRaw root0,
    LocalizedMarkedUncappedOperations.ordinary? cageRaw [] root0 with
    | some atoms, some (sorted, adjacent) =>
        (cageRaw.canonicalChildren root0).filter
          (fun (child : RawMolecule.CanonicalBranchNode) =>
            (eligibleOf atoms sorted adjacent).contains child.atom)
    | _, _ => []) = _
  rw [LocalizedMarkedUncappedCageAgreement.ordinary_root]
  rfl

theorem root_under_eq (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) (mark : Nat) (hm : mark = 3 ∨ mark = 9) :
    underWith cageRaw uncapped (geomOf P len) [] root0 (facts cageRaw uncapped 15) mark =
      LocalizedGenericMarkedRecalculation.underWith cageRaw 16 (geomOf P len) [] root0
        (LocalizedGenericMarkedRecalculation.facts cageRaw 16 15) mark := by
  unfold underWith LocalizedGenericMarkedRecalculation.underWith
  rw [root_tiedChildren_eq]
  apply flatMap_congr_mem
  intro child member
  rw [LocalizedGenericMarkedRecalculationCage.tiedChildren_root] at member
  have cases : child = nearA ∨ child = nearB := by simpa using member
  rcases cases with rfl | rfl
  · exact nearA_facts_eq P len nondeg 12 mark hm
  · exact nearB_facts_eq P len nondeg 12 mark hm

theorem root_raw_eq (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) :
    rawWith? cageRaw uncapped (geomOf P len) [] none root0 (facts cageRaw uncapped 15) =
      LocalizedGenericMarkedRecalculation.rawWith? cageRaw 16 (geomOf P len) [] none root0
        (LocalizedGenericMarkedRecalculation.facts cageRaw 16 15) := by
  unfold rawWith? LocalizedGenericMarkedRecalculation.rawWith?
  apply rawStep_eq_of_selected cageRaw uncapped bounded (geomOf P len) [] none root0 _ _
    [1, 2, 3, 9] [1, 2, 3, 0] [some .gt, some .eq, some .gt]
    (by simpa only [gFrame_eq] using root0_frameAtoms)
    (LocalizedMarkedUncappedCageAgreement.ordinary_root.trans
      LocalizedGenericMarkedRecalculationCage.root_ordinary)
    LocalizedGenericMarkedRecalculationCage.root_ordinary
  intro mark chosen
  have member : mark = 3 ∨ mark = 9 := by
    simpa [eligibleOf, LocalizedGenericMarkedRecalculation.atomsAt,
      LocalizedGenericMarkedRecalculation.tiedPositions] using chosen
  rw [root_under_eq P len nondeg mark member,
    LocalizedGenericMarkedRecalculationCage.underRoot P len nondeg mark member,
    LocalizedGenericMarkedRecalculationCage.appendRoot P len]
  simp only [Option.bind_some]
  exact marked_eq_bounded P len _ root0 mark
    (LocalizedMarkedUncappedCageAgreement.root_ranked mark member _ _ false)

/-- Complete root descriptor equality, after generating and reflecting both recursive states. -/
theorem assignCenter_eq_original (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) :
    LocalizedMarkedUncappedEvaluator.assignCenter? cageRaw (geomOf P len) 0 =
      LocalizedGenericMarkedRecalculation.assignCenter? cageRaw 16 (geomOf P len) 0 := by
  change descriptor? cageRaw uncapped 15 (geomOf P len) [] none root0 =
    LocalizedGenericMarkedRecalculation.descriptor? cageRaw 16 15 (geomOf P len) [] none root0
  unfold descriptor? descriptorWith? LocalizedGenericMarkedRecalculation.descriptor?
    LocalizedGenericMarkedRecalculation.descriptorWith?
  rw [root_raw_eq P len nondeg, geomOf_mirror,
    root_raw_eq _ _ (nondegenerate_mirror P len nondeg)]

/-- The actual uncapped constructor assigns the root exactly when the independent physical
branches are pairwise properly distinguishable, throughout the nondegenerate cage family. -/
theorem assignCenter_isSome_iff_pairwise (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) :
    (LocalizedMarkedUncappedEvaluator.assignCenter? cageRaw (geomOf P len) 0).isSome = true ↔
      MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
        (rootWith P len) := by
  rw [assignCenter_eq_original P len nondeg]
  exact LocalizedGenericMarkedRecalculationCage.assignCenter_isSome_iff_pairwise P len nondeg

end TetraStereo.OneCenter.LocalizedMarkedUncappedCageCorrectness

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageCorrectness.root_under_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageCorrectness.root_raw_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageCorrectness.assignCenter_eq_original
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageCorrectness.assignCenter_isSome_iff_pairwise
