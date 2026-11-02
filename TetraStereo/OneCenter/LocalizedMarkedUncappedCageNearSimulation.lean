import TetraStereo.OneCenter.LocalizedMarkedUncappedCageFarSimulation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Uncapped recursion generates the near cage snapshots

The equality propagates from actual far occurrence results through their oxygen parents and
the selected subtree concatenation. The near descriptors, including mirror-derived case,
then agree without a supplied-label or computed-state-correspondence premise.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation

open LocalizedMarkedOperationEvaluator LocalizedMarkedOperationSimulation
open LocalizedMarkedUncappedCageFarSimulation
open LocalizedHiddenParityMarkedProbe LocalizedHiddenParityPromotedReadback
open LocalizedHiddenParityPromotedReflection LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedGenericMarkedRecalculationCage
  (geomOf geomOf_mirror gFrame_eq farA_leafy farB_leafy oxA oxB
    oxA_noFrame oxB_noFrame children_oxA children_oxB children_nearA children_nearB)
open LocalizedGenericMarkedRecalculation (frameAtoms? eligibleOf flatMap_congr_mem)

theorem farA_facts_eq (P : List CartesianPoint3) (len : P.length = 15) (depth o r : Nat)
    (ho : o ∈ [5, 6, 7]) (hr : r ∈ [3, 9, 5, 6, 7]) :
    facts cageRaw uncapped (depth + 1) (geomOf P len) [] (some r) (farA o) =
      LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 1) (geomOf P len)
        [] (some r) (farA o) := by
  rw [facts_succ, farA_descriptor_eq P len depth o r ho hr,
    LocalizedGenericMarkedRecalculationCage.facts_farA o ho,
    flatMap_facts_eq_nil cageRaw uncapped depth (geomOf P len) [] (some r) _ (farA_leafy o ho)]
  simp

theorem oxA_facts_eq (P : List CartesianPoint3) (len : P.length = 15) (depth o r : Nat)
    (ho : o ∈ [5, 6, 7]) (hr : r ∈ [3, 9, 5, 6, 7]) :
    facts cageRaw uncapped (depth + 2) (geomOf P len) [] (some r) (oxA o) =
      LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2) (geomOf P len)
        [] (some r) (oxA o) := by
  rw [facts_succ_noFrame cageRaw uncapped (depth + 1) (geomOf P len) [] (some r) _
    (oxA_noFrame o ho), children_oxA o ho,
    LocalizedGenericMarkedRecalculationCage.facts_oxA o ho]
  simpa using farA_facts_eq P len depth o r ho hr

theorem nearA_tiedChildren_eq :
    tiedChildren cageRaw uncapped [] nearA =
      LocalizedGenericMarkedRecalculation.tiedChildren cageRaw 16 [] nearA := by
  unfold tiedChildren LocalizedGenericMarkedRecalculation.tiedChildren
  change (match frameAtoms? cageRaw nearA,
    LocalizedMarkedUncappedOperations.ordinary? cageRaw [] nearA with
    | some atoms, some (sorted, adjacent) =>
        (cageRaw.canonicalChildren nearA).filter
          (fun (child : RawMolecule.CanonicalBranchNode) =>
            (eligibleOf atoms sorted adjacent).contains child.atom)
    | _, _ => []) = _
  rw [LocalizedMarkedUncappedCageAgreement.ordinary_near.1]
  rfl

theorem nearA_under_eq (P : List CartesianPoint3) (len : P.length = 15)
    (depth mark : Nat) (member : mark ∈ [5, 6, 7]) :
    underWith cageRaw uncapped (geomOf P len) [] nearA (facts cageRaw uncapped (depth + 2)) mark =
      LocalizedGenericMarkedRecalculation.underWith cageRaw 16 (geomOf P len) [] nearA
        (LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2)) mark := by
  unfold underWith LocalizedGenericMarkedRecalculation.underWith
  rw [nearA_tiedChildren_eq]
  apply flatMap_congr_mem
  intro child present
  rw [LocalizedGenericMarkedRecalculationCage.tiedChildren_nearA] at present
  have cases : child = oxA 5 ∨ child = oxA 6 ∨ child = oxA 7 := by simpa using present
  have scope : mark ∈ [3, 9, 5, 6, 7] := by simp at member ⊢; omega
  rcases cases with rfl | rfl | rfl <;> exact oxA_facts_eq P len depth _ mark (by decide) scope

theorem nearA_raw_eq (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) (depth r : Nat) (hr : r = 3 ∨ r = 9) :
    rawWith? cageRaw uncapped (geomOf P len) [] (some r) nearA
        (facts cageRaw uncapped (depth + 2)) =
      LocalizedGenericMarkedRecalculation.rawWith? cageRaw 16 (geomOf P len) [] (some r) nearA
        (LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2)) := by
  unfold rawWith? LocalizedGenericMarkedRecalculation.rawWith?
  apply rawStep_eq_of_selected cageRaw uncapped bounded (geomOf P len) [] (some r) nearA _ _
    [0, 5, 6, 7] [1, 2, 3, 0] [some .eq, some .eq, some .gt]
    (by simpa only [gFrame_eq] using nearA_frameAtoms)
    (LocalizedMarkedUncappedCageAgreement.ordinary_near.1.trans
      LocalizedGenericMarkedRecalculationCage.nearA_ordinary)
    LocalizedGenericMarkedRecalculationCage.nearA_ordinary
  intro mark chosen
  have member : mark ∈ [5, 6, 7] := by
    simp [eligibleOf, LocalizedGenericMarkedRecalculation.atomsAt,
      LocalizedGenericMarkedRecalculation.tiedPositions] at chosen ⊢
    rcases hr with rfl | rfl <;> omega
  rw [nearA_under_eq P len depth mark member,
    LocalizedGenericMarkedRecalculationCage.underNearA P len nondeg depth mark member,
    LocalizedGenericMarkedRecalculationCage.appendStateA P len mark member]
  simp only [Option.bind_some]
  exact (LocalizedMarkedUncappedCagePhysicalReadback.nearA_readback P len mark member true).trans
    (LocalizedGenericMarkedRecalculationCage.markedReadback_eq P len _ nearA mark).symm

theorem nearA_descriptor_eq (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) (depth r : Nat) (hr : r = 3 ∨ r = 9) :
    descriptor? cageRaw uncapped (depth + 2) (geomOf P len) [] (some r) nearA =
      LocalizedGenericMarkedRecalculation.descriptor? cageRaw 16 (depth + 2) (geomOf P len)
        [] (some r) nearA := by
  unfold descriptor? descriptorWith? LocalizedGenericMarkedRecalculation.descriptor?
    LocalizedGenericMarkedRecalculation.descriptorWith?
  rw [nearA_raw_eq P len nondeg depth r hr, geomOf_mirror,
    nearA_raw_eq _ _ (nondegenerate_mirror P len nondeg) depth r hr]

theorem nearA_facts_eq (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) (depth r : Nat) (hr : r = 3 ∨ r = 9) :
    facts cageRaw uncapped (depth + 3) (geomOf P len) [] (some r) nearA =
      LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 3) (geomOf P len)
        [] (some r) nearA := by
  rw [facts_succ, LocalizedGenericMarkedRecalculation.facts_succ,
    nearA_descriptor_eq P len nondeg depth r hr]
  congr 1
  apply flatMap_congr_mem
  intro child present
  rw [children_nearA] at present
  have cases : child = oxA 5 ∨ child = oxA 6 ∨ child = oxA 7 := by simpa using present
  have scope : r ∈ [3, 9, 5, 6, 7] := by rcases hr with rfl | rfl <;> decide
  rcases cases with rfl | rfl | rfl <;> exact oxA_facts_eq P len depth _ r (by decide) scope

theorem farB_facts_eq (P : List CartesianPoint3) (len : P.length = 15) (depth o r : Nat)
    (ho : o ∈ [11, 12, 13]) (hr : r ∈ [3, 9, 11, 12, 13]) :
    facts cageRaw uncapped (depth + 1) (geomOf P len) [] (some r) (farB o) =
      LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 1) (geomOf P len)
        [] (some r) (farB o) := by
  rw [facts_succ, farB_descriptor_eq P len depth o r ho hr,
    LocalizedGenericMarkedRecalculationCage.facts_farB o ho,
    flatMap_facts_eq_nil cageRaw uncapped depth (geomOf P len) [] (some r) _ (farB_leafy o ho)]
  simp

theorem oxB_facts_eq (P : List CartesianPoint3) (len : P.length = 15) (depth o r : Nat)
    (ho : o ∈ [11, 12, 13]) (hr : r ∈ [3, 9, 11, 12, 13]) :
    facts cageRaw uncapped (depth + 2) (geomOf P len) [] (some r) (oxB o) =
      LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2) (geomOf P len)
        [] (some r) (oxB o) := by
  rw [facts_succ_noFrame cageRaw uncapped (depth + 1) (geomOf P len) [] (some r) _
    (oxB_noFrame o ho), children_oxB o ho,
    LocalizedGenericMarkedRecalculationCage.facts_oxB o ho]
  simpa using farB_facts_eq P len depth o r ho hr

theorem nearB_tiedChildren_eq :
    tiedChildren cageRaw uncapped [] nearB =
      LocalizedGenericMarkedRecalculation.tiedChildren cageRaw 16 [] nearB := by
  unfold tiedChildren LocalizedGenericMarkedRecalculation.tiedChildren
  change (match frameAtoms? cageRaw nearB,
    LocalizedMarkedUncappedOperations.ordinary? cageRaw [] nearB with
    | some atoms, some (sorted, adjacent) =>
        (cageRaw.canonicalChildren nearB).filter
          (fun (child : RawMolecule.CanonicalBranchNode) =>
            (eligibleOf atoms sorted adjacent).contains child.atom)
    | _, _ => []) = _
  rw [LocalizedMarkedUncappedCageAgreement.ordinary_near.2]
  rfl

theorem nearB_under_eq (P : List CartesianPoint3) (len : P.length = 15)
    (depth mark : Nat) (member : mark ∈ [11, 12, 13]) :
    underWith cageRaw uncapped (geomOf P len) [] nearB (facts cageRaw uncapped (depth + 2)) mark =
      LocalizedGenericMarkedRecalculation.underWith cageRaw 16 (geomOf P len) [] nearB
        (LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2)) mark := by
  unfold underWith LocalizedGenericMarkedRecalculation.underWith
  rw [nearB_tiedChildren_eq]
  apply flatMap_congr_mem
  intro child present
  rw [LocalizedGenericMarkedRecalculationCage.tiedChildren_nearB] at present
  have cases : child = oxB 11 ∨ child = oxB 12 ∨ child = oxB 13 := by simpa using present
  have scope : mark ∈ [3, 9, 11, 12, 13] := by simp at member ⊢; omega
  rcases cases with rfl | rfl | rfl <;> exact oxB_facts_eq P len depth _ mark (by decide) scope

theorem nearB_raw_eq (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) (depth r : Nat) (hr : r = 3 ∨ r = 9) :
    rawWith? cageRaw uncapped (geomOf P len) [] (some r) nearB
        (facts cageRaw uncapped (depth + 2)) =
      LocalizedGenericMarkedRecalculation.rawWith? cageRaw 16 (geomOf P len) [] (some r) nearB
        (LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2)) := by
  unfold rawWith? LocalizedGenericMarkedRecalculation.rawWith?
  apply rawStep_eq_of_selected cageRaw uncapped bounded (geomOf P len) [] (some r) nearB _ _
    [0, 11, 12, 13] [1, 2, 3, 0] [some .eq, some .eq, some .gt]
    (by simpa only [gFrame_eq] using nearB_frameAtoms)
    (LocalizedMarkedUncappedCageAgreement.ordinary_near.2.trans
      LocalizedGenericMarkedRecalculationCage.nearB_ordinary)
    LocalizedGenericMarkedRecalculationCage.nearB_ordinary
  intro mark chosen
  have member : mark ∈ [11, 12, 13] := by
    simp [eligibleOf, LocalizedGenericMarkedRecalculation.atomsAt,
      LocalizedGenericMarkedRecalculation.tiedPositions] at chosen ⊢
    rcases hr with rfl | rfl <;> omega
  rw [nearB_under_eq P len depth mark member,
    LocalizedGenericMarkedRecalculationCage.underNearB P len nondeg depth mark member,
    LocalizedGenericMarkedRecalculationCage.appendStateB P len mark member]
  simp only [Option.bind_some]
  exact (LocalizedMarkedUncappedCagePhysicalReadback.nearB_readback P len mark member true).trans
    (LocalizedGenericMarkedRecalculationCage.markedReadback_eq P len _ nearB mark).symm

theorem nearB_descriptor_eq (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) (depth r : Nat) (hr : r = 3 ∨ r = 9) :
    descriptor? cageRaw uncapped (depth + 2) (geomOf P len) [] (some r) nearB =
      LocalizedGenericMarkedRecalculation.descriptor? cageRaw 16 (depth + 2) (geomOf P len)
        [] (some r) nearB := by
  unfold descriptor? descriptorWith? LocalizedGenericMarkedRecalculation.descriptor?
    LocalizedGenericMarkedRecalculation.descriptorWith?
  rw [nearB_raw_eq P len nondeg depth r hr, geomOf_mirror,
    nearB_raw_eq _ _ (nondegenerate_mirror P len nondeg) depth r hr]

theorem nearB_facts_eq (P : List CartesianPoint3) (len : P.length = 15)
    (nondeg : Nondegenerate P len) (depth r : Nat) (hr : r = 3 ∨ r = 9) :
    facts cageRaw uncapped (depth + 3) (geomOf P len) [] (some r) nearB =
      LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 3) (geomOf P len)
        [] (some r) nearB := by
  rw [facts_succ, LocalizedGenericMarkedRecalculation.facts_succ,
    nearB_descriptor_eq P len nondeg depth r hr]
  congr 1
  apply flatMap_congr_mem
  intro child present
  rw [children_nearB] at present
  have cases : child = oxB 11 ∨ child = oxB 12 ∨ child = oxB 13 := by simpa using present
  have scope : r ∈ [3, 9, 11, 12, 13] := by rcases hr with rfl | rfl <;> decide
  rcases cases with rfl | rfl | rfl <;> exact oxB_facts_eq P len depth _ r (by decide) scope

end TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation.nearA_under_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation.nearA_raw_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation.nearA_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation.nearA_facts_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation.nearB_under_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation.nearB_raw_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation.nearB_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageNearSimulation.nearB_facts_eq
