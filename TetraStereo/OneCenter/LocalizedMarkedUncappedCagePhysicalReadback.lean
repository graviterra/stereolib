import TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Physical readback of uncapped cage operations on generated snapshots

The actual uncapped marked reader, on the accepted constructor's generated near snapshots,
distinguishes the two cyclic arms exactly when the independent physical domain does. No
temporary letter or desired ranking is a hypothesis: the snapshots are the previously proved
outputs of actual recursive fact generation on the arbitrary nondegenerate geometry.

This is a local replacement theorem. It does not assert that the uncapped recursion generates
these same snapshots; transferring the full recursive induction remains separate.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedCagePhysicalReadback

open LocalizedHiddenParityMarkedProbe LocalizedHiddenParityPromotedReadback
open LocalizedGenericMarkedRecalculationCage LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedMarkedUncappedCageAgreement
open LocalizedMarkedUncappedEvaluator (operations)
open LocalizedMarkedOperationEvaluator (markedReading?)

theorem markedReading_eq_ranked (geom : LocalizedGenericMarkedRecalculation.Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    markedReading? cageRaw (operations cageRaw) geom state node mark =
      (LocalizedMarkedUncappedCageAgreement.rankedAtoms? state node mark).bind
        (LocalizedGenericMarkedRecalculation.readback? geom) := by
  simp only [markedReading?, LocalizedMarkedUncappedCageAgreement.rankedAtoms?,
    operations]
  cases LocalizedGenericMarkedRecalculation.frameAtoms? cageRaw node <;>
    cases LocalizedMarkedUncappedOperations.marked? cageRaw state node mark <;> rfl

theorem markedReading_eq_accepted (P : List CartesianPoint3) (len : P.length = 15)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (mark : Nat)
    (ranked : LocalizedMarkedUncappedCageAgreement.rankedAtoms? state node mark =
      rankedAtomsWith? state node mark) :
    markedReading? cageRaw (operations cageRaw) (geomOf P len) state node mark =
      readbackWith? P len state node mark := by
  rw [markedReading_eq_ranked, ranked]
  rfl

theorem nearA_readback (P : List CartesianPoint3) (len : P.length = 15)
    (mark : Nat) (hm : mark ∈ [5, 6, 7]) (uppercase : Bool) :
    markedReading? cageRaw (operations cageRaw) (geomOf P len)
        (computedStateA P len mark uppercase) nearA mark =
      readbackWith? P len (computedStateA P len mark uppercase) nearA mark := by
  apply markedReading_eq_accepted
  have cases : mark = 5 ∨ mark = 6 ∨ mark = 7 := by simpa using hm
  rcases cases with rfl | rfl | rfl <;> exact nearA_ranked _ (by decide) _ _

theorem nearB_readback (P : List CartesianPoint3) (len : P.length = 15)
    (mark : Nat) (hm : mark ∈ [11, 12, 13]) (uppercase : Bool) :
    markedReading? cageRaw (operations cageRaw) (geomOf P len)
        (computedStateB P len mark uppercase) nearB mark =
      readbackWith? P len (computedStateB P len mark uppercase) nearB mark := by
  apply markedReading_eq_accepted
  have cases : mark = 11 ∨ mark = 12 ∨ mark = 13 := by simpa using hm
  rcases cases with rfl | rfl | rfl <;> exact nearB_ranked _ (by decide) _ _

/-- The snapshots are actual recursively generated lists, not assumed label assignments.
Both marks are arbitrary members of their independently generated reference populations. -/
theorem generated_near_readings_ne_iff_pairwise (P : List CartesianPoint3)
    (len : P.length = 15) (nondeg : Nondegenerate P len) (depth rA rB : Nat)
    (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13]) :
    markedReading? cageRaw (operations cageRaw) (geomOf P len)
        (LocalizedGenericMarkedRecalculation.underWith cageRaw 16 (geomOf P len) [] nearA
          (LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2)) rA) nearA rA ≠
      markedReading? cageRaw (operations cageRaw) (geomOf P len)
        (LocalizedGenericMarkedRecalculation.underWith cageRaw 16 (geomOf P len) [] nearB
          (LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2)) rB) nearB rB ↔
      MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
        (rootWith P len) := by
  rw [underNearA P len nondeg depth rA hA, underNearB P len nondeg depth rB hB,
    nearA_readback P len rA hA true, nearB_readback P len rB hB true]
  exact nearRecalc_ne_iff_pairwise P len nondeg rA hA rB hB true true

/-- Root marked readback also preserves the accepted geometry-derived near labels. -/
theorem generated_root_readback (P : List CartesianPoint3)
    (len : P.length = 15) (nondeg : Nondegenerate P len) (mark : Nat)
    (hm : mark = 3 ∨ mark = 9) :
    markedReading? cageRaw (operations cageRaw) (geomOf P len)
        (LocalizedGenericMarkedRecalculation.underWith cageRaw 16 (geomOf P len) [] root0
          (LocalizedGenericMarkedRecalculation.facts cageRaw 16 15) mark) root0 mark =
      readbackWith? P len
        (rootTemp (jointLetterA P len) (jointLetterB P len) false) root0 mark := by
  rw [underRoot P len nondeg mark hm]
  exact markedReading_eq_accepted P len _ root0 mark (root_ranked mark hm _ _ false)

end TetraStereo.OneCenter.LocalizedMarkedUncappedCagePhysicalReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCagePhysicalReadback.markedReading_eq_ranked
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCagePhysicalReadback.nearA_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCagePhysicalReadback.nearB_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCagePhysicalReadback.generated_near_readings_ne_iff_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCagePhysicalReadback.generated_root_readback
