import TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator
import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# Local operation agreement on the dependent-center cage

These finite checks compare the actual unrestricted operations at the general reroot bound
with the accepted cage operations. They check sorted atom lists, including refusal of
nonunique rankings, rather than choosing a replacement ordering or geometric letter.
The explicit temporary states below are the finite states occurring in the accepted generated
recalculation. This module alone does not transfer that recursive derivation to the new instance.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement

open LocalizedHiddenParityMarkedProbe
open LocalizedHiddenParityPromotedReadback LocalizedHiddenParityPromotedPipeline

def rankedAtoms? (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : Option (List Nat) := do
  let atoms ← LocalizedGenericMarkedRecalculation.frameAtoms? cageRaw node
  let ranking ← LocalizedMarkedUncappedOperations.marked? cageRaw state node mark
  LocalizedGenericMarkedRecalculation.rankedAtoms? atoms ranking

theorem ordinary_root :
    LocalizedMarkedUncappedOperations.ordinary? cageRaw [] root0 =
      LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] root0 := by
  decide +kernel

theorem ordinary_near :
    LocalizedMarkedUncappedOperations.ordinary? cageRaw [] nearA =
      LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] nearA ∧
    LocalizedMarkedUncappedOperations.ordinary? cageRaw [] nearB =
      LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] nearB := by
  decide +kernel

theorem ordinary_farA (o : Nat) (member : o ∈ [5, 6, 7]) :
    LocalizedMarkedUncappedOperations.ordinary? cageRaw [] (farA o) =
      LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] (farA o) := by
  have cases : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using member
  rcases cases with rfl | rfl | rfl <;> decide +kernel

theorem ordinary_farB (o : Nat) (member : o ∈ [11, 12, 13]) :
    LocalizedMarkedUncappedOperations.ordinary? cageRaw [] (farB o) =
      LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] (farB o) := by
  have cases : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using member
  rcases cases with rfl | rfl | rfl <;> decide +kernel

/-- Includes the diagonal nonunique refusal and both off-diagonal orders. -/
theorem farA_ranked (o mark : Nat) (ho : o ∈ [5, 6, 7]) (hm : mark ∈ [5, 6, 7]) :
    rankedAtoms? [] (farA o) mark = visitRankedAtoms? (farA o) mark := by
  have oc : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using ho
  have mc : mark = 5 ∨ mark = 6 ∨ mark = 7 := by simpa using hm
  rcases oc with rfl | rfl | rfl <;> rcases mc with rfl | rfl | rfl <;> decide +kernel

theorem farB_ranked (o mark : Nat) (ho : o ∈ [11, 12, 13]) (hm : mark ∈ [11, 12, 13]) :
    rankedAtoms? [] (farB o) mark = visitRankedAtoms? (farB o) mark := by
  have oc : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using ho
  have mc : mark = 11 ∨ mark = 12 ∨ mark = 13 := by simpa using hm
  rcases oc with rfl | rfl | rfl <;> rcases mc with rfl | rfl | rfl <;> decide +kernel

theorem nearA_ranked (mark : Nat) (hm : mark ∈ [5, 6, 7]) (first : RS) (uppercase : Bool) :
    rankedAtoms? (tempStateA mark first uppercase) nearA mark =
      rankedAtomsWith? (tempStateA mark first uppercase) nearA mark := by
  have mc : mark = 5 ∨ mark = 6 ∨ mark = 7 := by simpa using hm
  rcases mc with rfl | rfl | rfl <;> cases first <;> cases uppercase <;> decide +kernel

theorem nearB_ranked (mark : Nat) (hm : mark ∈ [11, 12, 13]) (first : RS) (uppercase : Bool) :
    rankedAtoms? (tempStateB mark first uppercase) nearB mark =
      rankedAtomsWith? (tempStateB mark first uppercase) nearB mark := by
  have mc : mark = 11 ∨ mark = 12 ∨ mark = 13 := by simpa using hm
  rcases mc with rfl | rfl | rfl <;> cases first <;> cases uppercase <;> decide +kernel

/-- Both root references, both near letters and both temporary casing conventions. -/
theorem root_ranked (mark : Nat) (hm : mark = 3 ∨ mark = 9)
    (left right : RS) (uppercase : Bool) :
    rankedAtoms? (rootTemp left right uppercase) root0 mark =
      rankedAtomsWith? (rootTemp left right uppercase) root0 mark := by
  rcases hm with rfl | rfl <;> cases left <;> cases right <;> cases uppercase <;> decide +kernel

end TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.ordinary_root
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.ordinary_near
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.ordinary_farA
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.ordinary_farB
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.farA_ranked
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.farB_ranked
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.nearA_ranked
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.nearB_ranked
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageAgreement.root_ranked
