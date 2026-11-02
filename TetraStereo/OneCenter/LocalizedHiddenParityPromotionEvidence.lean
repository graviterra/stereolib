import TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback
import TetraStereo.OneCenter.OccurrenceRule6RankingEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# Separate pseudo and promotion evidence on the experimental cage

These calls use the same explicit temporary snapshots as the accepted recalculation theorem.
Counts are runtime evidence, not an adopted chemical case policy. The far call uses the explicit
empty ordinary state. No identity with a production generated fixed point is claimed.
-/

namespace TetraStereo.OneCenter.LocalizedHiddenParityPromotionEvidence

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback

def evidenceAt? (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : Option OccurrenceRule6RankingEvidence := do
  let roots ← occurrenceLigandFrame? cageRaw node
  let ligands := roots.map fun cursor => cursor.node.atom
  let referencePosition := ligands.idxOf mark
  if referencePosition >= ligands.length then none else
    rankOccurrenceWithRule6Evidence? cageRaw state 16 roots ligands [0, 1, 2, 3]
      referencePosition

/-- Positions, uniqueness, ordinary final-pair pseudo count, final-pair promotion count,
and original insertion-time marker count, in that order. -/
def summary? (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : Option (List Nat × Bool × Nat × Nat × Nat) :=
  (evidenceAt? state node mark).map fun e =>
    (e.ranking.positions, e.ranking.unique, e.priorPseudoCount,
      e.adjacentPromotionCount, e.ranking.pseudoComparisons)

#eval summary? [] (farA 5) 6
#eval summary? (tempStateA 5 RS.S true) nearA 5
#eval summary? (tempStateA 5 RS.S false) nearA 5
#eval summary? (rootTemp RS.R RS.S true) root0 3
#eval summary? (rootTemp RS.R RS.S false) root0 3
#eval summary? (rootTemp RS.R RS.R true) root0 3
#eval summary? (rootTemp RS.R RS.R false) root0 3

/-- Uniqueness and the three distinct counts, retaining no arbitrary priority-position data. -/
def channels? (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : Option (Bool × Nat × Nat × Nat) :=
  (evidenceAt? state node mark).map fun e =>
    (e.ranking.unique, e.priorPseudoCount, e.adjacentPromotionCount,
      e.ranking.pseudoComparisons)

theorem far_channels : channels? [] (farA 5) 6 = some (true, 0, 1, 1) := by
  decide +kernel

theorem near_channels (first : RS) (uppercase : Bool) :
    channels? (tempStateA 5 first uppercase) nearA 5 =
      some (true, if uppercase then 1 else 0, 0, 0) := by
  cases first <;> cases uppercase <;> decide +kernel

theorem root_distinct_channels (first : RS) (uppercase : Bool) :
    channels? (rootTemp first first.swap uppercase) root0 3 =
      some (true, if uppercase then 1 else 0, 0, 0) := by
  cases first <;> cases uppercase <;> decide +kernel

theorem root_equal_channels (first : RS) (uppercase : Bool) :
    channels? (rootTemp first first uppercase) root0 3 = some (true, 0, 1, 1) := by
  cases first <;> cases uppercase <;> decide +kernel

/-- The old insertion marker count is zero for both near snapshots even though their ordinary
pseudo counts differ. Thus that marker count cannot replace the lost ordinary evidence. -/
theorem near_prior_evidence_differs (first : RS) :
    channels? (tempStateA 5 first true) nearA 5 = some (true, 1, 0, 0) ∧
      channels? (tempStateA 5 first false) nearA 5 = some (true, 0, 0, 0) := by
  constructor <;> exact near_channels first _

assert_kernel_only far_channels
assert_kernel_only near_channels
assert_kernel_only root_distinct_channels
assert_kernel_only root_equal_channels
assert_kernel_only near_prior_evidence_differs

end TetraStereo.OneCenter.LocalizedHiddenParityPromotionEvidence
