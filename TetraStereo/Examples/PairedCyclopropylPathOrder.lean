import TetraStereo.Examples.PairedCyclopropylDonorStore
import TetraStereo.Engine.RingTwoShellPathOrder

/-! The direct distal donor precedes the detour exit donor in their shared
sphere. Their first different edge leads to a substituted carbon or to CH₂. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylPathOrder
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingRetainedChemicalPreorder (Direction)
open RingActivePairs (Site)
open RingNestedActivePair (Reader)
open DecalinAuxiliary (history)
open PairedCyclopropylPaths (molecule route)
open RingRetainedStereoRefinement (priority Observation)
open RingStereoSiblingPass (Branch)
open private head_and_kind from TetraStereo.Examples.DecalinAuxiliary
open private sorted_eq from TetraStereo.Examples.DecalinAuxiliary

private def entry (side : Bool) : Nat := if side then 14 else 3

private theorem real_prefix {i : Input} {q : Site i} (a : Direction i q)
    {id x : Nat} {p t : List Nat} (parent : history q = id :: p)
    (child : history a.val = x :: t) (fresh : x ∉ t) :
    RingSecondShellDecision.prefixFor i q a =
      [[RingAtomicNeighborOrder.atomicNumber i.molecule x],RingSecondShellDecision.shell i.molecule id x] := by
  obtain ⟨_,hq,_⟩ := head_and_kind q (RingAllLigandTwoShell.site_current i q)
  obtain ⟨_,ha,kind⟩ := head_and_kind a.val (RingAllLigandTwoShell.site_current i a.val)
  have focus := (List.cons.inj (hq.symm.trans parent)).1
  have cur := List.cons.inj (ha.symm.trans child)
  have real := kind.mpr (by rwa [cur.1,cur.2])
  simp only [RingSecondShellDecision.prefixFor,focus,cur.1,if_pos real]

/-- A rank reader may use any reference and any sequence of stereo passes. On
either arm the CH₂ path loses at the first different edge, because [C,H,H]
precedes [C,C,H] in ascending lexicographic order. -/
theorem shared_priority {i : Input} (raw : i.molecule = molecule) (s : Bool)
    {q : Site i} (viaCH₂ direct : Direction i q)
    (parent : history q = route s 0) (exitPath : history direct.val = route s 1)
    (ch₂Path : history viaCH₂.val = (entry s + 2) :: route s 0)
    {r : Reader i} {rev : Bool} {os : List Observation} {lo hi : Branch}
    (low : priority i r rev os ⟨viaCH₂.val,some q⟩ = some lo)
    (high : priority i r rev os ⟨direct.val,some q⟩ = some hi) :
    lo.deep.length = hi.deep.length ∧ lo.deep < hi.deep := by
  have route0 : route s 0 = [entry s,0] := by cases s <;> rfl
  have route1 : route s 1 = (entry s + 1) :: route s 0 := by cases s <;> rfl
  have same := (RingRetainedSeedFrames.sizes _ _ _ (RingRetainedStereoRefinement.source os _ low)).2.trans
    (RingRetainedSeedFrames.sizes _ _ _ (RingRetainedStereoRefinement.source os _ high)).2.symm
  refine ⟨same,RingTwoShellPathOrder.rank_lt viaCH₂ direct ?_ low high⟩
  rw [real_prefix viaCH₂ (parent.trans route0) ch₂Path (by cases s <;> decide +kernel),
    real_prefix direct (parent.trans route0) (exitPath.trans route1) (by cases s <;> decide +kernel),raw]
  have sorted (xs : List Nat) : RingAtomicSecondShell.sorted xs = DecalinAuxiliary.sorted (fun x : Nat => x) xs :=
    sorted_eq (fun x : Nat => x) xs
  simp only [RingSecondShellDecision.shell,sorted]
  cases s <;> decide +kernel

end TetraStereo.Examples.PairedCyclopropylPathOrder
assert_kernel_only TetraStereo.Examples.PairedCyclopropylPathOrder.shared_priority
