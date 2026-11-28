import TetraStereo.Examples.CrossParentRootOrder
import TetraStereo.Examples.CrossParentPublicWords
import TetraStereo.Examples.AntipodalCyclohexaneRanking

/-! All four root ligands of the cross-parent fixture. Sulfur and oxygen
precede both nitrogen arms, whose complete keys compare by donor populations. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentPublicRanking
open OneCenter Engine LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedCentre (cursor)
open RingGroupedReport (origin)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey)
open CrossParentDonorStore (molecule ligandRow)
open CrossParentRootOrder (rank countWord)
open RingWrittenPHReadings (geometry)
open CrossParentClasses (publicRead)
open AntipodalCyclohexaneRanking (slotNumber compare_distinct_atoms)
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private slot_injective from TetraStereo.Engine.RingAtomicFramePriority
attribute [local instance] lexOrd

def rootFrame : List Nat := [40,39,1,2]
theorem neighbors0 : (RingAtomicNeighborOrder.neighbors molecule 0).Perm rootFrame := by
  exact (RingStereoSiblingPass.legal_order _ _).perm.trans (by decide +kernel)

theorem frameIds {i : Input} (raw : i.molecule = molecule) {v : i.certified.Atom}
    (hz : v.val = 0) (fr : RingNestedActivePair.Frame i (origin i v)) :
    (fr.atoms (List.finRange 4)).Perm rootFrame := by
  have all := frame_perm fr
  have focus : v = fr.center.val := Option.some.inj
    ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  rw [raw,←focus,hz] at all
  exact all.trans neighbors0

private abbrev z := RingAtomicNeighborOrder.atomicNumber molecule

private theorem numbers (h : Fin 8 → RS) (rev : Bool) (a b : Nat) (ha : a ∈ rootFrame) (hb : b ∈ rootFrame) :
    (z a ≠ z b → compare (z a) (z b) = compare (rank h rev a) (rank h rev b)) ∧
    (a ≠ b → z a = z b → (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) := by
  simp only [rootFrame,List.mem_cons,List.mem_nil_iff,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;>
    cases ho : CrossParentRootOrder.order h rev <;> simp only [rank,ho] <;> decide +kernel

theorem frame_order {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (hands : Fin 8 → RS)
    (signs : ∀ j, readback? (geometry i.spatial) (ligandRow j) = some (hands j))
    (rev : Bool) (ks : Fin 4 → Key) (got : RingFullPathPublication.keys? fr (publicRead i root) rev = some ks)
    (a b : Fin 4) : compare (trialKey (ks a) []) (trialKey (ks b) []) =
      compare (rank hands rev (atom fr a)) (rank hands rev (atom fr b)) := by
  have key (s : Fin 4) : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr s) = some (ks s) :=
    RingActivePairReport.four_at got s
  have reads (s : Fin 4) : Reads i (publicRead i root) rev (cursor fr s) (ks s) := by
    obtain ⟨k,hk,exactK⟩ := RingFullPathEligibility.key_exact (RingChemicalGraphProof.ready geom _)
      rev (cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    exact (exactK _).mpr (Option.some.inj ((key s).symm.trans hk))
  have forward (u v : Fin 4) (U : atom fr u = 1) (V : atom fr v = 2) :
      compare (trialKey (ks u) []) (trialKey (ks v) []) = compare (rank hands rev (atom fr u)) (rank hands rev (atom fr v)) := by
    obtain ⟨x,y,hx,hy,early,lower⟩ := CrossParentClasses.root_earlier graph geom root zero fr u v U V rev
    obtain rfl : x = ks u := Option.some.inj (hx.symm.trans (key u))
    obtain rfl : y = ks v := Option.some.inj (hy.symm.trans (key v))
    have l := CrossParentPublicWords.ring_word graph geom root zero fr u true U hands signs rev
    have r := CrossParentPublicWords.ring_word graph geom root zero fr v false V hands signs rev
    rw [U,V]
    exact CrossParentRootOrder.arm_order hands rev _ _ early lower
      (CrossParentRootOrder.fields hands true rev (key u) (l [] (Or.inl rfl)) (l [.lowercase] (Or.inr rfl) .R))
      (CrossParentRootOrder.fields hands false rev (key v) (r [] (Or.inl rfl)) (r [.lowercase] (Or.inr rfl) .R))
  by_cases same : atom fr a = atom fr b
  · have eq : a = b := slot_injective fr (Subtype.ext (Fin.ext (by simpa only [RingAtomicFramePriority.slotNeighbor_val] using same)))
    subst b; simp
  have mem (s : Fin 4) := (frameIds graph zero fr).mem_iff.mp (List.mem_map_of_mem (f := atom fr) (List.mem_finRange s))
  have pos := numbers hands rev _ _ (mem a) (mem b)
  by_cases diff : z (atom fr a) ≠ z (atom fr b)
  · have different : slotNumber fr a ≠ slotNumber fr b := by unfold slotNumber; rw [graph]; exact diff
    have out := compare_distinct_atoms fr (reads a) (reads b) different [] []
    unfold slotNumber at out
    rw [graph] at out
    exact out.trans (pos.1 diff)
  rcases pos.2 same (of_not_not diff) with ⟨A,B⟩|⟨B,A⟩
  · exact forward a b A B
  · calc
      _ = (compare (trialKey (ks b) []) (trialKey (ks a) [])).swap := Std.OrientedCmp.eq_swap ..
      _ = _ := congrArg Ordering.swap (forward b a A B)
      _ = _ := (Std.OrientedCmp.eq_swap ..).symm

end TetraStereo.Examples.CrossParentPublicRanking
assert_kernel_only TetraStereo.Examples.CrossParentPublicRanking.frame_order
