import TetraStereo.Examples.DecalinAuxiliary
import TetraStereo.Examples.DecalinAuxiliaryInventory

/-! An explicit public sphere store on decalin. The only nonconstant inputs are
the opposite junction's oriented volume and one local publication on a reader
whose values are already fixed by that volume. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinJunctionStore
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActiveDistanceSchedule (Cell View frozen distance height)
open RingActivePairs (Site)
open DecalinAuxiliary (history route)
open DecalinAuxiliaryInventory (routes)
open DecalinFrames (molecule junctionRow)

def shortPath (r : Fin 2) : List Nat := [1-r.val,r.val]

private theorem paths (r : Fin 2) :
    routes r.val = [shortPath r,route r 0,route r 1] ∧
    (shortPath r).length = 2 ∧ (route r 0).length = 6 ∧ (route r 1).length = 6 ∧
    route r 0 ≠ route r 1 := by fin_cases r <;> decide +kernel

def longEntry (i : Input) (r s : Fin 2) : Cell :=
  let hand := readback? (RingWrittenPHReadings.geometry i.spatial) (junctionRow (1-r.val))
  some ((if s.val = 0 then hand else hand.map RS.swap).map fun h =>
    (LocalizedTetrahedralRSPseudoDescriptor.chiral h,LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap))

def hands (i : Input) (r : Fin 2) : View i := fun q =>
  if history q = route r 0 then longEntry i r 0
  else if history q = route r 1 then longEntry i r 1 else some none

/-- The overall reader uses one direct-site decision made against the two
entries already known from the opposite junction volume. -/
def cells (i : Input) (r : Fin 2) : View i := fun q =>
  if history q = shortPath r then RingPyramidalPublication.publish i q (frozen (hands i r) q)
  else hands i r q

private theorem length_at {i : Input} (q : Site i) :
    (history q).length = distance q + 1 := by
  simpa only [history,List.length_map,distance] using i.certified.carrierOccurrence_history_length_eq_address_succ q

private theorem on_long {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2) (q : Site i)
    (hit : history q = route r 0 ∨ history q = route r 1) :
    RingChemicalGraphProof.state i q = hands i r q := by
  rcases hit with l|h
  · simpa [hands,l,longEntry] using DecalinAuxiliary.public_state graph ok r 0 l
  · have ne := (paths r).2.2.2.2.symm
    simpa [hands,h,ne,longEntry] using DecalinAuxiliary.public_state graph ok r 1 h

/-- After the fifth sphere the public reader seen by any positive-depth focus
is completely determined by one ordered junction frame. -/
theorem positive_reader {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2) (f : Site i)
    (root : f.val.root.val = r.val) (positive : 1 ≤ distance f) :
    frozen (RingChemicalGraphProof.state i) f = frozen (hands i r) f := by
  funext q
  unfold frozen
  split_ifs with diff vis
  · rfl
  · by_cases hit : history q = route r 0 ∨ history q = route r 1
    · exact on_long graph ok r q hit
    · obtain ⟨l,h⟩ := not_or.mp hit
      have dep := length_at q
      have short : history q ≠ shortPath r := by
        intro e
        rw [e,(paths r).2.1] at dep
        have := vis.1
        omega
      have off : DecalinAuxiliaryInventory.history q ∉ routes f.val.root.val := by
        change history q ∉ _
        simp [root,(paths r).1,short,l,h]
      simpa [hands,l,h] using DecalinAuxiliaryInventory.outside graph ok
        (r := f.val.root) (root ▸ r.isLt) q (of_not_not diff) vis.2 off
  · rfl

private theorem cell_exact {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2)
    (a : i.certified.Atom) (root : a.val = r.val) (q : Site i)
    (on : q.val.root = a) (other : q.val.node.current? ≠ some a) :
    RingChemicalGraphProof.state i q = cells i r q := by
  by_cases short : history q = shortPath r
  · have dep := length_at q
    rw [short,(paths r).2.1] at dep
    simpa only [cells,if_pos short] using (RingChemicalGraphProof.state_eq i q).trans
      (congrArg _ (positive_reader graph ok r q ((congrArg Fin.val on).trans root) (by omega)))
  · simp only [cells,if_neg short]
    by_cases hit : history q = route r 0 ∨ history q = route r 1
    · exact on_long graph ok r q hit
    · obtain ⟨l,h⟩ := not_or.mp hit
      have off : DecalinAuxiliaryInventory.history q ∉ routes a.val := by
        change history q ∉ _
        simp [root,(paths r).1,short,l,h]
      simpa [hands,l,h] using DecalinAuxiliaryInventory.outside graph ok
        (root ▸ r.isLt) q on other off

theorem frozen_exact {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2) (f : Site i)
    (root : f.val.root.val = r.val) :
    frozen (RingChemicalGraphProof.state i) f = frozen (cells i r) f := by
  funext q
  unfold frozen
  split_ifs with diff visible
  · rfl
  · exact cell_exact graph ok r f.val.root root q (of_not_not diff) visible.2
  · rfl

/-- Exact equality of the ordered public row lists after each commit,
including completed refusals at every eligible methylene occurrence. -/
theorem public_rows {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2)
    (a : i.certified.Atom) (root : a.val = r.val) (k : Nat) (bound : k ≤ height i + 1) :
    RingSphereStore.rows i a k = RingSphereQueue.stored (fun q _ => cells i r q)
      a (RingGlobalComparison.queue i a) (height i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change _ ++ RingSphereStore.rows i a k = _ ++ _
    apply congrArg₂ List.append _ (ih (by omega))
    apply List.map_congr_left
    intro q mem
    apply congrArg (Prod.mk q)
    have cand := ((RingEligibleGraph.inventory i (RingPyramidalPublication.eligible i) a) _ q).mp mem
    change RingPyramidalPublication.publish i q (RingGlobalComparison.prior i a k) = _
    rw [RingGlobalComparison.prior_exact (Or.inl ⟨by omega,mem⟩),← RingChemicalGraphProof.state_eq]
    exact cell_exact graph ok r a root q cand.1.1 cand.1.2.1

theorem public_root {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2)
    (a : i.certified.Atom) (root : a.val = r.val) :
    RingChemicalGraphProof.root i a = RingPyramidalPublication.publish i
      (RingGroupedReport.origin i a) (frozen (cells i r) (RingGroupedReport.origin i a)) := by
  exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a).trans
    ((RingChemicalGraphProof.state_eq i _).trans
      (congrArg _ (frozen_exact graph ok r (RingGroupedReport.origin i a) root)))

end TetraStereo.Examples.DecalinJunctionStore
assert_kernel_only TetraStereo.Examples.DecalinJunctionStore.positive_reader
assert_kernel_only TetraStereo.Examples.DecalinJunctionStore.public_rows
assert_kernel_only TetraStereo.Examples.DecalinJunctionStore.public_root
