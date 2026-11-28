import TetraStereo.Examples.CrossParentClasses
import TetraStereo.Engine.RingGlobalComparison

/-! Chronological public store at atom 0 of the 41-atom cross-parent graph. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentSphereStore
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (distance frozen)
open RingGroupedReport (origin)
open DecalinAuxiliary (history)
open CrossParentClasses (route hand expectedView)
open CrossParentDonorStore (molecule cell)
open private shell incident types pyramids from TetraStereo.Examples.CrossParentDonorStore
open private bound from TetraStereo.Engine.RingAtomicNeighborOrder
open private head_and_kind from TetraStereo.Examples.DecalinAuxiliary

private theorem depth {i : Input} (q : Site i) (j : Fin 8) (path : history q = route j) :
    distance q = 3 := by
  have len : (history q).length = distance q + 1 := by
    simpa [history,distance] using i.certified.carrierOccurrence_history_length_eq_address_succ q
  rw [path] at len
  change 4 = _ at len
  omega

theorem queued_iff {i : Input} (graph : i.molecule = molecule)
    (root : i.certified.Atom) (zero : root.val = 0) (q : Site i) (d : Nat) :
    q ∈ RingGlobalComparison.queue i root d ↔
      q.val.root = root ∧ d = 3 ∧ ∃ j : Fin 8, history q = route j := by
  rw [RingEligibleGraph.inventory i (RingPyramidalPublication.eligible i) root d q]
  constructor
  · rintro ⟨⟨on,other,real,a,current,poss⟩,dist⟩
    have size : a.val < 41 := by have h := bound i a; rwa [graph] at h
    have gate : RingPyramidalPublication.phosphorus i a = false := by
      change (RingAtomicNeighborOrder.neutralPyramidal i.molecule a.val && _) = false
      rw [graph,pyramids ⟨a.val,size⟩]; rfl
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
      simpa [RingPyramidalPublication.eligible,gate] using poss
    rw [RingAtomicNeighborOrder.degree_eq,graph] at four
    have len := (RingStereoSiblingPass.legal_order (RingAtomicNeighborOrder.atomicNumber molecule)
      (incident a.val)).perm.length_eq
    rcases types ⟨a.val,size⟩ (len.symm.trans four) with atZero | tip
    · exact (other (current.trans (congrArg some (Fin.ext (atZero.trans zero.symm))))).elim
    · let j : Fin 8 := ⟨a.val-7,by change 7 ≤ a.val ∧ a.val < 15 at tip; omega⟩
      have id : a.val = 7+j.val := by dsimp [j]; change 7 ≤ a.val ∧ a.val < 15 at tip; omega
      have path : history q = route j := CrossParentDonorStore.unique_history graph q
        ((congrArg Fin.val on).trans zero) real j (by rw [current]; exact congrArg some id)
      exact ⟨on,dist.symm.trans (depth q j path),j,path⟩
  · rintro ⟨on,rfl,j,path⟩
    let a := RingAllLigandTwoShell.siteAtom i q
    have cur := RingAllLigandTwoShell.site_current i q
    obtain ⟨tail,ht,kind⟩ := head_and_kind q cur
    have data : a.val = 7+j.val ∧ tail = [3+j.val/2,1+j.val/4,0] := by
      simpa [route] using ht.symm.trans path
    have real := kind.mpr (by rw [data.1,data.2]; simp; omega)
    have other : q.val.node.current? ≠ some root := fun eqn => by
      have bad := (congrArg Fin.val (Option.some.inj (cur.symm.trans eqn))).trans zero
      omega
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
      rw [RingAtomicNeighborOrder.degree_eq,graph,data.1]
      exact ((RingStereoSiblingPass.legal_order _ _).perm.trans (shell j).1.symm).length_eq.trans rfl
    exact ⟨⟨on,other,real,a,cur,by simp [RingPyramidalPublication.eligible,four]⟩,depth q j path⟩

theorem attained {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (zero : root.val = 0) (j : Fin 8) :
    ∃ q ∈ RingGlobalComparison.queue i root 3, history q = route j ∧
      RingChemicalGraphProof.state i q = cell (hand i.spatial j) := by
  obtain ⟨q,on,path,value⟩ := CrossParentClasses.observed graph ok root zero j
  exact ⟨q,(queued_iff graph root zero q 3).mpr ⟨on,rfl,j,path⟩,path,value⟩

theorem public_rows {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (zero : root.val = 0) (k : Nat) (le : k ≤ RingActiveDistanceSchedule.height i + 1) :
    RingSphereStore.rows i root k =
      RingSphereQueue.stored (fun q _ => expectedView q) root (RingGlobalComparison.queue i root)
        (RingActiveDistanceSchedule.height i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change _ ++ RingSphereStore.rows i root k = _ ++ _
    apply congrArg₂ List.append _ (ih (by omega))
    apply List.map_congr_left
    intro q mem
    apply congrArg (Prod.mk q)
    have active := ((RingEligibleGraph.inventory i (RingPyramidalPublication.eligible i) root) _ q).mp mem
    change RingPyramidalPublication.publish i q (RingGlobalComparison.prior i root k) = _
    rw [RingGlobalComparison.prior_exact (Or.inl ⟨by omega,mem⟩),←RingChemicalGraphProof.state_eq]
    obtain ⟨on,_,j,path⟩ := (queued_iff graph root zero q _).mp mem
    have same := congrFun (CrossParentClasses.reader graph ok (origin i root) zero) q
    change (if q.val.root ≠ root then _ else if 0 < distance q ∧ _ then _ else _) =
      (if q.val.root ≠ root then _ else if 0 < distance q ∧ _ then _ else _) at same
    have off : q.val.node.current? ≠ some (origin i root).val.root := active.1.2.1
    simpa [on,depth q j path,off] using same

end TetraStereo.Examples.CrossParentSphereStore
assert_kernel_only TetraStereo.Examples.CrossParentSphereStore.queued_iff
assert_kernel_only TetraStereo.Examples.CrossParentSphereStore.attained
assert_kernel_only TetraStereo.Examples.CrossParentSphereStore.public_rows
