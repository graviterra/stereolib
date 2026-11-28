import TetraStereo.Examples.HexachlorocyclohexanePublicStore
import TetraStereo.Engine.RingGlobalComparison

/-! The public chronological queue on fully written hexachlorocyclohexane.
Each stored value is determined by its directed ring path and local chlorine,
carbon, carbon, hydrogen frame. -/
set_option autoImplicit false
namespace TetraStereo.Examples.HexachlorocyclohexaneSphereStore
open Engine OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (distance frozen Cell View)
open RingGroupedReport (origin)
open DecalinAuxiliary (history)
open BlueBookHexachlorocyclohexane (molecule)
open HexachlorocyclohexaneFamily (fixedFrame)
open HexachlorocyclohexanePublicStore (tag? carbon)
open private at_route outside tag_some from TetraStereo.Examples.HexachlorocyclohexanePublicStore

def cell (i : Input) (r : Fin 6) (cw : Bool) (k : Fin 5) : Cell :=
  let h := readback? (RingWrittenPHReadings.geometry i.spatial) (fixedFrame (carbon r cw k))
  some ((if cw then h else h.map RS.swap).map fun v => (.chiral v,.chiral v.swap))

def store (i : Input) (r : Fin 6) : View i := fun q =>
  match tag? r (history q) with
  | some (cw,k) => cell i r cw k
  | none => some none

theorem visible_cell {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 6) (atRoot : root.val = r.val) (q : Site i) (on : q.val.root = root)
    (other : q.val.node.current? ≠ some root) :
    RingChemicalGraphProof.state i q = store i r q := by
  unfold store
  cases found : tag? r (history q) with
  | none => exact outside graph r atRoot q on other found
  | some t =>
    obtain ⟨cw,k⟩ := t
    exact HexachlorocyclohexanePublicStore.public_state graph ok r cw k (tag_some found)

/-- This also covers unqueued branches and the terminal copy of the root. -/
theorem positive_state {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 6) (atRoot : root.val = r.val) (q : Site i) (on : q.val.root = root)
    (positive : 0 < distance q) :
    RingChemicalGraphProof.state i q = store i r q := by
  by_cases real : q.val.node.provenance = .realAtom
  · apply visible_cell graph ok r atRoot q on
    simpa only [←on] using RingFrameTransport.positive_real_not_root q real positive
  have absent : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q := fun h => real h.1
  rw [RingChemicalGraphProof.state_eq,RingChemicalGraphProof.skips i q _ absent]
  unfold store
  cases hit : tag? r (history q) with
  | none => rfl
  | some t =>
    obtain ⟨cw,k⟩ := t
    exact (real (at_route r cw k (tag_some hit)).1).elim

open private enumerated scan_covers scanned no_pyramids atom_bound four_only graphRows
  from TetraStereo.Examples.HexachlorocyclohexanePublicStore

/-- A native queue address is present at exactly its own depth on a tagged
carbon path of the selected root. -/
theorem queued_iff {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (r : Fin 6) (atRoot : root.val = r.val) (q : Site i) (d : Nat) :
    q ∈ RingGlobalComparison.queue i root d ↔
      q.val.root = root ∧ (tag? r (history q)).isSome = true ∧ distance q = d := by
  rw [RingEligibleGraph.inventory i (RingPyramidalPublication.eligible i) root d q]
  constructor
  · rintro ⟨⟨on,other,real,a,current,poss⟩,dist⟩
    refine ⟨on,?_,dist⟩
    obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
    have same : b = a := Option.some.inj (hb.symm.trans current)
    subst b
    rw [on] at path
    have hp : RingPyramidalPublication.phosphorus i a = false := by
      change (RingAtomicNeighborOrder.neutralPyramidal i.molecule a.val && _) = false
      simp [graph,no_pyramids ⟨_,atom_bound graph a⟩]
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
      simpa [RingPyramidalPublication.eligible,hp] using poss
    obtain ⟨lastAtom,mem⟩ := enumerated graph path
    rw [atRoot] at mem
    have upper := RingGraphAuxiliaries.length_bound path
    have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
    rw [graph] at size
    change _ = 18 at size
    have distinct : a.val ≠ r.val := fun h => other (current.trans (congrArg some (Fin.ext (h.trans atRoot.symm))))
    have hit := scan_covers r 18 0 (scanned r) (by omega : q.val.node.history.length-1 < 18)
      (by simpa using mem) (lastAtom ▸ four_only graph a four) (lastAtom ▸ distinct)
    change (tag? r (history q)).isSome = true at hit
    exact hit
  · rintro ⟨on,tagged,dist⟩
    obtain ⟨⟨cw,k⟩,found⟩ := Option.isSome_iff_exists.mp tagged
    let a := RingAllLigandTwoShell.siteAtom i q
    have cur := RingAllLigandTwoShell.site_current i q
    obtain ⟨real,id⟩ := at_route r cw k (tag_some found)
    have away : ∀ (r : Fin 6) (cw : Bool) (k : Fin 5), carbon r cw k ≠ r.val := by decide +kernel
    have other : q.val.node.current? ≠ some root := fun h =>
      away r cw k (id.symm.trans ((congrArg Fin.val (Option.some.inj (cur.symm.trans h))).trans atRoot))
    have degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
      rw [RingAtomicNeighborOrder.degree_eq,graph,show a.val = carbon r cw k from id]
      exact (graphRows (carbon r cw k) (Nat.mod_lt _ (by decide))).length_eq.trans rfl
    exact ⟨⟨on,other,real,a,cur,by simp [RingPyramidalPublication.eligible,degree]⟩,dist⟩

theorem frozen_exact {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 6) (atRoot : root.val = r.val) :
    frozen (RingChemicalGraphProof.state i) (origin i root) = frozen (store i r) (origin i root) := by
  funext q
  unfold frozen
  split_ifs with off visible
  · rfl
  · exact visible_cell graph ok r atRoot q (of_not_not off) visible.2
  · rfl

/-- After every sphere the actual public list of addressed cells equals the
list produced by writing the directed cyclic frame reading at each address.
The statement retains list order, repeated values and completed refusals. -/
theorem public_rows {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 6) (atRoot : root.val = r.val) (k : Nat) (bound : k ≤ RingActiveDistanceSchedule.height i + 1) :
    RingSphereStore.rows i root k =
      RingSphereQueue.stored (fun q _ => store i r q) root (RingGlobalComparison.queue i root)
        (RingActiveDistanceSchedule.height i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have previous := ih (by omega)
    change _ ++ RingSphereStore.rows i root k = _ ++ _
    apply congrArg₂ List.append _ previous
    apply List.map_congr_left
    intro q mem
    apply congrArg (Prod.mk q)
    have active := ((RingEligibleGraph.inventory i (RingPyramidalPublication.eligible i) root) _ q).mp mem
    change RingPyramidalPublication.publish i q (RingGlobalComparison.prior i root k) = _
    rw [RingGlobalComparison.prior_exact (Or.inl ⟨by omega,mem⟩),← RingChemicalGraphProof.state_eq]
    exact visible_cell graph ok r atRoot q active.1.1 active.1.2.1

end TetraStereo.Examples.HexachlorocyclohexaneSphereStore
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSphereStore.positive_state
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSphereStore.frozen_exact
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSphereStore.public_rows
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSphereStore.queued_iff
