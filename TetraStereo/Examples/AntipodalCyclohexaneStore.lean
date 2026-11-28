import TetraStereo.Examples.AntipodalCyclohexaneHands
import TetraStereo.Engine.RingGlobalComparison
import TetraStereo.Engine.RingTerminalTwinRefusal

/-! The positive-distance store in the retained digraph rooted at either substituted carbon
of cyclohexane-1,4-diol. Only the two real paths to the opposite substituted carbon
carry a hand. Their signs come from its ordered physical frame. -/
set_option autoImplicit false
namespace TetraStereo.Examples.AntipodalCyclohexaneStore
open Engine OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingGraphPaths (Path)
open RingActiveDistanceSchedule (distance frozen Cell View)
open RingGroupedReport (origin)
open AntipodalCyclohexaneHands (molecule route opposite frameRow)
open DecalinAuxiliary (history)
open private raw_adj bound toAtom from TetraStereo.Engine.RingAtomicNeighborOrder

private theorem atom_bound {i : Input} (graph : i.molecule = molecule) (a : i.certified.Atom) : a.val < 20 := by
  simpa only [graph] using bound i a

private def incident (a : Nat) := (List.range molecule.atomCount).filter fun n => 0 < molecule.bondOrder a n

private theorem four_only {i : Input} (graph : i.molecule = molecule) (a : i.certified.Atom)
    (four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4) : a.val < 6 := by
  have test : ∀ n : Fin 20, (incident n.val).length = 4 → n.val < 6 := by decide +kernel
  rw [RingAtomicNeighborOrder.degree_eq,graph] at four
  exact test ⟨_,atom_bound graph a⟩ (((RingStereoSiblingPass.legal_order _ _).perm.length_eq).symm.trans four)

private theorem no_pyramids : ∀ a : Fin 20, RingAtomicNeighborOrder.neutralPyramidal molecule a.val = false := by
  decide +kernel

private def leaf (a : Nat) := if a < 3 then 7+2*a else 8+2*a

private theorem pair_at {i : Input} (graph : i.molecule = molecule) (c : i.certified.TetrahedralCenter)
    (carbon : c.val.val < 6) (nz : c.val.val ≠ 0) (nt : c.val.val ≠ 3)
    (root : i.certified.Atom) (top : root.val = 0 ∨ root.val = 3) :
    ∃ p : RingHydrogenSpelling.TwinPair i, p.c = c ∧ root ≠ p.u ∧ root ≠ p.v := by
  have facts : ∀ n : Fin 6, n.val ≠ 0 → n.val ≠ 3 →
      leaf n.val + 1 < 20 ∧ 3 < leaf n.val ∧
      (molecule.atoms[leaf n.val]?).map RingRawRenumbering.molecularRecord =
        (molecule.atoms[leaf n.val+1]?).map RingRawRenumbering.molecularRecord ∧
      ∀ b : Fin 20, molecule.bondOrder (leaf n.val) b.val = (if b.val = n.val then 1 else 0) ∧
        molecule.bondOrder (leaf n.val+1) b.val = (if b.val = n.val then 1 else 0) := by decide +kernel
  obtain ⟨hi,lo,records,edges⟩ := facts ⟨_,carbon⟩ nz nt
  change leaf c.val.val + 1 < 20 at hi
  change 3 < leaf c.val.val at lo
  let u := toAtom i (leaf c.val.val) (by rw [graph]; change _ < 20; omega)
  let v := toAtom i (leaf c.val.val+1) (by rw [graph]; exact hi)
  have hu : u.val = leaf c.val.val := rfl
  have hv : v.val = leaf c.val.val+1 := rfl
  let p : RingHydrogenSpelling.TwinPair i := {
    c := c, u := u, v := v
    distinct := fun e => by have h := congrArg Fin.val e; rw [hu,hv] at h; omega
    records := by rw [hu,hv,graph]; exact records
    lu := fun b => by rw [hu,graph]; simpa only [Fin.ext_iff] using (edges ⟨_,atom_bound graph b⟩).1
    lv := fun b => by rw [hv,graph]; simpa only [Fin.ext_iff] using (edges ⟨_,atom_bound graph b⟩).2 }
  refine ⟨p,rfl,?_,?_⟩
  · intro e
    have h : root.val = leaf c.val.val := congrArg Fin.val e
    omega
  · intro e
    have h : root.val = leaf c.val.val+1 := congrArg Fin.val e
    omega

private def routes (r : Fin 2) := [route r 0,route r 1]

private def neighbors := molecule.writtenNeighbors

private theorem edges : ∀ a b : Fin 20, b.val ∈ neighbors a.val ↔ 0 < molecule.bondOrder a.val b.val := by
  decide +kernel
private def expand (h : List Nat) : List (List Nat) :=
  ((neighbors (h.headD 20)).filter fun b => !h.contains b).map (· :: h)

private def paths (r : Nat) : Nat → List (List Nat)
  | 0 => [[r]]
  | n+1 => (paths r n).flatMap expand

private theorem enumerated {i : Input} (graph : i.molecule = molecule) {r a h}
    (p : Path i r h a) :
    (h.map Fin.val).headD 20 = a.val ∧ h.map Fin.val ∈ paths r.val (h.length-1) := by
  induction p with
  | origin => exact ⟨rfl,List.mem_singleton_self _⟩
  | @step hist cur next prev edge fresh ih =>
    have positive : 0 < hist.length := by cases prev <;> simp
    have n : (next::hist).length - 1 = (hist.length - 1) + 1 := by simp; omega
    have adj := (raw_adj i cur next).mp edge
    rw [graph] at adj
    have outside : next.val ∉ hist.map Fin.val := by
      rintro h
      obtain ⟨b,mem,e⟩ := List.mem_map.mp h
      exact fresh (Fin.ext e ▸ mem)
    refine ⟨rfl,?_⟩
    rw [n,paths,List.mem_flatMap]
    exact ⟨_,ih.2,List.mem_map.mpr ⟨next.val,by
      rw [List.mem_filter,ih.1]
      exact ⟨(edges ⟨cur.val,atom_bound graph cur⟩ ⟨next.val,atom_bound graph next⟩).mpr adj,by simpa using outside⟩,rfl⟩⟩

/-- The check traverses each layer once, including empty layers up to the
simple-path length bound. -/
private def scan (r : Fin 2) : Nat → List (List Nat) → Bool
  | 0,_ => true
  | n+1,hs => hs.all (fun h => h.headD 20 != opposite r || (routes r).contains h) &&
      scan r n (hs.flatMap expand)

private theorem scan_covers (r : Fin 2) (fuel start : Nat)
    (yes : scan r fuel (paths (3*r.val) start) = true) {n : Nat} (within : n < fuel)
    {h : List Nat} (mem : h ∈ paths (3*r.val) (start+n)) (lastAtom : h.headD 20 = opposite r) :
    h ∈ routes r := by
  induction fuel generalizing start n with
  | zero => omega
  | succ fuel ih =>
    have pair := Bool.and_eq_true_iff.mp yes
    cases n with
    | zero =>
      have hit := List.all_eq_true.mp pair.1 h (by simpa using mem)
      change (h.headD 20 != opposite r || (routes r).contains h) = true at hit
      rw [lastAtom] at hit
      simpa using hit
    | succ n =>
      apply ih (start+1) pair.2 (by omega : n < fuel)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using mem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem scanned : ∀ r : Fin 2, scan r 20 [[3*r.val]] = true := by decide +kernel

theorem path_to_opposite {i : Input} (graph : i.molecule = molecule) {root a h}
    (r : Fin 2) (atRoot : root.val = 3*r.val) (p : Path i root h a) (other : a.val = opposite r) :
    h.map Fin.val ∈ routes r := by
  obtain ⟨lastAtom,mem⟩ := enumerated graph p
  rw [atRoot] at mem
  have upper := RingGraphAuxiliaries.length_bound p
  have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  rw [graph] at size
  change _ = 20 at size
  exact scan_covers r 20 0 (scanned r) (by omega : h.length-1 < 20)
    (by simpa using mem) (lastAtom.trans other)

theorem outside {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 2) (atRoot : root.val = 3*r.val) (q : Site i) (on : q.val.root = root)
    (other : q.val.node.current? ≠ some root) (off : history q ∉ routes r) :
    RingChemicalGraphProof.state i q = some none := by
  by_cases eligible : RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q
  · obtain ⟨real,a,current,poss⟩ := eligible
    obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
    have same : b = a := Option.some.inj (hb.symm.trans current)
    subst b
    rw [on] at path
    have distinct : a.val ≠ root.val := fun e => other (current.trans (congrArg some (Fin.ext e)))
    have away : a.val ≠ opposite r := fun eqn => off (path_to_opposite graph r atRoot path eqn)
    have hp : RingPyramidalPublication.phosphorus i a = false := by
      change (RingAtomicNeighborOrder.neutralPyramidal i.molecule a.val && _) = false
      simp [graph,no_pyramids ⟨_,atom_bound graph a⟩]
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
      simpa [RingPyramidalPublication.eligible,hp] using poss
    let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
    have which : (root.val = 0 ∧ opposite r = 3) ∨ (root.val = 3 ∧ opposite r = 0) := by
      fin_cases r <;> simp_all [opposite]
    obtain ⟨pair,center,u,v⟩ := pair_at graph c (four_only graph a four)
      (by change a.val ≠ 0; omega) (by change a.val ≠ 3; omega) root (by omega)
    exact pair.occurrence_refusal ok q (on ▸ u) (on ▸ v) real (center ▸ current)
  · exact (RingChemicalGraphProof.state_eq i q).trans (RingChemicalGraphProof.skips i q _ eligible)

def cell (i : Input) (r s : Fin 2) : Cell :=
  let h := readback? (RingWrittenPHReadings.geometry i.spatial) (frameRow r)
  some ((if s.val = 0 then h else h.map RS.swap).map fun v => (.chiral v,.chiral v.swap))

def store (i : Input) (r : Fin 2) : View i := fun q =>
  if history q = route r 0 then cell i r 0 else if history q = route r 1 then cell i r 1 else some none

theorem visible_cell {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 2) (atRoot : root.val = 3*r.val) (q : Site i) (on : q.val.root = root)
    (other : q.val.node.current? ≠ some root) :
    RingChemicalGraphProof.state i q = store i r q := by
  unfold store
  split
  · exact AntipodalCyclohexaneHands.public_state graph ok r 0 ‹_›
  split
  · exact AntipodalCyclohexaneHands.public_state graph ok r 1 ‹_›
  exact outside graph ok r atRoot q on other (by simp_all [routes])

open private at_route from TetraStereo.Examples.AntipodalCyclohexaneHands

/-- A positive real occurrence cannot return to its original root; any
positive return copy is independently ineligible. This describes state cells
even before applying the frozen reader's visibility guard. -/
theorem positive_state {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 2) (atRoot : root.val = 3*r.val) (q : Site i) (on : q.val.root = root)
    (positive : 0 < distance q) :
    RingChemicalGraphProof.state i q = store i r q := by
  by_cases real : q.val.node.provenance = .realAtom
  · apply visible_cell graph ok r atRoot q on
    simpa only [←on] using RingFrameTransport.positive_real_not_root q real positive
  have absent : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q := fun h => real h.1
  have noRoute (s : Fin 2) : history q ≠ route r s := fun h => real ((at_route r s h).1)
  rw [RingChemicalGraphProof.state_eq,RingChemicalGraphProof.skips i q _ absent]
  simp [store,noRoute]

theorem frozen_exact {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 2) (atRoot : root.val = 3*r.val) :
    frozen (RingChemicalGraphProof.state i) (origin i root) = frozen (store i r) (origin i root) := by
  funext q
  unfold frozen
  split_ifs with off visible
  · rfl
  · exact visible_cell graph ok r atRoot q (of_not_not off) visible.2
  · rfl

/-- After every sphere the actual public list of addressed cells equals the
list produced by writing the explicit two-level calculation at each address.
The statement retains list order, repeated values and completed refusals. -/
theorem public_rows {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 2) (atRoot : root.val = 3*r.val) (k : Nat) (bound : k ≤ RingActiveDistanceSchedule.height i + 1) :
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


/-- The direct and reflected uppercase hand read at any cursor in this original digraph. -/
theorem handAt_eq {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 2) (atRoot : root.val = 3*r.val) (q : RingActivePairs.Arm i)
    (on : q.occurrence.val.root = root) (h : RS)
    (sense : readback? (RingWrittenPHReadings.geometry i.spatial) (frameRow r) = some h)
    (rev : Bool) :
    RingFullPathPairs.handAt i (frozen (RingChemicalGraphProof.state i) (origin i root)) rev q =
      if history q.occurrence = route r 0 then some (if rev then h.swap else h)
      else if history q.occurrence = route r 1 then some (if rev then h else h.swap) else none := by
  have routeHand (s : Fin 2) (here : history q.occurrence = route r s) :
      RingFullPathPairs.handAt i (frozen (RingChemicalGraphProof.state i) (origin i root)) rev q =
        some (if s.val = 0 then (if rev then h.swap else h) else (if rev then h else h.swap)) := by
    have len : (route r s).length = 4 := by fin_cases r <;> fin_cases s <;> rfl
    have d : (history q.occurrence).length = distance q.occurrence + 1 := by
      simpa only [history,List.length_map,distance] using
        i.certified.carrierOccurrence_history_length_eq_address_succ q.occurrence
    rw [here,len] at d
    have off : q.occurrence.val.node.current? ≠ some root := by
      intro eqn
      have a := (at_route r s here).2
      rw [Option.some.inj ((RingAllLigandTwoShell.site_current i q.occurrence).symm.trans eqn),atRoot] at a
      fin_cases r <;> contradiction
    have active : frozen (RingChemicalGraphProof.state i) (origin i root) q.occurrence =
        RingChemicalGraphProof.state i q.occurrence := by
      change (if q.occurrence.val.root ≠ root then _ else if 0 < distance q.occurrence ∧ _ then _ else _) = _
      rw [if_neg (not_not_intro on),if_pos ⟨by omega,off⟩]
    have state := AntipodalCyclohexaneHands.public_state graph ok r s here
    unfold RingFullPathPairs.handAt
    rw [active,state,sense]
    fin_cases s <;> cases rev <;> cases h <;> rfl
  split
  · exact routeHand 0 ‹_›
  split
  · exact routeHand 1 ‹_›
  rw [frozen_exact graph ok r atRoot]
  unfold RingFullPathPairs.handAt frozen store
  split_ifs <;> rfl

end TetraStereo.Examples.AntipodalCyclohexaneStore
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneStore.frozen_exact
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneStore.public_rows
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneStore.handAt_eq
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneStore.positive_state
