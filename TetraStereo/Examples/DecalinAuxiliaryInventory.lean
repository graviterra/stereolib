import TetraStereo.Examples.DecalinFrames

/-! Exact support for the auxiliary reader at either fusion root. The graph
has only three simple paths to the other junction. All other eligible atoms
encountered on the way have terminal hydrogen twins. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinAuxiliaryInventory
open TetraStereo.Engine OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingGraphPaths (Path)
open RingActiveDistanceSchedule (distance frozen Cell View)
open DecalinFrames (molecule)
open private methylene_pair four_only no_pyramids atom_bound atom incident neighbor_perm from TetraStereo.Examples.DecalinFrames
open private raw_adj bound from TetraStereo.Engine.RingAtomicNeighborOrder

private theorem unique_leaf : ∀ c : Fin 2, ∀ u : Fin 28,
    (∀ b : Fin 28, molecule.bondOrder u.val b.val = if b.val = c.val then 1 else 0) →
      u.val = 10+c.val := by decide +kernel

private theorem leaf_at_junction {i : Input} (graph : i.molecule = molecule) {c u : i.certified.Atom}
    (j : c.val < 2) (leaf : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val =
      if a = c then 1 else 0) : u.val = 10+c.val := by
  apply unique_leaf ⟨c.val,j⟩ ⟨u.val,atom_bound graph u⟩
  intro b
  have eq := leaf (atom i graph b)
  rw [graph] at eq
  simpa only [Fin.ext_iff] using eq

/-- At either junction root the public twin detector succeeds exactly at
the eight methylene centers. This removes its sorted neighbor indexing
from a closed calculation on this graph. -/
theorem detected {i : Input} (graph : i.molecule = molecule) (r : i.certified.Atom)
    (j : r.val < 2) (c : i.certified.TetrahedralCenter) :
    (RingRootTwinDecision.detectedTwinPair? i r c).isSome = decide (2 ≤ c.val.val) := by
  apply Bool.eq_iff_iff.mpr
  rw [RingRootTwinDecision.detected_iff,decide_eq_true_eq]
  constructor
  · rintro ⟨p,rfl,_,_⟩
    by_contra! low
    exact p.distinct (Fin.ext ((leaf_at_junction graph low p.lu).trans
      (leaf_at_junction graph low p.lv).symm))
  · intro low
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor c.val) = 4 :=
      (i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property
    rw [RingAtomicNeighborOrder.degree_eq,graph] at four
    exact methylene_pair graph c low (four_only ⟨c.val.val,atom_bound graph c.val⟩ four) r j

private theorem carbon_four : ∀ a : Fin 10, (incident a.val).length = 4 := by decide +kernel

def methylene {i : Input} (q : Site i) : Bool :=
  decide (q.val.node.provenance = .realAtom) && q.val.node.current?.any fun a => decide (2 ≤ a.val ∧ a.val < 10)

/-- A kernel-reducible test for the original public pruning decision at every
occurrence, including duplicate leaves and hydrogens. -/
theorem direct {i : Input} (graph : i.molecule = molecule) (q : Site i)
    (j : q.val.root.val < 2) : RingRootTwinDecision.direct i q =
      if methylene q then some (some none) else none := by
  unfold RingRootTwinDecision.direct
  cases hc : i.certified.localizedOccurrenceDescriptorCenter? q with
  | none =>
    suffices no : methylene q = false by simp [no]
    by_contra! hit
    have yes : methylene q = true := by cases h : methylene q <;> simp_all
    obtain ⟨real,test⟩ := Bool.and_eq_true_iff.mp yes
    have real' := of_decide_eq_true real
    cases cur : q.val.node.current? with
    | none => simp [cur] at test
    | some a =>
      simp only [cur,Option.any_some,decide_eq_true_eq] at test
      have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
        rw [RingAtomicNeighborOrder.degree_eq,graph]
        exact (neighbor_perm _).length_eq.trans (carbon_four ⟨a.val,test.2⟩)
      let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
      have := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨real',cur⟩
      simp [hc] at this
  | some c =>
    obtain ⟨real,cur⟩ := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp hc
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor c.val) = 4 :=
      (i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property
    rw [RingAtomicNeighborOrder.degree_eq,graph] at four
    have high := four_only ⟨c.val.val,atom_bound graph c.val⟩ four
    have det := detected graph q.val.root j c
    cases h : RingRootTwinDecision.detectedTwinPair? i q.val.root c <;>
      simp_all [methylene]

/-- Histories have the same newest-atom-first convention as the public reader. -/
def routes (r : Nat) : List (List Nat) :=
  if r = 0 then [[1,0],[1,3,5,4,2,0],[1,8,9,7,6,0]]
  else [[0,1],[0,2,4,5,3,1],[0,6,7,9,8,1]]

/-- Bond adjacency of the published graph in ascending atom order. -/
private def neighbors (a : Nat) : List Nat :=
  #[[1,2,6,10],[0,3,8,11],[0,4,12,13],[1,5,14,15],[2,5,16,17],
    [3,4,18,19],[0,7,20,21],[6,9,22,23],[1,9,24,25],[7,8,26,27],
    [0],[1],[2],[2],[3],[3],[4],[4],[5],[5],[6],[6],[7],[7],[8],[8],[9],[9]].getD a []

private theorem edges : ∀ a b : Fin 28, b.val ∈ neighbors a.val ↔ 0 < molecule.bondOrder a.val b.val := by
  decide +kernel

private def expand (h : List Nat) : List (List Nat) :=
  ((neighbors (h.headD 28)).filter fun b => !h.contains b).map (· :: h)

private def paths (r : Nat) : Nat → List (List Nat)
  | 0 => [[r]]
  | n+1 => (paths r n).flatMap expand

private theorem enumerated {i : Input} (graph : i.molecule = molecule) {r a h}
    (p : Path i r h a) :
    (h.map Fin.val).headD 28 = a.val ∧ h.map Fin.val ∈ paths r.val (h.length-1) := by
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
private def scan (r : Nat) : Nat → List (List Nat) → Bool
  | 0,_ => true
  | n+1,hs => hs.all (fun h => h.headD 28 != 1-r || (routes r).contains h) &&
      scan r n (hs.flatMap expand)

private theorem scan_covers (r : Nat) (fuel start : Nat)
    (yes : scan r fuel (paths r start) = true) {n : Nat} (within : n < fuel)
    {h : List Nat} (mem : h ∈ paths r (start+n)) (lastAtom : h.headD 28 = 1-r) :
    h ∈ routes r := by
  induction fuel generalizing start n with
  | zero => omega
  | succ fuel ih =>
    have pair := Bool.and_eq_true_iff.mp yes
    cases n with
    | zero =>
      have hit := List.all_eq_true.mp pair.1 h (by simpa using mem)
      change (h.headD 28 != 1-r || (routes r).contains h) = true at hit
      rw [lastAtom] at hit
      simpa using hit
    | succ n =>
      apply ih (start+1) pair.2 (by omega : n < fuel)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using mem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem scanned : ∀ r : Fin 2, scan r.val 28 [[r.val]] = true := by decide +kernel

theorem path_to_opposite {i : Input} (graph : i.molecule = molecule) {r a h}
    (junction : r.val < 2) (p : Path i r h a) (other : a.val = 1-r.val) :
    h.map Fin.val ∈ routes r.val := by
  obtain ⟨lastAtom,mem⟩ := enumerated graph p
  have upper := RingGraphAuxiliaries.length_bound p
  have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  rw [graph] at size
  change _ = 28 at size
  exact scan_covers r.val 28 0 (scanned ⟨r.val,junction⟩) (by omega : h.length-1 < 28)
    (by simpa using mem) (lastAtom.trans other)

def history {i : Input} (q : Site i) := q.val.node.history.map Fin.val

/-- Every real or duplicate occurrence outside these three histories has
a completed refusal whenever it is visible to this root. -/
theorem outside {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {r : i.certified.Atom}
    (junction : r.val < 2) (q : Site i) (on : q.val.root = r)
    (other : q.val.node.current? ≠ some r) (off : history q ∉ routes r.val) :
    RingChemicalGraphProof.state i q = some none := by
  by_cases eligible : RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q
  · obtain ⟨real,a,current,poss⟩ := eligible
    obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
    have same : b = a := Option.some.inj (hb.symm.trans current)
    subst b
    rw [on] at path
    have distinct : a ≠ r := fun e => other (current.trans (congrArg some e))
    have nonjunction : 2 ≤ a.val := by
      by_contra! near
      have ne : a.val ≠ r.val := fun e => distinct (Fin.ext e)
      exact off (path_to_opposite graph junction path (by omega))
    have ng := no_pyramids ⟨a.val,atom_bound graph a⟩
    have hp : RingPyramidalPublication.phosphorus i a = false := by
      change (RingAtomicNeighborOrder.neutralPyramidal i.molecule a.val && _) = false
      rw [graph]; simp [ng]
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
      simpa [RingPyramidalPublication.eligible,hp] using poss
    let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
    rw [RingAtomicNeighborOrder.degree_eq,graph] at four
    obtain ⟨pair,center,u,v⟩ := methylene_pair graph c nonjunction (four_only ⟨a.val,atom_bound graph a⟩ four) r junction
    exact pair.occurrence_refusal ok q (on ▸ u) (on ▸ v) real (center ▸ current)
  · exact (RingChemicalGraphProof.state_eq i q).trans (RingChemicalGraphProof.skips i q _ eligible)

/-- Supplying cells only for the three histories reconstructs the native
frozen reader. Unavailable lookups on other roots and invisible occurrences
are still handled by the public scheduling rule. -/
theorem reader {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {r : i.certified.Atom}
    (junction : r.val < 2) (f : Site i) (root : f.val.root = r) :
    frozen (RingChemicalGraphProof.state i) f =
      frozen (fun q => if history q ∈ routes r.val then RingChemicalGraphProof.state i q else some none) f := by
  funext q
  unfold frozen
  split_ifs with off visible
  · rfl
  · by_cases keep : history q ∈ routes r.val
    · simp [keep]
    · simpa [keep] using outside graph ok junction q ((of_not_not off).trans root) (root ▸ visible.2) keep
  · rfl

private theorem history_length {i : Input} (q : Site i) :
    (history q).length = distance q + 1 := by
  simpa only [history,List.length_map,distance] using
    i.certified.carrierOccurrence_history_length_eq_address_succ q

private theorem route_depth {r : Nat} {i : Input} {q : Site i} (h : history q ∈ routes r) :
    distance q = 1 ∨ distance q = 5 := by
  have len := history_length q
  unfold routes at h
  split at h <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at h <;>
    rcases h with e|e|e <;> rw [e] at len <;> simp at len <;> omega

/-- At a long-route occurrence all visible auxiliary labels are refusals. -/
theorem deep_reader {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {r : i.certified.Atom}
    (junction : r.val < 2) (f : Site i) (root : f.val.root = r) (deep : 5 ≤ distance f) :
    frozen (RingChemicalGraphProof.state i) f = frozen (fun _ => some none) f := by
  rw [reader graph ok junction f root]
  funext q
  unfold frozen
  split_ifs with same vis
  · rfl
  · have off : history q ∉ routes r.val := by
      intro h
      have := route_depth h
      have := vis.1
      omega
    simp [off]
  · rfl

/-- The local public calculation with all visible auxiliary labels empty. -/
def longCell (i : Input) (q : Site i) : Cell :=
  RingPyramidalPublication.publish i q (frozen (fun _ => some none) q)

def longStore (i : Input) (r : Nat) : View i := fun q =>
  if history q ∈ routes r ∧ distance q = 5 then longCell i q else some none

theorem short_reader {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {r : i.certified.Atom}
    (junction : r.val < 2) (f : Site i) (root : f.val.root = r) (positive : 1 ≤ distance f) :
    frozen (RingChemicalGraphProof.state i) f = frozen (longStore i r.val) f := by
  rw [reader graph ok junction f root]
  funext q
  unfold frozen
  split_ifs with same vis
  · rfl
  · by_cases keep : history q ∈ routes r.val
    · have depth : distance q = 5 := by
        have := route_depth keep
        have := vis.1
        omega
      simp only [if_pos keep,longStore,depth,and_true]
      simpa only [if_pos keep,longCell] using
        (RingChemicalGraphProof.state_eq i q).trans
          (congrArg _ (deep_reader graph ok junction q ((of_not_not same).trans root) (by omega)))
    · simp [longStore,keep]
  · rfl

/-- All three cells are computed without any reference to the recursive public state. -/
def junctionStore (i : Input) (r : Nat) : View i := fun q =>
  if history q ∈ routes r then
    if distance q = 5 then longCell i q
    else RingPyramidalPublication.publish i q (frozen (longStore i r) q)
  else some none

theorem junction_reader {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {r : i.certified.Atom}
    (junction : r.val < 2) (f : Site i) (root : f.val.root = r) :
    frozen (RingChemicalGraphProof.state i) f = frozen (junctionStore i r.val) f := by
  rw [reader graph ok junction f root]
  funext q
  unfold frozen
  split_ifs with same vis
  · rfl
  · by_cases keep : history q ∈ routes r.val
    · have qr := (of_not_not same).trans root
      rcases route_depth keep with shallow|deep
      · simp [junctionStore,keep,shallow]
        exact (RingChemicalGraphProof.state_eq i q).trans
          (congrArg _ (short_reader graph ok junction q qr (by omega)))
      · simp [junctionStore,keep,deep,longCell]
        exact (RingChemicalGraphProof.state_eq i q).trans
          (congrArg _ (deep_reader graph ok junction q qr (by omega)))
    · simp [junctionStore,keep]
  · rfl

theorem junction_state {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (f : Site i)
    (junction : f.val.root.val < 2) :
    RingChemicalGraphProof.state i f =
      RingPyramidalPublication.publish i f (frozen (junctionStore i f.val.root.val) f) := by
  rw [RingChemicalGraphProof.state_eq, junction_reader graph ok junction f rfl]

private theorem candidate_cell {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {r : i.certified.Atom}
    (junction : r.val < 2) (q : Site i)
    (active : RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r q) :
    RingChemicalGraphProof.state i q = junctionStore i r.val q := by
  by_cases keep : history q ∈ routes r.val
  · rcases route_depth keep with shallow|deep
    · simp only [junctionStore,if_pos keep,shallow,show (1:Nat) ≠ 5 by decide,if_false]
      rw [RingChemicalGraphProof.state_eq,short_reader graph ok junction q active.1 (by omega)]
    · simp [junctionStore,keep,deep,longCell]
      rw [RingChemicalGraphProof.state_eq,deep_reader graph ok junction q active.1 (by omega)]
  · simpa only [junctionStore,if_neg keep] using outside graph ok junction q active.1 active.2.1 keep

/-- After every sphere the actual public list of addressed cells equals the
list produced by writing the explicit two-level calculation at each address.
The statement retains list order, repeated values and completed refusals. -/
theorem sphere_rows {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : i.certified.Atom)
    (junction : r.val < 2) (k : Nat) (bound : k ≤ RingActiveDistanceSchedule.height i + 1) :
    RingSphereStore.rows i r k =
      RingSphereQueue.stored (fun q _ => junctionStore i r.val q) r (RingGlobalComparison.queue i r)
        (RingActiveDistanceSchedule.height i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have previous := ih (by omega)
    change _ ++ RingSphereStore.rows i r k = _ ++ _
    apply congrArg₂ List.append _ previous
    apply List.map_congr_left
    intro q mem
    apply congrArg (Prod.mk q)
    have active := ((RingEligibleGraph.inventory i (RingPyramidalPublication.eligible i) r) _ q).mp mem
    change RingPyramidalPublication.publish i q (RingGlobalComparison.prior i r k) = _
    rw [RingGlobalComparison.prior_exact (Or.inl ⟨by omega,mem⟩),← RingChemicalGraphProof.state_eq]
    exact candidate_cell graph ok junction q active.1

end TetraStereo.Examples.DecalinAuxiliaryInventory
assert_kernel_only TetraStereo.Examples.DecalinAuxiliaryInventory.path_to_opposite
assert_kernel_only TetraStereo.Examples.DecalinAuxiliaryInventory.outside
assert_kernel_only TetraStereo.Examples.DecalinAuxiliaryInventory.reader
assert_kernel_only TetraStereo.Examples.DecalinAuxiliaryInventory.junction_state
assert_kernel_only TetraStereo.Examples.DecalinAuxiliaryInventory.sphere_rows
assert_kernel_only TetraStereo.Examples.DecalinAuxiliaryInventory.direct
