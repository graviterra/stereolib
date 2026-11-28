import TetraStereo.Examples.PairedCyclopropylPaths
import TetraStereo.Examples.PairedCyclopropylDonorStore
import TetraStereo.Engine.RingGlobalComparison

/-! First publication and subsequent readback at each of the ten cyclic donor
histories. The public queue processes spheres from the outside inward. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylSphereStore
open Engine OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (distance height)
open RingPyramidalPublication (eligible publish)
open DecalinAuxiliary (history)
open PairedCyclopropylPaths (molecule route order)
open private head_and_kind from TetraStereo.Examples.DecalinAuxiliary

/-- Direct entry, direct exit, direct distal donor, detour exit, detour distal donor. -/
def depth (visit : Fin 5) : Nat := ![1,2,3,3,4] visit

/-- All ten keys are distinct, including visits that end at the same carbon. -/
theorem distinct_routes : ∀ (a b : Bool) (u v : Fin 5),
    route a u = route b v → a = b ∧ u = v := by decide +kernel

private theorem routes_shape : ∀ (side : Bool) (v : Fin 5),
    (route side v).length = depth v + 1 ∧ (route side v).head? ≠ some 0 := by
  decide +kernel

private theorem keys_at {i : Input} {q : Site i} {root : i.certified.Atom}
    (candidate : RingEligibleGraph.candidate (eligible i) root q)
    (k : Nat) (bound : k ≤ height i + 1) :
    q ∈ (RingSphereStore.rows i root k).map Prod.fst ↔ height i < distance q + k := by
  induction k with
  | zero =>
    have upper := RingActiveDistanceSchedule.distance_bound q
    simp [RingSphereStore.rows,RingSphereQueue.stored,Nat.not_lt.mpr upper]
  | succ k ih =>
    have step : (RingSphereStore.rows i root (k+1)).map Prod.fst =
        RingGlobalComparison.queue i root (height i-k) ++
        (RingSphereStore.rows i root k).map Prod.fst := by
      simp [RingSphereStore.rows,RingSphereQueue.stored,RingGlobalComparison.queue,
        List.map_map,Function.comp_def]
    rw [step,List.mem_append,RingEligibleGraph.inventory,ih (by omega)]
    simp only [candidate,true_and]
    omega

/-- For any admitted placement on the written graph each designated route has a
unique stored key after its own sphere commits, and zero keys before then. Its
stored value is the hand read from its four ordered physical coordinates and
the opposite hand for the mirror. Both statements hold at every public cut. -/
theorem donor_at_each_cut {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0) (side : Bool) (v : Fin 5) :
    ∃ (q : Site i) (h : RS), q.val.root = root ∧ q.val.node.provenance = .realAtom ∧
      history q = route side v ∧ distance q = depth v ∧
      (∀ t : Site i, t.val.root = root → history t = route side v → t = q) ∧
      readback? (RingWrittenPHReadings.geometry i.spatial) (order side v) = some h ∧
      ∀ k, k ≤ height i + 1 →
        ((RingSphereStore.rows i root k).map Prod.fst).count q =
          (if height i < depth v + k then 1 else 0) ∧
        RingSphereQueue.viewOf (RingSphereStore.rows i root k) q =
          (if height i < depth v + k then some (some (.chiral h,.chiral h.swap)) else some none) := by
  obtain ⟨q,on,real,path⟩ := PairedCyclopropylPaths.route_exists i graph side v
  change history q = route side v at path
  have same : q.val.root = root := Fin.ext (on.trans zero.symm)
  obtain ⟨h,read,value⟩ := PairedCyclopropylDonorStore.public_hand graph ok side v path
  have shape := routes_shape side v
  have len : (history q).length = distance q + 1 := by
    simpa [history,distance] using i.certified.carrierOccurrence_history_length_eq_address_succ q
  have dist : distance q = depth v := by rw [show history q = route side v from path,shape.1] at len; omega
  have off : q.val.node.current? ≠ some root := by
    intro equality
    obtain ⟨tail,ht,_⟩ := head_and_kind q equality
    exact shape.2 (by rw [←path,ht,zero]; rfl)
  have active : RingEligibleGraph.Eligible (eligible i) q := by
    by_contra no
    have dead := RingChemicalGraphProof.skips i q (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) q) no
    rw [←RingChemicalGraphProof.state_eq,value] at dead
    simp at dead
  have cand : RingEligibleGraph.candidate (eligible i) root q := ⟨same,off,active⟩
  have unique (t : Site i) (atRoot : t.val.root = root) (routeEq : history t = route side v) : t = q := by
    have hist : t.val.node.history = q.val.node.history :=
      List.map_injective_iff.mpr Fin.val_injective (routeEq.trans path.symm)
    apply i.certified.molecularFrameUnit_injective_on_simpleBonded_carrier i.single
    simp [molecularFrameUnit,atRoot,same,hist]
  refine ⟨q,h,same,real,path,dist,unique,read,?_⟩
  intro k bound
  have key := keys_at cand k bound
  rw [dist] at key
  constructor
  · split
    · rename_i done_
      exact List.count_eq_one_of_mem (RingSphereStore.chemical_stored_keys_nodup i root k bound) (key.mpr done_)
    · rename_i pending
      exact List.count_eq_zero.mpr (fun mem => pending (key.mp mem))
  · unfold RingSphereStore.rows
    rw [RingSphereQueue.stored_eq,RingEligibleGraph.run_exact (RingChemicalGraphProof.skips i)
      (RingEligibleGraph.inventory i (eligible i) root) k bound q]
    unfold RingChemicalGraphProof.state at value
    simp only [cand,true_and,dist,value]

/-- A physical row for each route, and a known refusal for all other queued
sites. It reads only the numbered graph history and the input coordinates. -/
def geometricCell {i : Input} (q : Site i) : RingActiveDistanceSchedule.Cell :=
  let visits := [false,true].flatMap fun s => (List.finRange 5).map fun v => (s,v)
  match visits.find? (fun p => history q == route p.1 p.2) with
  | none => some none
  | some (s,v) => (readback? (RingWrittenPHReadings.geometry i.spatial) (order s v)).map fun h =>
      some (.chiral h,.chiral h.swap)

private theorem geometric_exact {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i)
    (candidate : RingEligibleGraph.candidate (eligible i) (PairedCyclopropylPaths.atom i graph 0) q) :
    RingChemicalGraphProof.state i q = geometricCell q := by
  unfold geometricCell
  dsimp only
  split
  · rename_i miss
    rcases PairedCyclopropylPaths.candidate_cases i graph q candidate with ⟨s,v,path⟩ | twins
    · have listed : (s,v) ∈ [false,true].flatMap (fun b => (List.finRange 5).map fun n => (b,n)) := by
        apply List.mem_flatMap.mpr
        exact ⟨s,by cases s <;> simp,List.mem_map.mpr ⟨v,List.mem_finRange _,rfl⟩⟩
      have absent := List.find?_eq_none.mp miss (s,v) listed
      change history q = route s v at path
      simp [path] at absent
    · exact RingRootTwinDecision.sound i q ok _ twins
  · rename_i s v hit
    have path : history q = route s v := eq_of_beq (List.find?_some (p := fun p : Bool × Fin 5 => history q == route p.1 p.2) hit)
    obtain ⟨h,seen,value⟩ := PairedCyclopropylDonorStore.public_hand graph ok s v path
    simp [seen,value]

/-- Exact public row list after each batch: ten physical donor paths across
the whole run, with every other queued row a terminal-hydrogen twin refusal. -/
theorem public_rows {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (zero : root.val = 0) (k : Nat) (bound : k ≤ height i + 1) :
    RingSphereStore.rows i root k =
      RingSphereQueue.stored (fun q _ => geometricCell q) root (RingGlobalComparison.queue i root)
        (height i) k := by
  have same : root = PairedCyclopropylPaths.atom i graph 0 := Fin.ext zero
  induction k with
  | zero => rfl
  | succ k ih =>
    change _ ++ RingSphereStore.rows i root k = _ ++ _
    apply congrArg₂ List.append _ (ih (by omega))
    apply List.map_congr_left
    intro q mem
    apply congrArg (Prod.mk q)
    change publish i q (RingGlobalComparison.prior i root k) = _
    rw [RingGlobalComparison.prior_exact (Or.inl ⟨by omega,mem⟩),←RingChemicalGraphProof.state_eq]
    exact geometric_exact graph ok q (same ▸ ((RingEligibleGraph.inventory i (eligible i) root _ q).mp mem).1)

/-- Every scheduled off-route site is a known refusal from its identical
terminal hydrogens, on the actual public graph state. -/
theorem off_route_state {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i)
    (candidate : RingEligibleGraph.candidate (eligible i) (PairedCyclopropylPaths.atom i graph 0) q)
    (off : ∀ side v, history q ≠ route side v) :
    RingChemicalGraphProof.state i q = some none := by
  rcases PairedCyclopropylPaths.candidate_cases i graph q candidate with ⟨s,v,path⟩ | twins
  · exact (off s v path).elim
  · exact RingRootTwinDecision.sound i q ok _ twins

end TetraStereo.Examples.PairedCyclopropylSphereStore
assert_kernel_only TetraStereo.Examples.PairedCyclopropylSphereStore.distinct_routes
assert_kernel_only TetraStereo.Examples.PairedCyclopropylSphereStore.donor_at_each_cut
assert_kernel_only TetraStereo.Examples.PairedCyclopropylSphereStore.public_rows
assert_kernel_only TetraStereo.Examples.PairedCyclopropylSphereStore.off_route_state
