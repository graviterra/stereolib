import TetraStereo.Examples.PairedCyclopropylDonorStore
import TetraStereo.Examples.CrossParentAllAtoms

/-! Public roots at every peripheral atom of the paired cyclopropyl graph. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylPeripheral
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedReport (origin)
open RingNestedActivePair (Labels)
open RingWrittenPHReadings (geometry)
open PairedCyclopropylPaths (molecule order)
open PairedCyclopropylDonorStore (twoShells state_from_graph)
open private twoShells_eq from TetraStereo.Examples.PairedCyclopropylDonorStore
open private degree twins_at no_pyramid neighbors from TetraStereo.Examples.PairedCyclopropylPaths
open private bound toAtom from TetraStereo.Engine.RingAtomicNeighborOrder
open private row? from TetraStereo.Engine.RingChemicalReport

def donor? : Nat → Option (Bool × Fin 3)
  | 3 => some (false,0) | 4 => some (false,1) | 10 => some (false,2)
  | 14 => some (true,0) | 15 => some (true,1) | 21 => some (true,2) | _ => none

def donorRow (s : Bool) (v : Fin 3) := order s ⟨v.val,by omega⟩
private def donorId (s : Bool) (v : Fin 3) := (if s then 14 else 3) + ![0,1,7] v

private theorem donorId_of {n : Nat} {s : Bool} {k : Fin 3} (hit : donor? n = some (s,k)) :
    n = donorId s k := by
  unfold donor? at hit
  split at hit <;> simp_all [donorId]
  all_goals obtain ⟨_,rfl⟩ := hit; decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem strict (s : Bool) (v : Fin 3) :
    let n := donorId s v
    (donorRow s v).length = 4 ∧ (donorRow s v).Perm (RingAtomicNeighborOrder.neighbors molecule n) ∧
      ((donorRow s v).map (twoShells molecule [n])).Pairwise (· > ·) := by
  dsimp only
  rw [twoShells_eq]
  refine ⟨?_,List.Perm.trans ?_ (RingStereoSiblingPass.legal_order _ _).perm.symm,?_⟩
  all_goals cases s <;> fin_cases v <;> decide +kernel

theorem donor {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom) {s k}
    (hit : donor? v.val = some (s,k)) :
    ∃ h, readback? (geometry i.spatial) (donorRow s k) = some h ∧
      RingChemicalGraphProof.root i v = some (some (.chiral h,.chiral h.swap)) := by
  obtain ⟨four,layout,desc⟩ := strict s k
  have atId := donorId_of hit
  have path : DecalinAuxiliary.history (origin i v) = [donorId s k] := by change [v.val] = _; rw [atId]
  obtain ⟨h,seen,cell⟩ := state_from_graph (q := origin i v) ok path (by simp) four
    (by rw [raw]; exact layout) (by rw [raw]; exact desc)
  exact ⟨h,seen,(RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) v).trans cell⟩

private theorem inventory : ∀ n : Fin 25, n.val ≠ 0 → donor? n.val = none →
    (neighbors n.val).length = 4 → n.val = 5 ∨ n.val = 16 := by decide +kernel

theorem inactive {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom)
    (nz : v.val ≠ 0) (off : donor? v.val = none) : RingChemicalGraphProof.root i v = some none := by
  by_cases four : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4
  · let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
    have eqn := inventory (RingHydrogenSpelling.rawVertices i raw v) nz off ((degree i raw v).symm.trans four)
    obtain ⟨p,same,_⟩ := twins_at i raw c eqn
    simpa only [same] using p.root_refusal ok
  · have skipped : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) (origin i v) := by
      rintro ⟨_,a,current,on⟩
      obtain rfl : v = a := Option.some.inj current
      exact four (by simpa [RingPyramidalPublication.eligible,no_pyramid i raw] using on)
    exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) v).trans
      ((RingChemicalGraphProof.state_eq i _).trans (RingChemicalGraphProof.skips i _ _ skipped))

def expectedRow? (x : SpatialConfiguration) (central : Option Labels) (n : Nat) : Option (Nat × Option Labels) :=
  if n < 25 then
    if n = 0 then some (n,central) else
      match donor? n with
      | none => some (n,none)
      | some (s,k) => (readback? (geometry x) (donorRow s k)).map fun h => (n,some (.chiral h,.chiral h.swap))
  else none

private theorem closed : RingHydrogenCompletion.plan molecule = [] := by decide +kernel

/-- A central result determines the raw answer for every request list, including
repeated, out-of-range and peripheral IDs. -/
theorem raw_agreement (i : Input) (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (central : Option Labels)
    (root : ∀ v : i.certified.Atom, v.val = 0 → RingChemicalGraphProof.root i v = some central)
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = ids.mapM (expectedRow? i.spatial central) := by
  have size (v : i.certified.Atom) : v.val < 25 := by have h := bound i v; rwa [raw] at h
  by_cases good : ids.all (· < 25) = true
  · let vs := ids.attach.map fun n => toAtom i n.val (by rw [raw]; exact of_decide_eq_true (List.all_eq_true.mp good _ n.property))
    have resolved : vs.map Fin.val = ids := by simp [vs,List.map_map,Function.comp_def,toAtom]
    have native := RingWrittenPHReadings.fromRaw_closed_report i (raw ▸ closed) ok vs
    rw [raw,resolved] at native
    rw [native,←resolved,List.mapM_map]
    apply RingFrameTransport.mapM_congr_mem
    intro v _
    by_cases zero : v.val = 0
    · simp [row?,root v zero,expectedRow?,zero]
    · cases hit : donor? v.val with
      | none => simp [row?,inactive raw ok v zero hit,expectedRow?,size v,zero,hit]
      | some sk =>
        obtain ⟨s,k⟩ := sk
        obtain ⟨h,seen,cell⟩ := donor raw ok v hit
        simp [row?,cell,expectedRow?,size v,zero,hit,seen]
  · have failed : RingMolecularReport.resolve i ids = none := by
      cases h : RingMolecularReport.resolve i ids with
      | none => rfl
      | some vs =>
        exfalso
        apply good
        rw [← (RingMolecularReport.resolve_iff ..).mp h]
        apply List.all_eq_true.mpr
        intro n hn
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hn
        exact decide_eq_true (size v)
    have none : ids.mapM (expectedRow? i.spatial central) = none := by
      cases out : ids.mapM (expectedRow? i.spatial central) with
      | none => rfl
      | some rows =>
        exfalso
        apply good
        apply List.all_eq_true.mpr
        intro n hn
        obtain ⟨row,_,hit⟩ := RingRetainedReferenceGroup.forInput out hn
        apply decide_eq_true
        by_contra bad
        simp [expectedRow?,bad] at hit
    have accepted := RingSpatialTransport.readmit i
    rw [raw] at accepted
    simp [RingHydrogenReport.fromRaw_closed_eq closed,RingChemicalReport.fromRaw?,accepted,failed,none]

end TetraStereo.Examples.PairedCyclopropylPeripheral
assert_kernel_only TetraStereo.Examples.PairedCyclopropylPeripheral.raw_agreement
