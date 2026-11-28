import TetraStereo.Examples.CrossParentPublicReport
import TetraStereo.Examples.CrossParentClasses

/-! All 256 donor configurations of the cross-parent scaffold at its original
root orientation. Only the two terminal halogen positions at a donor can move. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
namespace TetraStereo.Examples.CrossParentFaces
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open CrossParentDonorStore (molecule original ligandRow)
open CrossParentPublicRanking (rootFrame)
open CrossParentPublicReport (outcome)
open RingWrittenPHReadings (geometry)
open private physicalNeighbors rawBond cert from TetraStereo.Examples.CrossParentDonorStore
open private coordinates_of_neighbor_volumes neighbors directVolume from TetraStereo.Examples.MixedHalogenSpiro

private def pair (n : Nat) : Option (Fin 8) :=
  if h : 15 ≤ n ∧ n < 39 ∧ (n-15)%3 < 2 then some ⟨(n-15)/3,by omega⟩ else none

private def index (hands : Fin 8 → RS) (n : Nat) :=
  match pair n with
  | none => n
  | some j =>
    if hands j = CrossParentDonorStore.hand 0 j then n
    else if (n-15)%3 = 0 then n+1 else n-1

private def point (hands : Fin 8 → RS) (n : Nat) :=
  original.positions.getD (index hands n) ⟨0,0,0⟩

def spatial (hands : Fin 8 → RS) : SpatialConfiguration :=
  ⟨List.ofFn (fun a : Fin 41 => point hands a.val)⟩

def input (hands : Fin 8 → RS) : Input := RingSpatialTransport.atGeometry (CrossParentDonorStore.input 0)
  (spatial hands) (by change (List.ofFn _).length = 41; simp)

private theorem lookup (h : Fin 8 → RS) {n : Nat} (hn : n < 41) :
    (spatial h).positions[n]? = some (point h n) := by
  change (List.ofFn (fun a : Fin 41 => point h a.val))[n]? = _
  rw [List.getElem?_ofFn,dif_pos hn]

private theorem local_point (h : Fin 8 → RS) (j : Fin 8) {n : Nat}
    (hit : (pair n).all (· == j) = true) : point h n = point (fun _ => h j) n := by
  unfold point index
  cases eq : pair n with
  | none => rfl
  | some k =>
    have same : k = j := by simpa [eq] using hit
    subst k
    rfl

private theorem donor_local : ∀ j : Fin 8, ∀ n ∈ ligandRow j,
    n < 41 ∧ (pair n).all (· == j) = true := by decide +kernel

private theorem constant_donor (b : RS) (j : Fin 8) :
    readback? (geometry (spatial (fun _ => b))) (ligandRow j) = some b := by
  cases b <;> fin_cases j <;> decide +kernel

theorem donor_hand (h : Fin 8 → RS) (j : Fin 8) :
    readback? (geometry (spatial h)) (ligandRow j) = some (h j) := by
  rw [← constant_donor (h j) j]
  have rows := RingFrameTransport.mapM_congr_mem (geometry (spatial h))
    (geometry (spatial (fun _ => h j))) (ligandRow j) (by
      intro n mem
      obtain ⟨small,localEq⟩ := donor_local j n mem
      exact (lookup _ small).trans ((congrArg some (local_point h j localEq)).trans (lookup _ small).symm))
  unfold readback?
  rw [rows]

theorem root_hand (h : Fin 8 → RS) : readback? (geometry (spatial h)) rootFrame = some .R := by
  have same : (rootFrame.mapM (geometry (spatial h))) = rootFrame.mapM (geometry original) := by
    apply RingFrameTransport.mapM_congr_mem
    intro n mem
    simp only [rootFrame,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl <;> rw [show ∀ m, geometry (spatial h) m = (spatial h).positions[m]? from fun _ => rfl]
    all_goals rw [lookup _ (by decide)]; rfl
  unfold readback?
  rw [same]
  decide +kernel

private def vol (h : Fin 8 → RS) (xs : List (Fin 41)) : Option ℚ := do
  let a ← xs[0]?
  let b ← xs[1]?
  let c ← xs[2]?
  let d ← xs[3]?
  return CartesianPoint3.orientedVolume (point h a.val) (point h b.val) (point h c.val) (point h d.val)

private def owner (a : Fin 41) : Fin 8 := ⟨(a.val-7)%8,Nat.mod_lt _ (by decide)⟩

private theorem local_neighbors : ∀ a : Fin 41, (physicalNeighbors a).length = 4 →
    ∀ b ∈ physicalNeighbors a, (pair b.val).all (· == owner a) = true := by decide +kernel

private theorem vol_local (h : Fin 8 → RS) (a : Fin 41) (four : (physicalNeighbors a).length = 4) :
    vol h (physicalNeighbors a) = vol (fun _ => h (owner a)) (physicalNeighbors a) := by
  obtain ⟨u,v,w,t,row⟩ := List.length_eq_four.mp four
  have loc (b : Fin 41) (hb : b ∈ [u,v,w,t]) :=
    local_point h (owner a) (local_neighbors a four b (row ▸ hb))
  rw [row]
  change some (CartesianPoint3.orientedVolume _ _ _ _) = some (CartesianPoint3.orientedVolume _ _ _ _)
  rw [loc u (by simp),loc v (by simp),loc w (by simp),loc t (by simp)]

private theorem nonzero (s : RS) : ∀ a : Fin 41, (physicalNeighbors a).length = 4 →
    (vol (fun _ => s) (physicalNeighbors a)).any (· != 0) = true := by cases s <;> decide +kernel

theorem admitted (h : Fin 8 → RS) : LocalizedChemicalRing.coordinatesAdmitted (input h) = true := by
  apply coordinates_of_neighbor_volumes
  intro a four
  have ns : neighbors (input h).certified a = physicalNeighbors a := by
    apply List.filter_congr
    intro b _
    change decide (0 < (cert 0).moleculeGraph.bond a b) = _
    rw [rawBond]
  rw [ns] at four ⊢
  have read (b : Fin 41) : (input h).certified.spatialPointAt? b = some (point h b.val) := by
    change (spatial h).positions[b.val]? = _
    exact lookup _ b.isLt
  have dv : directVolume (input h).certified (physicalNeighbors a) = vol h (physicalNeighbors a) := by
    obtain ⟨u,v,w,t,row⟩ := List.length_eq_four.mp four
    rw [row]
    change (do
      let p ← (input h).certified.spatialPointAt? u
      let q ← (input h).certified.spatialPointAt? v
      let r ← (input h).certified.spatialPointAt? w
      let s ← (input h).certified.spatialPointAt? t
      pure (CartesianPoint3.orientedVolume p q r s)) = _
    rw [read,read,read,read]
    rfl
  rw [dv,vol_local h a four]
  exact nonzero _ a four

def maskHand (m : Fin 256) (j : Fin 8) : RS := if m.val.testBit j.val then .R else .S

def maskOutcome (m : Fin 256) := outcome (CrossParentRootOrder.rCount (maskHand m) true false)
  (CrossParentRootOrder.rCount (maskHand m) false false) .R

/-- Refusals, uppercase R/S, then lowercase r/s, over the 256 labeled donor configurations. -/
theorem distribution :
    let results := (List.finRange 256).map maskOutcome
    [results.count none,results.count (some (.chiral .R,.chiral .S)),
      results.count (some (.chiral .S,.chiral .R)),results.count (some (.pseudoasymmetric .r,.pseudoasymmetric .r)),
      results.count (some (.pseudoasymmetric .s,.pseudoasymmetric .s))] = [70,76,76,17,17] := by decide +kernel

/-- Bit one denotes R. The original validation drawing and its two F/Cl
swaps are exactly the 83, 87, and 71 coordinate tables in this family. -/
def controlMask (v : Fin 3) : Fin 256 := if v.val = 0 then 83 else if v.val = 1 then 87 else 71

theorem control_geometry (v : Fin 3) :
    spatial (maskHand (controlMask v)) = CrossParentDonorStore.geometry v := by
  fin_cases v <;> decide +kernel

theorem expected_mask (m : Fin 256) :
    CrossParentPublicReport.expected? (spatial (maskHand m)) = some [(0,maskOutcome m)] := by
  have seen := donor_hand (maskHand m)
  have present : ∀ j : Fin 8, (readback? (geometry (spatial (maskHand m))) (ligandRow j)).isSome = true :=
    fun j => by rw [seen j]; rfl
  simp only [CrossParentPublicReport.expected?,root_hand,dif_pos present]
  have hs : (fun j => (readback? (geometry (spatial (maskHand m))) (ligandRow j)).get (present j)) = maskHand m := by
    funext j
    simp [seen j]
  rw [hs]
  rfl

/-- The public raw root report on each of the 256 admitted coordinate tables. -/
theorem raw_mask (m : Fin 256) :
    RingHydrogenReport.fromRaw? molecule (spatial (maskHand m)) [0] = some [(0,maskOutcome m)] :=
  (CrossParentPublicReport.raw_root (input (maskHand m)) rfl (admitted _)).trans (expected_mask m)

theorem raw_distribution :
    let reports := (List.finRange 256).map fun m => RingHydrogenReport.fromRaw? molecule (spatial (maskHand m)) [0]
    [reports.count (some [(0,none)]),reports.count (some [(0,some (.chiral .R,.chiral .S))]),
      reports.count (some [(0,some (.chiral .S,.chiral .R))]),
      reports.count (some [(0,some (.pseudoasymmetric .r,.pseudoasymmetric .r))]),
      reports.count (some [(0,some (.pseudoasymmetric .s,.pseudoasymmetric .s))])] = [70,76,76,17,17] := by
  simp only [raw_mask]
  decide +kernel

end TetraStereo.Examples.CrossParentFaces
assert_kernel_only TetraStereo.Examples.CrossParentFaces.donor_hand
assert_kernel_only TetraStereo.Examples.CrossParentFaces.admitted
assert_kernel_only TetraStereo.Examples.CrossParentFaces.distribution
assert_kernel_only TetraStereo.Examples.CrossParentFaces.expected_mask
assert_kernel_only TetraStereo.Examples.CrossParentFaces.raw_distribution
