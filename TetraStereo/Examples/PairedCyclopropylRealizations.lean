import TetraStereo.Examples.PairedCyclopropylRoot
import TetraStereo.Examples.Dimethyldiaziridine

/-! Independent control of all seven physical frames by private hydrogen positions. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylRealizations
open Engine OneCenter LocalizedGenericMarkedRecalculation
open PairedCyclopropylPaths (molecule order)
open PairedCyclopropylComparison (Hands fromGeometry?)
open PairedCyclopropylRoot (rootFrame)
open RingWrittenPHReadings (geometry)
open private gate_of_written writtenVolume writtenNeighbors Nonflat from TetraStereo.Examples.Dimethyldiaziridine
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def point (t : ℚ) : CartesianPoint3 := ⟨t,t*t,t*t*t⟩

private def hydrogen (n : Nat) (wanted high : RS) :=
  point (if wanted = high then 26 + (n : ℚ) else -1 - (n : ℚ))

private def owner : Nat → Option (Fin 7 × RS)
  | 2 => some (0,.R) | 6 => some (1,.R) | 7 => some (2,.R) | 11 => some (3,.S)
  | 17 => some (4,.R) | 18 => some (5,.R) | 22 => some (6,.S) | _ => none

private def atomPoint (f : Fin 7 → RS) (n : Nat) := match owner n with
  | some (j,high) => hydrogen n (f j) high
  | none => point n

/-- On the rational moment curve each of the seven private hydrogens can
independently precede or follow the three fixed carriers of its center. -/
def placement (f : Fin 7 → RS) : SpatialConfiguration :=
  ⟨(List.range 25).map (atomPoint f)⟩

private def frame (j : Fin 7) := ![rootFrame,order false 0,order false 1,order false 2,
  order true 0,order true 1,order true 2] j

private theorem reading (f : Fin 7 → RS) (j : Fin 7) :
    readback? (geometry (placement f)) (frame j) = some (f j) := by
  trans readback? (geometry (placement (fun _ => f j))) (frame j)
  · fin_cases j <;> rfl
  · generalize f j = h
    fin_cases j <;> cases h <;> decide +kernel

private theorem admitted (f : Fin 7 → RS) :
    (LocalizedChemicalRing.admitRawSpatial? molecule (placement f)).isSome = true := by
  rfl

/-- The written neighbor lists in atom-index order. Checking this table once
keeps bond lookup out of the subsequent determinant calculations. -/
private def carriers : Fin 25 → List (Fin 25) :=
  ![[1,2,3,14],[0],[0],[0,4,5,6],[3,5,7,10],[3,4,8,9],[3],[4],[5],[5],
    [4,11,12,13],[10],[10],[10],[0,15,16,17],[14,16,18,21],[14,15,19,20],
    [14],[15],[16],[16],[15,22,23,24],[21],[21],[21]]

private theorem carriers_eq (a : Fin 25) : writtenNeighbors molecule a = carriers a := by
  fin_cases a <;> rfl

private theorem uniform (h : RS) : ∀ a : Fin 25, (carriers a).length = 4 →
    ((writtenVolume (placement (fun _ => h)) (carriers a)).any (· != 0)) = true := by
  cases h <;> decide +kernel

private def localHand (n : Fin 25) : Fin 7 := match n.val with
  | 3 => 1 | 4 => 2 | 10 => 3 | 14 => 4 | 15 => 5 | 21 => 6 | _ => 0

private def carrierPoint (g : SpatialConfiguration) (a : Fin 25) (j : Fin 4) :=
  (carriers a)[j.val]?.bind fun n => g.positions[n.val]?

private theorem volume_points (g : SpatialConfiguration) (a : Fin 25) :
    writtenVolume g (carriers a) = (do
      let p ← carrierPoint g a 0
      let q ← carrierPoint g a 1
      let r ← carrierPoint g a 2
      let s ← carrierPoint g a 3
      pure (CartesianPoint3.orientedVolume p q r s)) := by
  simp only [writtenVolume,carrierPoint,Option.bind_eq_bind,Option.bind_assoc]
  rfl

private theorem ownership : ∀ (a n : Fin 25), n ∈ carriers a →
    (owner n.val).all (fun p => p.1 == localHand a) = true := by decide +kernel

private theorem point_lookup (f : Fin 7 → RS) (n : Fin 25) :
    (placement f).positions[n.val]? = some (atomPoint f n.val) := by
  simp [placement,n.isLt]

private theorem locality (f : Fin 7 → RS) (a : Fin 25) (j : Fin 4) :
    carrierPoint (placement f) a j =
    carrierPoint (placement (fun _ => f (localHand a))) a j := by
  unfold carrierPoint
  cases e : (carriers a)[j.val]? with
  | none => rfl
  | some n =>
    simp only [Option.bind_some,point_lookup]
    have own := ownership a n (List.mem_of_getElem? e)
    unfold atomPoint
    cases ho : owner n.val with
    | none => rfl
    | some p =>
      have eq : p.1 = localHand a := by simpa only [ho,Option.all_some,beq_iff_eq] using own
      simp [eq]

private theorem nonflat (f : Fin 7 → RS) : Nonflat 25 molecule (placement f) := by
  intro a four
  rw [carriers_eq] at four ⊢
  have cert := uniform (f (localHand a)) a four
  rw [volume_points] at cert ⊢
  simp only [locality f a]
  exact cert

/-- Every pair of physical donor triples and either central reference hand
occurs on a structurally and spatially admitted raw input. -/
theorem realize (l r : Hands) (c : RS) :
    ∃ (g : SpatialConfiguration) (i : LocalizedChemicalRing.Input),
      LocalizedChemicalRing.admitRawSpatial? molecule g = some i ∧
      LocalizedChemicalRing.coordinatesAdmitted i = true ∧
      fromGeometry? (geometry g) false = some l ∧
      fromGeometry? (geometry g) true = some r ∧ readback? (geometry g) rootFrame = some c := by
  let f : Fin 7 → RS := ![c,l.entry,l.exitHand,l.distal,r.entry,r.exitHand,r.distal]
  let i := (LocalizedChemicalRing.admitRawSpatial? molecule (placement f)).get (admitted f)
  have source : LocalizedChemicalRing.admitRawSpatial? molecule (placement f) = some i :=
    (Option.some_get _).symm
  obtain ⟨graph,space⟩ := RingChemicalReport.admission_fields source
  refine ⟨placement f,i,source,gate_of_written i ?_,?_,?_,reading f 0⟩
  · rw [graph,space]
    exact nonflat f
  · unfold fromGeometry?
    rw [show readback? _ (order false 0) = some l.entry from reading f 1,
      show readback? _ (order false 1) = some l.exitHand from reading f 2,
      show readback? _ (order false 2) = some l.distal from reading f 3]
    rfl
  · unfold fromGeometry?
    rw [show readback? _ (order true 0) = some r.entry from reading f 4,
      show readback? _ (order true 1) = some r.exitHand from reading f 5,
      show readback? _ (order true 2) = some r.distal from reading f 6]
    rfl

end TetraStereo.Examples.PairedCyclopropylRealizations
assert_kernel_only TetraStereo.Examples.PairedCyclopropylRealizations.realize
