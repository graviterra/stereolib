import TetraStereo.Engine.RingMarkedDistanceOrder
import TetraStereo.Engine.RingMarkedOccurrenceRows

/-! Trace the first deciding atom pair of a marked comparison through the
actual rerooted arms, including duplicate occurrences. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingMarkedDecisionWitness
open OneCenter RingMarkedDistanceOrder
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingGroupedMark (bit)
open RingRule5Shape (Valid On)
open RingRetainedChemicalTrace (Reaches)
open RingFullPathTrialReadings (trialKey)
open RingMarkedOccurrenceRows (rows? rows_exact rows_reachable)
attribute [local instance] lexOrd

/-- Scan aligned sites in reading order. The index counts entries from zero. -/
def first {α : Type} (value : α → Nat) : List α → List α → Option (Nat × α × α)
  | a::as,b::bs =>
    if value a = value b then (first value as bs).map (fun (n,x,y) => (n+1,x,y))
    else some (0,a,b)
  | _,_ => none

private theorem order_exact {α : Type} (v : α → Nat) (xs ys : List α)
    (len : xs.length = ys.length) :
    ((first v xs ys).map fun (_,x,y) => compare (v x) (v y)).getD .eq =
      compare (xs.map v) (ys.map v) := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | rfl | contradiction
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys =>
      have tail := ih ys (Nat.succ.inj len)
      by_cases same : v x = v y
      · simpa [first,same,List.compare_cons_cons,Option.map_map,Function.comp_def] using tail
      · have strict : compare (v x) (v y) ≠ .eq := fun h => same (Nat.compare_eq_eq.mp h)
        simp only [first,if_neg same,Option.map_some,Option.getD_some,List.map_cons,List.compare_cons_cons]
        cases cmp : compare (v x) (v y) <;> simp_all

/-- A returned index names the two sites at that slot. Every earlier slot
carries the same mark bit on both sides. -/
theorem first_spec {α : Type} (v : α → Nat) {xs ys : List α} {i x y}
    (hit : first v xs ys = some (i,x,y)) :
    xs[i]? = some x ∧ ys[i]? = some y ∧ v x ≠ v y ∧
      ∀ j < i, xs[j]?.map v = ys[j]?.map v := by
  induction xs generalizing ys i x y with
  | nil => contradiction
  | cons a as ih =>
    cases ys with
    | nil => contradiction
    | cons b bs =>
      by_cases same : v a = v b
      · simp only [first,if_pos same,Option.map_eq_some_iff] at hit
        obtain ⟨⟨j,c,d⟩,found,out⟩ := hit
        cases out
        obtain ⟨cx,dy,ne,before⟩ := ih found
        refine ⟨cx,dy,ne,?_⟩
        intro k lt
        cases k with
        | zero => simpa using same
        | succ k => exact before k (by omega)
      · simp only [first,if_neg same,Option.some.injEq] at hit
        cases hit
        exact ⟨rfl,rfl,same,by intro j lt; omega⟩

def witness? {i : Input} (r : RingNestedActivePair.Reader i) (atom : Nat) (a b : Arm i) := do
  let xs ← rows? i r atom a
  let ys ← rows? i r atom b
  return first (bit atom) xs.flatten ys.flatten

/-- Locate the deciding atom pair for an actually evaluated marked trial with
equal ordinary priority. The outer option records trace availability, the
inner option records whether a distinguishing pair exists. -/
theorem witness_order {i f r rev a b atom x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : RingGroupedMark.Reading i r atom a x) (mb : RingGroupedMark.Reading i r atom b y) :
    (witness? r atom a b).map (fun h => (h.map (fun (_,c,d) => compare (bit atom c) (bit atom d))).getD .eq) =
      some (compare (trialKey k x.word) (trialKey k y.word)) := by
  obtain ⟨as,ha⟩ := RingMarkedOccurrenceRows.rows_ready ready atom a va oa
  obtain ⟨bs,hb⟩ := RingMarkedOccurrenceRows.rows_ready ready atom b vb ob
  have paint {q z rs} (vq : Valid q) (oq : On f q) (read : RingGroupedMark.Reading i r atom q z)
      (h : rows? i r atom q = some rs) : rs.map (List.map (bit atom)) = z.word := by
    obtain ⟨e,he⟩ := RingGroupedMark.arm_ready ready atom q vq oq
    have eqn := (RingGroupedMark.arm_source he).2.unique read
    simpa [h,he,eqn] using rows_exact ready atom q vq oq
  have pa := paint va oa ma ha
  have pb := paint vb ob mb hb
  have len := widths ready va vb oa ob ka kb ma mb
  rw [← pa,← pb] at len
  have sizes : as.flatten.length = bs.flatten.length := by
    simpa [List.length_flatten,List.map_map,Function.comp_def] using congrArg List.sum len
  rw [trial_compare ready va vb oa ob ka kb ma mb,← pa,← pb]
  simpa only [witness?,ha,hb,bind,pure,Option.bind_some,Option.map_some,List.map_flatten] using
    congrArg some (order_exact (bit atom) as.flatten bs.flatten sizes)

theorem witness_reachable {i r atom a b n c d} (h : @witness? i r atom a b = some (some (n,c,d))) :
    Reaches i a c ∧ Reaches i b d ∧ bit atom c ≠ bit atom d := by
  obtain ⟨xs,hx,more⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys,hy,out⟩ := Option.bind_eq_some_iff.mp more
  have hit := Option.some.inj out
  obtain ⟨left,right,ne,_⟩ := first_spec _ hit
  have reached {q rs c} (got : rows? i r atom q = some rs) (mem : c ∈ rs.flatten) : Reaches i q c := by
    obtain ⟨row,hr,hc⟩ := List.mem_flatten.mp mem
    exact rows_reachable got row hr c hc
  exact ⟨reached hx (List.mem_of_getElem? left),reached hy (List.mem_of_getElem? right),ne⟩

end TetraStereo.Engine.RingMarkedDecisionWitness
assert_kernel_only TetraStereo.Engine.RingMarkedDecisionWitness.witness_order
assert_kernel_only TetraStereo.Engine.RingMarkedDecisionWitness.witness_reachable
