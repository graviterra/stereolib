import TetraStereo.Engine.RingHistoryReport
import TetraStereo.Engine.RingGlobalComparison

/-! Exact comparison of any local publication rule with the public ring evaluator.
The metric and history readings of ring-duplicate distance are one application. Only the public rule supplies previous sphere rows
to the diagnostic. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStoreDecision
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (height)
open RingPyramidalPublication (eligible publish)

open RingGlobalComparison (prior queue)
open RingActiveDistanceSchedule (Rule)

variable {i : Input} (source : Rule i) (r : i.certified.Atom)

/-- The candidate computes a separate store, reading its own earlier cells. -/
abbrev candidateRows (k : Nat) :=
  RingSphereQueue.stored source r (queue i r) (height i) k

/-- First differing occurrence in one batch, in queue order. -/
def batchDifference? (n : Nat) : Option (Site i) :=
  (queue i r (height i - n)).find? fun q =>
    decide (source q (prior i r n) ≠ publish i q (prior i r n))

/-- First differing batch and address among the first `k` batches. -/
def firstDifference? : Nat → Option (Nat × Site i)
  | 0 => none
  | n+1 => (firstDifference? n).orElse fun _ => (batchDifference? source r n).map (n, ·)

private theorem batch_none (n : Nat) : batchDifference? source r n = none ↔
    ∀ q ∈ queue i r (height i - n),
      source q (prior i r n) = publish i q (prior i r n) := by
  simp [batchDifference?]

private theorem rows_step (n : Nat) :
    candidateRows source r (n+1) = RingSphereStore.rows i r (n+1) ↔
      candidateRows source r n = RingSphereStore.rows i r n ∧
      batchDifference? source r n = none := by
  rw [batch_none]
  constructor
  · intro h
    change _ ++ candidateRows source r n = _ ++ RingSphereStore.rows i r n at h
    obtain ⟨news,old⟩ := List.append_inj h (by simp)
    refine ⟨old, ?_⟩
    change List.map _ _ = List.map _ _ at news
    rw [List.map_inj_left] at news
    intro q mem
    have cell := congrArg Prod.snd (news q mem)
    change source q
      (RingSphereQueue.reader r (RingSphereQueue.viewOf (candidateRows source r n))) = _ at cell
    rwa [old] at cell
  · rintro ⟨old,on⟩
    change _ ++ candidateRows source r n = _ ++ RingSphereStore.rows i r n
    simp only [candidateRows, RingSphereStore.rows] at old
    simp only [candidateRows, RingSphereStore.rows,old]
    apply congrArg (· ++ _)
    apply List.map_congr_left
    intro q mem
    exact congrArg (q, ·) (on q mem)

/-- Equality of the final addressed list in the prefix is equivalent to passing
every local check. Old rows are retained, so a later batch cannot mask a difference. -/
theorem firstDifference_none_iff (k : Nat) : firstDifference? source r k = none ↔
    candidateRows source r k = RingSphereStore.rows i r k := by
  induction k with
  | zero => exact iff_of_true rfl rfl
  | succ n ih =>
    rw [rows_step, ← ih]
    cases prev : firstDifference? source r n <;> cases nextBatch : batchDifference? source r n <;>
      simp_all [firstDifference?]

/-- A single decision covers all prefixes of the requested trajectory. -/
theorem trajectory_iff (k : Nat) : firstDifference? source r k = none ↔
    ∀ n ≤ k, candidateRows source r n = RingSphereStore.rows i r n := by
  rw [firstDifference_none_iff]
  constructor
  · intro full n le
    induction le with
    | refl => exact full
    | step _ ih => exact ih ((rows_step source r _).mp full).1
  · intro all
    exact all k le_rfl

/-- A returned address differs on an equal prior, including outer failures
and completed refusals. The batch index starts at zero, outside in. -/
theorem firstDifference_some {k n : Nat} {q : Site i}
    (found : firstDifference? source r k = some (n,q)) :
    n < k ∧ q ∈ queue i r (height i - n) ∧
    candidateRows source r n = RingSphereStore.rows i r n ∧
    source q (prior i r n) ≠ publish i q (prior i r n) := by
  induction k with
  | zero => contradiction
  | succ k ih =>
    cases old : firstDifference? source r k with
    | some hit =>
      have same : hit = (n,q) := Option.some.inj (by simpa [firstDifference?,old] using found)
      obtain ⟨lt,rest⟩ := ih (old.trans (congrArg some same))
      exact ⟨Nat.lt_succ_of_lt lt,rest⟩
    | none =>
      cases batch : batchDifference? source r k with
      | none => simp [firstDifference?,old,batch] at found
      | some a =>
        obtain ⟨rfl,rfl⟩ : k = n ∧ a = q := by simpa [firstDifference?,old,batch] using found
        exact ⟨Nat.lt_succ_self _, List.mem_of_find?_eq_some batch,
          (firstDifference_none_iff source r k).mp old, of_decide_eq_true (List.find?_some
            (p := fun t => decide (source t (prior i r k) ≠ publish i t (prior i r k))) batch)⟩

/-- The executable scan retains one public store. A successful batch commits its
computed public cells once. A discrepancy returns its address immediately. -/
def scan : Nat → Except (Nat × Site i) (List (Site i × RingActiveDistanceSchedule.Cell))
  | 0 => .ok []
  | n+1 => do
    let before ← scan n
    let read := RingSphereQueue.reader r (RingSphereQueue.viewOf before)
    let batch := (queue i r (height i - n)).map fun q => (q, publish i q read)
    match batch.find? (fun row => decide (source row.1 read ≠ row.2)) with
    | some row => throw (n, row.1)
    | none => return batch ++ before

private theorem scan_exact (k : Nat) : scan source r k =
    match firstDifference? source r k with
    | some hit => .error hit
    | none => .ok (RingSphereStore.rows i r k) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp only [scan, ih, firstDifference?]
    cases h : firstDifference? source r n with
    | some hit => rfl
    | none =>
      let read := prior i r n
      let row := fun q : Site i => (q,publish i q read)
      let sites := queue i r (height i - n)
      change (match (sites.map row).find? (fun x => decide (source x.1 read ≠ x.2)) with
        | some x => Except.error (n,x.1)
        | none => Except.ok (sites.map row ++ RingSphereStore.rows i r n)) = _
      rw [List.find?_map]
      change (match (batchDifference? source r n).map row with
        | some x => Except.error (n,x.1)
        | none => Except.ok (sites.map row ++ RingSphereStore.rows i r n)) = _
      cases batchDifference? source r n <;> rfl

private def scanResult (k : Nat) : Option (Nat × Site i) :=
  match scan source r k with
  | .error hit => some hit
  | .ok _ => none

@[csimp] theorem firstDifference_compiled : @firstDifference? = @scanResult := by
  funext i source r k
  rw [scanResult, scan_exact]
  cases firstDifference? source r k <;> rfl

/-- The same exact decision compares the two executable origin readings on
admitted coordinates. The history interpreter independently reconstructs the public rows. -/
theorem history_comparison (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (k : Nat) :
    firstDifference? (RingOriginMetricReport.publish i) r k = none ↔
      RingOriginMetricReport.rows i r k = RingHistoryReport.rows i r k := by
  rw [RingHistoryReport.rows_exact geom]
  exact firstDifference_none_iff _ r k

end TetraStereo.Engine.RingStoreDecision

assert_kernel_only TetraStereo.Engine.RingStoreDecision.firstDifference_none_iff
assert_kernel_only TetraStereo.Engine.RingStoreDecision.firstDifference_some
assert_kernel_only TetraStereo.Engine.RingStoreDecision.trajectory_iff
assert_kernel_only TetraStereo.Engine.RingStoreDecision.firstDifference_compiled
assert_kernel_only TetraStereo.Engine.RingStoreDecision.history_comparison
