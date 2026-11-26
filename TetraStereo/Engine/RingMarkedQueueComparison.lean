import TetraStereo.Engine.RingMarkedDistanceOrder

/-! A two-queue, row-by-row early-exit comparator for native Rule 6 branches. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedQueueComparison
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingGroupedMark (Reading)
open RingRule5Shape (Valid On)
open RingFullPathTrialReadings (trialKey)
attribute [local instance] lexOrd

/-- A trace of the actual control flow. Only the two current child-bit rows
are compared. Deep children join the end of the waiting queue after a tie.
Each side may independently choose any permitted legal expansion. -/
inductive Runs (left right : Branch → List Branch → List Branch → Prop) :
    List Branch → List Branch → List Branch → List Branch → Ordering → Prop where
  | stop : Runs left right [] [] [] [] .eq
  | left_done {b bs ys sh de} (row : right b sh de) : Runs left right [] [] (b::bs) ys .eq
  | right_done {a as xs sh de} (row : left a sh de) : Runs left right (a::as) xs [] [] .eq
  | rotate_left {a as bs ys out}
      (next : Runs left right (a::as) [] bs ys out) : Runs left right [] (a::as) bs ys out
  | rotate_right {as xs b bs out}
      (next : Runs left right as xs (b::bs) [] out) : Runs left right as xs [] (b::bs) out
  | shallow {a as xs b bs ys sa da sb db}
      (la : left a sa da) (lb : right b sb db)
      (decisive : compare (sa.map Branch.value) (sb.map Branch.value) ≠ .eq) :
      Runs left right (a::as) xs (b::bs) ys (compare (sa.map Branch.value) (sb.map Branch.value))
  | deep {a as xs b bs ys sa da sb db}
      (la : left a sa da) (lb : right b sb db)
      (shallow_tie : compare (sa.map Branch.value) (sb.map Branch.value) = .eq)
      (decisive : compare (da.map Branch.value) (db.map Branch.value) ≠ .eq) :
      Runs left right (a::as) xs (b::bs) ys (compare (da.map Branch.value) (db.map Branch.value))
  | next {a as xs b bs ys sa da sb db out}
      (la : left a sa da) (lb : right b sb db)
      (shallow_tie : compare (sa.map Branch.value) (sb.map Branch.value) = .eq)
      (deep_tie : compare (da.map Branch.value) (db.map Branch.value) = .eq)
      (rest : Runs left right as (xs++da) bs (ys++db) out) :
      Runs left right (a::as) xs (b::bs) ys out

/-- Specification invariant for the residual queues. `queueRows` occurs only
in this proof, never as the comparator's next action. -/
theorem Runs.sound {left right : Branch → List Branch → List Branch → Prop}
    (ls : ∀ b sh de, left b sh de → b.levels = rows sh de)
    (rs : ∀ b sh de, right b sh de → b.levels = rows sh de)
    (lw : ∀ b sh de, left b sh de → sh.length = de.length)
    (rw : ∀ b sh de, right b sh de → sh.length = de.length)
    {as xs bs ys out} (run : Runs left right as xs bs ys out)
    (balance : as.length + xs.length = bs.length + ys.length) :
    compare (queueRows as xs) (queueRows bs ys) = out := by
  induction run with
  | stop => rfl
  | left_done row => simp only [List.length_nil,List.length_cons] at balance; omega
  | right_done row => simp only [List.length_nil,List.length_cons] at balance; omega
  | rotate_left _ ih =>
    rw [queue_rotate]
    apply ih
    simpa only [List.length_nil,Nat.zero_add,Nat.add_zero] using balance
  | rotate_right _ ih =>
    rw [queue_rotate]
    apply ih
    simpa only [List.length_nil,Nat.zero_add,Nat.add_zero] using balance
  | @shallow a as xs b bs ys sa da sb db la lb decisive =>
    rw [queue_pop (ls _ _ _ la),queue_pop (rs _ _ _ lb)]
    simp only [List.cons_append,List.compare_cons_cons]
    cases h : compare (sa.map Branch.value) (sb.map Branch.value) with
    | eq => exact False.elim (decisive h)
    | lt => rfl
    | gt => rfl
  | @deep a as xs b bs ys sa da sb db la lb tie decisive =>
    rw [queue_pop (ls _ _ _ la),queue_pop (rs _ _ _ lb)]
    simp only [List.cons_append,List.compare_cons_cons,tie,Ordering.eq_then]
    cases h : compare (da.map Branch.value) (db.map Branch.value) with
    | eq => exact False.elim (decisive h)
    | lt => rfl
    | gt => rfl
  | @next a as xs b bs ys sa da sb db out la lb sh de rest ih =>
    have equal := congrArg List.length (Std.compare_eq_eq_iff_eq.mp sh)
    simp only [List.length_map] at equal
    have wa := lw _ _ _ la
    have wb := rw _ _ _ lb
    have queued : as.length + (xs++da).length = bs.length + (ys++db).length := by
      simp only [List.length_append,List.length_cons] at balance ⊢
      omega
    rw [queue_pop (ls _ _ _ la),queue_pop (rs _ _ _ lb)]
    simpa only [List.cons_append,List.compare_cons_cons,sh,de,Ordering.eq_then,List.nil_append] using ih queued

/-- Every pair of finite allowed traversals admits an early-exit run, including
full ties and exhaustion of either side. -/
theorem complete {left right : Branch → List Branch → List Branch → Prop}
    {as xs bs ys outA outB} (a : Visits left as xs outA) (b : Visits right bs ys outB) :
    ∃ out, Runs left right as xs bs ys out := by
  induction a generalizing bs ys outB with
  | stop =>
    induction b with
    | stop => exact ⟨.eq,.stop⟩
    | rotate _ ih => obtain ⟨out,h⟩ := ih; exact ⟨out,.rotate_right h⟩
    | pop row _ _ => exact ⟨.eq,.left_done row⟩
  | rotate _ ih => obtain ⟨out,h⟩ := ih b; exact ⟨out,.rotate_left h⟩
  | @pop a as xs sa da tail la next ih =>
    induction b with
    | stop => exact ⟨.eq,.right_done la⟩
    | rotate _ ihr => obtain ⟨out,h⟩ := ihr; exact ⟨out,.rotate_right h⟩
    | @pop b bs ys sb db tailB lb nextB _ =>
      by_cases sh : compare (sa.map Branch.value) (sb.map Branch.value) = .eq
      · by_cases de : compare (da.map Branch.value) (db.map Branch.value) = .eq
        · obtain ⟨out,h⟩ := ih nextB
          exact ⟨out,.next la lb sh de h⟩
        · exact ⟨_,.deep la lb sh de⟩
      · exact ⟨_,.shallow la lb sh⟩

/-- The root's own bit is inspected once, before either queue is expanded. -/
inductive RootRuns (left right : Branch → List Branch → List Branch → Prop)
    (a b : Branch) : Ordering → Prop where
  | head (decisive : compare a.value b.value ≠ .eq) : RootRuns left right a b (compare a.value b.value)
  | tail {out} (tie : compare a.value b.value = .eq)
      (run : Runs left right [a] [] [b] [] out) : RootRuns left right a b out

theorem RootRuns.sound {left right : Branch → List Branch → List Branch → Prop}
    (ls : ∀ b sh de, left b sh de → b.levels = rows sh de)
    (rs : ∀ b sh de, right b sh de → b.levels = rows sh de)
    (lw : ∀ b sh de, left b sh de → sh.length = de.length)
    (rw : ∀ b sh de, right b sh de → sh.length = de.length)
    {a b out} (run : RootRuns left right a b out) : compare a.word b.word = out := by
  rw [queue_start,queue_start]
  simp only [List.compare_cons_cons,List.compare_nil_nil]
  cases run with
  | head decisive =>
    cases h : compare a.value b.value with
    | eq => exact False.elim (decisive h)
    | lt => rfl
    | gt => rfl
  | tail tie next => simpa only [tie,Ordering.eq_then] using next.sound ls rs lw rw rfl

theorem root_complete {left right : Branch → List Branch → List Branch → Prop}
    {a b outA outB} (wa : Visits left [a] [] outA) (wb : Visits right [b] [] outB) :
    ∃ out, RootRuns left right a b out := by
  by_cases tie : compare a.value b.value = .eq
  · obtain ⟨out,h⟩ := complete wa wb
    exact ⟨out,.tail tie h⟩
  · exact ⟨_,.head tie⟩

/-- An expansion witnesses both native molecular child populations and the two
independent legal marked sorts. No comparison result is among its fields. -/
structure NativeRow (i : Input) (r : Reader i) (atom : Nat)
    (parent : Branch) (sh de : List Branch) where
  cursor : Arm i
  valid : Valid cursor
  reading : Reading i r atom cursor parent
  native : List Branch
  lookup : Arm i → Option Branch
  complete : (RingRule5Shape.kids i cursor).mapM lookup = some native
  below : ∀ c ∈ RingRule5Shape.kids i cursor, ∀ {b}, lookup c = some b → Reading i r atom c b
  shallow : Legal Branch.shallow native sh
  deep : Legal Branch.deep native de
  layout : parent.levels = rows sh de

abbrev NativeExpansion (i : Input) (r : Reader i) (atom : Nat)
    (parent : Branch) (sh de : List Branch) : Prop := Nonempty (NativeRow i r atom parent sh de)

/-- Every actual finite valid arm supplies the native queue interface. The
strict cursor budget proves termination independently of comparison outcomes. -/
theorem native_walk {i : Input} {r : Reader i} {atom : Nat} {q : Arm i} {b : Branch}
    (valid : Valid q) (read : Reading i r atom q b) :
    ∃ out, Visits (NativeExpansion i r atom) [b] [] out := by
  let good (n : Nat) (b : Branch) := ∃ q : Arm i, Valid q ∧
    i.certified.localizedRerootCursorBudget q < n ∧ Reading i r atom q b
  apply visits_exist good (fun b h => by obtain ⟨q,v,h,_⟩ := h; omega) ?_
    (i.certified.localizedRerootCursorBudget q+1) [b]
    (fun c hc => by obtain rfl := List.mem_singleton.mp hc; exact ⟨q,valid,Nat.lt_succ_self _,read⟩)
  intro n b h
  obtain ⟨q,vq,budget,src⟩ := h
  have original := src
  cases src with
  | @node q prior cs sh de before look all sub first second =>
    refine ⟨sh,de,⟨⟨q,vq,original,cs,look,all,sub,first,second,rfl⟩⟩,?_⟩
    intro c hc
    obtain ⟨t,ht,hit⟩ := RingRetainedUnitPass.forOutput all (second.perm.mem_iff.mp hc)
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    have smaller := i.certified.localizedRerootChild_budget_lt _ _ _ vq frame ht
    exact ⟨t,i.certified.localizedRerootChild_valid _ _ _ frame ht,by omega,sub t ht hit⟩

/-- Native source readings admit a complete operational run; every allowed
choice of sorts computes exactly the complete marked-word comparison. -/
theorem native_complete {i : Input} {r : Reader i} {atom other : Nat} {a b : Arm i} {x y : Branch}
    (va : Valid a) (vb : Valid b) (ma : Reading i r atom a x) (mb : Reading i r other b y) :
    ∃ out, RootRuns (NativeExpansion i r atom) (NativeExpansion i r other) x y out ∧
      compare x.word y.word = out := by
  obtain ⟨wa,ha⟩ := native_walk va ma
  obtain ⟨wb,hb⟩ := native_walk vb mb
  obtain ⟨out,h⟩ := root_complete ha hb
  exact ⟨out,h,h.sound (fun _ _ _ h => h.elim fun row => row.layout) (fun _ _ _ h => h.elim fun row => row.layout)
    (fun _ _ _ h => h.elim fun row => row.shallow.perm.length_eq.trans row.deep.perm.length_eq.symm)
    (fun _ _ _ h => h.elim fun row => row.shallow.perm.length_eq.trans row.deep.perm.length_eq.symm)⟩

/-- At an ordinary native tie, the same queue run is the entire public trial
comparison. Equal radii and repeated duplicate occurrences require no exception. -/
theorem trial_sound {i f r rev a b atom other x y k out}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r other b y)
    (run : RootRuns (NativeExpansion i r atom) (NativeExpansion i r other) x y out) :
    compare (trialKey k x.word) (trialKey k y.word) = out := by
  have same := run.sound (fun _ _ _ h => h.elim fun row => row.layout) (fun _ _ _ h => h.elim fun row => row.layout)
    (fun _ _ _ h => h.elim fun row => row.shallow.perm.length_eq.trans row.deep.perm.length_eq.symm)
    (fun _ _ _ h => h.elim fun row => row.shallow.perm.length_eq.trans row.deep.perm.length_eq.symm)
  have flattened := RingMarkedDistanceOrder.flatten_compare x.word y.word
    (RingMarkedDistanceOrder.widths ready va vb oa ob ka kb ma mb)
  rw [RingMarkedDistanceOrder.trial_compare ready va vb oa ob ka kb ma mb,flattened,same]
end TetraStereo.Engine.RingMarkedQueueComparison
assert_kernel_only TetraStereo.Engine.RingMarkedQueueComparison.Runs.sound
assert_kernel_only TetraStereo.Engine.RingMarkedQueueComparison.complete
assert_kernel_only TetraStereo.Engine.RingMarkedQueueComparison.RootRuns.sound
assert_kernel_only TetraStereo.Engine.RingMarkedQueueComparison.native_walk
assert_kernel_only TetraStereo.Engine.RingMarkedQueueComparison.native_complete
assert_kernel_only TetraStereo.Engine.RingMarkedQueueComparison.trial_sound
