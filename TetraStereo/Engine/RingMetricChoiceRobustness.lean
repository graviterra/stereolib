import TetraStereo.Engine.RingOriginIndexedKeys
import TetraStereo.Engine.RingOriginCausal
import TetraStereo.Engine.RingStoreDecision
import TetraStereo.Engine.RingRootLayerStore

/-! Exact robustness of each requested root under independent choices of
the duplicate-origin distance convention at its auxiliary occurrences. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMetricChoiceRobustness
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (height)
open RingOriginCausal (inventory policy trial)
open RingStoreDecision (candidateRows firstDifference?)
open private same_run from TetraStereo.Engine.RingOriginCausal

variable {i : Input} (r : i.certified.Atom)

/-- Two endpoint stores can bound a family of policies at a fixed batch.
At each publication, the intermediate rule chooses one of the two local
outputs on that reader. No ordering of chemical descriptors is involved. -/
theorem stores_between (low high middle : RingActiveDistanceSchedule.Rule i)
    (pick : ∀ q read, middle q read = low q read ∨ middle q read = high q read)
    (n : Nat) (ends : candidateRows low r n = candidateRows high r n) :
    candidateRows middle r n = candidateRows low r n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change _ ++ candidateRows low r n = _ ++ candidateRows high r n at ends
    obtain ⟨batch,old⟩ := List.append_inj ends (by simp)
    have mid := ih old
    change List.map _ _ = List.map _ _ at batch
    rw [List.map_inj_left] at batch
    change _ ++ candidateRows middle r n = _ ++ candidateRows low r n
    rw [mid]
    apply congrArg (· ++ _)
    apply List.map_congr_left
    intro q mem
    simp only [candidateRows] at old mid
    dsimp only
    rw [mid]
    apply congrArg (q, ·)
    rcases pick q _ with same | same
    · exact same
    · refine same.trans ?_
      have eqn := (congrArg Prod.snd (batch q mem)).symm
      dsimp only at eqn
      rwa [← old] at eqn

/-- Identical addressed stores at the uniform endpoints force identical stores
for *every* independent choice of local convention, even on its own readers. -/
theorem all_stores (n : Nat)
    (agree : candidateRows (RingOriginMetricReport.publish i) r n = RingSphereStore.rows i r n)
    (choose : List (Site i)) :
    candidateRows (policy i choose) r n = RingSphereStore.rows i r n := by
  apply stores_between r (RingPyramidalPublication.publish i) (RingOriginMetricReport.publish i)
    (policy i choose) _ n agree.symm
  intro q read
  by_cases h : q ∈ choose <;> simp [policy,h]

private def selectedRule (choose : List (Site i)) : RingActiveDistanceSchedule.Rule i := fun q =>
  if q ∈ choose then RingOriginIndexedKeys.publish i q else RingPyramidalPublication.publish i q

private theorem selectedRule_eq (choose : List (Site i)) : selectedRule choose = policy i choose := by
  unfold selectedRule policy
  rw [RingOriginIndexedKeys.publish_exact]

private def result (choose : List (Site i)) :=
  RingPyramidalPublication.publish i (RingGroupedReport.origin i r)
    (RingSphereQueue.reader r (RingSphereQueue.viewOf
      (candidateRows (selectedRule choose) r (height i + 1))))

private theorem result_exact (choose : List (Site i)) : result r choose = trial i r choose := by
  simp only [result,selectedRule_eq,candidateRows,RingSphereQueue.stored_eq,trial]

/-- Forward, zero-based raw atom IDs, starting with the original root. -/
def address (q : Site i) : List Nat := q.val.node.history.reverse.map Fin.val

/-- A single full rerun on a supplied intervention. Filtering the inventory is
needed only in the specification: execution matches paths at queued sites. -/
def trialPaths (j : Input) (root : j.certified.Atom) (paths : List (List Nat)) :=
  let hybrid : RingActiveDistanceSchedule.Rule j := fun q =>
    if address q ∈ paths then RingOriginIndexedKeys.publish j q else RingPyramidalPublication.publish j q
  RingPyramidalPublication.publish j (RingGroupedReport.origin j root)
    (RingSphereQueue.reader root (RingSphereQueue.viewOf
      (RingRootLayerStore.rows j (RingPyramidalPublication.eligible j) hybrid root)))

theorem trialPaths_exact (paths : List (List Nat)) :
    trialPaths i r paths = trial i r ((inventory i r).filter fun q => address q ∈ paths) := by
  unfold trialPaths trial
  dsimp only
  rw [RingRootLayerStore.rows_eq,RingSphereQueue.stored_eq,RingOriginIndexedKeys.publish_exact]
  rw [same_run r _ (policy i ((inventory i r).filter fun q => address q ∈ paths)) (fun d q h => by
    have listed := RingOriginCausal.mem_inventory.mpr
      (((RingEligibleGraph.inventory i _ r d q).mp h).1)
    simp [policy,listed])]

private theorem normalized (choose : List (Site i)) :
    trial i r ((inventory i r).filter (· ∈ choose)) = trial i r choose := by
  unfold trial
  rw [same_run r _ (policy i choose) (fun d q h => by
    have listed := RingOriginCausal.mem_inventory.mpr
      (((RingEligibleGraph.inventory i _ r d q).mp h).1)
    simp [policy,listed])]

/-- Lazy subset search. Its result is an actual selection of auxiliary sites. -/
private def search {α : Type} : List α → (List α → Option (List α)) → Option (List α)
  | [], test => test []
  | x::xs, test => (search xs test).orElse fun _ => search xs (fun s => test (x::s))

private theorem orElse_none {α : Type} (a : Option α) (b : Unit → Option α) :
    a.orElse b = none ↔ a = none ∧ b () = none := by cases a <;> simp [Option.orElse]

private theorem search_none {α : Type} (xs : List α) (test : List α → Option (List α)) :
    search xs test = none ↔ ∀ s, List.Sublist s xs → test s = none := by
  induction xs generalizing test with
  | nil => simp [search]
  | cons x xs ih =>
    simp only [search,orElse_none,ih]
    constructor
    · rintro ⟨skip,take⟩ s h
      cases h with
      | cons _ h => exact skip _ h
      | cons₂ _ h => exact take _ h
    · intro all
      exact ⟨fun s h => all s (h.cons x),fun s h => all _ (h.cons₂ x)⟩

private theorem search_some {α : Type} (xs : List α) (test : List α → Option (List α)) (v : List α)
    (found : search xs test = some v) : ∃ s, List.Sublist s xs ∧ test s = some v := by
  induction xs generalizing test with
  | nil => exact ⟨[],.slnil,found⟩
  | cons x xs ih =>
    cases h : search xs test with
    | none =>
      obtain ⟨s,sub,hit⟩ := ih (fun s => test (x::s)) (by simpa [search,h] using found)
      exact ⟨x::s,sub.cons₂ _,hit⟩
    | some w =>
      obtain ⟨s,sub,hit⟩ := ih test (h.trans (by simpa [search,h] using found))
      exact ⟨s,sub.cons _,hit⟩

private def highRule (support chosen : List (Site i)) : RingActiveDistanceSchedule.Rule i := fun q =>
  if q ∉ support ∨ q ∈ chosen then RingOriginIndexedKeys.publish i q else RingPyramidalPublication.publish i q

/-- The independently evaluated stores agree when every off-support site is
flipped at once. Retain the common store for inspecting this intervention. -/
def supportedRows? (support chosen : List (Site i)) :=
  let low := candidateRows (selectedRule chosen) r (height i+1)
  let high := candidateRows (highRule support chosen) r (height i+1)
  if low = high then some low else none

/-- Evaluate and certify one row of a support truth table. Outer absence means
the support test failed; a completed refusal is an ordinary root result. -/
def supportedTrial? (support chosen : List (Site i)) :=
  (supportedRows? r support chosen).map fun rows =>
    RingPyramidalPublication.publish i (RingGroupedReport.origin i r)
      (RingSphereQueue.reader r (RingSphereQueue.viewOf rows))

theorem supportedTrial_exact (support chosen : List (Site i)) {cell}
    (hit : supportedTrial? r support chosen = some cell) : cell = trial i r chosen := by
  unfold supportedTrial? supportedRows? at hit
  dsimp only at hit
  split at hit
  · exact (Option.some.inj hit).symm.trans (result_exact r chosen)
  · contradiction

/-- Verify a proposed small set of sensitive sites on a single root. For each
subset, compare addressed stores with every outside site switched versus none.
Uses two full materialized runs per subset, independent of the outside count. -/
def supportCheck (support : List (Site i)) : Bool :=
  (search support fun chosen =>
    if (supportedRows? r support chosen).isSome then none else some chosen).isNone

/-- Certifying every sublist by a successful trial is equivalent to passing
the whole support check. This allows a diagnostic to print each result as it runs. -/
theorem supportCheck_iff (support : List (Site i)) : supportCheck r support = true ↔
    ∀ chosen, List.Sublist chosen support → (supportedTrial? r support chosen).isSome = true := by
  simp only [supportCheck,Option.isNone_iff_eq_none,search_none]
  apply forall_congr'
  intro chosen
  apply forall_congr'
  intro _
  cases h : supportedRows? r support chosen <;> simp [supportedTrial?,h]

/-- Resolve a proposed support stated as forward, zero-based atom paths. -/
def supportFromPaths (paths : List (List Nat)) : List (Site i) :=
  (inventory i r).filter fun q => address q ∈ paths

/-- Passing the small-support certificate lets any intervention be reduced to
its intersection with that support, preserving all stored cells. -/
theorem support_stores (support : List (Site i)) (pass : supportCheck r support = true)
    (choose : List (Site i)) :
    candidateRows (policy i choose) r (height i+1) =
      candidateRows (policy i (support.filter (· ∈ choose))) r (height i+1) := by
  let chosen := support.filter (· ∈ choose)
  have sub : List.Sublist chosen support := List.filter_sublist ..
  have all := (search_none _ _).mp (Option.isNone_iff_eq_none.mp pass) chosen sub
  have ends : candidateRows (selectedRule chosen) r (height i+1) =
      candidateRows (highRule support chosen) r (height i+1) := by
    by_contra neq
    simp [supportedRows?,neq] at all
  change _ = candidateRows (policy i chosen) r (height i+1)
  rw [← selectedRule_eq chosen]
  apply stores_between r _ _ _ _ _ ends
  intro q read
  by_cases inside : q ∈ support <;> by_cases picked : q ∈ choose <;>
    simp [policy,selectedRule,highRule,chosen,inside,picked,RingOriginIndexedKeys.publish_exact]

theorem support_root (support : List (Site i)) (pass : supportCheck r support = true)
    (choose : List (Site i)) : trial i r choose = trial i r (support.filter (· ∈ choose)) := by
  rw [← result_exact,← result_exact]
  simp only [result,selectedRule_eq,support_stores r support pass choose]

/-- Returns a selection whose fully recomputed root differs from the public
root. Equal uniform stores skip the subset search. -/
def witness? : Option (List (Site i)) :=
  if (firstDifference? (RingOriginIndexedKeys.publish i) r (height i+1)).isNone then none
  else
    let baseline := result r []
    search (inventory i r) fun s => if result r s = baseline then none else some s

theorem witness_none : witness? r = none ↔
    ∀ choose, trial i r choose = RingChemicalGraphProof.root i r := by
  rw [← RingOriginCausal.trial_nil]
  unfold witness?
  split
  next h =>
    rw [RingOriginIndexedKeys.publish_exact] at h
    have rows := (RingStoreDecision.firstDifference_none_iff _ r _).mp (Option.isNone_iff_eq_none.mp h)
    simp only [true_iff]
    intro choose
    rw [← result_exact,← result_exact]
    simp only [result,selectedRule_eq]
    rw [all_stores r _ rows choose,all_stores r _ rows []]
  next =>
    rw [search_none]
    simp only [ite_eq_left_iff, reduceCtorEq, imp_false, not_not,result_exact]
    constructor
    · intro all choose
      rw [← normalized r choose]
      exact all _ (List.filter_sublist ..)
    · exact fun all s _ => all s

theorem witness_some {choose : List (Site i)} (found : witness? r = some choose) :
    List.Sublist choose (inventory i r) ∧ trial i r choose ≠ RingChemicalGraphProof.root i r := by
  unfold witness? at found
  split at found
  · contradiction
  · obtain ⟨s,sub,hit⟩ := search_some _ _ _ found
    by_cases eqn : result r s = result r []
    · simp [eqn] at hit
    · have same : s = choose := by simpa [eqn] using hit
      subst choose
      exact ⟨sub,by simpa only [result_exact,RingOriginCausal.trial_nil] using eqn⟩

/-- Test each requested original atom independently, preserving repeated requests. -/
def request (atoms : List i.certified.Atom) : Bool := atoms.all fun a => (witness? a).isNone

theorem request_iff (atoms : List i.certified.Atom) : request atoms = true ↔
    ∀ a ∈ atoms, ∀ choose, trial i a choose = RingChemicalGraphProof.root i a := by
  simp only [request,List.all_eq_true,Option.isNone_iff_eq_none,witness_none]

/-- The alternative may choose a different local convention at each occurrence
of each original atom, separately for every prepared geometry. -/
def reportWith (choose : (j : Input) → j.certified.Atom → List (Site j)) :
    RingRawComparisonLift.TypedEvaluation := fun j atoms =>
  atoms.mapM fun a => (result a (choose j a)).map fun labels => (a.val,labels)

/-- Passing the tests on every reachable preparation preserves the complete
raw report, including public implicit-hydrogen consensus. -/
theorem raw {m : OneCenter.RawMolecule} {g : OneCenter.SpatialConfiguration} {ids : List Nat}
    (pass : ∀ j atoms, RingRawComparisonLift.RawTrace m g ids j atoms → request atoms = true)
    (choose : (j : Input) → j.certified.Atom → List (Site j)) :
    RingRawComparisonLift.fromRaw (reportWith choose) m g ids = RingHydrogenReport.fromRaw? m g ids := by
  apply RingRawComparisonLift.eq_native
  intro j atoms reached
  apply RingFrameTransport.mapM_congr_mem
  intro a mem
  simp only [result_exact,(request_iff atoms).mp (pass j atoms reached) a mem (choose j a)]
  rfl

end TetraStereo.Engine.RingMetricChoiceRobustness
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.all_stores
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.witness_none
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.witness_some
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.request_iff
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.raw
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.trialPaths_exact
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.support_stores
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.support_root
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.supportCheck_iff
assert_kernel_only TetraStereo.Engine.RingMetricChoiceRobustness.supportedTrial_exact
