import TetraStereo.Engine.RingOrdinaryPairVerdict
import TetraStereo.Engine.RingMetricChoiceRobustness

/-! Which ligand wins at a requested root when auxiliary duplicate distances can
vary by occurrence? A finite search tests both strict directions, the first
deciding rule, an actual tie, and absence of a requested comparison. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMetricPairOutcomes
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (height)
open RingActivePairReport (Slot)
open RingOriginCausal (inventory policy)
open RingResidualPairDecision (Verdict)
open RingStoreDecision (candidateRows)
open RingMetricChoiceRobustness (supportCheck support_stores)
open private search search_none search_some selectedRule selectedRule_eq
  from TetraStereo.Engine.RingMetricChoiceRobustness

inductive Pass where
  | ordinary
  | scheduled (ordinal : Nat)

/-- The outer option records whether the requested comparison produced a verdict.
The inner option records the Rule 6 nomination, when present. -/
abbrev Answer := Option (Option Slot × Verdict)

open private frame_eq from TetraStereo.Engine.RingGroupedReport

variable {i : Input} (r : i.certified.Atom)

def answer (pass : Pass) (rev : Bool) (a b : Slot) (choose : List (Site i)) : Answer := do
  let fr ← RingNestedActivePair.frame? i (RingGroupedReport.origin i r)
  let read := RingSphereQueue.reader r (RingSphereQueue.viewOf
    (candidateRows (selectedRule choose) r (height i+1)))
  match pass with
  | .ordinary =>
    let t ← RingOrdinaryPairVerdict.onReader? fr read rev
    return (none,t[a.val][b.val])
  | .scheduled n =>
    let rows ← RingResidualPairDecision.diagnose? fr read
    let t ← rows[n]?
    return (t.nomination,(t.table rev)[a.val][b.val])

private theorem normalized_rows (choose : List (Site i)) (n : Nat) :
    candidateRows (policy i ((inventory i r).filter (· ∈ choose))) r n =
      candidateRows (policy i choose) r n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change _ ++ candidateRows _ r n = _ ++ candidateRows _ r n
    rw [ih]
    apply congrArg (· ++ _)
    apply List.map_congr_left
    intro q mem
    have listed := RingOriginCausal.mem_inventory.mpr
      (((RingEligibleGraph.inventory i _ r _ q).mp mem).1)
    simp only [policy,List.mem_filter,decide_eq_true_eq,listed,true_and]
    unfold candidateRows at ih
    rw [ih]

/-- A previously verified support can replace the full inventory. If the
proposed support fails its store test, the full inventory remains exact. -/
def domain (proposed : List (Site i)) :=
  if supportCheck r proposed then proposed else inventory i r

private theorem restrict_answer (proposed choose : List (Site i)) (p : Pass) (rev : Bool) (a b : Slot) :
    answer r p rev a b ((domain r proposed).filter (· ∈ choose)) = answer r p rev a b choose := by
  have same : candidateRows (policy i ((domain r proposed).filter (· ∈ choose))) r (height i+1) =
      candidateRows (policy i choose) r (height i+1) := by
    unfold domain
    split
    next ok => exact (support_stores r proposed ok choose).symm
    next => exact normalized_rows r choose _
  simp only [answer,selectedRule_eq,same]

/-- A witness is an actual selection of sites whose recomputed comparison
equals the requested answer, including its nomination and first deciding rule. -/
def witness? (proposed : List (Site i)) (p : Pass) (rev : Bool) (a b : Slot) (want : Answer) :=
  search (domain r proposed) fun choose =>
    if answer r p rev a b choose = want then some choose else none

theorem witness_none (proposed : List (Site i)) (p : Pass) (rev : Bool) (a b : Slot) (want : Answer) :
    witness? r proposed p rev a b want = none ↔ ∀ choose, answer r p rev a b choose ≠ want := by
  simp only [witness?, search_none, ite_eq_right_iff, reduceCtorEq, imp_false]
  constructor
  · intro h choose
    rw [← restrict_answer r proposed choose p rev a b]
    exact h _ (List.filter_sublist ..)
  · exact fun h choose _ => h choose

theorem witness_some {proposed : List (Site i)} {p : Pass} {rev : Bool} {a b : Slot}
    {want : Answer} {choose : List (Site i)} (hit : witness? r proposed p rev a b want = some choose) :
    choose.Sublist (domain r proposed) ∧ answer r p rev a b choose = want := by
  obtain ⟨s,sub,found⟩ := search_some _ _ _ hit
  split at found
  next eqn => exact Option.some.inj found ▸ ⟨sub,eqn⟩
  next => contradiction

/-- The search succeeds exactly for reachable pair answers. -/
theorem possible_iff (proposed : List (Site i)) (p : Pass) (rev : Bool) (a b : Slot) (want : Answer) :
    (witness? r proposed p rev a b want).isSome = true ↔ ∃ choose, answer r p rev a b choose = want := by
  cases found : witness? r proposed p rev a b want with
  | none => simpa using (witness_none r proposed p rev a b want).mp found
  | some choose => exact iff_of_true rfl ⟨choose,(witness_some r found).2⟩

private theorem native_rows : candidateRows (selectedRule ([] : List (Site i))) r (height i+1) =
    RingSphereStore.rows i r (height i+1) := by
  have base : policy i [] = RingPyramidalPublication.publish i := by funext q read; simp [policy]
  rw [selectedRule_eq,base]

/-- With the public distance convention the ordinary answer is exactly the
pair on the public preceding store, even if the root went on to nomination. -/
theorem native_ordinary (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (fr : RingNestedActivePair.Frame i (RingGroupedReport.origin i r)) (rev : Bool) (a b : Slot) :
    ∃ t, RingResidualPairDecision.TableExact fr (RingGlobalComparison.prior i r (height i+1))
      rev none t ∧ answer r .ordinary rev a b [] = some (none,t[a.val][b.val]) := by
  have call : RingGlobalComparison.Called i r (height i+1) (RingGroupedReport.origin i r) :=
    Or.inr ⟨rfl,rfl⟩
  obtain ⟨t,got,lawful⟩ := RingOrdinaryPairVerdict.exact geom call fr rev
  rw [RingOrdinaryPairVerdict.at_call geom call fr rev] at got
  refine ⟨t,lawful,?_⟩
  unfold RingGlobalComparison.prior at got
  simp [answer,frame_eq fr,native_rows,got]

/-- All actual public nominations, on both geometries. Each pair query agrees
with its exact trial table, and an ordinal past the end returns no comparison. -/
theorem native_schedule (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (fr : RingNestedActivePair.Frame i (RingGroupedReport.origin i r)) :
    ∃ ts, RingResidualPairDecision.Exact fr (RingGlobalComparison.prior i r (height i+1)) ts ∧
      ∀ (n : Nat) (rev : Bool) (a b : Slot), answer r (.scheduled n) rev a b [] =
        ts[n]?.map (fun t => (t.nomination,(t.table rev)[a.val][b.val])) := by
  have call : RingGlobalComparison.Called i r (height i+1) (RingGroupedReport.origin i r) :=
    Or.inr ⟨rfl,rfl⟩
  obtain ⟨ts,got,lawful⟩ := RingResidualPairDecision.public_exact fr geom call
  simp [RingResidualPairDecision.atSite?,frame_eq fr,RingGlobalComparison.prior] at got
  refine ⟨ts,lawful,?_⟩
  intro n rev a b
  cases h : ts[n]? <;> simp [answer,frame_eq fr,native_rows,got,h]

end TetraStereo.Engine.RingMetricPairOutcomes
assert_kernel_only TetraStereo.Engine.RingMetricPairOutcomes.witness_none
assert_kernel_only TetraStereo.Engine.RingMetricPairOutcomes.witness_some
assert_kernel_only TetraStereo.Engine.RingMetricPairOutcomes.native_ordinary
assert_kernel_only TetraStereo.Engine.RingMetricPairOutcomes.possible_iff
assert_kernel_only TetraStereo.Engine.RingMetricPairOutcomes.native_schedule
