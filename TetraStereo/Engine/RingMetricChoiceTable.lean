import TetraStereo.Engine.RingMetricChoiceRobustness

/-! Evaluate all auxiliary-origin interventions together. Equal materialized
priors share the two actual local publications at every queued occurrence. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMetricChoiceTable
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell Rule height)
open RingStoreDecision (candidateRows)
open RingMetricChoiceRobustness (supportedTrial? supportedRows? supportCheck)
open private selectedRule highRule from TetraStereo.Engine.RingMetricChoiceRobustness

variable {i : Input} (r : i.certified.Atom)
private abbrev Rows (i : Input) := List (Site i × Cell)

private def alternatives (n : Nat) (rows : Rows i) :=
  let reader := RingSphereQueue.reader r (RingSphereQueue.viewOf rows)
  (RingGlobalComparison.queue i r (height i - n)).map fun q =>
    (q,RingPyramidalPublication.publish i q reader,RingOriginIndexedKeys.publish i q reader)

private def resolve (mark : Site i → Bool) (cells : List (Site i × Cell × Cell)) : Rows i :=
  cells.map fun (q,ordinary,active) => (q,if mark q then active else ordinary)

private def mergeRule (mark : Site i → Bool) : Rule i := fun q =>
  if mark q then RingOriginIndexedKeys.publish i q else RingPyramidalPublication.publish i q

private def family {α : Type} (tags : List α) (marks : α → Site i → Bool) :
    Nat → List (α × Rows i)
  | 0 => tags.map (·,[])
  | n+1 =>
    let before := family tags marks n
    let distinct := (before.map Prod.snd).dedup
    let cache := distinct.map fun rows => (rows, alternatives r n rows)
    before.map fun (tag,rows) => (tag,resolve (marks tag) ((cache.lookup rows).getD []) ++ rows)

private theorem family_exact {α : Type} (tags : List α) (marks : α → Site i → Bool) (n : Nat) :
    family r tags marks n = tags.map fun t => (t,candidateRows (mergeRule (marks t)) r n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [family,ih,List.map_map]
    apply List.map_congr_left
    intro tag member
    let rows := candidateRows (mergeRule (marks tag)) r n
    let before := tags.map fun t => (t,candidateRows (mergeRule (marks t)) r n)
    have old : (tag,rows) ∈ before := List.mem_map_of_mem member
    have listed : rows ∈ (before.map Prod.snd).dedup :=
      List.mem_dedup.mpr (List.mem_map_of_mem (f := Prod.snd) old)
    have hit := List.lookup_graph (alternatives r n) listed
    change (tag, resolve (marks tag) (((before.map Prod.snd).dedup.map
      (fun old => (old,alternatives r n old))).lookup rows |>.getD []) ++ rows) = _
    rw [hit]
    simp only [Option.getD_some,resolve,alternatives,List.map_map]
    apply congrArg (tag, ·)
    apply congrArg (· ++ rows)
    apply List.map_congr_left
    intro q _
    dsimp only [Function.comp_apply]
    unfold mergeRule
    cases marks tag q <;> rfl

private abbrev Tag (i : Input) := List (Site i) × Bool

private def marks (support : List (Site i)) (t : Tag i) (q : Site i) : Bool :=
  if t.2 then decide (q ∉ support ∨ q ∈ t.1) else decide (q ∈ t.1)

private theorem ordinary (support chosen : List (Site i)) :
    mergeRule (marks support (chosen,false)) = selectedRule chosen := by
  funext q
  simp [marks,mergeRule,selectedRule]

private theorem active (support chosen : List (Site i)) :
    mergeRule (marks support (chosen,true)) = highRule support chosen := by
  funext q
  simp [marks,mergeRule,highRule]

/-- A complete support truth table, preserving each site's physical identity.
Outer absence in a row means its endpoint stores differ. -/
def table (support : List (Site i)) :=
  let choices := support.sublists
  let tags := choices.flatMap fun chosen => [(chosen,false),(chosen,true)]
  let runs := family r tags (marks support) (height i+1)
  choices.map fun chosen =>
    (chosen, do
      let low ← runs.lookup (chosen,false)
      let high ← runs.lookup (chosen,true)
      guard (low = high)
      return RingPyramidalPublication.publish i (RingGroupedReport.origin i r)
        (RingSphereQueue.reader r (RingSphereQueue.viewOf low)))

theorem table_exact (support : List (Site i)) : table r support =
    support.sublists.map fun chosen => (chosen,supportedTrial? r support chosen) := by
  unfold table
  dsimp only
  rw [family_exact]
  apply List.map_congr_left
  intro chosen listed
  let tags := support.sublists.flatMap fun s => [(s,false),(s,true)]
  let store := fun t : Tag i => candidateRows (mergeRule (marks support t)) r (height i+1)
  have low : (chosen,false) ∈ tags := List.mem_flatMap.mpr ⟨chosen,listed,by simp⟩
  have high : (chosen,true) ∈ tags := List.mem_flatMap.mpr ⟨chosen,listed,by simp⟩
  change (_,(do
    let lo ← (tags.map fun t => (t,store t)).lookup (chosen,false)
    let hi ← (tags.map fun t => (t,store t)).lookup (chosen,true)
    guard (lo = hi)
    return _)) = _
  rw [List.lookup_graph store low,List.lookup_graph store high]
  dsimp only [store,Option.bind_some]
  rw [ordinary,active]
  unfold supportedTrial? supportedRows?
  dsimp only
  split <;> simp_all

theorem all_supported (support : List (Site i)) :
    (table r support).all (fun row => row.2.isSome) = true ↔ supportCheck r support = true := by
  rw [table_exact,RingMetricChoiceRobustness.supportCheck_iff]
  simp [List.all_eq_true,List.mem_sublists]

/-- A checked truth table establishes the predicted root for arbitrary choices
at every auxiliary occurrence, including all occurrences outside the support. -/
theorem predicts (support : List (Site i)) (prediction : List (Site i) → Cell)
    (checked : (table r support).all (fun row => decide (row.2 = some (prediction row.1))) = true)
    (chosen : List (Site i)) : RingOriginCausal.trial i r chosen =
      prediction (support.filter (· ∈ chosen)) := by
  rw [table_exact,List.all_eq_true] at checked
  have cert (s : List (Site i)) (h : List.Sublist s support) :
      supportedTrial? r support s = some (prediction s) :=
    of_decide_eq_true (checked _ (List.mem_map_of_mem (List.mem_sublists.mpr h)))
  have pass : supportCheck r support = true :=
    (RingMetricChoiceRobustness.supportCheck_iff r support).mpr fun s h => by rw [cert s h]; rfl
  rw [RingMetricChoiceRobustness.support_root r support pass chosen]
  exact (RingMetricChoiceRobustness.supportedTrial_exact r _ _ (cert _ (List.filter_sublist ..))).symm

end TetraStereo.Engine.RingMetricChoiceTable
assert_kernel_only TetraStereo.Engine.RingMetricChoiceTable.table_exact
assert_kernel_only TetraStereo.Engine.RingMetricChoiceTable.all_supported
assert_kernel_only TetraStereo.Engine.RingMetricChoiceTable.predicts
