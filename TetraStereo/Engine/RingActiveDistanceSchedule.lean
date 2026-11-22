import TetraStereo.Engine.RingActivePairs

set_option autoImplicit false

namespace TetraStereo.Engine.RingActiveDistanceSchedule
open OneCenter CertifiedLocalizedCIPInput RingActivePairs
open LocalizedChemicalRing (Input)

/-- The outer option records coverage. A known absence and an unresolved occurrence
have different values. The two labels are the publications in the two geometries. -/
abbrev Cell := Option (Option (LocalizedAuxiliaryLabel × LocalizedAuxiliaryLabel))
abbrev View (i : Input) := Site i → Cell
abbrev Rule (i : Input) := Site i → View i → Cell

def distance {i : Input} (q : Site i) := q.val.address.length

/-- Read only publications from completed, strictly more distant batches of this original
digraph, excluding the original configuration even when it reappears on a ring path. -/
def frozen {i : Input} (s : View i) (focus q : Site i) : Cell :=
  if q.val.root ≠ focus.val.root then none
  else if distance focus < distance q ∧ q.val.node.current? ≠ some focus.val.root then s q
  else some none

def sites (i : Input) : List (Site i) :=
  (i.certified.localizedOccurrences (i.certified.certified.input.molecule.atomCount+1)).attach

def height (i : Input) := (sites i).foldr (fun q k => max (distance q) k) 0

theorem distance_bound {i : Input} (q : Site i) : distance q ≤ height i := by
  have upper (xs : List (Site i)) (mem : q ∈ xs) :
      distance q ≤ xs.foldr (fun a k => max (distance a) k) 0 := by
    induction xs with
    | nil => simp at mem
    | cons a xs ih =>
      rcases List.mem_cons.mp mem with rfl | tail
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih tail) (Nat.le_max_right ..)
  exact upper (sites i) (List.mem_attach ..)

private theorem frozen_congr {i : Input} {s t : View i} (focus : Site i)
    (deeper : ∀ q, distance focus < distance q → s q = t q) :
    frozen s focus = frozen t focus := by
  funext q
  unfold frozen
  split_ifs with _ available
  · rfl
  · exact deeper q available.1
  · rfl

/-- A single distance batch. Force the molecular evaluator exactly once for each site
at this distance, before making its publications visible to any shallower site. -/
def batch {i : Input} (rule : Rule i) (d : Nat) (before : View i) : View i :=
  let rows := ((sites i).filter (fun q => distance q == d)).map
    (fun q => (q,rule q (frozen before q)))
  fun q => match rows.findSome? (fun r => if r.1 = q then some r.2 else none) with
    | some cell => cell
    | none => before q

private theorem lookup_map {α β : Type} [DecidableEq α] (f : α → β) (q : α) (qs : List α) :
    ((qs.map (fun a => (a,f a))).findSome? (fun r => if r.1 = q then some r.2 else none)) = if q ∈ qs then some (f q) else none := by
  induction qs with
  | nil => rfl
  | cons a qs ih =>
    by_cases same : q = a
    · subst a; simp
    · simp [same, Ne.symm same, ih]

theorem batch_at {i : Input} (rule : Rule i) (d : Nat) (s : View i) (q : Site i) :
    batch rule d s q = if distance q = d then rule q (frozen s q) else s q := by
  unfold batch
  rw [lookup_map (fun a => rule a (frozen s a)) q]
  have present : q ∈ sites i := List.mem_attach ..
  by_cases same : distance q = d <;> simp [present,same]

/-- The finite pass starts above the greatest original address and descends to zero. -/
def pass {i : Input} (rule : Rule i) : Nat → View i
  | 0 => fun _ => none
  | k+1 => batch rule (height i - k) (pass rule k)

def evaluate {i : Input} (rule : Rule i) := pass rule (height i+1)

/-- Materialized publication cells retain the original occurrence as the key. Building
the next distance reads an existing list of values and shares it among all comparisons. -/
abbrev Table (i : Input) := List (Site i × Cell)

def snapshot {i : Input} (rows : Table i) (q : Site i) : Cell :=
  (rows.findSome? (fun r => if r.1 = q then some r.2 else none)).getD none

def table {i : Input} (rule : Rule i) : Nat → Table i
  | 0 => []
  | k+1 =>
    let previous := table rule k
    let batchSites := (sites i).filter (fun q => distance q == height i - k)
    (batchSites.map fun q => (q,rule q (frozen (snapshot previous) q))) ++ previous

private theorem find_append {α β : Type} (f : α → Option β) (xs ys : List α) :
    (xs ++ ys).findSome? f = (xs.findSome? f).or (ys.findSome? f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : f a <;> simp [h,ih,Option.or]

theorem snapshot_table {i : Input} (rule : Rule i) (k : Nat) :
    snapshot (table rule k) = pass rule k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext q
    rw [pass,batch_at]
    simp only [table,ih]
    unfold snapshot
    rw [find_append,lookup_map (fun a => rule a (frozen (pass rule k) a)) q]
    have present : q ∈ sites i := List.mem_attach ..
    have old := congrFun ih q
    by_cases here : distance q = height i - k <;> simp [present,here,Option.or,snapshot] at old ⊢; exact old

/-- Pass the complete site list and its maximum depth as explicit values, outside
the recursive loop. The filter never reconstructs either from the molecular input. -/
private def tableOn {i : Input} (rule : Rule i) (allSites : List (Site i)) (top : Nat) : Nat → Table i
  | 0 => []
  | k+1 =>
    let previous := tableOn rule allSites top k
    let d := top - k
    let batchSites := allSites.filter (fun q => distance q == d)
    (batchSites.map fun q => (q,rule q (frozen (snapshot previous) q))) ++ previous

def sharedTable {i : Input} (rule : Rule i) (k : Nat) : Table i :=
  let allSites := sites i
  tableOn rule allSites (allSites.foldr (fun q d => max (distance q) d) 0) k

@[csimp] theorem table_shared : @table = @sharedTable := by
  funext i rule k
  change table rule k = tableOn rule (sites i) (height i) k
  induction k with
  | zero => rfl
  | succ k ih => simp only [table,tableOn,ih]

def cached {i : Input} (rule : Rule i) : View i := snapshot (table rule (height i+1))

/-- Replace the function iteration by an explicitly materialized table in executable
clients. The kernel checks all observations, including misses and inner absences. -/
@[csimp] theorem evaluate_cached : @evaluate = @cached := by
  funext i rule
  exact (snapshot_table rule (height i+1)).symm

/-- A completed deeper row never changes again during the descent. -/
theorem pass_stable {i : Input} (rule : Rule i) {j k : Nat} (jk : j ≤ k) (bound : k ≤ height i+1)
    (q : Site i) (done_ : height i < distance q + j) :
    pass rule k q = pass rule j q := by
  induction k,jk using Nat.le_induction with
  | base => rfl
  | succ n jn ih =>
    have old : distance q ≠ height i - n := by omega
    rw [pass,batch_at,if_neg old,ih (by omega)]

/-- Every site satisfies its distance equation, including the sites returning a proven
absence or an unresolved value. No depth or termination assumption is supplied. -/
theorem evaluate_eq {i : Input} (rule : Rule i) (q : Site i) :
    evaluate rule q = rule q (frozen (evaluate rule) q) := by
  let j := height i - distance q
  have bound := distance_bound q
  have atDepth : height i - j = distance q := by dsimp [j]; omega
  have done_ : height i < distance q + (j+1) := by dsimp [j]; omega
  have last : j+1 ≤ height i+1 := by dsimp [j]; omega
  have before : frozen (evaluate rule) q = frozen (pass rule j) q := by
    apply frozen_congr
    intro child deeper
    exact pass_stable rule (by omega) (Nat.le_refl _) child (by dsimp [j]; omega)
  unfold evaluate
  rw [pass_stable rule last (Nat.le_refl _) q done_,pass,batch_at,atDepth,if_pos rfl]
  exact congrArg (rule q) before.symm

/-- Unique molecular publication state for any evaluator whose only dependencies are the
frozen original-address reads. Equal-distance discovery order never enters these equations. -/
theorem unique {i : Input} (rule : Rule i) (s : View i)
    (equations : ∀ q, s q = rule q (frozen s q)) : s = evaluate rule := by
  funext q
  suffices h : ∀ n (q : Site i), height i - distance q = n → s q = evaluate rule q from h _ q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q rank
    rw [equations q,evaluate_eq rule q]
    apply congrArg (rule q)
    apply frozen_congr
    intro child deeper
    have upper := distance_bound child
    exact ih _ (by omega) child rfl

/-- The exact dependency scope of a publication on the original digraph. -/
def Visible {i : Input} (q t : Site i) : Prop :=
  t.val.root = q.val.root ∧ distance q < distance t ∧ t.val.node.current? ≠ some q.val.root

instance {i : Input} (q t : Site i) : Decidable (Visible q t) := by unfold Visible; infer_instance

theorem Visible.trans {i : Input} {a b c : Site i} (ab : Visible a b) (bc : Visible b c) :
    Visible a c := ⟨bc.1.trans ab.1, Nat.lt_trans ab.2.1 bc.2.1, ab.1 ▸ bc.2.2⟩

/-- A local obstruction is a failure of the actual molecular rule after every eligible
deeper publication in its original digraph has already been determined. -/
def Obstruction {i : Input} (rule : Rule i) (q : Site i) : Prop :=
  rule q (frozen (evaluate rule) q) = none ∧
    ∀ t, Visible q t → (evaluate rule t).isSome = true

/-- Every uncovered occurrence leads to a local obstruction on this same digraph,
at the original occurrence or strictly deeper. No assumption of complete comparison
coverage, successful rankings or independently supplied labels is needed. -/
theorem obstruction_of_uncovered {i : Input} (rule : Rule i) (q : Site i)
    (missing : evaluate rule q = none) :
    ∃ t, (t = q ∨ Visible q t) ∧ Obstruction rule t := by
  suffices h : ∀ n (a : Site i), height i - distance a = n → evaluate rule a = none →
      ∃ t, (t = a ∨ Visible a t) ∧ Obstruction rule t from h _ q rfl missing
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a rank bad
    classical
    by_cases allKnown : ∀ b, Visible a b → (evaluate rule b).isSome = true
    · exact ⟨a,Or.inl rfl,(evaluate_eq rule a).symm.trans bad,allKnown⟩
    · push_neg at allKnown
      obtain ⟨b,vis,unknown⟩ := allKnown
      have upper := distance_bound b
      have strict := vis.2.1
      have miss : evaluate rule b = none := by cases read : evaluate rule b <;> simp_all
      obtain ⟨t,step,obs⟩ := ih _ (by omega) b rfl miss
      rcases step with rfl | next
      · exact ⟨_,Or.inr vis,obs⟩
      · exact ⟨_,Or.inr (vis.trans next),obs⟩

theorem universal_iff_no_obstruction {i : Input} (rule : Rule i) :
    (∀ q, (evaluate rule q).isSome = true) ↔ ¬ ∃ q, Obstruction rule q := by
  constructor
  · rintro full ⟨q,h,_⟩
    have hit := full q
    rw [evaluate_eq, h] at hit
    contradiction
  · intro clean q
    cases h : evaluate rule q with
    | some => rfl
    | none =>
      obtain ⟨t,_,obs⟩ := obstruction_of_uncovered rule q h
      exact False.elim (clean ⟨t,obs⟩)

end TetraStereo.Engine.RingActiveDistanceSchedule

assert_kernel_only TetraStereo.Engine.RingActiveDistanceSchedule.batch_at
assert_kernel_only TetraStereo.Engine.RingActiveDistanceSchedule.evaluate_eq
assert_kernel_only TetraStereo.Engine.RingActiveDistanceSchedule.unique

assert_kernel_only TetraStereo.Engine.RingActiveDistanceSchedule.obstruction_of_uncovered
assert_kernel_only TetraStereo.Engine.RingActiveDistanceSchedule.universal_iff_no_obstruction

assert_kernel_only TetraStereo.Engine.RingActiveDistanceSchedule.evaluate_cached

assert_kernel_only TetraStereo.Engine.RingActiveDistanceSchedule.table_shared
