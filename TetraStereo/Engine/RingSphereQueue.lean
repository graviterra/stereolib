import TetraStereo.Engine.RingGeometryCriterion

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereQueue
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View Rule distance height frozen sites evaluate)

/-- A separate store for one original root. All its unwritten nodes initially have
no descriptor. A query outside the original digraph is unavailable. -/
def reader {i : Input} (root : i.certified.Atom) (store : View i) : View i :=
  fun q => if q.val.root = root then store q else none

/-- The auxiliary inventory excludes the original atom and occurrences that do
not denote real tetrahedral centres. The original root is evaluated last. -/
def candidate {i : Input} (root : i.certified.Atom) (q : Site i) : Prop :=
  q.val.root = root ∧ q.val.node.current? ≠ some root ∧
    (i.certified.localizedOccurrenceDescriptorCenter? q).isSome = true

instance {i : Input} (root : i.certified.Atom) (q : Site i) : Decidable (candidate root q) := by
  unfold candidate
  infer_instance

/-- Characterize the complete single-focus auxiliary inventory directly on
the molecular graph. The same physical atom may occur at several addresses. -/
theorem candidate_iff {i : Input} (root : i.certified.Atom) (q : Site i) :
    candidate root q ↔ q.val.root = root ∧ q.val.node.provenance = .realAtom ∧
      ∃ a : i.certified.Atom, q.val.node.current? = some a ∧ a ≠ root ∧
        Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
  constructor
  · rintro ⟨on,other,seen⟩
    obtain ⟨c,found⟩ := Option.isSome_iff_exists.mp seen
    obtain ⟨real,current⟩ := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp found
    exact ⟨on,real,c.val,current,fun h => other (current.trans (congrArg some h)),
      (i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property⟩
  · rintro ⟨on,real,a,current,other,four⟩
    let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
    exact ⟨on,fun h => other (Option.some.inj (current.symm.trans h)),
      Option.isSome_iff_exists.mpr ⟨c,(i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨real,current⟩⟩⟩

/-- Queue all results using the old store, then commit. Lookup preserves an actual
failed evaluation as well as an examined centre with no assignment. -/
def commit {i : Input} (rule : Rule i) (root : i.certified.Atom) (before : View i)
    (queue : List (Site i)) : View i :=
  let pending := queue.map fun q => (q, rule q (reader root before))
  fun q => ((pending.find? (fun row => decide (row.1 = q))).map Prod.snd).getD (before q)

private theorem lookup {i : Input} (rule : Rule i) (root : i.certified.Atom) (before : View i)
    (queue : List (Site i)) (q : Site i) :
    commit rule root before queue q = if q ∈ queue then rule q (reader root before) else before q := by
  induction queue with
  | nil => rfl
  | cons x xs ih =>
    by_cases same : x = q
    · subst x; simp [commit]
    · simpa only [commit,List.map_cons,List.find?_cons,same,decide_false,cond_false,
        List.mem_cons,Ne.symm same,false_or] using ih

/-- A batch enumeration may use any order. Its membership law is the sole
inventory requirement; even repeated visits within a batch are harmless. -/
def Inventory {i : Input} (root : i.certified.Atom) (queue : Nat → List (Site i)) : Prop :=
  ∀ d q, q ∈ queue d ↔ candidate root q ∧ distance q = d

def molecularQueue (i : Input) (root : i.certified.Atom) (d : Nat) : List (Site i) :=
  (sites i).filter fun q => decide (candidate root q ∧ distance q = d)

theorem inventory (i : Input) (root : i.certified.Atom) : Inventory root (molecularQueue i root) := by
  intro d q
  have mem : q ∈ sites i := List.mem_attach ..
  simp [molecularQueue,mem]

def run {i : Input} (rule : Rule i) (root : i.certified.Atom) (queue : Nat → List (Site i)) :
    Nat → View i
  | 0 => fun _ => some none
  | k + 1 => commit rule root (run rule root queue k) (queue (height i - k))

/-- Structural noncentres never publish a descriptor, independently of the store. -/
def SkipsNoncentres {i : Input} (rule : Rule i) : Prop :=
  ∀ q read, i.certified.localizedOccurrenceDescriptorCenter? q = none → rule q read = some none

private theorem reads_at {i : Input} {rule : Rule i} (skip : SkipsNoncentres rule)
    {root : i.certified.Atom} {store : View i} {d : Nat}
    (before : ∀ q, store q = if candidate root q ∧ d < distance q then evaluate rule q else some none)
    {focus : Site i} (on : focus.val.root = root) (atDepth : distance focus = d) :
    reader root store = frozen (evaluate rule) focus := by
  funext q
  by_cases here : q.val.root = root
  · by_cases original : q.val.node.current? = some root
    · simp [reader,here,before,candidate,original,frozen,on]
    · cases found : i.certified.localizedOccurrenceDescriptorCenter? q with
      | none =>
        have empty : evaluate rule q = some none :=
          (RingActiveDistanceSchedule.evaluate_eq rule q).trans (skip q _ found)
        simp [reader,here,before,candidate,original,found,frozen,on,empty]
      | some c => simp [reader,here,before,candidate,original,found,frozen,on,atDepth]
  · simp [reader,here,frozen,on]

/-- Exact snapshot after *every* batch for any local rule. The operational
reader never consults distance, eligibility, or a publication-table oracle. -/
theorem run_exact {i : Input} {rule : Rule i} (skip : SkipsNoncentres rule)
    {root : i.certified.Atom} {queue : Nat → List (Site i)} (listed : Inventory root queue)
    (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    run rule root queue k q =
      if candidate root q ∧ height i < distance q + k then evaluate rule q else some none := by
  induction k generalizing q with
  | zero =>
    have upper := RingActiveDistanceSchedule.distance_bound q
    simp [run,Nat.not_lt.mpr upper]
  | succ k ih =>
    have le : k ≤ height i := by omega
    have old (t : Site i) := ih (by omega) t
    simp only [run,lookup,listed (height i - k) q]
    by_cases hit : candidate root q ∧ distance q = height i - k
    · rw [if_pos hit,if_pos ⟨hit.1,by omega⟩]
      rw [reads_at skip (focus := q) (root := root) (store := run rule root queue k) (fun t => by
        rw [old]; have eqn : (height i < distance t + k) ↔ height i - k < distance t := by omega
        simp only [eqn]) hit.1.1 hit.2]
      exact (RingActiveDistanceSchedule.evaluate_eq rule q).symm
    · rw [if_neg hit,old]
      by_cases keep : candidate root q
      · have ne : distance q ≠ height i - k := fun h => hit ⟨keep,h⟩
        have eqn : (height i < distance q + k) ↔ height i < distance q + (k+1) := by omega
        simp only [eqn]
      · simp [keep]

/-- Run the auxiliary queue and evaluate the original atom on the committed store. -/
def finalCell {i : Input} (rule : Rule i) (root : i.certified.Atom) (queue : Nat → List (Site i)) : Cell :=
  rule (RingGroupedReport.origin i root) (reader root (run rule root queue (height i + 1)))

/-- Materialize each queued result once. A missing address initially carries
no descriptor; a stored evaluation failure keeps its outer `none`. -/
def viewOf {i : Input} (rows : List (Site i × Cell)) (q : Site i) : Cell :=
  ((rows.find? (fun row => decide (row.1 = q))).map Prod.snd).getD (some none)

/-- Materialize the first `k` batches so several ligand comparisons can read the same cells. -/
def stored {i : Input} (rule : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) (top : Nat) : Nat → List (Site i × Cell)
  | 0 => []
  | k+1 =>
    let previous := stored rule root queue top k
    let read := reader root (viewOf previous)
    (queue (top - k)).map (fun q => (q,rule q read)) ++ previous

/-- Every lookup in the materialized table equals the sphere procedure after the same batches. -/
theorem stored_eq {i : Input} (rule : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) (k : Nat) :
    viewOf (stored rule root queue (height i) k) = run rule root queue k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext q
    simp only [stored,run,commit,← ih,viewOf,List.find?_append]
    have first (a b : Option (Site i × Cell)) : ((a.or b).map Prod.snd).getD (some none) =
        (a.map Prod.snd).getD ((b.map Prod.snd).getD (some none)) := by cases a <;> rfl
    exact first _ _

private def storedFinal {i : Input} (rule : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) : Cell :=
  let top := height i
  let rows := stored rule root queue top (top+1)
  rule (RingGroupedReport.origin i root) (reader root (viewOf rows))

@[csimp] theorem final_stored : @finalCell = @storedFinal := by
  funext i rule root queue
  simp only [finalCell,storedFinal,stored_eq]

theorem final_exact {i : Input} {rule : Rule i} (skip : SkipsNoncentres rule)
    {root : i.certified.Atom} {queue : Nat → List (Site i)} (listed : Inventory root queue) :
    finalCell rule root queue = evaluate rule (RingGroupedReport.origin i root) := by
  have positive {q : Site i} (h : candidate root q) : 0 < distance q := by
    by_contra! zero
    have empty : q.val.address = [] := List.length_eq_zero_iff.mp (by change distance q = 0; omega)
    have same := RingGroupedReport.origin_unique q empty
    exact h.2.1 (by rw [← h.1]; exact (congrArg (fun t : Site i => t.val.node.current?) same).trans rfl)
  unfold finalCell
  rw [reads_at skip (focus := RingGroupedReport.origin i root) (root := root)
    (store := run rule root queue (height i + 1)) (d := 0) (fun t => by
    rw [run_exact skip listed _ (by omega)]
    by_cases cand : candidate root t
    · simp [cand,positive cand,show height i < distance t + (height i+1) by omega]
    · simp [cand]) rfl rfl]
  exact (RingActiveDistanceSchedule.evaluate_eq rule _).symm

theorem grouped_skips (i : Input) : SkipsNoncentres (RingGroupedPublication.publish? i) := by
  intro q read no
  simp [RingGroupedPublication.publish?,RingGroupedPublication.certify?,no]

/-- Exact public root output, including casing, refusal and coverage. -/
theorem grouped_root {i : Input} {root : i.certified.Atom} {queue : Nat → List (Site i)}
    (listed : Inventory root queue) :
    finalCell (RingGroupedPublication.publish? i) root queue =
      RingGroupedPublication.state i (RingGroupedReport.origin i root) := by
  rw [final_exact (grouped_skips i) listed]
  exact congrFun (RingActiveDistanceSchedule.snapshot_table ..).symm _

/-- If two local procedures produce different stores, a real queued occurrence
already distinguishes them on a literally identical prior store. -/
private theorem first_batch {i : Input} (source baseline : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) (k : Nat)
    (diff : run source root queue k ≠ run baseline root queue k) :
    ∃ n < k, ∃ q ∈ queue (height i - n),
      run source root queue n = run baseline root queue n ∧
      source q (reader root (run source root queue n)) ≠ baseline q (reader root (run source root queue n)) := by
  classical
  induction k with
  | zero => exact False.elim (diff rfl)
  | succ n ih =>
    by_cases same : run source root queue n = run baseline root queue n
    · by_contra! no
      apply diff
      funext q
      rw [run,run,lookup,lookup,← same]
      by_cases member : q ∈ queue (height i - n)
      · simpa only [if_pos member] using no n (Nat.lt_succ_self n) q member same
      · simp [member]
    · obtain ⟨m,smaller,q,queued,before,unequal⟩ := ih same
      exact ⟨m,Nat.lt_succ_of_lt smaller,q,queued,before,unequal⟩

/-- Any disagreement at the public root localizes to one comparison of local
procedures on a shared physical store. The alternative supplies its own rule
and builds its own auxiliary state; no agreement of recursive outputs is assumed. -/
theorem disagreement {i : Input} (source : Rule i) {root : i.certified.Atom}
    {queue : Nat → List (Site i)} (listed : Inventory root queue)
    (diff : finalCell source root queue ≠ RingGroupedPublication.state i (RingGroupedReport.origin i root)) :
    ∃ n ≤ height i + 1, ∃ q : Site i,
      ((n = height i + 1 ∧ q = RingGroupedReport.origin i root) ∨
       (n < height i + 1 ∧ candidate root q ∧ distance q = height i - n)) ∧
      run source root queue n = run (RingGroupedPublication.publish? i) root queue n ∧
      source q (reader root (run source root queue n)) ≠
        RingGroupedPublication.publish? i q (reader root (run source root queue n)) := by
  classical
  let baseline := RingGroupedPublication.publish? i
  let k := height i + 1
  by_cases same : run source root queue k = run baseline root queue k
  · refine ⟨k,le_rfl,_,Or.inl ⟨rfl,rfl⟩,same,?_⟩
    intro equal
    apply diff
    rw [← grouped_root listed]
    exact equal.trans (congrArg (fun store => baseline (RingGroupedReport.origin i root) (reader root store)) same)
  · obtain ⟨n,prior,q,member,before,unequal⟩ := first_batch source baseline root queue k same
    exact ⟨n,prior.le,q,Or.inr ⟨prior,(listed _ q).mp member⟩,before,unequal⟩

section ConstitutionalGate
open RingNestedActivePair (Frame)
open RingActivePairReport (Slot)
open RingGroupedCentre (Arms)
open RingGeometryCriterion (Signature)
attribute [local instance] lexOrd

private def constitutional {i f} (fr : Frame i f) (s : Slot) :=
  RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor (fr.direction s))



def early? (i : Input) (q : Site i) : Option Signature := do
  let fr ← RingNestedActivePair.frame? i q
  let parity := RingOrientation.orientation (constitutional fr)
  if parity = 0 then none else some ⟨RingOrientation.baseline fr * parity,0⟩

private theorem strict_comparison {i f fr read} (a : @Arms i f fr read)
    (strict : Function.Injective (constitutional fr)) (rev : Bool) (j k : Slot) :
    compare (a.key rev j) (a.key rev k) = compare (constitutional fr j) (constitutional fr k) := by
  by_cases same : j = k
  · subst k; simp
  · have differ := strict.ne same
    have firstKey (s : Slot) : (a.key rev s).1 = constitutional fr s := by
      cases rev
      · exact a.constitution false s
      · exact a.constitution true s
    change (compare (a.key rev j).1 (a.key rev k).1).then _ = _
    rw [firstKey,firstKey]
    cases order : compare (constitutional fr j) (constitutional fr k) with
    | lt | gt => rfl
    | eq => exact (differ (Std.compare_eq_eq_iff_eq.mp order)).elim

private theorem strict_signature {i f fr read} (a : @Arms i f fr read)
    (strict : Function.Injective (constitutional fr)) :
    RingOrientation.index a = RingOrientation.orientation (constitutional fr) ∧
    RingGeometryCriterion.reversals a = 0 := by
  have no : RingGroupedOrders.marks a = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j member
    obtain ⟨k,ne,tie⟩ := (RingGroupedOrders.marked_iff a j false).mp member
    exact ne (strict (Std.compare_eq_eq_iff_eq.mp (by rw [← strict_comparison a strict false j k,tie]; simp)))
  constructor
  · simp only [RingOrientation.index,no,List.length_nil,show 0 < 3 by decide,if_true]
    unfold RingOrientation.orientation
    simp only [strict_comparison a strict]
  · unfold RingGeometryCriterion.reversals
    simp [strict_comparison a strict]

/-- Every constitutional early exit agrees with the full molecular publication
at that occurrence, even when other occurrences depend on stereo rules. -/
theorem early_exact {i : Input} (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {sig : Signature} (hit : early? i q = some sig) :
    RingGroupedPublication.state i q = some sig.letters := by
  unfold early? at hit
  obtain ⟨fr,hf,tail⟩ := Option.bind_eq_some_iff.mp hit
  dsimp only at tail
  split at tail
  · contradiction
  rename_i nonzero
  obtain rfl := Option.some.inj tail
  have strict : Function.Injective (constitutional fr) := by
    by_contra h
    exact nonzero ((RingOrientation.orientation_zero _).mpr h)
  obtain ⟨s,found,issued,_⟩ := RingGeometryCriterion.at_centre coord q fr.recognized
  rw [RingGeometryCriterion.state_eq coord] at found
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (RingGroupedCentre.arms_ready fr
    (RingGroupedPublication.ready (RingGroupedGeometry.physical coord) q))
  have h := strict_signature a strict
  simp [RingGeometryCriterion.signature?,hf,ha,h.1,h.2] at found
  exact found.symm ▸ issued

/-- Skip the sparse auxiliary pass completely at a constitutionally strict
root; otherwise run the molecular inventory and commit equal distances together. -/
def stagedRoot (i : Input) (root : i.certified.Atom) : Cell :=
  match early? i (RingGroupedReport.origin i root) with
  | some s => some s.letters
  | none => finalCell (RingGroupedPublication.publish? i) root (molecularQueue i root)

theorem staged_exact (i : Input) (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) :
    stagedRoot i root = RingGroupedPublication.state i (RingGroupedReport.origin i root) := by
  unfold stagedRoot
  cases found : early? i (RingGroupedReport.origin i root) with
  | none => exact grouped_root (inventory i root)
  | some s => exact (early_exact coord found).symm

/-- The staged algorithm may evaluate each requested root independently. -/
def stagedReport (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (stagedRoot i a).map fun v => (a.val,v)

theorem staged_report_exact (i : Input) (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : stagedReport i atoms = RingGroupedReport.forAtoms? i atoms := by
  unfold stagedReport
  simp only [staged_exact i coord]
  rfl

end ConstitutionalGate

end TetraStereo.Engine.RingSphereQueue

assert_kernel_only TetraStereo.Engine.RingSphereQueue.run_exact
assert_kernel_only TetraStereo.Engine.RingSphereQueue.final_exact
assert_kernel_only TetraStereo.Engine.RingSphereQueue.grouped_root
assert_kernel_only TetraStereo.Engine.RingSphereQueue.disagreement
assert_kernel_only TetraStereo.Engine.RingSphereQueue.early_exact
assert_kernel_only TetraStereo.Engine.RingSphereQueue.staged_report_exact
assert_kernel_only TetraStereo.Engine.RingSphereQueue.candidate_iff
