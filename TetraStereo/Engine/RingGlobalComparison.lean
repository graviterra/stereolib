import TetraStereo.Engine.RingSphereStore
import Batteries.Tactic.OpenPrivate

/-! Whole-graph transfer from molecular observations on the native, reachable
readers. The alternative computes its own stores. Every prefix is an equality
of actual lists, including the order, multiplicity and values of all rows. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingGlobalComparison
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (View Rule Cell height distance frozen)
open RingPyramidalPublication (publish eligible)
open RingSphereQueue (reader stored viewOf)
open private reads_at from TetraStereo.Engine.RingEligibleGraph

abbrev queue (i : Input) (a : i.certified.Atom) := RingEligibleGraph.queue i (eligible i) a

/-- The call made at a committed sphere or at the concluding root read. -/
def Called (i : Input) (a : i.certified.Atom) (k : Nat) (q : Site i) : Prop :=
  (k < height i + 1 ∧ q ∈ queue i a (height i - k)) ∨
  (k = height i + 1 ∧ q = RingGroupedReport.origin i a)

def prior (i : Input) (a : i.certified.Atom) (k : Nat) : View i :=
  reader a (viewOf (RingSphereStore.rows i a k))

/-- Every actual call reads exactly the native frozen store for its occurrence. -/
theorem prior_exact {i : Input} {a : i.certified.Atom} {k : Nat} {q : Site i}
    (called : Called i a k q) :
    prior i a k = frozen (RingChemicalGraphProof.state i) q := by
  unfold prior RingSphereStore.rows
  rw [RingSphereQueue.stored_eq]
  let inv := RingEligibleGraph.inventory i (eligible i) a
  have skip := RingChemicalGraphProof.skips i
  rcases called with ⟨lt,mem⟩ | ⟨rfl,rfl⟩
  · obtain ⟨cand,dep⟩ := (inv _ q).mp mem
    apply reads_at skip (d := height i - k) _ cand.1 dep
    intro t
    rw [RingEligibleGraph.run_exact skip inv k (by omega)]
    have condition : (height i < distance t + k) ↔ height i - k < distance t := by omega
    simp only [condition]
  · apply reads_at skip (focus := RingGroupedReport.origin i a) (root := a) (d := 0) _ rfl rfl
    intro t
    rw [RingEligibleGraph.run_exact skip inv _ (by omega)]
    by_cases c : RingEligibleGraph.candidate (eligible i) a t
    · have pos : 0 < distance t := by
        by_contra! h
        have addr : t.val.address = [] := List.length_eq_zero_iff.mp (by change distance t = 0; omega)
        have atRoot := RingGroupedReport.origin_unique t addr
        exact c.2.1 (by rw [←c.1]; exact (congrArg (fun u : Site i => u.val.node.current?) atRoot).trans rfl)
      simp [c,pos,show height i < distance t + (height i + 1) by omega]
    · simp [c]

/-- A projection and interpreter, shared across all roots, queues and request lists. -/
structure Interface (i : Input) where
  Data : Site i → Type
  native : ∀ q, View i → Data q
  interpret : ∀ q, Data q → Cell
  reachable : ∀ q, interpret q (native q (frozen (RingChemicalGraphProof.state i) q)) =
    publish i q (frozen (RingChemicalGraphProof.state i) q)

variable {i : Input} (p : Interface i)
abbrev Source := ∀ q : Site i, View i → p.Data q

def rule (source : Source p) : Rule i := fun q r => p.interpret q (source q r)

def rows (source : Source p) (a : i.certified.Atom) (k : Nat) :=
  stored (rule p source) a (queue i a) (height i) k

def root (source : Source p) (a : i.certified.Atom) :=
  rule p source (RingGroupedReport.origin i a) (reader a (viewOf (rows p source a (height i+1))))

/-- Disagreement is tested on a complete native prefix, before either calculation
publishes the next sphere. It is independent of equality of any assigned labels. -/
def Difference (source : Source p) (a : i.certified.Atom) (k : Nat) (q : Site i) : Prop :=
  Called i a k q ∧ rows p source a k = RingSphereStore.rows i a k ∧
    rule p source q (prior i a k) ≠ publish i q (prior i a k) ∧
    source q (prior i a k) ≠ p.native q (prior i a k)

private theorem one {source : Source p} {a : i.certified.Atom} {k : Nat} {q : Site i}
    (call : Called i a k q) (same : source q (prior i a k) = p.native q (prior i a k)) :
    rule p source q (prior i a k) = publish i q (prior i a k) := by
  rw [rule,same,prior_exact call]
  exact p.reachable q

/-- The first divergent materialized sphere contains a comparison-data disagreement
while reading identical complete prior stores. -/
theorem rows_or_difference (source : Source p) (a : i.certified.Atom) (k : Nat) (bound : k ≤ height i+1) :
    rows p source a k = RingSphereStore.rows i a k ∨ ∃ n < k, ∃ q, Difference p source a n q := by
  classical
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rcases ih (by omega) with prev | ⟨n,lt,q,found⟩
    · by_cases agree : ∀ q ∈ queue i a (height i-k), rule p source q (prior i a k) = publish i q (prior i a k)
      · left
        change (_ ++ rows p source a k) = (_ ++ RingSphereStore.rows i a k)
        rw [prev]
        apply congrArg (· ++ RingSphereStore.rows i a k)
        apply List.map_congr_left
        intro q h
        change (_,rule p source q (reader a (viewOf (rows p source a k)))) = (_,publish i q (prior i a k))
        rw [prev]
        exact congrArg (fun v => (q,v)) (agree q h)
      · push_neg at agree
        obtain ⟨q,h,bad⟩ := agree
        have call : Called i a k q := Or.inl ⟨by omega,h⟩
        exact Or.inr ⟨k,by omega,q,call,prev,bad,fun equal => bad (one p call equal)⟩
    · exact Or.inr ⟨n,by omega,q,found⟩

/-- A different native root has a local comparison-data witness on the same
molecular root, on exactly matching previously committed rows. -/
theorem root_disagreement (source : Source p) (a : i.certified.Atom)
    (bad : root p source a ≠ RingChemicalGraphProof.root i a) :
    ∃ k ≤ height i+1, ∃ q, Difference p source a k q := by
  classical
  rcases rows_or_difference p source a _ (Nat.le_refl (height i+1)) with eqn | ⟨n,lt,q,h⟩
  · let q := RingGroupedReport.origin i a
    have call : Called i a (height i+1) q := Or.inr ⟨rfl,rfl⟩
    have different : rule p source q (prior i a (height i+1)) ≠ publish i q (prior i a (height i+1)) := by
      intro same
      apply bad
      unfold root
      rw [eqn]
      change rule p source q (prior i a (height i+1)) = _
      rw [same,prior_exact call,←RingChemicalGraphProof.state_eq]
      exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a).symm
    exact ⟨_,le_rfl,q,call,eqn,different,fun equal => different (one p call equal)⟩
  · exact ⟨n,lt.le,q,h⟩

def report (source : Source p) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (root p source a).map fun v => (a.val,v)

/-- Any report mismatch has a comparison witness at one of the requested
roots, whether a row changes hand, changes case, refuses, or fails. -/
theorem report_disagreement (source : Source p) (atoms : List i.certified.Atom)
    (different : report p source atoms ≠ RingChemicalReport.report? i atoms) :
    ∃ a ∈ atoms, ∃ k ≤ height i + 1, ∃ q, Difference p source a k q := by
  classical
  by_contra! no
  apply different
  apply RingFrameTransport.mapM_congr_mem
  intro a mem
  apply congrArg (Option.map (fun v => (a.val,v)))
  by_contra wrong
  obtain ⟨k,bound,q,found⟩ := root_disagreement p source a wrong
  exact no a mem k bound q found

end TetraStereo.Engine.RingGlobalComparison
assert_kernel_only TetraStereo.Engine.RingGlobalComparison.rows_or_difference
assert_kernel_only TetraStereo.Engine.RingGlobalComparison.report_disagreement
