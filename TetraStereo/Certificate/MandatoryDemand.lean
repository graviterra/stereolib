import TetraStereo.Certificate.WeightedDemandGraph

/-!
# Refusal from cycles of mandatory dependencies

Generic, chemistry-free refusal theory for the conservative demand graph of
`TetraStereo.Certificate.WeightedDemandGraph`.

A cursor `parent` has a mandatory dependency on `child` exactly when `Edge g parent child`, i.e.
`child` occurs among the ordinary children or callback references in `successors g parent`.  This
module assumes nothing about the graph besides that data: no finiteness, no proposed rank table, no
desired output and no acyclicity hypothesis enter the statements.

The only semantic input is `Propagates g Successful`: whenever `v` succeeds at budget `n`, every
mandatory dependency `w` succeeds at some strictly smaller budget `m < n`.  This is exactly the
local obligation that an actual evaluator must prove about itself; it is *not* derived here.

Under that interface:

* `success_path` / `success_transgen`: the success budget strictly decreases along dependency
  paths (non-strictly along reflexive-transitive paths, strictly along transitive paths);
* `not_successful_of_cycle`: a cursor on a nonempty mandatory cycle is unsuccessful at every
  budget (well-founded induction on the budget);
* `acyclic_of_all_successful`: simultaneous success of all requested roots forces the reachable
  mandatory graph to be acyclic;
* `exists_unsuccessful_of_not_acyclic` and `exists_unsuccessful_of_reachable_cycle`: dually, a
  cyclic reachable graph yields a requested root that is unsuccessful at every budget.

An Option-valued evaluator satisfying the same local demand obligation instantiates the interface
(`evaluator_propagates`, `evaluator_refusal_of_reachable_cycle`).  No declaration in this module
claims chemical nonexistence or unconditional acyclicity of an input graph: every acyclicity
conclusion is derived from the propagated-success hypothesis.
-/

set_option autoImplicit false

namespace TetraStereo.Certificate.WeightedDemand

/-- `Successful` propagates backwards along every mandatory demand edge: success at budget `n` needs
each mandatory dependency to be successful at some strictly smaller budget. -/
def Propagates {α : Type} (g : Graph α) (Successful : Nat → α → Prop) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃v : α⦄, Successful n v → ∀ w, Edge g v w →
    ∃ m, m < n ∧ Successful m w

/-! ## The budget decreases along dependency paths -/

/-- Along a reflexive-transitive dependency path the success budget can only decrease. -/
theorem success_path {α : Type} {g : Graph α} {Successful : Nat → α → Prop}
    (prop : Propagates g Successful) {v w : α} {n : Nat}
    (hsuccess : Successful n v) (path : Relation.ReflTransGen (Edge g) v w) :
    ∃ m, m ≤ n ∧ Successful m w := by
  induction path with
  | refl => exact ⟨n, Nat.le_refl n, hsuccess⟩
  | tail _ edge ih =>
      obtain ⟨m, bound, hm⟩ := ih
      obtain ⟨k, smaller, hk⟩ := prop hm _ edge
      exact ⟨k, Nat.le_trans (Nat.le_of_lt smaller) bound, hk⟩

/-- Along a nonempty dependency path the success budget strictly decreases. -/
theorem success_transgen {α : Type} {g : Graph α} {Successful : Nat → α → Prop}
    (prop : Propagates g Successful) {v w : α} {n : Nat}
    (hsuccess : Successful n v) (path : Relation.TransGen (Edge g) v w) :
    ∃ m, m < n ∧ Successful m w := by
  induction path with
  | single edge => exact prop hsuccess _ edge
  | tail _ edge ih =>
      obtain ⟨m, bound, hm⟩ := ih
      obtain ⟨k, smaller, hk⟩ := prop hm _ edge
      exact ⟨k, Nat.lt_trans smaller bound, hk⟩

/-- A nonempty mandatory cycle is refused at every budget.  Strong induction on the budget: one
traversal of the cycle strictly lowers the successful budget and therefore contradicts minimality. -/
theorem not_successful_of_cycle {α : Type} {g : Graph α} {Successful : Nat → α → Prop}
    (prop : Propagates g Successful) {cursor : α}
    (cycle : Relation.TransGen (Edge g) cursor cursor) :
    ∀ n, ¬ Successful n cursor := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hsuccess
      obtain ⟨m, smaller, hm⟩ := success_transgen prop hsuccess cycle
      exact ih m smaller hm

/-- A root cannot succeed at any budget when one of its dependencies lies on a mandatory cycle. -/
theorem not_successful_of_reachable_cycle {α : Type} {g : Graph α}
    {Successful : Nat → α → Prop} (prop : Propagates g Successful)
    {root cursor : α} (path : Relation.ReflTransGen (Edge g) root cursor)
    (cycle : Relation.TransGen (Edge g) cursor cursor) :
    ∀ n, ¬ Successful n root := by
  intro n hsuccess
  obtain ⟨m, _, hm⟩ := success_path prop hsuccess path
  exact not_successful_of_cycle prop cycle m hm

/-! ## Acyclicity and refusal for root lists -/

/-- Simultaneous success of every requested root forces the reachable mandatory-dependency graph to
be acyclic.  No finiteness, rank table or desired output is assumed. -/
theorem acyclic_of_all_successful {α : Type} {g : Graph α} {Successful : Nat → α → Prop}
    (prop : Propagates g Successful) {roots : List α}
    (success : ∀ root ∈ roots, ∃ n, Successful n root) :
    Acyclic g roots := by
  intro cursor reachable cycle
  obtain ⟨root, member, path⟩ := reachable
  obtain ⟨n, hn⟩ := success root member
  exact not_successful_of_reachable_cycle prop path cycle n hn

/-- Dual refusal form: if the reachable mandatory graph is cyclic, some requested root is
unsuccessful at every budget. -/
theorem exists_unsuccessful_of_not_acyclic {α : Type} {g : Graph α}
    {Successful : Nat → α → Prop} (prop : Propagates g Successful) {roots : List α}
    (notAcyclic : ¬ Acyclic g roots) :
    ∃ root ∈ roots, ∀ n, ¬ Successful n root := by
  classical
  refine Classical.byContradiction ?_
  intro absent
  apply notAcyclic
  apply acyclic_of_all_successful prop
  intro root member
  refine Classical.byContradiction ?_
  intro never
  exact absent ⟨root, member, fun n hn => never ⟨n, hn⟩⟩

/-- Concrete refusal certificate: a cycle at any reachable cursor refutes simultaneous success of
the root list.  This is the form an evaluator layer uses once discovery has reported a cycle. -/
theorem exists_unsuccessful_of_reachable_cycle {α : Type} {g : Graph α}
    {Successful : Nat → α → Prop} (prop : Propagates g Successful) {roots : List α}
    {cursor : α} (reachable : Reachable g roots cursor)
    (cycle : Relation.TransGen (Edge g) cursor cursor) :
    ∃ root ∈ roots, ∀ n, ¬ Successful n root := by
  obtain ⟨root, member, path⟩ := reachable
  exact ⟨root, member, fun n hn => not_successful_of_reachable_cycle prop path cycle n hn⟩

/-- A reachable mandatory cycle is exactly a witness that the root list is not acyclic. -/
theorem not_acyclic_of_reachable_cycle {α : Type} {g : Graph α} {roots : List α} {cursor : α}
    (reachable : Reachable g roots cursor)
    (cycle : Relation.TransGen (Edge g) cursor cursor) :
    ¬ Acyclic g roots :=
  fun acyclic => acyclic cursor reachable cycle

/-- Single-root form of `acyclic_of_all_successful`: success at any budget makes the mandatory
graph reachable from `root` acyclic. -/
theorem acyclic_singleton_of_successful {α : Type} {g : Graph α}
    {Successful : Nat → α → Prop} (prop : Propagates g Successful) {root : α}
    (success : ∃ n, Successful n root) :
    Acyclic g [root] := by
  apply acyclic_of_all_successful prop
  intro candidate member
  obtain rfl := List.mem_singleton.mp member
  exact success

/-! ## Option-valued evaluator interface -/

/-- An evaluator meets the propagation interface when a successful evaluation at budget `n` forces
every mandatory dependency to evaluate successfully at a strictly smaller budget.  The context and
value may change freely between the parent and the dependency. -/
theorem evaluator_propagates {α σ β : Type} {g : Graph α}
    (evaluate : Nat → σ → α → Option β)
    (demand : ∀ ⦃n : Nat⦄ ⦃context : σ⦄ ⦃v : α⦄ ⦃value : β⦄,
      evaluate n context v = some value → ∀ w, Edge g v w →
        ∃ m, m < n ∧ ∃ context' value', evaluate m context' w = some value') :
    Propagates g (fun n v => ∃ context value, evaluate n context v = some value) := by
  intro n v hsuccess w edge
  obtain ⟨context, value, computed⟩ := hsuccess
  exact demand computed w edge

/-- Evaluator-specific refusal: a reachable mandatory cycle makes some root return `none` at every
budget under every context. -/
theorem evaluator_refusal_of_reachable_cycle {α σ β : Type} {g : Graph α}
    (evaluate : Nat → σ → α → Option β)
    (demand : ∀ ⦃n : Nat⦄ ⦃context : σ⦄ ⦃v : α⦄ ⦃value : β⦄,
      evaluate n context v = some value → ∀ w, Edge g v w →
        ∃ m, m < n ∧ ∃ context' value', evaluate m context' w = some value')
    {roots : List α} {cursor : α} (reachable : Reachable g roots cursor)
    (cycle : Relation.TransGen (Edge g) cursor cursor) :
    ∃ root ∈ roots, ∀ n, ¬ ∃ context value, evaluate n context root = some value :=
  exists_unsuccessful_of_reachable_cycle (evaluator_propagates evaluate demand) reachable cycle

/-- Simultaneous-evaluation form: universal evaluator success on the roots forces acyclicity. -/
theorem evaluator_acyclic_of_all_successful {α σ β : Type} {g : Graph α}
    (evaluate : Nat → σ → α → Option β)
    (demand : ∀ ⦃n : Nat⦄ ⦃context : σ⦄ ⦃v : α⦄ ⦃value : β⦄,
      evaluate n context v = some value → ∀ w, Edge g v w →
        ∃ m, m < n ∧ ∃ context' value', evaluate m context' w = some value')
    {roots : List α}
    (success : ∀ root ∈ roots, ∃ n context value, evaluate n context root = some value) :
    Acyclic g roots := by
  apply acyclic_of_all_successful (evaluator_propagates evaluate demand)
  intro root member
  exact success root member

end TetraStereo.Certificate.WeightedDemand
