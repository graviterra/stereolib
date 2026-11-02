import TetraStereo.Certificate.Dependency

set_option autoImplicit false

namespace TetraStereo.Certificate.Dependency
open OneCenter.DeclarativeCIP

universe u v w
variable {F : Type u} {O : Type v} {L : Type w}

/-- Reference indices are computed from earlier fact targets. -/
def producerReferences [DecidableEq O] (dependencies : O → List O)
    (facts : List (Fact O L)) (target : O) : List Nat :=
  (dependencies target).map (fun inner => (facts.map Prod.fst).idxOf inner)

/-- A proposed node recomputes the local step from exactly its indexed references. -/
def producerNode [DecidableEq O] (system : OccurrenceSystem F O L)
    (dependencies : O → List O) (facts : List (Fact O L)) (target : O) : Node O L :=
  let refs := producerReferences dependencies facts target
  { target := target, references := refs,
    outcome := system.executableStep (lookup (referenced facts refs)) target }

/-- Deterministic executable production along a supplied order. -/
def produceFrom [DecidableEq O] (system : OccurrenceSystem F O L)
    (dependencies : O → List O) (facts : List (Fact O L)) : List O → List (Node O L)
  | [] => []
  | target :: rest =>
      let node := producerNode system dependencies facts target
      node :: produceFrom system dependencies (facts ++ [(node.target, node.outcome)]) rest

def produce [DecidableEq O] (system : OccurrenceSystem F O L)
    (dependencies : O → List O) (order : List O) : List (Node O L) :=
  produceFrom system dependencies [] order

/-- Only dependency membership in the already visited prefix is assumed. -/
def PrefixReady (dependencies : O → List O) (known : List O) : List O → Prop
  | [] => True
  | target :: rest =>
      (∀ inner ∈ dependencies target, inner ∈ known) ∧
        PrefixReady dependencies (known ++ [target]) rest

/-! ### Reference-index arithmetic

The index a producer writes for an occurrence is the position of its first fact in the prefix. The
lemmas below record exactly what the checker needs: the indexed fact is the occurrence itself, the
indices of a duplicate-free dependency list are duplicate-free, and every index is in range. -/

/-- A present occurrence names a genuine fact at its own key position. -/
theorem exists_getElem?_idxOf_fact [DecidableEq O] {facts : List (Fact O L)} {inner : O}
    (present : inner ∈ facts.map Prod.fst) :
    ∃ fact : Fact O L, facts[(facts.map Prod.fst).idxOf inner]? = some fact ∧ fact.1 = inner := by
  have indexed : (facts.map Prod.fst)[(facts.map Prod.fst).idxOf inner]? = some inner :=
    List.getElem?_idxOf present
  have mapped : (facts[(facts.map Prod.fst).idxOf inner]?).map Prod.fst = some inner := by
    simpa only [List.getElem?_map] using indexed
  obtain ⟨fact, found, fst_eq⟩ := Option.map_eq_some_iff.mp mapped
  exact ⟨fact, found, fst_eq⟩

/-- A `filterMap` that returns every visited element unchanged is the identity. -/
theorem filterMap_eq_self_of {α : Type v} {f : α → Option α} {l : List α}
    (fixed : ∀ a ∈ l, f a = some a) : l.filterMap f = l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [List.filterMap_cons_some (fixed a (by simp))]
      rw [ih (fun b hb => fixed b (by simp [hb]))]

/-- Projecting the produced references onto occurrences recovers the dependency list exactly. -/
theorem map_fst_referenced_producerReferences [DecidableEq O]
    (dependencies : O → List O) (facts : List (Fact O L)) (target : O)
    (present : ∀ inner ∈ dependencies target, inner ∈ facts.map Prod.fst) :
    (referenced facts (producerReferences dependencies facts target)).map Prod.fst
      = dependencies target := by
  unfold producerReferences referenced
  rw [List.map_filterMap, List.filterMap_map]
  refine filterMap_eq_self_of ?_
  intro inner hin
  obtain ⟨fact, found, fst_eq⟩ := exists_getElem?_idxOf_fact (present inner hin)
  show (facts[(facts.map Prod.fst).idxOf inner]?).map Prod.fst = some inner
  rw [found, Option.map_some]
  exact congrArg some fst_eq

/-- Distinct occurrences get distinct key positions, prefix duplicates notwithstanding. -/
theorem producerReferences_nodup [DecidableEq O]
    (dependencies : O → List O) (facts : List (Fact O L)) (target : O)
    (nodup : (dependencies target).Nodup)
    (present : ∀ inner ∈ dependencies target, inner ∈ facts.map Prod.fst) :
    (producerReferences dependencies facts target).Nodup := by
  unfold producerReferences
  refine List.Nodup.map_on ?_ nodup
  intro inner hin inner' hin' equal
  exact (List.idxOf_inj (l := facts.map Prod.fst) (present inner hin)).mp equal

/-- Every produced reference is a valid index into the prefix. -/
theorem producerReferences_lt [DecidableEq O]
    (dependencies : O → List O) (facts : List (Fact O L)) (target : O)
    (present : ∀ inner ∈ dependencies target, inner ∈ facts.map Prod.fst) :
    ∀ index ∈ producerReferences dependencies facts target, index < facts.length := by
  intro index member
  unfold producerReferences at member
  obtain ⟨inner, hin, rfl⟩ := List.mem_map.mp member
  have bounded := List.idxOf_lt_length_of_mem (present inner hin)
  simpa using bounded

/-- The proposed node passes the structural reference checks and recomputes the local step. -/
theorem producerNode_valid [DecidableEq O]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (facts : List (Fact O L)) (target : O)
    (nodup : (dependencies target).Nodup)
    (present : ∀ inner ∈ dependencies target, inner ∈ facts.map Prod.fst) :
    ValidNode system dependencies facts (producerNode system dependencies facts target) := by
  refine ⟨producerReferences_nodup dependencies facts target nodup present,
    producerReferences_lt dependencies facts target present,
    map_fst_referenced_producerReferences dependencies facts target present, rfl⟩

/-! ### Production along an order

The producer is a plain fold over the requested order. The two facts the checker needs are recorded
below: one unfolding step, and the acceptance of the whole run. -/

/-- The proposed node carries the requested occurrence and its computed outcome. -/
theorem producerNode_target [DecidableEq O]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (facts : List (Fact O L)) (target : O) :
    (producerNode system dependencies facts target).target = target := rfl

/-- The proposed node evaluates the recovered dependency environment from the prefix. -/
theorem producerNode_outcome [DecidableEq O]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (facts : List (Fact O L)) (target : O) :
    (producerNode system dependencies facts target).outcome =
      system.executableStep
        (lookup (referenced facts (producerReferences dependencies facts target))) target := rfl

/-- One unfolding step of the producer. -/
theorem produceFrom_cons [DecidableEq O]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (facts : List (Fact O L)) (target : O) (rest : List O) :
    produceFrom system dependencies facts (target :: rest) =
      producerNode system dependencies facts target ::
        produceFrom system dependencies
          (facts ++ [(target, (producerNode system dependencies facts target).outcome)]) rest :=
  rfl

/-- The produced node list targets exactly the requested order, in order. -/
theorem produceFrom_targets [DecidableEq O]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (facts : List (Fact O L)) (order : List O) :
    (produceFrom system dependencies facts order).map (fun node => node.target) = order := by
  induction order generalizing facts with
  | nil => rfl
  | cons target rest ih =>
      rw [produceFrom_cons, List.map_cons,
        ih (facts ++ [(target, (producerNode system dependencies facts target).outcome)])]
      rfl

/-- The existing checker accepts the produced node list. The accepted facts are the prefix extended
by the produced outcomes, so the run adds exactly one fact per requested occurrence. -/
theorem produceFrom_checkFrom [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (facts : List (Fact O L)) (order : List O)
    (ready : PrefixReady dependencies (facts.map Prod.fst) order)
    (nodup : ∀ target ∈ order, (dependencies target).Nodup) :
    checkFrom system dependencies facts (produceFrom system dependencies facts order) =
      some (facts ++ (produceFrom system dependencies facts order).map
        (fun node => (node.target, node.outcome))) := by
  induction order generalizing facts with
  | nil => simp [produceFrom, checkFrom]
  | cons target rest ih =>
      obtain ⟨deps_present, rest_ready⟩ := ready
      have target_nodup : (dependencies target).Nodup := nodup target (by simp)
      have rest_nodup : ∀ occurrence ∈ rest, (dependencies occurrence).Nodup :=
        fun occurrence present => nodup occurrence (List.mem_cons_of_mem target present)
      have valid : ValidNode system dependencies facts
          (producerNode system dependencies facts target) :=
        producerNode_valid system dependencies facts target target_nodup deps_present
      have rest_ready' : PrefixReady dependencies
          ((facts ++ [(target,
            (producerNode system dependencies facts target).outcome)]).map Prod.fst) rest := by
        simpa only [List.map_append, List.map_cons, List.map_nil] using rest_ready
      have recursive := ih
        (facts ++ [(target, (producerNode system dependencies facts target).outcome)])
        rest_ready' rest_nodup
      simp only [produceFrom_cons, checkFrom, if_pos valid]
      rw [producerNode_target]
      rw [recursive]
      simp only [List.map_cons, List.append_assoc, List.singleton_append, producerNode_target]

/-- Projecting recorded facts onto occurrences forgets nothing about the node targets. -/
theorem map_nodes_fst_eq (nodes : List (Node O L)) :
    (nodes.map (fun node => (node.target, node.outcome))).map Prod.fst
      = nodes.map (fun node => node.target) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      rw [List.map_cons, List.map_cons, ih]
      rfl

/-- The accepted facts of a produced run are the prefix followed by exactly the requested order. -/
theorem produceFrom_result_targets [DecidableEq O]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (facts : List (Fact O L)) (order : List O) :
    (facts ++ (produceFrom system dependencies facts order).map
        (fun node => (node.target, node.outcome))).map Prod.fst
      = facts.map Prod.fst ++ order := by
  rw [List.map_append, map_nodes_fst_eq, produceFrom_targets]

/-- The empty-prefix run targets exactly the requested order, in order. -/
theorem produce_targets [DecidableEq O]
    (system : OccurrenceSystem F O L) (dependencies : O → List O) (order : List O) :
    (produce system dependencies order).map (fun node => node.target) = order :=
  produceFrom_targets system dependencies [] order

/-- The checker accepts the empty-prefix run under prefix readiness and duplicate-free dependencies. -/
theorem produce_check [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O) (order : List O)
    (ready : PrefixReady dependencies [] order)
    (nodup : ∀ target ∈ order, (dependencies target).Nodup) :
    check system dependencies (produce system dependencies order) =
      some ((produce system dependencies order).map
        (fun node => (node.target, node.outcome))) :=
  produceFrom_checkFrom system dependencies [] order ready nodup

/-- What the checker accepts for an empty-prefix run is exactly the requested order. -/
theorem produce_covers [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O) (order : List O)
    (ready : PrefixReady dependencies [] order)
    (nodup : ∀ target ∈ order, (dependencies target).Nodup) :
    (check system dependencies (produce system dependencies order)).map (List.map Prod.fst)
      = some order := by
  have accepted := produce_check system dependencies order ready nodup
  rw [accepted, Option.map_some, map_nodes_fst_eq, produce_targets]

/-- The recorded facts of an empty-prefix run have exactly the requested occurrence list. -/
theorem produce_result_targets [DecidableEq O]
    (system : OccurrenceSystem F O L) (dependencies : O → List O) (order : List O) :
    (((produce system dependencies order).map (fun node => (node.target, node.outcome))).map
        Prod.fst) = order := by
  rw [map_nodes_fst_eq, produce_targets]

/-- Produced outcomes carry evaluation certificates whenever the prefix does. -/
theorem produceFrom_certified [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (facts : List (Fact O L)) (order : List O)
    (ready : PrefixReady dependencies (facts.map Prod.fst) order)
    (nodup : ∀ target ∈ order, (dependencies target).Nodup)
    (certified : Certified system dependencies facts) :
    Certified system dependencies
      (facts ++ (produceFrom system dependencies facts order).map
        (fun node => (node.target, node.outcome))) :=
  checkFrom_certified system dependencies (produceFrom system dependencies facts order) facts _
    certified (produceFrom_checkFrom system dependencies facts order ready nodup)

/-- Every fact produced from the empty prefix is certified by the existing checker. -/
theorem produce_certified [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O) (order : List O)
    (ready : PrefixReady dependencies [] order)
    (nodup : ∀ target ∈ order, (dependencies target).Nodup) :
    Certified system dependencies
      ((produce system dependencies order).map (fun node => (node.target, node.outcome))) := by
  have accepted : checkFrom system dependencies [] (produce system dependencies order) =
      some ((produce system dependencies order).map
        (fun node => (node.target, node.outcome))) :=
    produce_check system dependencies order ready nodup
  exact checkFrom_certified system dependencies (produce system dependencies order) []
    ((produce system dependencies order).map (fun node => (node.target, node.outcome)))
    (by intro fact member; simp at member) accepted

/-- Under a well-founded dependency relation, every produced outcome is the actual solution value. -/
theorem produce_outcome_eq_solution [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O) (order : List O)
    (wellFounded : WellFounded (relation dependencies))
    (ready : PrefixReady dependencies [] order)
    (nodup : ∀ target ∈ order, (dependencies target).Nodup)
    (node : Node O L) (member : node ∈ produce system dependencies order) :
    node.outcome = system.buildOccurrenceState (relation dependencies) wellFounded node.target :=
  checked_outcome_eq_solution system dependencies wellFounded
    (produce system dependencies order)
    ((produce system dependencies order).map (fun node => (node.target, node.outcome)))
    (produce_check system dependencies order ready nodup) (node.target, node.outcome)
    (List.mem_map.mpr ⟨node, member, rfl⟩)

end TetraStereo.Certificate.Dependency
