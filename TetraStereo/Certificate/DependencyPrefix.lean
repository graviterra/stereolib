import TetraStereo.Certificate.DependencyProducer

set_option autoImplicit false
namespace TetraStereo.Certificate.Dependency
open OneCenter.DeclarativeCIP OneCenter.DeclarativeCIP.OccurrenceScheduler
universe u v w
variable {F : Type u} {O : Type v} {L : Type w}

/-- A finite causal proof agrees with any local fixed state. No complete prefix or
well-foundedness premise is needed: the certificate itself supplies the induction. -/
theorem certificate_outcome_eq_of_fixed
    (system : OccurrenceSystem F O L) (dependency : O → O → Prop)
    (state : OccurrenceState O L)
    (locality : system.EvaluatorLocalFor dependency)
    (fixed : ∀ target, system.executableStep state target = state target)
    (target : O) (outcome : Option L)
    (certificate : EvaluationCertificate system dependency target outcome) :
    outcome = state target := by
  induction certificate with
  | node current outcomes certificates computed ih =>
      apply computed.trans
      apply Eq.trans _ (fixed current)
      apply locality
      intro inner depends
      simpa [OccurrenceSystem.dependencyEnvironment, depends] using ih inner depends

/-- Every fact in an accepted partial prefix agrees with the fixed state, including an
explicitly certified absent label. -/
theorem checked_fact_eq_of_fixed [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (state : OccurrenceState O L)
    (locality : system.EvaluatorLocalFor (relation dependencies))
    (fixed : ∀ target, system.executableStep state target = state target)
    (nodes : List (Node O L)) (facts : List (Fact O L))
    (accepted : check system dependencies nodes = some facts)
    (fact : Fact O L) (present : fact ∈ facts) : fact.2 = state fact.1 := by
  obtain ⟨certificate⟩ := check_sound system dependencies nodes facts accepted fact present
  exact certificate_outcome_eq_of_fixed system (relation dependencies) state locality fixed _ _ certificate

/-- Lookup is justified only for a listed fact. An absent entry cannot masquerade as a
verified `none`; duplicate accepted facts are harmless because all agree with the same state. -/
theorem checked_lookup_eq_of_fixed [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (state : OccurrenceState O L)
    (locality : system.EvaluatorLocalFor (relation dependencies))
    (fixed : ∀ target, system.executableStep state target = state target)
    (nodes : List (Node O L)) (facts : List (Fact O L))
    (accepted : check system dependencies nodes = some facts)
    (target : O) (present : target ∈ facts.map Prod.fst) : lookup facts target = state target := by
  obtain ⟨certificate⟩ := lookup_certified system dependencies facts
    (check_sound system dependencies nodes facts accepted) target present
  exact certificate_outcome_eq_of_fixed system (relation dependencies) state locality fixed _ _ certificate

/-- Stopping a ready schedule early preserves readiness of every visited node. -/
theorem PrefixReady.take (dependencies : O → List O) (n : Nat) :
    ∀ known order, PrefixReady dependencies known order →
      PrefixReady dependencies known (order.take n) := by
  induction n with
  | zero => intros; trivial
  | succ n ih =>
      intro known order ready
      cases order with
      | nil => trivial
      | cons target rest =>
          exact ⟨ready.1, ih (known ++ [target]) rest ready.2⟩

/-- A ready schedule provides all dependencies before the target's position. -/
theorem PrefixReady.dependencies_mem_prefix
    (dependencies : O → List O) (pre : List O) :
    ∀ known target rest,
      PrefixReady dependencies known (pre ++ target :: rest) →
      ∀ source ∈ dependencies target, source ∈ known ++ pre := by
  induction pre with
  | nil =>
      intro known target rest ready source present
      simpa using ready.1 source present
  | cons first pre ih =>
      intro known target rest ready source present
      have found := ih (known ++ [first]) target rest ready.2 source present
      simpa only [List.append_assoc, List.singleton_append] using found

/-- Split a finite order immediately before the first occurrence of a known target. -/
theorem split_at_idxOf [DecidableEq O] (target : O) :
    ∀ order : List O, target ∈ order →
      ∃ rest, order = order.take (order.idxOf target) ++ target :: rest
  | [], present => by simp at present
  | first :: rest, present => by
      by_cases same : first = target
      · subst first
        exact ⟨rest, by simp⟩
      · have inside : target ∈ rest := by simpa [Ne.symm same] using present
        obtain ⟨tail, split⟩ := split_at_idxOf target rest inside
        refine ⟨tail, ?_⟩
        simpa [List.idxOf_cons, same, Ne.symm same] using congrArg (List.cons first) split

/-- Fix the equality instance used to locate the target throughout the generic prefix API. -/
def prefixBeforeTarget [DecidableEq O] (order : List O) (target : O) : List O :=
  order.take (order.idxOf target)

/-- The prefix contains every dependency and omits the target itself when the order has
unique targets. It can therefore justify evaluation without already containing the answer. -/
theorem prefix_before_target [DecidableEq O]
    (dependencies : O → List O) (order : List O) (target : O)
    (ready : PrefixReady dependencies [] order) (distinct : order.Nodup)
    (present : target ∈ order) :
    (∀ source ∈ dependencies target, source ∈ order.take (order.idxOf target)) ∧
      target ∉ order.take (order.idxOf target) := by
  obtain ⟨rest, split⟩ := split_at_idxOf target order present
  constructor
  · intro source depends
    have readySplit := ready
    rw [split] at readySplit
    simpa using PrefixReady.dependencies_mem_prefix dependencies
      (order.take (order.idxOf target)) [] target rest readySplit source depends
  · intro included
    have nodupSplit := distinct
    rw [split] at nodupSplit
    exact (List.nodup_append.mp nodupSplit).2.2 target included target (by simp) rfl

/-- Checked selected dependency facts agree with a fixed state wherever the selected list
contains an explicit fact. -/
theorem checked_referenced_lookup_eq_of_fixed [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (state : OccurrenceState O L)
    (locality : system.EvaluatorLocalFor (relation dependencies))
    (fixed : ∀ target, system.executableStep state target = state target)
    (nodes : List (Node O L)) (facts : List (Fact O L))
    (accepted : check system dependencies nodes = some facts)
    (indices : List Nat) (target : O)
    (present : target ∈ (referenced facts indices).map Prod.fst) :
    lookup (referenced facts indices) target = state target := by
  obtain ⟨certificate⟩ := lookup_certified system dependencies (referenced facts indices)
    (referenced_certified system dependencies facts indices
      (check_sound system dependencies nodes facts accepted)) target present
  exact certificate_outcome_eq_of_fixed system (relation dependencies) state locality fixed _ _ certificate

/-- Replay concatenation continues from exactly the checked prefix facts. -/
theorem checkFrom_append [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (earlier suffix : List (Node O L)) : ∀ facts,
    checkFrom system dependencies facts (earlier ++ suffix) =
      (checkFrom system dependencies facts earlier).bind
        (fun next => checkFrom system dependencies next suffix) := by
  induction earlier with
  | nil => intro facts; rfl
  | cons node rest ih =>
      intro facts
      by_cases valid : ValidNode system dependencies facts node
      · simp [checkFrom, valid, ih]
      · simp [checkFrom, valid]

/-- Extend a checked prefix with one valid new node, retaining the exact recorded optional value. -/
theorem check_append_node [DecidableEq O] [DecidableEq L]
    (system : OccurrenceSystem F O L) (dependencies : O → List O)
    (nodes : List (Node O L)) (facts : List (Fact O L)) (node : Node O L)
    (accepted : check system dependencies nodes = some facts)
    (valid : ValidNode system dependencies facts node) :
    check system dependencies (nodes ++ [node]) = some (facts ++ [(node.target, node.outcome)]) := by
  unfold check at accepted ⊢
  rw [checkFrom_append, accepted]
  simp [checkFrom, valid]

end TetraStereo.Certificate.Dependency
