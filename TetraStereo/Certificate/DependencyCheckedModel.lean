import TetraStereo.Certificate.Dependency

set_option autoImplicit false

namespace TetraStereo.Certificate.DependencyCheckedModel

open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.DeclarativeCIP.OccurrenceScheduler
open TetraStereo.Certificate.Dependency

universe u v w

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

/-!
# From an accepted complete dependency-checked certificate to a global model

The dependency checker (`check`) computes an internal prefix while it replays the certificate nodes.
This module proves that, *without* assuming that the declared dependency relation is well-founded,
an accepted, duplicate-free and occurrence-complete certificate induces a global fixed point for the
executable evaluator, hence a declarative CIP model under the existing step/derivation
correspondence.

The well-foundedness-free argument is possible because the checked data itself supplies its own
recursive schedule: each node is valid against the prefix of already-accepted facts, and the
final result is exactly that prefix extended by the remaining node facts.  Duplicate freedom of the
final occurrence list is what makes the selected dependency view (`referenced`) of a node agree with
the whole prefix view, and locality then transfers the local evaluator equation to the completed
global state.
-/

/-- The fact recorded by a certificate node. -/
def nodeFact (node : Node Occurrence Label) : Fact Occurrence Label :=
  (node.target, node.outcome)

@[simp] theorem nodeFact_fst (node : Node Occurrence Label) :
    (nodeFact node).1 = node.target := rfl

@[simp] theorem nodeFact_snd (node : Node Occurrence Label) :
    (nodeFact node).2 = node.outcome := rfl

/-- The occurrences recorded by a node list are exactly the node targets. -/
theorem map_nodeFact_fst (nodes : List (Node Occurrence Label)) :
    (nodes.map nodeFact).map Prod.fst = nodes.map (fun node => node.target) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp only [List.map_cons, ih, nodeFact_fst]

/-! ## List facts used by the prefix argument -/

/-- `lookup` scans from the left, so extending a list on the right does not change the lookup value
of any occurrence already present on the left. -/
theorem lookup_append_left_of_mem [DecidableEq Occurrence]
    (pre suffix : List (Fact Occurrence Label)) {target : Occurrence}
    (htarget : target ∈ pre.map Prod.fst) :
    lookup (pre ++ suffix) target = lookup pre target := by
  induction pre with
  | nil =>
      simp only [List.map_nil, List.not_mem_nil] at htarget
  | cons fact rest ih =>
      rcases fact with ⟨occurrence, outcome⟩
      have htarget' : target ∈ occurrence :: rest.map Prod.fst := by
        simpa only [List.map_cons] using htarget
      by_cases heq : occurrence = target
      · rw [List.cons_append]
        simp only [lookup, if_pos heq]
      · have htail : target ∈ rest.map Prod.fst := by
          rcases List.mem_cons.mp htarget' with h | h
          · exact absurd h.symm heq
          · exact h
        rw [List.cons_append]
        simp only [lookup, if_neg heq]
        exact ih htail

/-- In a list whose first components are duplicate-free, the first lookup returns the stored outcome
of any member fact. -/
theorem lookup_eq_some_of_mem_nodup [DecidableEq Occurrence]
    {facts : List (Fact Occurrence Label)} {fact : Fact Occurrence Label}
    (nodup : (facts.map Prod.fst).Nodup) (member : fact ∈ facts) :
    lookup facts fact.1 = fact.2 := by
  induction facts with
  | nil => simp only [List.not_mem_nil] at member
  | cons head rest ih =>
      rcases head with ⟨occurrence, outcome⟩
      rcases List.mem_cons.mp member with h_eq | h_rest
      · have hfst : fact.1 = occurrence := by rw [h_eq]
        have hsnd : fact.2 = outcome := by rw [h_eq]
        rw [hfst, hsnd]
        show (if occurrence = occurrence then outcome else lookup rest occurrence) = outcome
        rw [if_pos rfl]
      · have hnodup' : (occurrence :: rest.map Prod.fst).Nodup := by simpa using nodup
        have hcons := List.nodup_cons.mp hnodup'
        have hnot : occurrence ∉ rest.map Prod.fst := hcons.1
        have nodup_rest : (rest.map Prod.fst).Nodup := hcons.2
        have hne : occurrence ≠ fact.1 := by
          intro heq
          refine hnot ?_
          rw [heq]
          exact List.mem_map_of_mem h_rest
        simp only [lookup, if_neg hne]
        exact ih nodup_rest h_rest

/-- Any occurrence selected by `referenced` is present in the underlying fact list. -/
theorem referenced_map_fst_subset_facts
    (facts : List (Fact Occurrence Label)) (indices : List Nat) {target : Occurrence}
    (htarget : target ∈ (referenced facts indices).map Prod.fst) :
    target ∈ facts.map Prod.fst := by
  obtain ⟨fact, hfact_ref, hfst⟩ := List.mem_map.mp htarget
  obtain ⟨index, _, hget⟩ := List.mem_filterMap.mp hfact_ref
  have htarget' : fact.1 ∈ facts.map Prod.fst :=
    List.mem_map_of_mem (List.mem_of_getElem? hget)
  rw [hfst] at htarget'
  exact htarget'

/-- Because `lookup` returns the first match and a duplicate-free fact list stores at most one fact
per occurrence, consulting a sublist of the stored facts gives the same value as consulting all of
them, as long as the queried occurrence is still present. -/
theorem lookup_eq_lookup_of_subset_nodup [DecidableEq Occurrence]
    (facts : List (Fact Occurrence Label))
    (facts_nodup : (facts.map Prod.fst).Nodup) :
    ∀ sub : List (Fact Occurrence Label),
      (∀ fact ∈ sub, fact ∈ facts) → ∀ target : Occurrence,
        target ∈ sub.map Prod.fst → lookup sub target = lookup facts target := by
  intro sub
  induction sub with
  | nil =>
      intro _ target htarget
      simp only [List.map_nil, List.not_mem_nil] at htarget
  | cons head rest ih =>
      intro hsub target htarget
      rcases head with ⟨occurrence, outcome⟩
      have htarget' : target ∈ occurrence :: rest.map Prod.fst := by
        simpa only [List.map_cons] using htarget
      by_cases heq : occurrence = target
      · have hhead : lookup ((occurrence, outcome) :: rest) target = outcome := by
          simp only [lookup, if_pos heq]
        have hmem : (occurrence, outcome) ∈ facts :=
          hsub (occurrence, outcome) List.mem_cons_self
        have hlook : lookup facts occurrence = outcome :=
          lookup_eq_some_of_mem_nodup facts_nodup hmem
        rw [hhead, ← heq]
        exact hlook.symm
      · have htail : target ∈ rest.map Prod.fst := by
          rcases List.mem_cons.mp htarget' with h | h
          · exact absurd h.symm heq
          · exact h
        have hrest : ∀ fact ∈ rest, fact ∈ facts := fun fact hmem =>
          hsub fact (List.mem_cons_of_mem (occurrence, outcome) hmem)
        have hdrop : lookup ((occurrence, outcome) :: rest) target = lookup rest target := by
          simp only [lookup, if_neg heq]
        rw [hdrop]
        exact ih hrest target htail

/-- When the underlying fact list has no duplicate occurrences, `lookup` on the selected dependency
view (`referenced`) agrees with `lookup` on the whole prefix at every selected occurrence.  The
selected indices only have to be in range; duplicate freedom of the fact list already forces the
`references.Nodup` check of `ValidNode` to be consistent with the prefix view. -/
theorem lookup_referenced_eq_lookup [DecidableEq Occurrence]
    (facts : List (Fact Occurrence Label)) (indices : List Nat) {target : Occurrence}
    (facts_nodup : (facts.map Prod.fst).Nodup)
    (_indices_nodup : indices.Nodup)
    (htarget : target ∈ (referenced facts indices).map Prod.fst) :
    lookup (referenced facts indices) target = lookup facts target :=
  lookup_eq_lookup_of_subset_nodup facts facts_nodup (referenced facts indices)
    (fun _fact hmem => by
      obtain ⟨index, _, hget⟩ := List.mem_filterMap.mp hmem
      exact List.mem_of_getElem? hget)
    target htarget

/-! ## The checker prefix, exactly -/

/-- A successful replay of a node list returns the initial prefix plus all node facts, in order. -/
theorem checkFrom_result_eq_append [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (nodes : List (Node Occurrence Label))
    (facts result : List (Fact Occurrence Label))
    (accepted : checkFrom system dependencies facts nodes = some result) :
    result = facts ++ nodes.map nodeFact := by
  induction nodes generalizing facts with
  | nil =>
      simp only [checkFrom, Option.some.injEq] at accepted
      simpa only [List.append_nil, List.map_nil] using accepted.symm
  | cons node rest ih =>
      simp only [checkFrom] at accepted
      split at accepted
      · rename_i valid
        have hrest := ih (facts := facts ++ [(node.target, node.outcome)]) accepted
        simpa only [List.map_cons, nodeFact, List.append_assoc, List.singleton_append] using hrest
      · contradiction

/-! ## Fixedness of the completed lookup state -/

/-- The local evaluator equations of every replayed node transfer to the final lookup state, provided
the final occurrence list is duplicate-free.  No well-foundedness assumption on the dependency
relation is used: the accepted node list itself is the schedule, and the prefix is the already
replayed part of that schedule. -/
theorem checkFrom_fixed_on_nodes [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (nodes : List (Node Occurrence Label))
    (facts result : List (Fact Occurrence Label))
    (accepted : checkFrom system dependencies facts nodes = some result)
    (result_nodup : (result.map Prod.fst).Nodup)
    (locality : system.EvaluatorLocalFor (relation dependencies)) :
    ∀ target, target ∈ nodes.map (fun node => node.target) →
      system.executableStep (lookup result) target = lookup result target := by
  induction nodes generalizing facts with
  | nil =>
      intro target htarget
      simp only [List.map_nil, List.not_mem_nil] at htarget
  | cons node rest ih =>
      intro target htarget
      have hfull : result = facts ++ (node :: rest).map nodeFact :=
        checkFrom_result_eq_append system dependencies (node :: rest) facts result accepted
      simp only [checkFrom] at accepted
      split at accepted
      · rename_i valid
        have htarget' : target ∈ node.target :: rest.map (fun node => node.target) := by
          simpa only [List.map_cons] using htarget
        rcases List.mem_cons.mp htarget' with htarget_eq | htarget_rest
        · rw [htarget_eq]
          have hnodup_append : (facts.map Prod.fst ++
              ((node :: rest).map nodeFact).map Prod.fst).Nodup := by
            have h1 : ((facts ++ (node :: rest).map nodeFact).map Prod.fst).Nodup := by
              simpa only [hfull] using result_nodup
            simpa only [List.map_append] using h1
          have facts_nodup : (facts.map Prod.fst).Nodup :=
            (List.nodup_append.mp hnodup_append).1
          have deps_eq : (referenced facts node.references).map Prod.fst =
              dependencies node.target := valid.2.2.1
          have eval_eq : node.outcome =
              system.executableStep (lookup (referenced facts node.references)) node.target :=
            valid.2.2.2
          have hmem : nodeFact node ∈ result := by
            rw [hfull, List.map_cons]
            exact List.mem_append_right facts List.mem_cons_self
          have lookup_result_node : lookup result node.target = node.outcome := by
            simpa only [nodeFact_fst, nodeFact_snd] using
              (lookup_eq_some_of_mem_nodup result_nodup hmem)
          have hlocal : system.executableStep (lookup result) node.target =
              system.executableStep (lookup (referenced facts node.references)) node.target := by
            refine locality (lookup result) (lookup (referenced facts node.references))
              node.target ?_
            intro source hdep
            have href : source ∈ (referenced facts node.references).map Prod.fst := by
              rw [deps_eq]
              exact hdep
            have hsrc_facts : source ∈ facts.map Prod.fst :=
              referenced_map_fst_subset_facts facts node.references href
            have hpre : lookup result source = lookup facts source := by
              rw [hfull]
              exact lookup_append_left_of_mem facts ((node :: rest).map nodeFact) hsrc_facts
            have href_lookup : lookup (referenced facts node.references) source =
                lookup facts source :=
              lookup_referenced_eq_lookup facts node.references facts_nodup valid.1 href
            rw [hpre, href_lookup]
          rw [lookup_result_node]
          exact hlocal.trans eval_eq.symm
        · exact ih (facts := facts ++ [(node.target, node.outcome)]) accepted target htarget_rest
      · contradiction

/-- Main fixed-point result for the empty-prefix checker: duplicate-free and occurrence-complete
checked facts induce a fixed point of the executable evaluator. -/
theorem checked_lookup_fixed [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (nodes : List (Node Occurrence Label)) (result : List (Fact Occurrence Label))
    (accepted : check system dependencies nodes = some result)
    (result_nodup : (result.map Prod.fst).Nodup)
    (complete : ∀ occurrence, occurrence ∈ result.map Prod.fst)
    (locality : system.EvaluatorLocalFor (relation dependencies)) :
    system.executableStateStep (lookup result) = lookup result := by
  funext occurrence
  have hcheck : checkFrom system dependencies [] nodes = some result := by
    simpa only [check] using accepted
  have hresult : result = nodes.map nodeFact := by
    simpa only [List.nil_append] using
      (checkFrom_result_eq_append system dependencies nodes [] result hcheck)
  have htargets : result.map Prod.fst = nodes.map (fun node => node.target) := by
    rw [hresult]
    exact map_nodeFact_fst nodes
  have hnode : occurrence ∈ nodes.map (fun node => node.target) := by
    rw [← htargets]
    exact complete occurrence
  exact checkFrom_fixed_on_nodes system dependencies nodes [] result hcheck result_nodup
    locality occurrence hnode

/-- The completed lookup state is a declarative CIP model under the existing evaluator/derivation
correspondence. -/
theorem checked_lookup_cipModel [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (nodes : List (Node Occurrence Label)) (result : List (Fact Occurrence Label))
    (accepted : check system dependencies nodes = some result)
    (result_nodup : (result.map Prod.fst).Nodup)
    (complete : ∀ occurrence, occurrence ∈ result.map Prod.fst)
    (locality : system.EvaluatorLocalFor (relation dependencies))
    (correspondence : system.DerivationStepCorrespondence) :
    system.CIPModel (lookup result) := by
  rw [system.cipModel_iff_executableStateStep_fixed correspondence]
  exact checked_lookup_fixed system dependencies nodes result accepted result_nodup complete locality

end TetraStereo.Certificate.DependencyCheckedModel
