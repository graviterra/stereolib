import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedUniversalReference.Cached

open CertifiedLocalizedCIPInput Certificate.Dependency

/-!
# One-shot materialization for the universal reference pipeline

`LocalizedUniversalReference` generates the reference certificate from the universal descriptor
evaluator, but every node target re-enumerates the occurrence carrier and re-filters it for its
strict dependencies.  This module materializes both once:

* `RuntimeCache` holds the carrier with an erased exactness proof and a dependency table built as
  `carrier.map dependencyEntry`, with no readiness/state component (the universal evaluator is used
  unchanged, so no old-pipeline precondition is needed).
* `dependenciesUsingCache` reads a table row; `orderUsingCache` merge-sorts the materialized
  carrier; `nodesUsingCache` is the single generic `produce` over the unchanged universal system,
  cached dependencies and cached order.
* `checkUsingCache?` replays caller nodes against the same universal system and cached
  dependencies, requiring duplicate-free targets and full coverage of the materialized carrier.
* `referenceEvaluation` binds one `nodesUsingCache` production and projects its facts from that
  same list; `evaluate` either accepts replay or falls back to it.

Every cached quantity is proved equal to the corresponding `LocalizedUniversalReference`
definition, so the cached pipeline computes exactly the universal reference state and report.
No new global-state assumption and no equality to the old production evaluator are introduced.
-/

/-! ## Materialized cache -/

/-- One dependency-table row: a target together with the carrier occurrences on which it strictly
depends.  This is the same executable strict-dependency filter as the generic dependency list. -/
def dependencyEntry (input : Input) (carrier : List (Occurrence input))
    (target : Occurrence input) : Occurrence input × List (Occurrence input) :=
  (target, carrier.filter fun source =>
    decide (input.certified.LocalizedDepthDependency source target))

/-- Carrier and dependency table materialized once per input.  There is deliberately no readiness
field: the universal evaluator is used as-is and needs no old-pipeline certificate. -/
structure RuntimeCache (input : Input) where
  carrier : List (Occurrence input)
  exact : carrier = input.certified.localizedOccurrenceCarrier (carrierFuel input)
  table : List (Occurrence input × List (Occurrence input))
  table_exact : table = carrier.map (dependencyEntry input carrier)

/-- Materialize the carrier and the whole dependency table once, outside all target evaluators. -/
@[noinline] def buildRuntimeCache (input : Input) : RuntimeCache input :=
  let carrier := input.certified.localizedOccurrenceCarrier (carrierFuel input)
  { carrier
    exact := rfl
    table := carrier.map (dependencyEntry input carrier)
    table_exact := rfl }

/-! ## Cached dependencies, ranked order and production -/

/-- Look a target up in the materialized dependency table.  The fallback keeps the function total
even for targets outside the carrier; it never runs for carrier members. -/
@[inline] def dependenciesUsingCache (input : Input) (cache : RuntimeCache input)
    (target : Occurrence input) : List (Occurrence input) :=
  match cache.table.find? (fun entry => decide (entry.1 = target)) with
  | some entry => entry.2
  | none => cache.carrier.filter fun source =>
      decide (input.certified.LocalizedDepthDependency source target)

/-- The cached dependency function is exactly the universal dependency function. -/
theorem dependenciesUsingCache_eq (input : Input) (cache : RuntimeCache input) :
    dependenciesUsingCache input cache = dependencies input := by
  funext target
  unfold dependenciesUsingCache
  rw [cache.table_exact, cache.exact]
  cases found : ((input.certified.localizedOccurrenceCarrier (carrierFuel input)).map
      (dependencyEntry input (input.certified.localizedOccurrenceCarrier (carrierFuel input)))).find?
        (fun entry => decide (entry.1 = target)) with
  | none => rfl
  | some entry =>
      have decided := List.find?_some found
      have entryKey : entry.1 = target :=
        of_decide_eq_true (decided : decide (entry.1 = target) = true)
      obtain ⟨occurrence, _, shape⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
      have same : occurrence = target := (congrArg Prod.fst shape).trans entryKey
      rw [← shape]
      change (input.certified.localizedOccurrenceCarrier (carrierFuel input)).filter
          (fun source =>
            decide (input.certified.LocalizedDepthDependency source occurrence)) = _
      rw [same]
      rfl

/-- The ranked certificate order computed from the materialized carrier (a stable merge sort; no
carrier enumeration). -/
def orderUsingCache (input : Input) (cache : RuntimeCache input) : List (Occurrence input) :=
  Certificate.FiniteRankedOrder.rankedOrder
    (input.certified.localizedCertificateRank (carrierFuel input)) cache.carrier

/-- The cached ranked order is exactly the repository certificate order. -/
theorem orderUsingCache_eq (input : Input) (cache : RuntimeCache input) :
    orderUsingCache input cache =
      input.certified.localizedCertificateOrder (carrierFuel input) := by
  unfold orderUsingCache CertifiedLocalizedCIPInput.localizedCertificateOrder
  rw [cache.exact]

/-- The single ranked production over the unchanged universal system, cached dependencies and the
materialized carrier order. -/
def nodesUsingCache (input : Input) (cache : RuntimeCache input) : Nodes input :=
  produce (runtimeSystem input) (dependenciesUsingCache input cache)
    (orderUsingCache input cache)

/-- The cached production is exactly the universal reference production. -/
theorem nodesUsingCache_eq (input : Input) (cache : RuntimeCache input) :
    nodesUsingCache input cache = referenceNodes input := by
  unfold nodesUsingCache referenceNodes
    CertifiedLocalizedCIPInput.localizedCertificateNodes
  rw [dependenciesUsingCache_eq, orderUsingCache_eq]
  rfl

/-! ## Cached checked replay -/

/-- Replay caller-supplied nodes against the same universal system and the cached dependencies.
Acceptance additionally requires duplicate-free fact targets and full coverage of the materialized
carrier. -/
def checkUsingCache? (input : Input) (cache : RuntimeCache input) (nodes : Nodes input) :
    Option (Facts input) := do
  let facts ← check (runtimeSystem input) (dependenciesUsingCache input cache) nodes
  if (facts.map Prod.fst).Nodup ∧
      cache.carrier.all (fun occurrence => decide (occurrence ∈ facts.map Prod.fst)) = true
    then some facts else none

/-- Cached replay is exactly the public universal checked replay. -/
theorem checkUsingCache?_eq (input : Input) (cache : RuntimeCache input) (nodes : Nodes input) :
    checkUsingCache? input cache nodes =
      LocalizedUniversalReference.checkProposals? input nodes := by
  simp only [checkUsingCache?, LocalizedUniversalReference.checkProposals?,
    dependenciesUsingCache_eq, cache.exact, LocalizedUniversalReference.covered]

/-- Cached checked replay that materializes its cache from the input. -/
def checkProposals? (input : Input) (nodes : Nodes input) : Option (Facts input) :=
  checkUsingCache? input (buildRuntimeCache input) nodes

/-- The cached checked replay equals the public universal checked replay. -/
theorem checkProposals?_eq (input : Input) (nodes : Nodes input) :
    checkProposals? input nodes =
      LocalizedUniversalReference.checkProposals? input nodes :=
  checkUsingCache?_eq input (buildRuntimeCache input) nodes

/-! ## Single-production cached reference evaluation -/

/-- Generated fallback over the cache.  The node list is bound once and the facts are the
target/outcome projection of that same list, so exactly one ranked production is performed. -/
def referenceEvaluation (input : Input) (cache : RuntimeCache input) : Evaluation input :=
  let nodes := nodesUsingCache input cache
  { nodes
    facts := nodes.map fun node => (node.target, node.outcome)
    accepted := by
      dsimp only [nodes]
      rw [nodesUsingCache_eq]
      exact reference_accepted input }

/-- The fallback facts are precisely the projection of the fallback nodes. -/
theorem referenceEvaluation_facts_eq_nodes_map (input : Input) (cache : RuntimeCache input) :
    (referenceEvaluation input cache).facts =
      (referenceEvaluation input cache).nodes.map
        fun node => (node.target, node.outcome) := rfl

/-- The fallback facts are the universal reference facts. -/
theorem referenceEvaluation_facts (input : Input) (cache : RuntimeCache input) :
    (referenceEvaluation input cache).facts = referenceFacts input := by
  rw [referenceEvaluation_facts_eq_nodes_map]
  change (nodesUsingCache input cache).map
      (fun node => (node.target, node.outcome)) = referenceFacts input
  rw [nodesUsingCache_eq]
  exact (referenceFacts_eq_nodes_map input).symm

/-- Replay proposed nodes against the cached table; on rejection produce the single generated
fallback from the same cache.  The result is a public `Evaluation`, so all universal
`Evaluation` theorems apply. -/
def evaluate (input : Input) (nodes : Nodes input) : Evaluation input :=
  let cache := buildRuntimeCache input
  match checked : checkUsingCache? input cache nodes with
  | some facts =>
      ⟨nodes, facts, (checkUsingCache?_eq input cache nodes).symm.trans checked⟩
  | none => referenceEvaluation input cache

/-- Every cached evaluation, accepted or generated, computes the unique universal reference
state. -/
theorem evaluate_state (input : Input) (nodes : Nodes input) :
    lookup (evaluate input nodes).facts = referenceState input :=
  LocalizedUniversalReference.evaluation_eq_reference input (evaluate input nodes)

/-- The cached evaluation report is exactly the universal reference report. -/
theorem evaluate_report_eq_reference (input : Input) (nodes : Nodes input) :
    report input (evaluate input nodes).facts = referenceReport input := by
  unfold report referenceReport
  rw [evaluate_state]
  rfl

/-- Positive outcomes of the cached evaluation carry independent universal descriptor evidence at
the computed Rule-3 budget, via the universal `Evaluation` soundness theorem. -/
theorem evaluate_positive_sound (input : Input) (nodes : Nodes input)
    (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel)
    (computed : lookup (evaluate input nodes).facts target = some descriptor) :
    ∃ (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
        (evaluationBudget : Nat),
      input.certified.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        evaluationBudget =
          (prepareUniversalRule3EvaluationOutcome input.certified base.cursors target
            (input.certified.localizedDependencyView
              (lookup (evaluate input nodes).facts) target)).1 ∧
          input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
            (input.certified.localizedDependencyView
              (lookup (evaluate input nodes).facts) target)
            evaluationBudget descriptor :=
  LocalizedUniversalReference.evaluation_positive_sound input (evaluate input nodes)
    target descriptor computed

end TetraStereo.OneCenter.LocalizedUniversalReference.Cached
