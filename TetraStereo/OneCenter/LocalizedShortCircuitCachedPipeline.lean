import TetraStereo.OneCenter.LocalizedShortCircuitCheckedPipeline
import TetraStereo.OneCenter.LocalizedTerminalLigandTieRefusal
import TetraStereo.OneCenter.LocalizedRerootChildrenCache

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedShortCircuit.Cached
open CertifiedLocalizedCIPInput Certificate.Dependency

def dependencyEntry (input : Input) (carrier : List (Occurrence input))
    (target : Occurrence input) : Occurrence input × List (Occurrence input) :=
  (target, carrier.filter fun source => decide (input.certified.LocalizedDepthDependency source target))

/-- Explicit materialized carrier data prevents repeated construction inside the child reader.
The cache carries an erased exactness proof; it is built from the admitted input itself. -/
structure RuntimeCache (input : Input) where
  carrier : List (Occurrence input)
  exact : carrier = input.certified.localizedOccurrenceCarrier (carrierFuel input)
  table : List (Occurrence input × List (Occurrence input))
  table_exact : table = carrier.map (dependencyEntry input carrier)

@[noinline] def buildRuntimeCache (input : Input) : RuntimeCache input :=
  let carrier := input.certified.localizedOccurrenceCarrier (carrierFuel input)
  { carrier, exact := rfl, table := carrier.map (dependencyEntry input carrier), table_exact := rfl }

@[inline] def dependenciesUsingCache (input : Input) (cache : RuntimeCache input)
    (target : Occurrence input) : List (Occurrence input) :=
  match cache.table.find? (fun entry => decide (entry.1 = target)) with
  | some entry => entry.2
  | none => cache.carrier.filter fun source =>
      decide (input.certified.LocalizedDepthDependency source target)

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
          (fun source => decide (input.certified.LocalizedDepthDependency source occurrence)) = _
      rw [same]
      rfl

@[inline] def evaluatorUsingCache (input : Input) (cache : RuntimeCache input) :
    input.certified.LocalizedRestrictedEvaluator (carrierFuel input) :=
  TerminalTie.descriptor? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier)

theorem evaluatorUsingCache_eq (input : Input) (cache : RuntimeCache input) :
    evaluatorUsingCache input cache = evaluator input (carrierFuel input) := by
  funext target view
  change TerminalTie.descriptor? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier) target view = _
  rw [TerminalTie.descriptor?_eq_original]
  apply WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor?_eq_original
  intro cursor
  rw [cache.exact]
  exact input.certified.localizedRerootChildrenFromCarrier?_eq_executable cursor

def semanticsUsingCache (input : Input) (cache : RuntimeCache input) :
    input.certified.LocalizedAuxiliaryRuleSemantics (carrierFuel input) where
  DeclarativeDerivation := OperationalOutcome input (carrierFuel input)
  executableRule := evaluatorUsingCache input cache
  derivation_executable_iff := by
    intros
    rw [evaluatorUsingCache_eq]
    rfl

theorem semanticsUsingCache_eq (input : Input) (cache : RuntimeCache input) :
    semanticsUsingCache input cache = runtimeSemantics input (carrierFuel input) := by
  simp only [semanticsUsingCache, runtimeSemantics, evaluatorUsingCache_eq]

def systemUsingCache (input : Input) (cache : RuntimeCache input) :=
  input.certified.localizedCertificateSystem (carrierFuel input) (semanticsUsingCache input cache)

theorem systemUsingCache_eq (input : Input) (cache : RuntimeCache input) :
    systemUsingCache input cache = runtimeSystem input := by
  unfold systemUsingCache runtimeSystem
  rw [semanticsUsingCache_eq]

def nodesUsingCache (input : Input) (cache : RuntimeCache input) : Nodes input :=
  produce (systemUsingCache input cache) (dependenciesUsingCache input cache)
    (Certificate.FiniteRankedOrder.rankedOrder
      (input.certified.localizedCertificateRank (carrierFuel input)) cache.carrier)

theorem nodesUsingCache_eq (input : Input) (cache : RuntimeCache input) :
    nodesUsingCache input cache = referenceNodes input := by
  unfold nodesUsingCache referenceNodes localizedCertificateNodes localizedCertificateOrder
  rw [systemUsingCache_eq, dependenciesUsingCache_eq, cache.exact]
  rfl

def checkUsingCache? (input : Input) (cache : RuntimeCache input) (nodes : Nodes input) :
    Option (Facts input) := do
  let facts ← check (systemUsingCache input cache) (dependenciesUsingCache input cache) nodes
  if (facts.map Prod.fst).Nodup ∧
      cache.carrier.all (fun occurrence => decide (occurrence ∈ facts.map Prod.fst)) = true
    then some facts else none

theorem checkUsingCache?_eq (input : Input) (cache : RuntimeCache input) (nodes : Nodes input) :
    checkUsingCache? input cache nodes = checkProposals? input nodes := by
  simp only [checkUsingCache?, checkProposals?, systemUsingCache_eq,
    dependenciesUsingCache_eq, cache.exact, covered]

def referenceUsingCache (input : Input) (cache : RuntimeCache input) : Evaluation input :=
  let nodes := nodesUsingCache input cache
  { nodes
    facts := nodes.map (fun node => (node.target, node.outcome))
    accepted := by
      dsimp only [nodes]
      rw [nodesUsingCache_eq]
      exact reference_accepted input }

/-- Construct one cache, replay proposals against the exact successor evaluator, and lazily produce
the reference certificate when replay rejects. Returned evidence uses the public checker invariant. -/
def evaluate (input : Input) (nodes : Nodes input) : Evaluation input :=
  let cache := buildRuntimeCache input
  match checked : checkUsingCache? input cache nodes with
  | some facts => ⟨nodes, facts, (checkUsingCache?_eq input cache nodes).symm.trans checked⟩
  | none => referenceUsingCache input cache

def checkProposals? (input : Input) (nodes : Nodes input) : Option (Facts input) :=
  checkUsingCache? input (buildRuntimeCache input) nodes

theorem checkProposals?_eq (input : Input) (nodes : Nodes input) :
    checkProposals? input nodes = LocalizedShortCircuit.checkProposals? input nodes :=
  checkUsingCache?_eq input (buildRuntimeCache input) nodes

theorem evaluate_report_eq (input : Input) (nodes : Nodes input) :
    report input (evaluate input nodes).facts = analyze input :=
  evaluation_report_eq_reference input (evaluate input nodes)

def evaluateSource? (source : AuthoritativeChemicalInput)
    (propose : Proposer := fun _ => []) : Option ((input : Input) × Evaluation input) := do
  let input ← admitSource? source
  pure ⟨input, evaluate input (propose input)⟩

end TetraStereo.OneCenter.LocalizedShortCircuit.Cached
