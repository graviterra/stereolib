import TetraStereo.OneCenter.LocalizedDependencyPrefix
import TetraStereo.OneCenter.LocalizedShortCircuitBoundedDescriptor

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedShortCircuit.Linear
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- The proved linear Rule3 compiler is used throughout the dependency schedule. -/
def evaluatorUsingCache (input : Input) (cache : Cached.RuntimeCache input) :
    input.certified.LocalizedRestrictedEvaluator (carrierFuel input) :=
  Bounded.descriptor? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier)

theorem evaluatorUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input)) :
    evaluatorUsingCache input cache = evaluator input (carrierFuel input) := by
  funext target view
  apply Bounded.descriptor?_eq_production
  · intro cursor
    rw [cache.exact]
    exact input.certified.localizedRerootChildrenFromCarrier?_eq_executable cursor
  · exact ready

def semanticsUsingCache (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input)) :
    input.certified.LocalizedAuxiliaryRuleSemantics (carrierFuel input) where
  DeclarativeDerivation := OperationalOutcome input (carrierFuel input)
  executableRule := evaluatorUsingCache input cache
  derivation_executable_iff := by
    intros
    rw [evaluatorUsingCache_eq input cache ready]
    rfl

theorem semanticsUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input)) :
    semanticsUsingCache input cache ready = runtimeSemantics input (carrierFuel input) := by
  simp only [semanticsUsingCache, runtimeSemantics, evaluatorUsingCache_eq input cache ready]

def systemUsingCache (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input)) :=
  input.certified.localizedCertificateSystem (carrierFuel input) (semanticsUsingCache input cache ready)

theorem systemUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input)) :
    systemUsingCache input cache ready = runtimeSystem input := by
  unfold systemUsingCache runtimeSystem
  rw [semanticsUsingCache_eq]

/-- Construct predecessor support with the smaller proved budget at every node. -/
def produceDependencySupport (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input))
    (target : Occurrence input) : DependencySupport input target :=
  let nodes := produce (systemUsingCache input cache ready)
    (Cached.dependenciesUsingCache input cache) (dependencyPrefixOrder input target)
  let facts := nodes.map (fun node => (node.target, node.outcome))
  have targets : facts.map Prod.fst = dependencyPrefixOrder input target :=
    produce_result_targets _ _ _
  { nodes, facts
    accepted := by
      dsimp only [nodes, facts]
      rw [systemUsingCache_eq, Cached.dependenciesUsingCache_eq]
      exact produce_check _ _ _ (dependencyPrefixOrder_ready input target)
        (fun source _ => input.certified.localizedDependencyList_nodup (carrierFuel input) source)
    covers := by
      rw [targets]
      exact (dependencyPrefixOrder_support input target).1
    targetAbsent := by
      rw [targets]
      exact (dependencyPrefixOrder_support input target).2 }

def nodesUsingCache (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input)) : Nodes input :=
  produce (systemUsingCache input cache ready) (Cached.dependenciesUsingCache input cache)
    (Certificate.FiniteRankedOrder.rankedOrder
      (input.certified.localizedCertificateRank (carrierFuel input)) cache.carrier)

theorem nodesUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input)) :
    nodesUsingCache input cache ready = referenceNodes input := by
  unfold nodesUsingCache referenceNodes localizedCertificateNodes localizedCertificateOrder
  rw [systemUsingCache_eq, Cached.dependenciesUsingCache_eq, cache.exact]
  rfl

def checkUsingCache? (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input))
    (nodes : Nodes input) : Option (Facts input) := do
  let facts ← check (systemUsingCache input cache ready) (Cached.dependenciesUsingCache input cache) nodes
  if (facts.map Prod.fst).Nodup ∧
      cache.carrier.all (fun occurrence => decide (occurrence ∈ facts.map Prod.fst)) = true
    then some facts else none

theorem checkUsingCache?_eq (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input))
    (nodes : Nodes input) : checkUsingCache? input cache ready nodes = checkProposals? input nodes := by
  simp only [checkUsingCache?, checkProposals?, systemUsingCache_eq,
    Cached.dependenciesUsingCache_eq, cache.exact, covered]

def referenceUsingCache (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input)) : Evaluation input :=
  let nodes := nodesUsingCache input cache ready
  { nodes
    facts := nodes.map (fun node => (node.target, node.outcome))
    accepted := by
      dsimp only [nodes]
      rw [nodesUsingCache_eq]
      exact reference_accepted input }

/-- Fast proposals are replayed with the proved linear compiler when its readiness check succeeds.
Otherwise the existing cached evaluator remains available. Rejected proposals generate a full
reference certificate. Both branches have exactly the same public acceptance invariant. -/
def evaluate (input : Input) (nodes : Nodes input) : Evaluation input :=
  let cache := Cached.buildRuntimeCache input
  match input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input) with
  | none =>
      match checked : Cached.checkUsingCache? input cache nodes with
      | some facts => ⟨nodes, facts, (Cached.checkUsingCache?_eq input cache nodes).symm.trans checked⟩
      | none => Cached.referenceUsingCache input cache
  | some ready =>
      match checked : checkUsingCache? input cache ready nodes with
      | some facts => ⟨nodes, facts, (checkUsingCache?_eq input cache ready nodes).symm.trans checked⟩
      | none => referenceUsingCache input cache ready

theorem evaluate_report_eq (input : Input) (nodes : Nodes input) :
    report input (evaluate input nodes).facts = analyze input :=
  evaluation_report_eq_reference input (evaluate input nodes)

def evaluateSource? (source : AuthoritativeChemicalInput)
    (propose : Proposer := fun _ => []) : Option ((input : Input) × Evaluation input) := do
  let input ← admitSource? source
  pure ⟨input, evaluate input (propose input)⟩

def evaluateSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) (propose : Proposer := fun _ => []) :
    Except ParserError (Option ((input : Input) × Evaluation input)) :=
  (admitSmilesSpatial? text spatial cycles).map fun admitted =>
    admitted.map fun input => ⟨input, evaluate input (propose input)⟩

end TetraStereo.OneCenter.LocalizedShortCircuit.Linear
