import TetraStereo.OneCenter.LocalizedDependencyCertificate
import TetraStereo.OneCenter.LocalizedNoDoubleReferencePipeline
import TetraStereo.OneCenter.LocalizedRerootChildrenCache
import TetraStereo.OneCenter.LocalizedNoDoubleWithChildren
import TetraStereo.Certificate.DependencyProducer
import TetraStereo.Certificate.DependencyCheckedModel

set_option autoImplicit false

/-!
# Materialized runtime data for reference evaluation and ranked certificate replay

`RuntimeCache` contains the complete occurrence carrier and its dependency table, with erased proofs
that both are exact. `buildRuntimeCache` returns data, and the runtime entry points construct that
data before producing or checking nodes. Their callbacks take the cache explicitly. This boundary
matters: a function-returning `let` alone permits Lean's eta expansion to reconstruct data per target.

`cachedReferenceFacts`, `cachedGeneratedNodes`, and `cachedCheckProposals?` are proved equal to their
uncached counterparts. The evaluator uses the independently proved reader-parameterized pipeline;
no descriptor is assumed. Producer and checker each construct their own cache. Child reads still
filter the carrier, and fact lookup remains list-based; no asymptotic bound is claimed here.

The local `checkProposals?` replays generated nodes. Their complete duplicate-free coverage is proved.
The separate `LocalizedNoDoubleCachedPublicPipeline` checks arbitrary proposals with runtime coverage
guards. Both preserve every optional outcome of the existing no-order-two-source-record semantics;
a returned `none` is not a theorem of chemical nonexistence.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-- **Exactness of the carrier-bound runtime reader at the canonical carrier.**  Reading the reroot
children from `localizedOccurrenceCarrier fuel` reproduces the executable expansion exactly; the
right-hand side is `some (input.executableLocalizedRerootChildren cursor)`, which is definitionally
`input.executableLocalizedRerootChildren? cursor`. -/
theorem localizedRerootChildrenFromCarrier?_canonical_eq_executable
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ∀ cursor : input.LocalizedRerootCursor fuel,
      localizedRerootChildrenFromCarrier? input
          (carrier := input.localizedOccurrenceCarrier fuel) cursor =
        input.executableLocalizedRerootChildren? cursor := by
  intro cursor
  rw [executableLocalizedRerootChildren?]
  exact input.localizedRerootChildrenFromCarrier?_eq_executable cursor

/-- One strict-depth dependency table entry: a carried occurrence together with the filtered carrier
of its strict-depth dependencies. -/
def cachedDependencyEntry
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (carrier : List (input.LocalizedCIPOccurrence fuel))
    (target : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedCIPOccurrence fuel × List (input.LocalizedCIPOccurrence fuel) :=
  (target, carrier.filter fun source => decide (input.LocalizedDepthDependency source target))

end CertifiedLocalizedCIPInput

namespace LocalizedNoDoubleCachedEvaluation

open CertifiedLocalizedCIPInput

/-! ## The `let`-bound evaluator -/

/-- Extensional evaluator used in refinement statements. Runtime entry points use
`evaluatorUsingCache` with explicitly materialized data to preserve sharing after eta expansion. -/
@[inline] def cachedEvaluator (input : LocalizedNoDoubleReference.Input) :
    input.certified.LocalizedRestrictedEvaluator (LocalizedNoDoubleReference.carrierFuel input) :=
  let carrier := input.certified.localizedOccurrenceCarrier
    (LocalizedNoDoubleReference.carrierFuel input)
  CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleDescriptorExec? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? carrier)

/-- The cached evaluator computes exactly the repository's executable descriptor twin. -/
theorem cachedEvaluator_eq_evaluator (input : LocalizedNoDoubleReference.Input) :
    cachedEvaluator input =
      LocalizedNoDoubleReference.evaluator input (LocalizedNoDoubleReference.carrierFuel input) := by
  funext target view
  rw [cachedEvaluator, LocalizedNoDoubleReference.evaluator]
  exact CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleDescriptorExec?_eq_original
    input.certified _
    (input.certified.localizedRerootChildrenFromCarrier?_canonical_eq_executable
      (LocalizedNoDoubleReference.carrierFuel input))
    target view

/-- Pointwise form of `cachedEvaluator_eq_evaluator`. -/
theorem cachedEvaluator_apply_eq_evaluator (input : LocalizedNoDoubleReference.Input)
    (target : input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
    (view : input.certified.LocalizedDependencyView target) :
    cachedEvaluator input target view =
      LocalizedNoDoubleReference.evaluator input (LocalizedNoDoubleReference.carrierFuel input)
        target view :=
  congrFun (congrFun (cachedEvaluator_eq_evaluator input) target) view

/-- The cached evaluator computes exactly the original descriptor-bearing occurrence descriptor,
using only the admitted source-record no-double-bond proof. -/
theorem cachedEvaluator_apply_eq_descriptorBearing (input : LocalizedNoDoubleReference.Input)
    (target : input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
    (view : input.certified.LocalizedDependencyView target) :
    cachedEvaluator input target view =
      input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? target view := by
  rw [cachedEvaluator_apply_eq_evaluator input target view]
  exact LocalizedNoDoubleReference.evaluator_apply_eq_descriptorBearing input
    (LocalizedNoDoubleReference.carrierFuel input) target view

/-- Runtime data, kept in a structure so compiler eta expansion cannot defer its construction
inside a per-target callback. Proof fields certify the exact carrier and dependency table. -/
structure RuntimeCache (input : LocalizedNoDoubleReference.Input) where
  carrier : List (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
  carrier_eq : carrier = input.certified.localizedOccurrenceCarrier (LocalizedNoDoubleReference.carrierFuel input)
  table : List (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input) ×
    List (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input)))
  table_eq : table = carrier.map (input.certified.cachedDependencyEntry
    (LocalizedNoDoubleReference.carrierFuel input) carrier)

@[noinline] def buildRuntimeCache (input : LocalizedNoDoubleReference.Input) : RuntimeCache input :=
  let carrier := input.certified.localizedOccurrenceCarrier (LocalizedNoDoubleReference.carrierFuel input)
  { carrier, carrier_eq := rfl,
    table := carrier.map (input.certified.cachedDependencyEntry
      (LocalizedNoDoubleReference.carrierFuel input) carrier), table_eq := rfl }

@[inline] def evaluatorUsingCache (input : LocalizedNoDoubleReference.Input) (cache : RuntimeCache input) :
    input.certified.LocalizedRestrictedEvaluator (LocalizedNoDoubleReference.carrierFuel input) :=
  CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleDescriptorExec? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier)

theorem evaluatorUsingCache_eq_cachedEvaluator (input : LocalizedNoDoubleReference.Input)
    (cache : RuntimeCache input) : evaluatorUsingCache input cache = cachedEvaluator input := by
  simp only [evaluatorUsingCache, cachedEvaluator, cache.carrier_eq]

/-! ## Cached reference round tabulation -/

/-- The reference round tabulation with the `let`-bound evaluator. -/
def cachedReferenceFacts (input : LocalizedNoDoubleReference.Input) :
    List (Certificate.Dependency.Fact
      (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
      LocalizedAuxiliaryLabel) :=
  let cache := buildRuntimeCache input
  FiniteStateIteration.tabulatedFacts cache.carrier
    (input.certified.localizedExecutableStep (evaluatorUsingCache input cache))
    (fun _ => none) (LocalizedNoDoubleReference.carrierFuel input + 2)

/-- **Exactness of the cached reference tabulation.**  The cached fact list is exactly the repository's
reference fact list; only the child reads inside the descriptor evaluator changed. -/
theorem cachedReferenceFacts_eq_evaluatedFacts (input : LocalizedNoDoubleReference.Input) :
    cachedReferenceFacts input = LocalizedNoDoubleReference.evaluatedFacts input := by
  simp only [cachedReferenceFacts, LocalizedNoDoubleReference.evaluatedFacts,
    LocalizedNoDoubleReference.iterationRounds, evaluatorUsingCache_eq_cachedEvaluator,
    RuntimeCache.carrier_eq, cachedEvaluator_eq_evaluator input]

/-- The cached reference state is exactly the computed state of the reference pipeline. -/
theorem cachedReferenceState_eq_evaluatedState (input : LocalizedNoDoubleReference.Input) :
    Certificate.Dependency.lookup (cachedReferenceFacts input) =
      LocalizedNoDoubleReference.evaluatedState input := by
  rw [cachedReferenceFacts_eq_evaluatedFacts input]
  rfl

/-! ## Cached ranked certificate runtime -/

/-- The cached runtime semantics: the repository's declarative descriptor-bearing outcome relation
with the cached executable rule.  Only the executable member differs from
`LocalizedNoDoubleReference.runtimeSemantics`. -/
@[inline] def cachedRuntimeSemantics (input : LocalizedNoDoubleReference.Input) :
    input.certified.LocalizedAuxiliaryRuleSemantics (LocalizedNoDoubleReference.carrierFuel input) where
  DeclarativeDerivation :=
    input.certified.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
  executableRule := cachedEvaluator input
  derivation_executable_iff := by
    intro state target outcome
    rw [cachedEvaluator_apply_eq_descriptorBearing input target
      (input.certified.localizedDependencyView state target)]
    exact input.certified.declarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome_iff
      state target outcome

/-- The cached certificate system is the repository's certificate system: the occurrence system is a
function of the declarative relation and the restricted executable step only, and both agree. -/
theorem cachedCertificateSystem_eq_certificateSystem (input : LocalizedNoDoubleReference.Input) :
    input.certified.localizedCertificateSystem (LocalizedNoDoubleReference.carrierFuel input)
        (cachedRuntimeSemantics input) =
      input.certified.localizedCertificateSystem (LocalizedNoDoubleReference.carrierFuel input)
        (LocalizedNoDoubleReference.runtimeSemantics input
          (LocalizedNoDoubleReference.carrierFuel input)) := by
  simp only [localizedCertificateSystem, localizedAuxiliaryOccurrenceSystemExecutableRoot,
    localizedOccurrenceSystemWithExecutableRoot, cachedRuntimeSemantics,
    LocalizedNoDoubleReference.runtimeSemantics, cachedEvaluator_eq_evaluator input]

/-- Extensional dependency lookup used in refinement statements. Runtime entry points use
`dependenciesUsingCache` on a preconstructed data cache. -/
@[inline] def cachedCertificateDependencies (input : LocalizedNoDoubleReference.Input) :
    input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input) →
      List (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input)) :=
  let carrier := input.certified.localizedOccurrenceCarrier
    (LocalizedNoDoubleReference.carrierFuel input)
  let table := carrier.map (input.certified.cachedDependencyEntry
    (LocalizedNoDoubleReference.carrierFuel input) carrier)
  fun target =>
    match table.find? (fun entry => decide (entry.1 = target)) with
    | some entry => entry.2
    | none => carrier.filter fun source => decide (input.certified.LocalizedDepthDependency source target)

/-- **Exactness of the cached dependency lookup.**  At the canonical carrier the cached lookup is
exactly the repository's executable strict-dependency list. -/
theorem cachedCertificateDependencies_eq_localizedCertificateDependencies
    (input : LocalizedNoDoubleReference.Input) :
    cachedCertificateDependencies input =
      input.certified.localizedCertificateDependencies (LocalizedNoDoubleReference.carrierFuel input) := by
  funext target
  unfold cachedCertificateDependencies
  cases found : (List.map (input.certified.cachedDependencyEntry
      (LocalizedNoDoubleReference.carrierFuel input)
      (input.certified.localizedOccurrenceCarrier (LocalizedNoDoubleReference.carrierFuel input)))
        (input.certified.localizedOccurrenceCarrier
          (LocalizedNoDoubleReference.carrierFuel input))).find?
      (fun entry => decide (entry.1 = target)) with
  | none => rfl
  | some entry =>
      have decided := List.find?_some found
      have entryKey : entry.1 = target :=
        of_decide_eq_true (decided : decide (entry.1 = target) = true)
      obtain ⟨occurrence, _present, shape⟩ :=
        List.mem_map.mp (List.mem_of_find?_eq_some found)
      have hocc : occurrence = target :=
        (congrArg (fun pair => pair.1) shape).trans entryKey
      have step : entry.2 = (input.certified.localizedOccurrenceCarrier
          (LocalizedNoDoubleReference.carrierFuel input)).filter
          (fun source => decide (input.certified.LocalizedDepthDependency source target)) := by
        rw [← shape]
        exact congrArg (fun occ => (input.certified.localizedOccurrenceCarrier
          (LocalizedNoDoubleReference.carrierFuel input)).filter
          (fun source => decide (input.certified.LocalizedDepthDependency source occ))) hocc
      show entry.2 =
        input.certified.localizedDependencyList (LocalizedNoDoubleReference.carrierFuel input) target
      rw [step]
      rw [localizedDependencyList]

@[inline] def dependenciesUsingCache (input : LocalizedNoDoubleReference.Input)
    (cache : RuntimeCache input) : input.certified.LocalizedCIPOccurrence
        (LocalizedNoDoubleReference.carrierFuel input) →
      List (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input)) :=
  fun target =>
    match cache.table.find? (fun entry => decide (entry.1 = target)) with
    | some entry => entry.2
    | none => cache.carrier.filter fun source => decide (input.certified.LocalizedDepthDependency source target)

theorem dependenciesUsingCache_eq_cachedCertificateDependencies
    (input : LocalizedNoDoubleReference.Input) (cache : RuntimeCache input) :
    dependenciesUsingCache input cache = cachedCertificateDependencies input := by
  funext target
  unfold dependenciesUsingCache cachedCertificateDependencies
  rw [cache.table_eq, cache.carrier_eq]

@[inline] def runtimeSemanticsUsingCache (input : LocalizedNoDoubleReference.Input)
    (cache : RuntimeCache input) :
    input.certified.LocalizedAuxiliaryRuleSemantics (LocalizedNoDoubleReference.carrierFuel input) where
  DeclarativeDerivation :=
    input.certified.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
  executableRule := evaluatorUsingCache input cache
  derivation_executable_iff := by
    intro state target outcome
    rw [evaluatorUsingCache_eq_cachedEvaluator]
    exact (cachedRuntimeSemantics input).derivation_executable_iff state target outcome

theorem runtimeSemanticsUsingCache_eq_cachedRuntimeSemantics
    (input : LocalizedNoDoubleReference.Input) (cache : RuntimeCache input) :
    runtimeSemanticsUsingCache input cache = cachedRuntimeSemantics input := by
  simp only [runtimeSemanticsUsingCache, cachedRuntimeSemantics,
    evaluatorUsingCache_eq_cachedEvaluator]

/-- The ranked order of the certificate runtime: the existing rank of the bound carrier. -/
def cachedCertificateOrder (input : LocalizedNoDoubleReference.Input) :=
  input.certified.localizedCertificateOrder (LocalizedNoDoubleReference.carrierFuel input)

/-- The ranked order is duplicate free. -/
theorem cachedCertificateOrder_nodup (input : LocalizedNoDoubleReference.Input) :
    (cachedCertificateOrder input).Nodup :=
  input.certified.localizedCertificateOrder_nodup (LocalizedNoDoubleReference.carrierFuel input)

/-- The ranked order covers every carried occurrence. -/
theorem cachedCertificateOrder_complete (input : LocalizedNoDoubleReference.Input)
    (occurrence : input.certified.LocalizedCIPOccurrence
      (LocalizedNoDoubleReference.carrierFuel input)) :
    occurrence ∈ cachedCertificateOrder input :=
  input.certified.localizedCertificateOrder_complete (LocalizedNoDoubleReference.carrierFuel input)
    occurrence

/-- The cached dependency enumeration is duplicate free at every ranked node. -/
theorem cachedDependencies_nodup (input : LocalizedNoDoubleReference.Input)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedNoDoubleReference.carrierFuel input))
    (_member : target ∈ cachedCertificateOrder input) :
    (cachedCertificateDependencies input target).Nodup := by
  rw [cachedCertificateDependencies_eq_localizedCertificateDependencies input]
  exact input.certified.localizedDependencyList_nodup (LocalizedNoDoubleReference.carrierFuel input)
    target

/-- The ranked order is prefix ready for the cached dependency enumeration. -/
theorem cachedPrefixReady (input : LocalizedNoDoubleReference.Input) :
    Certificate.Dependency.PrefixReady (cachedCertificateDependencies input) []
      (cachedCertificateOrder input) := by
  rw [cachedCertificateDependencies_eq_localizedCertificateDependencies input]
  exact input.certified.prefixReady_localizedCertificateOrder
    (LocalizedNoDoubleReference.carrierFuel input)

/-- The ranked certificate node list of the repository runtime: the same ranked production the
existing certificate module runs, at the runtime semantics. -/
def generatedNodes (input : LocalizedNoDoubleReference.Input) :
    List (Certificate.Dependency.Node
      (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
      LocalizedAuxiliaryLabel) :=
  Certificate.Dependency.produce
    (input.certified.localizedCertificateSystem (LocalizedNoDoubleReference.carrierFuel input)
      (LocalizedNoDoubleReference.runtimeSemantics input
        (LocalizedNoDoubleReference.carrierFuel input)))
    (input.certified.localizedCertificateDependencies (LocalizedNoDoubleReference.carrierFuel input))
    (input.certified.localizedCertificateOrder (LocalizedNoDoubleReference.carrierFuel input))

/-- The repository runtime node list is the certificate module's node list, definitionally. -/
theorem generatedNodes_eq_localizedCertificateNodes (input : LocalizedNoDoubleReference.Input) :
    generatedNodes input =
      input.certified.localizedCertificateNodes (LocalizedNoDoubleReference.carrierFuel input)
        (LocalizedNoDoubleReference.runtimeSemantics input
          (LocalizedNoDoubleReference.carrierFuel input)) := rfl

/-- The cached ranked certificate node list: the same ranked order and the same occurrence system,
run with the cached evaluator and the cached dependency lookup. -/
def cachedGeneratedNodes (input : LocalizedNoDoubleReference.Input) :
    List (Certificate.Dependency.Node
      (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
      LocalizedAuxiliaryLabel) :=
  let cache := buildRuntimeCache input
  Certificate.Dependency.produce
    (input.certified.localizedCertificateSystem (LocalizedNoDoubleReference.carrierFuel input)
      (runtimeSemanticsUsingCache input cache))
    (dependenciesUsingCache input cache) (cachedCertificateOrder input)

/-- **Exactness of the cached ranked production.**  The cached node list is exactly the repository's
certificate node list at the runtime semantics: same bound carrier, same ranked order, same occurrence
system, cached evaluator and cached dependency lookup. -/
theorem cachedGeneratedNodes_eq_localizedCertificateNodes (input : LocalizedNoDoubleReference.Input) :
    cachedGeneratedNodes input =
      input.certified.localizedCertificateNodes (LocalizedNoDoubleReference.carrierFuel input)
        (LocalizedNoDoubleReference.runtimeSemantics input
          (LocalizedNoDoubleReference.carrierFuel input)) := by
  dsimp only [cachedGeneratedNodes]
  rw [runtimeSemanticsUsingCache_eq_cachedRuntimeSemantics,
    dependenciesUsingCache_eq_cachedCertificateDependencies,
    cachedCertificateDependencies_eq_localizedCertificateDependencies input,
    cachedCertificateSystem_eq_certificateSystem input]
  rfl

/-- The cached node list is exactly the repository runtime node list. -/
theorem cachedGeneratedNodes_eq_generatedNodes (input : LocalizedNoDoubleReference.Input) :
    cachedGeneratedNodes input = generatedNodes input :=
  (cachedGeneratedNodes_eq_localizedCertificateNodes input).trans
    (generatedNodes_eq_localizedCertificateNodes input).symm

/-! ## Cached ranked check -/

/-- The repository ranked check: the existing runtime node list passed through the dependency
checker. -/
def checkProposals? (input : LocalizedNoDoubleReference.Input) :
    Option (List (Certificate.Dependency.Fact
      (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
      LocalizedAuxiliaryLabel)) :=
  Certificate.Dependency.check
    (input.certified.localizedCertificateSystem (LocalizedNoDoubleReference.carrierFuel input)
      (LocalizedNoDoubleReference.runtimeSemantics input
        (LocalizedNoDoubleReference.carrierFuel input)))
    (input.certified.localizedCertificateDependencies (LocalizedNoDoubleReference.carrierFuel input))
    (generatedNodes input)

/-- The cached ranked check: the cached evaluator, the cached dependency lookup and the cached node
list. Producer and checker each bind their own carrier and dependency table. -/
def cachedCheckProposals? (input : LocalizedNoDoubleReference.Input) :
    Option (List (Certificate.Dependency.Fact
      (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
      LocalizedAuxiliaryLabel)) :=
  let cache := buildRuntimeCache input
  Certificate.Dependency.check
    (input.certified.localizedCertificateSystem (LocalizedNoDoubleReference.carrierFuel input)
      (runtimeSemanticsUsingCache input cache))
    (dependenciesUsingCache input cache) (cachedGeneratedNodes input)

/-- The accepted facts of the cached node list, in ranked order. -/
def cachedCertificateFacts (input : LocalizedNoDoubleReference.Input) :
    List (Certificate.Dependency.Fact
      (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
      LocalizedAuxiliaryLabel) :=
  (cachedGeneratedNodes input).map fun node => (node.target, node.outcome)

/-- **The cached ranked check accepts its own node list**, exactly like the existing certificate
theorem: the generated nodes have proved duplicate freedom and completeness. -/
theorem cachedCheckProposals?_eq_some_cachedCertificateFacts
    (input : LocalizedNoDoubleReference.Input) :
    cachedCheckProposals? input = some (cachedCertificateFacts input) := by
  simp only [cachedCheckProposals?, cachedGeneratedNodes, cachedCertificateFacts,
    runtimeSemanticsUsingCache_eq_cachedRuntimeSemantics,
    dependenciesUsingCache_eq_cachedCertificateDependencies]
  exact Certificate.Dependency.produce_check _ _ _
    (cachedPrefixReady input)
    (fun target member => cachedDependencies_nodup input target member)

/-- **Exactness of the cached ranked check.**  The cached check returns exactly what the repository
runtime check returns, including its refusals. -/
theorem cachedCheckProposals?_eq_checkProposals? (input : LocalizedNoDoubleReference.Input) :
    cachedCheckProposals? input = checkProposals? input := by
  dsimp only [cachedCheckProposals?]
  rw [runtimeSemanticsUsingCache_eq_cachedRuntimeSemantics,
    dependenciesUsingCache_eq_cachedCertificateDependencies, checkProposals?,
    cachedGeneratedNodes_eq_localizedCertificateNodes input,
    generatedNodes_eq_localizedCertificateNodes input,
    cachedCertificateSystem_eq_certificateSystem input,
    cachedCertificateDependencies_eq_localizedCertificateDependencies input]

/-- The cached accepted facts are the repository certificate facts at the runtime semantics. -/
theorem cachedCertificateFacts_eq_localizedCertificateFacts
    (input : LocalizedNoDoubleReference.Input) :
    cachedCertificateFacts input =
      input.certified.localizedCertificateFacts (LocalizedNoDoubleReference.carrierFuel input)
        (LocalizedNoDoubleReference.runtimeSemantics input
          (LocalizedNoDoubleReference.carrierFuel input)) := by
  simp only [cachedCertificateFacts, cachedGeneratedNodes_eq_localizedCertificateNodes input]
  rfl

/-! ## The ranked certificate facts are the computed state -/

/-- **The ranked certificate facts decode to the computed reference state.**  The certificate state
and the reference state are both complete models of the same runtime semantics, and the runtime
semantics has a unique model, so the looked-up fact list is the reference state.  This is the bridge
that lets the ranked checker's accepted facts replace the reference round tabulation in the report. -/
theorem certificateFacts_lookup_eq_evaluatedState (input : LocalizedNoDoubleReference.Input) :
    Certificate.Dependency.lookup
        (input.certified.localizedCertificateFacts (LocalizedNoDoubleReference.carrierFuel input)
          (LocalizedNoDoubleReference.runtimeSemantics input
            (LocalizedNoDoubleReference.carrierFuel input))) =
      LocalizedNoDoubleReference.evaluatedState input := by
  obtain ⟨witness, witnessModel, unique⟩ :=
    input.certified.existsUnique_localizedAuxiliaryCIPModel
      (LocalizedNoDoubleReference.runtimeSemantics input
        (LocalizedNoDoubleReference.carrierFuel input))
  have factsModel :=
    input.certified.localizedCertificateFacts_cipModel (LocalizedNoDoubleReference.carrierFuel input)
      (LocalizedNoDoubleReference.runtimeSemantics input
        (LocalizedNoDoubleReference.carrierFuel input))
  simp only [localizedCertificateSystem] at factsModel
  rw [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old
    (LocalizedNoDoubleReference.runtimeSemantics input
      (LocalizedNoDoubleReference.carrierFuel input))] at factsModel
  have evaluatedModel := LocalizedNoDoubleReference.cipModel_evaluatedState input
  rw [unique _ factsModel, unique _ evaluatedModel]

/-- The cached acceptance facts also decode to the computed reference state. -/
theorem cachedCertificateFacts_lookup_eq_evaluatedState
    (input : LocalizedNoDoubleReference.Input) :
    Certificate.Dependency.lookup (cachedCertificateFacts input) =
      LocalizedNoDoubleReference.evaluatedState input := by
  rw [cachedCertificateFacts_eq_localizedCertificateFacts input,
    certificateFacts_lookup_eq_evaluatedState input]

/-! ## The cached center report -/

/-- Project the optional outcome of every canonical center out of a fact list. -/
def centersLookup (input : LocalizedNoDoubleReference.Input)
    (facts : List (Certificate.Dependency.Fact
      (input.certified.LocalizedCIPOccurrence (LocalizedNoDoubleReference.carrierFuel input))
      LocalizedAuxiliaryLabel)) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, Certificate.Dependency.lookup facts
      (input.certified.localizedFinalOccurrenceExecutable
        (LocalizedNoDoubleReference.carrierFuel input) center))

/-- The cached report path used when the ranked check refuses: the cached reference tabulation.  The
explicit `match` in `cachedAnalyze` keeps this computation from being performed eagerly. -/
def cachedAnalyzeFallback (input : LocalizedNoDoubleReference.Input) :
    List (Nat × Option LocalizedAuxiliaryLabel) :=
  centersLookup input (cachedReferenceFacts input)

/-- **The cached center report.**  When the ranked check accepts, the report is read off the accepted
ranked facts; otherwise it falls back to the cached reference tabulation.  Every canonical center is
reported, entry for entry. -/
def cachedAnalyze (input : LocalizedNoDoubleReference.Input) :
    List (Nat × Option LocalizedAuxiliaryLabel) :=
  match cachedCheckProposals? input with
  | some facts => centersLookup input facts
  | none => cachedAnalyzeFallback input

/-- The reference report is the projection of the reference facts. -/
theorem analyze_eq_centersLookup (input : LocalizedNoDoubleReference.Input) :
    LocalizedNoDoubleReference.analyze input =
      centersLookup input (LocalizedNoDoubleReference.evaluatedFacts input) := rfl

/-- The fallback branch is exact: the cached reference tabulation reports exactly the reference
report. -/
theorem cachedAnalyzeFallback_eq_analyze (input : LocalizedNoDoubleReference.Input) :
    cachedAnalyzeFallback input = LocalizedNoDoubleReference.analyze input := by
  rw [cachedAnalyzeFallback, analyze_eq_centersLookup,
    cachedReferenceFacts_eq_evaluatedFacts input]

/-- **Main report equality.**  The cached runtime reports exactly the reference report — every
detected center with its optional computed label, nothing dropped, reordered or invented. -/
theorem cachedAnalyze_eq_analyze (input : LocalizedNoDoubleReference.Input) :
    cachedAnalyze input = LocalizedNoDoubleReference.analyze input := by
  have lookupEq : Certificate.Dependency.lookup (cachedCertificateFacts input) =
      Certificate.Dependency.lookup (LocalizedNoDoubleReference.evaluatedFacts input) := by
    rw [cachedCertificateFacts_lookup_eq_evaluatedState input]
    rfl
  rw [cachedAnalyze, cachedCheckProposals?_eq_some_cachedCertificateFacts input]
  simp only [centersLookup, analyze_eq_centersLookup input]
  rw [lookupEq]

/-- The cached report has exactly one entry per detected center: no filtering. -/
theorem cachedAnalyze_length (input : LocalizedNoDoubleReference.Input) :
    (cachedAnalyze input).length = input.certified.canonicalTetrahedralCenters.length := by
  rw [cachedAnalyze_eq_analyze input]
  exact LocalizedNoDoubleReference.analyze_length input

/-- Every detected center is reported by the cached runtime, with its atom index. -/
theorem cachedAnalyze_center_reported (input : LocalizedNoDoubleReference.Input)
    (center : input.certified.TetrahedralCenter)
    (present : center ∈ input.certified.canonicalTetrahedralCenters) :
    ∃ label : Option LocalizedAuxiliaryLabel, (center.val.val, label) ∈ cachedAnalyze input := by
  rw [cachedAnalyze_eq_analyze input]
  exact LocalizedNoDoubleReference.analyze_center_reported input center present

end LocalizedNoDoubleCachedEvaluation

end TetraStereo.OneCenter
