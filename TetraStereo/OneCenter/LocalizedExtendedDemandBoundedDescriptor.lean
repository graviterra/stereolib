import TetraStereo.OneCenter.LocalizedExtendedDemandRankAdapter
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitCachedPipeline
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitEngineBridge

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedDemandBounded













/-- Use a checked demand bound only when it lies below production fuel. Discovery refusal or an
excessive bound retains the existing extended production computation. -/
def frame? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  let productionFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  match input.prepareRule3DemandPlan cursors with
  | .error _ => WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
      input readChildren target view productionFuel cursors
  | .ok plan =>
      if plan.bound ≤ productionFuel then
        WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
          input readChildren target view plan.bound cursors
      else WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
        input readChildren target view productionFuel cursors

/-- Every optional outcome is preserved; no callback-free certificate, successful geometry or
successful callback is assumed.  The computed rank certificate alone justifies the budget. -/
theorem frame?_eq_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    frame? input readChildren target view cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) cursors := by
  have frameEq := fun budget =>
    (WithChildren.extendedShortCircuitRule3_mutual_eq_original
      input readChildren readEq target view budget).2 cursors
  unfold frame?
  cases found : input.prepareRule3DemandPlan cursors with
  | error failure => exact frameEq _
  | ok plan =>
      dsimp only
      split
      next enough =>
        exact (frameEq plan.bound).trans
          (plan.extended_evaluate_eq_above target view _ enough)
      next tooLarge => exact frameEq _

/-- Descriptor-bearing four-ligand frame.  The Rule3 budget is selected by `frame?`; the
Rule4a--5 budget, key lengths and frame assembly are exactly the production ones. -/
def keyFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (readChildren : input.LocalizedRerootCursor carrierFuel →
        Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let rule3Frame ← frame? input readChildren target view base.cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM
      (WithChildren.buildLocalizedRerootCompoundRule45KeyExec? input readChildren target view rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame
          rule3Length
          rule45Keys
          rule45Length }
    else none
  else none

theorem keyFrame?_eq_production
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    keyFrame? input readChildren target view base =
      input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? target view base := by
  have rule45Eq : WithChildren.buildLocalizedRerootCompoundRule45KeyExec? input readChildren target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) =
      input.buildLocalizedRerootCompoundRule45KeyExec? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) := by
    funext cursor
    exact WithChildren.buildLocalizedRerootCompoundRule45KeyExec?_eq_original
      input readChildren readEq target view _ cursor
  simp only [keyFrame?, buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?,
    frame?_eq_production input readChildren readEq, rule45Eq]

def spatialEvidence?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (readChildren : input.LocalizedRerootCursor carrierFuel →
        Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target
  let keys ← keyFrame? input readChildren
    target view base
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

theorem spatialEvidence?_eq_production
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    spatialEvidence? input readChildren target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence? target view := by
  simp only [spatialEvidence?, localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?,
    WithChildren.localizedNoDoubleFourLigandFrameExec?_eq_original input readChildren readEq,
    keyFrame?_eq_production input readChildren readEq]

def descriptor?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (readChildren : input.LocalizedRerootCursor carrierFuel →
        Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← spatialEvidence? input readChildren
    target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- Exact agreement with the extended production descriptor, including every refusal and the
actual Rule5 pseudo count.  Only the outer Rule3 frame budget changes. -/
theorem descriptor?_eq_production
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    descriptor? input readChildren target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view := by
  simp only [descriptor?, localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?,
    spatialEvidence?_eq_production input readChildren readEq]

/-- Runtime dispatch.  A checked callback-free certificate keeps the existing linear
`ExtendedBounded` evaluator; otherwise the automatic demand-bounded descriptor is used.  The
certified terminal-tie rejection is evaluated first, so a rejected tie is never reinterpreted by
either evaluator. -/
def descriptorWithReady? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel →
      Option (List (input.LocalizedRerootCursor fuel)))
    (ready? : Option (input.LocalizedExtendedRule3NoCallbackCertificate fuel))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => none
  | some _ =>
      match WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target with
      | none => none
      | some base =>
          match ExtendedTerminalTie.refusalCertificate? input readChildren target view base with
          | some _ => none
          | none =>
              match ready? with
              | some _ => ExtendedBounded.descriptor? input readChildren target view
              | none => descriptor? input readChildren target view

/-- Universal exactness of the runtime dispatch: both branches, and both possible values of the
readiness option, compute the extended production descriptor. -/
theorem descriptorWithReady?_eq_production
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (ready? : Option (input.LocalizedExtendedRule3NoCallbackCertificate fuel))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    descriptorWithReady? input readChildren ready? target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view := by
  have unchanged :
      (match ready? with
        | some _ => ExtendedBounded.descriptor? input readChildren target view
        | none => descriptor? input readChildren target view) =
      WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        input readChildren target view := by
    cases ready? with
    | none =>
        exact (descriptor?_eq_production input readChildren readEq target view).trans
          (WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
            input readChildren readEq target view).symm
    | some ready =>
        exact (ExtendedBounded.descriptor?_eq_production input readChildren readEq ready
          target view).trans
          (WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
            input readChildren readEq target view).symm
  have early : descriptorWithReady? input readChildren ready? target view =
      ExtendedTerminalTie.descriptor? input readChildren target view := by
    simp only [descriptorWithReady?, ExtendedTerminalTie.descriptor?, unchanged]
    rfl
  exact early.trans ((ExtendedTerminalTie.descriptor?_eq_original input readChildren target view).trans
    (WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
      input readChildren readEq target view))

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedDemandBounded

namespace TetraStereo.OneCenter.LocalizedExtendedShortCircuit.DemandBounded
open CertifiedLocalizedCIPInput Certificate.Dependency





/-- Shared cached child reader with automatic checked demand bounds, the ready-only linear
shortcut, and certified terminal-tie rejection. -/
def evaluatorUsingCache (input : Input) (cache : Cached.RuntimeCache input) :
    input.certified.LocalizedRestrictedEvaluator (carrierFuel input) :=
  CertifiedLocalizedCIPInput.ExtendedDemandBounded.descriptorWithReady? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier) cache.ready?

theorem evaluatorUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input) :
    evaluatorUsingCache input cache = evaluator input (carrierFuel input) := by
  funext target view
  apply CertifiedLocalizedCIPInput.ExtendedDemandBounded.descriptorWithReady?_eq_production
  intro cursor
  rw [cache.exact]
  exact input.certified.localizedRerootChildrenFromCarrier?_eq_executable cursor

def semanticsUsingCache (input : Input) (cache : Cached.RuntimeCache input) :
    input.certified.LocalizedAuxiliaryRuleSemantics (carrierFuel input) where
  DeclarativeDerivation := OperationalOutcome input (carrierFuel input)
  executableRule := evaluatorUsingCache input cache
  derivation_executable_iff := by
    intros
    rw [evaluatorUsingCache_eq]
    rfl

theorem semanticsUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input) :
    semanticsUsingCache input cache = runtimeSemantics input (carrierFuel input) := by
  simp only [semanticsUsingCache, runtimeSemantics, evaluatorUsingCache_eq]

def systemUsingCache (input : Input) (cache : Cached.RuntimeCache input) :=
  input.certified.localizedCertificateSystem (carrierFuel input) (semanticsUsingCache input cache)

theorem systemUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input) :
    systemUsingCache input cache = runtimeSystem input := by
  unfold systemUsingCache runtimeSystem
  rw [semanticsUsingCache_eq]

/-- Reuse the existing ranked dependency producer through the exactly equal evaluator. -/
def nodesUsingCache (input : Input) (cache : Cached.RuntimeCache input) : Nodes input :=
  produce (systemUsingCache input cache) (Cached.dependenciesUsingCache input cache)
    (Certificate.FiniteRankedOrder.rankedOrder
      (input.certified.localizedCertificateRank (carrierFuel input)) cache.carrier)

theorem nodesUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input) :
    nodesUsingCache input cache = referenceNodes input := by
  unfold nodesUsingCache referenceNodes localizedCertificateNodes localizedCertificateOrder
  rw [systemUsingCache_eq, Cached.dependenciesUsingCache_eq, cache.exact]
  rfl

def referenceUsingCache (input : Input) (cache : Cached.RuntimeCache input) : Evaluation input :=
  let nodes := nodesUsingCache input cache
  { nodes
    facts := nodes.map (fun node => (node.target, node.outcome))
    accepted := by
      dsimp only [nodes]
      rw [nodesUsingCache_eq]
      exact reference_accepted input }

/-- Replay proposals against the exact demand-bounded evaluator.  Acceptance requires the public
checker result, target uniqueness and full materialized-carrier coverage. -/
def checkUsingCache? (input : Input) (cache : Cached.RuntimeCache input) (nodes : Nodes input) :
    Option (Facts input) := do
  let facts ← check (systemUsingCache input cache) (Cached.dependenciesUsingCache input cache) nodes
  if (facts.map Prod.fst).Nodup ∧
      cache.carrier.all (fun occurrence => decide (occurrence ∈ facts.map Prod.fst)) = true
    then some facts else none

theorem checkUsingCache?_eq (input : Input) (cache : Cached.RuntimeCache input) (nodes : Nodes input) :
    checkUsingCache? input cache nodes = checkProposals? input nodes := by
  simp only [checkUsingCache?, checkProposals?, systemUsingCache_eq,
    Cached.dependenciesUsingCache_eq, cache.exact, covered]

/-- Construct one cache, replay proposals against the exact extended evaluator, and lazily
produce the reference certificate when replay rejects. -/
def evaluate (input : Input) (nodes : Nodes input) : Evaluation input :=
  let cache := Cached.buildRuntimeCache input
  match checked : checkUsingCache? input cache nodes with
  | some facts => ⟨nodes, facts, (checkUsingCache?_eq input cache nodes).symm.trans checked⟩
  | none => referenceUsingCache input cache

def checkProposals? (input : Input) (nodes : Nodes input) : Option (Facts input) :=
  checkUsingCache? input (Cached.buildRuntimeCache input) nodes

theorem checkProposals?_eq (input : Input) (nodes : Nodes input) :
    checkProposals? input nodes =
      TetraStereo.OneCenter.LocalizedExtendedShortCircuit.checkProposals? input nodes :=
  checkUsingCache?_eq input (Cached.buildRuntimeCache input) nodes

/-- Every result, whether accepted or lazily produced, has the reference report. -/
theorem evaluate_report_eq (input : Input) (nodes : Nodes input) :
    report input (evaluate input nodes).facts = analyze input :=
  evaluation_report_eq_reference input (evaluate input nodes)

/-- Every result state is the existing extended reference state. -/
theorem evaluate_reference_eq (input : Input) (nodes : Nodes input) :
    lookup (evaluate input nodes).facts = referenceState input :=
  evaluation_eq_reference input (evaluate input nodes)

/-- Admit a source and evaluate it; by default no speculative proposals are offered. -/
def evaluateSource? (source : AuthoritativeChemicalInput)
    (propose : Proposer := emptyProposer) : Option ((input : Input) × Evaluation input) := do
  let input ← admitSource? source
  pure ⟨input, evaluate input (propose input)⟩



def evaluateFast (input : Input) : Evaluation input :=
  evaluate input (EngineBridge.propose input)

theorem evaluateFast_report_eq (input : Input) :
    report input (evaluateFast input).facts = analyze input :=
  evaluate_report_eq input _

end TetraStereo.OneCenter.LocalizedExtendedShortCircuit.DemandBounded
