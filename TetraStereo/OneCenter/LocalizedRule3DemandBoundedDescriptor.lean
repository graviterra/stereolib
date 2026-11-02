import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer
import TetraStereo.OneCenter.LocalizedShortCircuitWithChildren
import TetraStereo.OneCenter.LocalizedShortCircuitCachedPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.DemandBounded

/-- Use a checked demand bound only when it lies below production fuel. Discovery refusal or
an excessive bound retains the existing production computation. -/
def frame? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  let productionFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  match input.prepareRule3DemandPlan cursors with
  | .error _ => WithChildren.buildLocalizedShortCircuitRule3FrameExec?
      input readChildren target view productionFuel cursors
  | .ok plan =>
      if plan.bound ≤ productionFuel then
        WithChildren.buildLocalizedShortCircuitRule3FrameExec?
          input readChildren target view plan.bound cursors
      else WithChildren.buildLocalizedShortCircuitRule3FrameExec?
        input readChildren target view productionFuel cursors

/-- Every optional outcome is preserved; no callback-free or successful-geometry premise. -/
theorem frame?_eq_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    frame? input readChildren target view cursors =
      input.buildLocalizedShortCircuitRule3FrameExec? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) cursors := by
  have frameEq := fun budget =>
    (WithChildren.shortCircuitRule3_mutual_eq_original
      input readChildren readEq target view budget).2 cursors
  unfold frame?
  cases found : input.prepareRule3DemandPlan cursors with
  | error failure => exact frameEq _
  | ok plan =>
      dsimp only
      split
      next enough =>
        exact (frameEq plan.bound).trans (plan.evaluate_eq_above target view _ enough)
      next tooLarge => exact frameEq _

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

theorem keyFrame?_eq_production
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    keyFrame? input readChildren target view base =
      input.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame? target view base := by
  have rule45Eq : WithChildren.buildLocalizedRerootCompoundRule45KeyExec? input readChildren target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) =
      input.buildLocalizedRerootCompoundRule45KeyExec? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) := by
    funext cursor
    exact WithChildren.buildLocalizedRerootCompoundRule45KeyExec?_eq_original
      input readChildren readEq target view _ cursor
  simp only [keyFrame?, buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?,
    frame?_eq_production input readChildren readEq, rule45Eq]

theorem spatialEvidence?_eq_production
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    spatialEvidence? input readChildren target view =
      input.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence? target view := by
  simp only [spatialEvidence?, localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?,
    WithChildren.localizedNoDoubleFourLigandFrameExec?_eq_original input readChildren readEq,
    keyFrame?_eq_production input readChildren readEq]

/-- Exact agreement with the successor production descriptor, including refusals and actual
Rule5 pseudo counts. The checked graph bound changes only the outer Rule3 frame budget. -/
theorem descriptor?_eq_production
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    descriptor? input readChildren target view =
      input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view := by
  simp only [descriptor?, localizedOccurrenceShortCircuitRule3Through5Descriptor?,
    spatialEvidence?_eq_production input readChildren readEq]

/-- Keep the existing certified terminal-tie rejection ahead of demand-graph discovery. -/
def descriptorWithTerminalTie? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => none
  | some _ =>
      match WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target with
      | none => none
      | some base =>
          match TerminalTie.refusalCertificate? input readChildren target view base with
          | some _ => none
          | none => descriptor? input readChildren target view

theorem descriptorWithTerminalTie?_eq_production
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    descriptorWithTerminalTie? input readChildren target view =
      input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view := by
  have unchanged : descriptor? input readChildren target view =
      WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor? input readChildren target view :=
    (descriptor?_eq_production input readChildren readEq target view).trans
      (WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor?_eq_original
        input readChildren readEq target view).symm
  have early : descriptorWithTerminalTie? input readChildren target view =
      TerminalTie.descriptor? input readChildren target view := by
    simp only [descriptorWithTerminalTie?, TerminalTie.descriptor?, unchanged]
    rfl
  exact early.trans ((TerminalTie.descriptor?_eq_original input readChildren target view).trans
    (WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor?_eq_original
      input readChildren readEq target view))

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.DemandBounded

namespace TetraStereo.OneCenter.LocalizedShortCircuit.DemandBounded
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- Shared cached child reader with automatic checked demand bounds and production fallback. -/
def evaluatorUsingCache (input : Input) (cache : Cached.RuntimeCache input) :
    input.certified.LocalizedRestrictedEvaluator (carrierFuel input) :=
  CertifiedLocalizedCIPInput.DemandBounded.descriptorWithTerminalTie? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier)

theorem evaluatorUsingCache_eq (input : Input) (cache : Cached.RuntimeCache input) :
    evaluatorUsingCache input cache = evaluator input (carrierFuel input) := by
  funext target view
  apply CertifiedLocalizedCIPInput.DemandBounded.descriptorWithTerminalTie?_eq_production
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

/-- Reuse the existing ranked dependency producer with the exactly equal evaluator. -/
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

end TetraStereo.OneCenter.LocalizedShortCircuit.DemandBounded
