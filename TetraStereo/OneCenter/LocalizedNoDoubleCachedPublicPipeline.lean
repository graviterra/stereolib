import TetraStereo.OneCenter.LocalizedNoDoublePublicPipeline
import TetraStereo.OneCenter.LocalizedNoDoubleCachedEvaluation

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedNoDoubleReference.CachedPublic
open CertifiedLocalizedCIPInput Certificate.Dependency
open LocalizedNoDoubleCachedEvaluation (cachedRuntimeSemantics cachedCertificateDependencies
  cachedReferenceFacts cachedGeneratedNodes centersLookup)

/-- Replay arbitrary proposals with the proved cached evaluator, then require duplicate-free complete
coverage. Producer and checker each construct their own shared carrier and dependency table. -/
def checkProposals? (input : Input) (nodes : Public.Proposals input) :=
  let cache := LocalizedNoDoubleCachedEvaluation.buildRuntimeCache input
  (check (input.certified.localizedCertificateSystem (carrierFuel input)
      (LocalizedNoDoubleCachedEvaluation.runtimeSemanticsUsingCache input cache))
      (LocalizedNoDoubleCachedEvaluation.dependenciesUsingCache input cache) nodes).bind fun facts =>
    if (facts.map Prod.fst).Nodup ∧ carrierCoveredBool input facts = true
    then some facts else none

theorem checkProposals?_eq_original (input : Input) (nodes : Public.Proposals input) :
    checkProposals? input nodes = LocalizedNoDoubleReference.checkProposals? input nodes := by
  dsimp only [checkProposals?, LocalizedNoDoubleReference.checkProposals?]
  rw [LocalizedNoDoubleCachedEvaluation.runtimeSemanticsUsingCache_eq_cachedRuntimeSemantics,
    LocalizedNoDoubleCachedEvaluation.dependenciesUsingCache_eq_cachedCertificateDependencies,
    LocalizedNoDoubleCachedEvaluation.cachedCertificateSystem_eq_certificateSystem input,
    LocalizedNoDoubleCachedEvaluation.cachedCertificateDependencies_eq_localizedCertificateDependencies input]
  rfl

/-- Rejection evaluates the cached reference branch lazily. -/
def evaluateCheckedOrReference (input : Input) (nodes : Public.Proposals input) :=
  match checkProposals? input nodes with
  | some facts => facts
  | none => cachedReferenceFacts input

theorem evaluateCheckedOrReference_eq_original (input : Input) (nodes : Public.Proposals input) :
    evaluateCheckedOrReference input nodes =
      LocalizedNoDoubleReference.evaluateCheckedOrReference input nodes := by
  unfold evaluateCheckedOrReference LocalizedNoDoubleReference.evaluateCheckedOrReference
  rw [checkProposals?_eq_original]
  cases LocalizedNoDoubleReference.checkProposals? input nodes with
  | none => exact LocalizedNoDoubleCachedEvaluation.cachedReferenceFacts_eq_evaluatedFacts input
  | some facts => rfl

/-- Complete canonical-center report from checked cached facts or the cached reference fallback. -/
def analyzeWithProposals (input : Input) (nodes : Public.Proposals input) : Public.Report :=
  centersLookup input (evaluateCheckedOrReference input nodes)

theorem analyzeWithProposals_eq_reference (input : Input) (nodes : Public.Proposals input) :
    analyzeWithProposals input nodes = analyze input := by
  rw [analyzeWithProposals, evaluateCheckedOrReference_eq_original]
  exact Public.analyzeWithProposals_eq_analyze input nodes


def analyzeSource? (source : AuthoritativeChemicalInput)
    (propose : Public.Proposer := cachedGeneratedNodes) : Option Public.Report := do
  let input ← admitSource? source
  pure (analyzeWithProposals input (propose input))

theorem analyzeSource?_eq_reference (source : AuthoritativeChemicalInput) (propose : Public.Proposer) :
    analyzeSource? source propose = (admitSource? source).map analyze := by
  unfold analyzeSource?
  cases admitSource? source with
  | none => rfl
  | some input => simp only [analyzeWithProposals_eq_reference]; rfl

/-- OpenSMILES and exact hydrogen-expanded coordinates, with checked cached proposals and fallback. -/
def analyzeSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) (propose : Public.Proposer := cachedGeneratedNodes) :
    Except ParserError (Option Public.Report) :=
  (admitSmilesSpatial? text spatial cycles).map fun admitted =>
    admitted.map fun input => analyzeWithProposals input (propose input)

theorem analyzeSmilesSpatial?_eq_reference (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle) (propose : Public.Proposer) :
    analyzeSmilesSpatial? text spatial cycles propose =
      (admitSmilesSpatial? text spatial cycles).map (Option.map analyze) := by
  unfold analyzeSmilesSpatial?
  simp only [analyzeWithProposals_eq_reference]

end TetraStereo.OneCenter.LocalizedNoDoubleReference.CachedPublic
