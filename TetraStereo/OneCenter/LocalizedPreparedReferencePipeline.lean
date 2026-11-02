import TetraStereo.OneCenter.LocalizedExtendedDemandPreparation
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitEngineBridge

set_option autoImplicit false






































namespace TetraStereo.OneCenter.LocalizedExtendedShortCircuit.PreparedPipeline

open CertifiedLocalizedCIPInput Certificate.Dependency

/-! ## Semantic adapter around the prepared evaluator -/

/-- Operational semantics whose executable rule is the prepared evaluator.  This is the only
place where the prepared rule enters the generic certificate machinery. -/
def preparedSemantics (input : Input) (prep : Prepared.Preparation input) :
    input.certified.LocalizedAuxiliaryRuleSemantics (carrierFuel input) where
  DeclarativeDerivation := OperationalOutcome input (carrierFuel input)
  executableRule := Prepared.evaluatorUsingPreparation input prep
  derivation_executable_iff := by
    intros
    rw [Prepared.evaluatorUsingPreparation_eq]
    rfl

/-- The prepared semantics is the production runtime semantics. -/
theorem preparedSemantics_eq (input : Input) (prep : Prepared.Preparation input) :
    preparedSemantics input prep = runtimeSemantics input (carrierFuel input) := by
  simp only [preparedSemantics, runtimeSemantics, Prepared.evaluatorUsingPreparation_eq]

/-- Occurrence system driven by the prepared evaluator. -/
def preparedSystem (input : Input) (prep : Prepared.Preparation input) :=
  input.certified.localizedCertificateSystem (carrierFuel input) (preparedSemantics input prep)

/-- The prepared system is the production runtime system. -/
theorem preparedSystem_eq (input : Input) (prep : Prepared.Preparation input) :
    preparedSystem input prep = runtimeSystem input := by
  unfold preparedSystem runtimeSystem
  rw [preparedSemantics_eq]

/-! ## One ranked production over the materialized cache -/

/-- The ranked certificate order of the carrier already held by `prep.cache`.  This is a stable
merge sort of the materialized list: it neither calls `localizedOccurrenceCarrier` nor builds a
new carrier. -/
def preparedCertificateOrder (input : Input) (prep : Prepared.Preparation input) :
    List (Occurrence input) :=
  Certificate.FiniteRankedOrder.rankedOrder
    (input.certified.localizedCertificateRank (carrierFuel input)) prep.cache.carrier

/-- The materialized order is exactly the repository's certificate order. -/
theorem preparedCertificateOrder_eq (input : Input) (prep : Prepared.Preparation input) :
    preparedCertificateOrder input prep =
      input.certified.localizedCertificateOrder (carrierFuel input) := by
  unfold preparedCertificateOrder CertifiedLocalizedCIPInput.localizedCertificateOrder
  rw [prep.cache.exact]

/-- The prepared reference nodes: one ranked production over the carrier, child reader and
dependency table already materialized in `prep.cache`, with the prepared executable rule.
This is the only definition in this module that calls `Certificate.Dependency.produce`. -/
def preparedReferenceNodes (input : Input) (prep : Prepared.Preparation input) : Nodes input :=
  produce (preparedSystem input prep) (Cached.dependenciesUsingCache input prep.cache)
    (preparedCertificateOrder input prep)

/-- Facts are exactly the target/outcome projection of the node list produced by
`preparedReferenceNodes`.  This definition contains no call to `produce`, to a dependency lookup,
or to an evaluator. -/
def preparedReferenceFacts (input : Input) (prep : Prepared.Preparation input) : Facts input :=
  (preparedReferenceNodes input prep).map fun node => (node.target, node.outcome)

/-- Source-level statement of the fact projection: the facts are the single production's pairs. -/
theorem preparedReferenceFacts_eq_map (input : Input) (prep : Prepared.Preparation input) :
    preparedReferenceFacts input prep =
      (preparedReferenceNodes input prep).map
        (fun node => (node.target, node.outcome)) := rfl

/-- State of the prepared reference iteration, read from the single fact projection. -/
def preparedReferenceState (input : Input) (prep : Prepared.Preparation input) :
    input.certified.LocalizedAuxiliaryState (carrierFuel input) :=
  lookup (preparedReferenceFacts input prep)

theorem preparedReferenceNodes_eq (input : Input) (prep : Prepared.Preparation input) :
    preparedReferenceNodes input prep = referenceNodes input := by
  unfold preparedReferenceNodes referenceNodes
    CertifiedLocalizedCIPInput.localizedCertificateNodes
  rw [preparedSystem_eq, Cached.dependenciesUsingCache_eq, preparedCertificateOrder_eq]
  rfl

theorem preparedReferenceFacts_eq (input : Input) (prep : Prepared.Preparation input) :
    preparedReferenceFacts input prep = referenceFacts input := by
  unfold preparedReferenceFacts referenceFacts
    CertifiedLocalizedCIPInput.localizedCertificateFacts
  rw [preparedReferenceNodes_eq]
  rfl

theorem preparedReferenceState_eq (input : Input) (prep : Prepared.Preparation input) :
    preparedReferenceState input prep = referenceState input := by
  unfold preparedReferenceState referenceState
  exact congrArg lookup (preparedReferenceFacts_eq input prep)

/-- The generic producer accepts the prepared reference nodes with exactly the prepared facts. -/
theorem preparedReference_check (input : Input) (prep : Prepared.Preparation input) :
    check (preparedSystem input prep) (dependencies input)
        (preparedReferenceNodes input prep) =
      some (preparedReferenceFacts input prep) := by
  rw [preparedSystem_eq, preparedReferenceNodes_eq, preparedReferenceFacts_eq]
  exact reference_check input

/-- The same production is accepted when replayed against the dependency table materialized in
`prep.cache`.  The replay therefore uses the cached table directly rather than re-enumerating
the carrier or recomputing dependency lists. -/
theorem preparedReference_check_usingCache (input : Input) (prep : Prepared.Preparation input) :
    check (preparedSystem input prep) (Cached.dependenciesUsingCache input prep.cache)
        (preparedReferenceNodes input prep) =
      some (preparedReferenceFacts input prep) := by
  rw [preparedSystem_eq, Cached.dependenciesUsingCache_eq, preparedReferenceNodes_eq,
    preparedReferenceFacts_eq]
  exact reference_check input

/-- Reference evaluation whose producer runs with the same one preparation pass.  The node list is
bound once; the facts are its target/outcome projection and are **not** produced by a second call
to `produce`.  Its public invariant is the existing checker invariant; the produced facts are
proved equal to the plain reference facts below. -/
def preparedReferenceEvaluation (input : Input) (prep : Prepared.Preparation input) :
    Evaluation input :=
  let nodes := preparedReferenceNodes input prep
  { nodes
    facts := nodes.map fun node => (node.target, node.outcome)
    accepted := by
      dsimp only [nodes]
      rw [preparedReferenceNodes_eq]
      exact reference_accepted input }

/-- The runnable evaluation exposes exactly the single ranked production: its node field is that
production and its fact field is the projection of the same list. -/
theorem preparedReferenceEvaluation_production (input : Input)
    (prep : Prepared.Preparation input) :
    (preparedReferenceEvaluation input prep).nodes = preparedReferenceNodes input prep ∧
      (preparedReferenceEvaluation input prep).facts =
        (preparedReferenceNodes input prep).map
          (fun node => (node.target, node.outcome)) :=
  ⟨rfl, rfl⟩

theorem preparedReferenceEvaluation_facts (input : Input) (prep : Prepared.Preparation input) :
    (preparedReferenceEvaluation input prep).facts = referenceFacts input := by
  dsimp only [preparedReferenceEvaluation]
  rw [preparedReferenceNodes_eq]
  rfl

theorem preparedReferenceEvaluation_nodes (input : Input) (prep : Prepared.Preparation input) :
    (preparedReferenceEvaluation input prep).nodes = referenceNodes input :=
  preparedReferenceNodes_eq input prep

/-- The prepared reference report is the exact reference report. -/
theorem preparedReference_report_eq_reference (input : Input) (prep : Prepared.Preparation input) :
    report input (preparedReferenceFacts input prep) = analyze input :=
  evaluation_report_eq_reference input (preparedReferenceEvaluation input prep)

/-- Every positive prepared-reference outcome carries the independent recursive rule evidence. -/
theorem preparedReference_positive_sound (input : Input) (prep : Prepared.Preparation input)
    (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel)
    (computed : preparedReferenceState input prep target = some descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
      target (input.certified.localizedDependencyView (preparedReferenceState input prep) target)
      descriptor := by
  rw [preparedReferenceState_eq input prep] at computed ⊢
  exact reference_positive_sound input target descriptor computed

/-! ## Candidate replay over the prepared system -/

/-- Replay candidate nodes against the prepared system, using the dependency table and carrier
already materialized in `prep.cache`.  Acceptance requires the same `Nodup` and full-carrier
coverage conditions as the existing checked pipeline. -/
def checkPrepared? (input : Input) (prep : Prepared.Preparation input) (nodes : Nodes input) :
    Option (Facts input) := do
  let facts ← check (preparedSystem input prep)
    (Cached.dependenciesUsingCache input prep.cache) nodes
  if (facts.map Prod.fst).Nodup ∧
      prep.cache.carrier.all
        (fun occurrence => decide (occurrence ∈ facts.map Prod.fst)) = true
    then some facts else none

/-- Prepared replay is extensionally the public checked pipeline. -/
theorem checkPrepared?_eq (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) :
    checkPrepared? input prep nodes = checkProposals? input nodes := by
  simp only [checkPrepared?, checkProposals?, preparedSystem_eq,
    Cached.dependenciesUsingCache_eq, prep.cache.exact, covered]

/-- Prepared replay is extensionally the existing cached replay. -/
theorem checkPrepared?_eq_cached (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) :
    checkPrepared? input prep nodes = Cached.checkUsingCache? input prep.cache nodes := by
  rw [checkPrepared?_eq, Cached.checkUsingCache?_eq]

/-- Exact `some` behaviour of prepared replay in terms of the public checker. -/
theorem checkPrepared?_exact (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input) :
    checkPrepared? input prep nodes = some facts ↔
      check (runtimeSystem input) (dependencies input) nodes = some facts ∧
        (facts.map Prod.fst).Nodup ∧ covered input facts = true := by
  rw [checkPrepared?_eq]
  exact checkProposals?_exact input nodes facts

/-- Exact `some` behaviour of prepared replay directly at the prepared system and cached
dependency table. -/
theorem checkPrepared?_exactAtSystem (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input) :
    checkPrepared? input prep nodes = some facts ↔
      check (preparedSystem input prep)
          (Cached.dependenciesUsingCache input prep.cache) nodes = some facts ∧
        (facts.map Prod.fst).Nodup ∧
          prep.cache.carrier.all
            (fun occurrence => decide (occurrence ∈ facts.map Prod.fst)) = true := by
  rw [checkPrepared?_exact input prep nodes facts]
  constructor
  · rintro ⟨checked, nodup, cover⟩
    refine ⟨?_, nodup, ?_⟩
    · rwa [preparedSystem_eq, Cached.dependenciesUsingCache_eq]
    · unfold covered at cover
      rw [prep.cache.exact]
      exact cover
  · rintro ⟨checked, nodup, cover⟩
    refine ⟨?_, nodup, ?_⟩
    · rw [preparedSystem_eq, Cached.dependenciesUsingCache_eq] at checked
      exact checked
    · unfold covered
      rw [prep.cache.exact] at cover
      exact cover

/-- Rejection is exactly rejection by the public checker.  This includes the empty-candidate
case: `none` is returned only when replay actually fails or coverage is incomplete. -/
theorem checkPrepared?_none_iff (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) :
    checkPrepared? input prep nodes = none ↔ checkProposals? input nodes = none := by
  rw [checkPrepared?_eq]

/-- Acceptance exposes the exact prepared check, without weakening hypotheses. -/
theorem checkPrepared?_sound (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input)
    (accepted : checkPrepared? input prep nodes = some facts) :
    check (preparedSystem input prep)
        (Cached.dependenciesUsingCache input prep.cache) nodes = some facts ∧
      (facts.map Prod.fst).Nodup ∧
        prep.cache.carrier.all
          (fun occurrence => decide (occurrence ∈ facts.map Prod.fst)) = true :=
  (checkPrepared?_exactAtSystem input prep nodes facts).mp accepted

/-! ## Accepted candidate correctness -/

/-- An accepted candidate computes exactly the reference state. -/
theorem accepted_eq_reference (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input)
    (accepted : checkPrepared? input prep nodes = some facts) :
    lookup facts = referenceState input := by
  have checkedPublic : checkProposals? input nodes = some facts :=
    (checkPrepared?_eq input prep nodes).symm.trans accepted
  exact checked_eq_reference input nodes facts checkedPublic

/-- An accepted candidate is a CIP model of the prepared system itself. -/
theorem accepted_model (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input)
    (accepted : checkPrepared? input prep nodes = some facts) :
    (preparedSystem input prep).CIPModel (lookup facts) := by
  have checkedPublic : checkProposals? input nodes = some facts :=
    (checkPrepared?_eq input prep nodes).symm.trans accepted
  have model := checked_model input nodes facts checkedPublic
  rwa [← preparedSystem_eq] at model

/-- Every positive accepted outcome carries the independent recursive rule evidence. -/
theorem accepted_positive_sound (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input)
    (accepted : checkPrepared? input prep nodes = some facts)
    (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel)
    (computed : lookup facts target = some descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
      target (input.certified.localizedDependencyView (lookup facts) target) descriptor := by
  have checkedPublic : checkProposals? input nodes = some facts :=
    (checkPrepared?_eq input prep nodes).symm.trans accepted
  exact evaluation_positive_sound input ⟨nodes, facts, checkedPublic⟩ target descriptor computed

/-! ## Runnable checked fast path with prepared reference fallback -/

/-- One preparation is supplied by the caller.  Candidate replay and, on rejection, the ranked
reference iteration both use that same value.  On the fallback branch the reference production is
performed exactly once. -/
def evaluatePrepared (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) : Evaluation input :=
  match checked : checkPrepared? input prep nodes with
  | some facts => ⟨nodes, facts, (checkPrepared?_eq input prep nodes).symm.trans checked⟩
  | none => preparedReferenceEvaluation input prep

/-- The result never changes the reference report, on either branch. -/
theorem evaluatePrepared_report_eq_reference (input : Input)
    (prep : Prepared.Preparation input) (nodes : Nodes input) :
    report input (evaluatePrepared input prep nodes).facts = analyze input :=
  evaluation_report_eq_reference input (evaluatePrepared input prep nodes)

theorem evaluatePrepared_facts_accepted (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input)
    (accepted : checkPrepared? input prep nodes = some facts) :
    (evaluatePrepared input prep nodes).facts = facts := by
  unfold evaluatePrepared
  split
  · rename_i values checked
    have valuesEq : values = facts := Option.some.inj (checked.symm.trans accepted)
    subst valuesEq
    rfl
  · rename_i checked
    rw [checked] at accepted
    simp at accepted

theorem evaluatePrepared_nodes_accepted (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input)
    (accepted : checkPrepared? input prep nodes = some facts) :
    (evaluatePrepared input prep nodes).nodes = nodes := by
  unfold evaluatePrepared
  split
  · rename_i values checked
    have valuesEq : values = facts := Option.some.inj (checked.symm.trans accepted)
    subst valuesEq
    rfl
  · rename_i checked
    rw [checked] at accepted
    simp at accepted

/-- A rejected or incomplete candidate falls to the prepared reference evaluation. -/
theorem evaluatePrepared_rejected (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input)
    (rejected : checkPrepared? input prep nodes = none) :
    evaluatePrepared input prep nodes = preparedReferenceEvaluation input prep := by
  unfold evaluatePrepared
  split
  · rename_i values checked
    rw [checked] at rejected
    simp at rejected
  · rename_i checked
    rfl

theorem evaluatePrepared_rejected_facts (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input)
    (rejected : checkPrepared? input prep nodes = none) :
    (evaluatePrepared input prep nodes).facts = referenceFacts input := by
  rw [evaluatePrepared_rejected input prep nodes rejected]
  exact preparedReferenceFacts_eq input prep

theorem evaluatePrepared_rejected_state (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input)
    (rejected : checkPrepared? input prep nodes = none) :
    lookup (evaluatePrepared input prep nodes).facts = referenceState input := by
  rw [evaluatePrepared_rejected_facts input prep nodes rejected]
  rfl

theorem evaluatePrepared_accepted_state (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input)
    (accepted : checkPrepared? input prep nodes = some facts) :
    lookup (evaluatePrepared input prep nodes).facts = referenceState input := by
  rw [evaluatePrepared_facts_accepted input prep nodes facts accepted]
  exact accepted_eq_reference input prep nodes facts accepted

theorem evaluatePrepared_accepted_report (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (facts : Facts input)
    (accepted : checkPrepared? input prep nodes = some facts) :
    report input facts = analyze input := by
  simpa only [evaluatePrepared_facts_accepted input prep nodes facts accepted] using
    evaluatePrepared_report_eq_reference input prep nodes

/-- Positive outcomes of the runnable pipeline have independent rule evidence. -/
theorem evaluatePrepared_positive_sound (input : Input) (prep : Prepared.Preparation input)
    (nodes : Nodes input) (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel)
    (computed : lookup (evaluatePrepared input prep nodes).facts target = some descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
      target
      (input.certified.localizedDependencyView
        (lookup (evaluatePrepared input prep nodes).facts) target) descriptor :=
  evaluation_positive_sound input (evaluatePrepared input prep nodes) target descriptor computed



/-- Candidates come from the existing graph engine, unchanged. -/
abbrev propose : Proposer :=
  _root_.TetraStereo.OneCenter.LocalizedExtendedShortCircuit.EngineBridge.propose



def evaluate (input : Input) : Evaluation input :=
  let prep := Prepared.prepare input
  evaluatePrepared input prep (propose input)

/-- The engine pipeline buffers exactly one preparation. -/
theorem evaluate_eq_prepared (input : Input) :
    evaluate input = evaluatePrepared input (Prepared.prepare input) (propose input) := rfl

def analyze (input : Input) : Report :=
  report input (evaluate input).facts

theorem evaluate_report_eq_reference (input : Input) :
    report input (evaluate input).facts =
      _root_.TetraStereo.OneCenter.LocalizedExtendedShortCircuit.analyze input :=
  evaluation_report_eq_reference input (evaluate input)

/-- The engine pipeline's report is exactly the reference report. -/
theorem analyze_eq_reference (input : Input) :
    analyze input =
      _root_.TetraStereo.OneCenter.LocalizedExtendedShortCircuit.analyze input :=
  evaluate_report_eq_reference input

/-- Positive pipeline outcomes carry independent rule evidence. -/
theorem evaluate_positive_sound (input : Input) (target : Occurrence input)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : lookup (evaluate input).facts target = some descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
      target (input.certified.localizedDependencyView (lookup (evaluate input).facts) target)
      descriptor :=
  evaluation_positive_sound input (evaluate input) target descriptor computed

/-! ## Source admission wrapper -/

def evaluateSource? (source : AuthoritativeChemicalInput)
    (proposeFn : Proposer := propose) :
    Option ((input : Input) × Evaluation input) := do
  let input ← admitSource? source
  let prep := Prepared.prepare input
  pure ⟨input, evaluatePrepared input prep (proposeFn input)⟩

def analyzeSource? (source : AuthoritativeChemicalInput)
    (proposeFn : Proposer := propose) : Option Report :=
  (evaluateSource? source proposeFn).map fun result =>
    report result.1 result.2.facts

/-- No admission, no evaluation: the wrapper returns `none` exactly when admission fails. -/
theorem evaluateSource?_none_iff (source : AuthoritativeChemicalInput)
    (proposeFn : Proposer) :
    evaluateSource? source proposeFn = none ↔ admitSource? source = none := by
  unfold evaluateSource?
  cases admitted : admitSource? source with
  | none => simp
  | some input => simp

/-- The admitted evaluation exposes the prepared pipeline on its unique input. -/
theorem evaluateSource?_eq_prepared (source : AuthoritativeChemicalInput)
    (proposeFn : Proposer) :
    evaluateSource? source proposeFn =
      (admitSource? source).map (fun input =>
        ⟨input, evaluatePrepared input (Prepared.prepare input) (proposeFn input)⟩) := by
  unfold evaluateSource?
  cases admitted : admitSource? source with
  | none => simp
  | some input => simp

theorem analyzeSource?_none_iff (source : AuthoritativeChemicalInput)
    (proposeFn : Proposer) :
    analyzeSource? source proposeFn = none ↔ admitSource? source = none := by
  unfold analyzeSource?
  rw [Option.map_eq_none_iff]
  exact evaluateSource?_none_iff source proposeFn

/-- The source wrapper reports exactly the reference analysis of every admitted input. -/
theorem analyzeSource?_eq_reference (source : AuthoritativeChemicalInput)
    (proposeFn : Proposer) :
    analyzeSource? source proposeFn =
      (admitSource? source).map
        (_root_.TetraStereo.OneCenter.LocalizedExtendedShortCircuit.analyze) := by
  unfold analyzeSource?
  rw [evaluateSource?_eq_prepared]
  cases admitted : admitSource? source with
  | none => rfl
  | some input =>
      simp only [Option.map_some]
      exact congrArg some (evaluation_report_eq_reference input
        (evaluatePrepared input (Prepared.prepare input) (proposeFn input)))

end TetraStereo.OneCenter.LocalizedExtendedShortCircuit.PreparedPipeline
