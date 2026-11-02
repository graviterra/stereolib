import TetraStereo.OneCenter.LocalizedExtendedShortCircuitPipeline
import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.OneCenter.LocalizedUniversalFuelRuntimeAdapter

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedUniversalReference

open CertifiedLocalizedCIPInput Certificate.Dependency











































































/-! ## The runtime input and carrier budget -/

abbrev Input := LocalizedExtendedShortCircuit.Input
abbrev admitSource? := LocalizedExtendedShortCircuit.admitSource?

/-- The carrier budget is the existing pipeline budget. -/
abbrev carrierFuel (input : Input) : Nat := LocalizedExtendedShortCircuit.carrierFuel input

/-- The existing iteration bound. -/
abbrev iterationRounds (input : Input) : Nat := LocalizedExtendedShortCircuit.iterationRounds input

abbrev Occurrence (input : Input) := input.certified.LocalizedCIPOccurrence (carrierFuel input)
abbrev Facts (input : Input) := List (Fact (Occurrence input) LocalizedAuxiliaryLabel)
abbrev Nodes (input : Input) := List (Node (Occurrence input) LocalizedAuxiliaryLabel)
abbrev Report := List (Nat × Option LocalizedAuxiliaryLabel)

/-! ## The policy evaluator as a restricted occurrence rule -/

/-- The production universal evaluator at the universal-floored fuel policy.  This is the actual
parameterized production descriptor run at
`productionUniversalRule3EvaluationFuel`; it is not a second solver. -/
def evaluator (input : Input) (fuel : Nat) :
    input.certified.LocalizedRestrictedEvaluator fuel :=
  fun target view => input.certified.productionUniversalDescriptor? target view

/-- The evaluator performs the actual `descriptorAt?` call at the executable policy maximum of the
legacy descriptor-bearing production fuel and the input-derived universal Rule-3 bound.  This is
the exact runtime call; no inequality between the two budgets is asserted. -/
theorem evaluator_eq_descriptorAt_policy (input : Input) (fuel : Nat) :
    evaluator input fuel =
      fun target view => input.certified.descriptorAt? target view
        (input.certified.productionUniversalRule3EvaluationFuel fuel) := by
  funext target view
  rfl

/-- The policy evaluator, viewed as a function, is exactly the universal descriptor evaluator.
The proof is the supplied pointwise equality plus function extensionality. -/
theorem evaluator_eq_universalDescriptor (input : Input) (fuel : Nat) :
    evaluator input fuel =
      fun target view => input.certified.universalDescriptor? target view := by
  funext target view
  exact input.certified.productionUniversalDescriptor?_eq_universalDescriptor? target view

/-- Pointwise (application) form of `evaluator_eq_universalDescriptor`, derived from that function
equality by congruence.  This is the rewrite form used where a proof must replace a single
evaluator call rather than a whole function. -/
theorem evaluator_eq_universalDescriptor_apply (input : Input) (fuel : Nat)
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target) :
    evaluator input fuel target view =
      input.certified.universalDescriptor? target view :=
  congrFun (congrFun (evaluator_eq_universalDescriptor input fuel) target) view

/-- Exact public-API connection: the localized universal evaluator is definitionally the runtime
adapter `LocalizedExtendedShortCircuit.universalFuelEvaluator`, hence the same production
descriptor call at the same policy fuel. -/
theorem evaluator_eq_universalFuelEvaluator (input : Input) (fuel : Nat) :
    evaluator input fuel =
      TetraStereo.OneCenter.LocalizedExtendedShortCircuit.universalFuelEvaluator
        input fuel := rfl

/-- Exact operational outcome of the policy evaluator.  This is an executable equality, not an
independent chemical relation. -/
def OperationalOutcome (input : Input) (fuel : Nat)
    (state : input.certified.LocalizedAuxiliaryState fuel)
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  evaluator input fuel target (input.certified.localizedDependencyView state target) = outcome

/-- Adapter to the existing ranked equation/certificate infrastructure.  Its derivation relation
is operational; the independent positive meaning is exported separately. -/
def runtimeSemantics (input : Input) (fuel : Nat) :
    input.certified.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation := OperationalOutcome input fuel
  executableRule := evaluator input fuel
  derivation_executable_iff := by
    intros
    rfl

/-! ## Generated reference nodes and facts -/

def runtimeSystem (input : Input) :=
  input.certified.localizedCertificateSystem (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

def dependencies (input : Input) :=
  input.certified.localizedCertificateDependencies (carrierFuel input)

/-- The single ranked certificate production over the occurrence carrier with the policy
executable rule. -/
def referenceNodes (input : Input) : Nodes input :=
  input.certified.localizedCertificateNodes (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

/-- The generated facts are the target/outcome projection of `referenceNodes`.  This definition
is used in statements; the runnable fallback maps the node list directly (see
`referenceEvaluation`). -/
def referenceFacts (input : Input) : Facts input :=
  input.certified.localizedCertificateFacts (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

/-- State of the generated reference iteration. -/
def referenceState (input : Input) : input.certified.LocalizedAuxiliaryState (carrierFuel input) :=
  lookup (referenceFacts input)

/-- The generated facts are definitionally the projection of the generated nodes. -/
theorem referenceFacts_eq_nodes_map (input : Input) :
    referenceFacts input =
      (referenceNodes input).map fun node => (node.target, node.outcome) := rfl

/-- The generated production is accepted by the existing checker. -/
theorem reference_check (input : Input) :
    check (runtimeSystem input) (dependencies input) (referenceNodes input) =
      some (referenceFacts input) :=
  input.certified.localizedCertificate_check (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

/-- Every carrier occurrence is a target of the generated facts, through the complete ranked
certificate order. -/
theorem reference_targets (input : Input) :
    (referenceFacts input).map Prod.fst =
      input.certified.localizedCertificateOrder (carrierFuel input) :=
  input.certified.localizedCertificateFacts_targets (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

/-! ## Unique operational reference state -/

/-- The generated state is a CIP model of the policy occurrence system. -/
theorem reference_model (input : Input) :
    (runtimeSystem input).CIPModel (referenceState input) :=
  input.certified.localizedCertificateFacts_cipModel (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

/-- The generated state is the existing bounded occurrence iteration at the policy evaluator. -/
theorem reference_eq_boundedIteration (input : Input) :
    referenceState input = input.certified.evaluateLocalizedOccurrences (carrierFuel input)
      (evaluator input (carrierFuel input)) := by
  have model := reference_model input
  unfold runtimeSystem localizedCertificateSystem at model
  rw [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old] at model
  exact (input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
    (runtimeSemantics input (carrierFuel input)) model).symm

/-- **Universal iteration preservation.**  The generated reference state is exactly the existing
bounded occurrence iteration run with the unconditional universal descriptor evaluator.  This
follows from `reference_eq_boundedIteration` and the evaluator function equality
`evaluator_eq_universalDescriptor`.  It is an explicit preservation statement about the
universal state only; it does not assert equality with, or transport labels from, the legacy
production `LocalizedExtendedShortCircuit.referenceState`. -/
theorem referenceState_eq_universalIteration (input : Input) :
    referenceState input =
      input.certified.evaluateLocalizedOccurrences (carrierFuel input)
        (fun target view => input.certified.universalDescriptor? target view) := by
  rw [reference_eq_boundedIteration input,
    evaluator_eq_universalDescriptor input (carrierFuel input)]

/-- Every local operational equation holds at the generated state. -/
theorem reference_equation (input : Input) (target : Occurrence input) :
    evaluator input (carrierFuel input) target
      (input.certified.localizedDependencyView (referenceState input) target) =
        referenceState input target :=
  reference_model input target

/-- **Uniqueness.**  Any operational model of the policy occurrence system is the generated
reference state.  This is the existing fixed-point uniqueness theorem at the policy rule. -/
theorem reference_state_unique (input : Input)
    {state : input.certified.LocalizedAuxiliaryState (carrierFuel input)}
    (model : (runtimeSystem input).CIPModel state) :
    state = referenceState input := by
  have iterate := reference_eq_boundedIteration input
  have modelOld : (input.certified.localizedAuxiliaryOccurrenceSystem
      (runtimeSemantics input (carrierFuel input))).CIPModel state := by
    unfold runtimeSystem localizedCertificateSystem at model
    rwa [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old] at model
  have stateEq : input.certified.evaluateLocalizedOccurrences (carrierFuel input)
      (evaluator input (carrierFuel input)) = state :=
    input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
      (runtimeSemantics input (carrierFuel input)) modelOld
  rw [iterate, stateEq]

/-! ## Independent positive descriptor meaning at the computed Rule-3 budget

The universal descriptor is the parameterized descriptor pipeline evaluated at the Rule-3 budget
returned by its own preparation.  `LocalizedUniversalDescriptorEvaluation` already proves the
positive soundness theorem `universalDescriptor?_sound`: a successful universal outcome has the
independent `DeclarativeLocalizedOccurrenceUniversalDescriptor` meaning at the computed bound for
the executable four-ligand base.  We lift that theorem to the generated reference state through
the evaluator equality.  The conclusion keeps the original computed budget; it is neither
replaced by nor weakened to the policy fuel.  No completeness direction is proved or assumed.
-/

/-- Positive reference outcomes carry independent universal descriptor evidence at the computed
Rule-3 budget, relative to the generated reference state. -/
theorem reference_positive_sound (input : Input) (target : Occurrence input)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : referenceState input target = some descriptor) :
    ∃ (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
        (evaluationBudget : Nat),
      input.certified.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        evaluationBudget =
          (prepareUniversalRule3EvaluationOutcome input.certified base.cursors target
            (input.certified.localizedDependencyView (referenceState input) target)).1 ∧
          input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
            (input.certified.localizedDependencyView (referenceState input) target)
            evaluationBudget descriptor := by
  have equation := reference_equation input target
  rw [evaluator_eq_universalDescriptor_apply input (carrierFuel input) target
    (input.certified.localizedDependencyView (referenceState input) target)] at equation
  have universalSome : input.certified.universalDescriptor? target
      (input.certified.localizedDependencyView (referenceState input) target) =
        some descriptor := by
    rw [equation]
    exact computed
  obtain ⟨base, baseComputed, meaning⟩ :=
    input.certified.universalDescriptor?_sound target _ descriptor universalSome
  exact ⟨base, _, baseComputed, rfl, meaning⟩

/-! ## Checked candidate replay and the single-production fallback -/

/-- Every occurrence of the materialized carrier is a fact target. -/
def covered (input : Input) (facts : Facts input) : Bool :=
  (input.certified.localizedOccurrenceCarrier (carrierFuel input)).all fun occurrence =>
    decide (occurrence ∈ facts.map Prod.fst)

/-- Replay caller-supplied candidate nodes against the policy system.  Acceptance requires the
existing checker success, target duplicate-freeness and full carrier coverage. -/
def checkProposals? (input : Input) (nodes : Nodes input) : Option (Facts input) := do
  let facts ← check (runtimeSystem input) (dependencies input) nodes
  if (facts.map Prod.fst).Nodup ∧ covered input facts = true then some facts else none

theorem checkProposals?_exact (input : Input) (nodes : Nodes input) (facts : Facts input) :
    checkProposals? input nodes = some facts ↔
      check (runtimeSystem input) (dependencies input) nodes = some facts ∧
        (facts.map Prod.fst).Nodup ∧ covered input facts = true := by
  unfold checkProposals?
  cases hc : check (runtimeSystem input) (dependencies input) nodes with
  | none => simp
  | some values =>
      change (if (values.map Prod.fst).Nodup ∧ covered input values = true
        then some values else none) = some facts ↔
          some values = some facts ∧ (facts.map Prod.fst).Nodup ∧ covered input facts = true
      by_cases valid : (values.map Prod.fst).Nodup ∧ covered input values = true
      · simp only [if_pos valid, Option.some.injEq]
        constructor
        · intro eq; subst values; exact ⟨rfl, valid⟩
        · rintro ⟨eq, _⟩; exact eq
      · simp only [if_neg valid, reduceCtorEq, false_iff, Option.some.injEq]
        rintro ⟨eq, nodup, coverage⟩
        subst values
        exact valid ⟨nodup, coverage⟩

/-- The generated production passes the checked replay path. -/
theorem reference_accepted (input : Input) :
    checkProposals? input (referenceNodes input) = some (referenceFacts input) := by
  apply (checkProposals?_exact input _ _).mpr
  refine ⟨reference_check input, ?_, ?_⟩
  · rw [reference_targets]
    exact input.certified.localizedCertificateOrder_nodup (carrierFuel input)
  · unfold covered
    rw [List.all_eq_true]
    intro occurrence _
    apply decide_eq_true
    rw [reference_targets]
    exact input.certified.localizedCertificateOrder_complete (carrierFuel input) occurrence

/-- Every carrier occurrence is covered by the generated facts. -/
theorem reference_covered (input : Input) : covered input (referenceFacts input) = true := by
  unfold covered
  rw [List.all_eq_true]
  intro occurrence _
  apply decide_eq_true
  rw [reference_targets]
  exact input.certified.localizedCertificateOrder_complete (carrierFuel input) occurrence

/-- An accepted candidate computes a CIP model of the policy system. -/
theorem checked_model (input : Input) (nodes : Nodes input) (facts : Facts input)
    (accepted : checkProposals? input nodes = some facts) :
    (runtimeSystem input).CIPModel (lookup facts) := by
  obtain ⟨accepted, nodup, complete⟩ := (checkProposals?_exact input nodes facts).mp accepted
  apply Certificate.DependencyCheckedModel.checked_lookup_cipModel _ _ nodes facts
    accepted nodup
  · intro occurrence
    have found := (List.all_eq_true.mp complete) occurrence
      (input.certified.localizedOccurrenceCarrier_complete (carrierFuel input) occurrence)
    exact of_decide_eq_true found
  · exact input.certified.localizedCertificateSystem_evaluatorLocal (carrierFuel input)
      (runtimeSemantics input (carrierFuel input))
  · exact input.certified.localizedCertificateSystem_derivationStepCorrespondence (carrierFuel input)
      (runtimeSemantics input (carrierFuel input))

/-- An accepted candidate computes exactly the unique generated reference state. -/
theorem checked_eq_reference (input : Input) (nodes : Nodes input) (facts : Facts input)
    (accepted : checkProposals? input nodes = some facts) :
    lookup facts = referenceState input := by
  have model := checked_model input nodes facts accepted
  unfold runtimeSystem localizedCertificateSystem at model
  rw [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old] at model
  rw [reference_eq_boundedIteration]
  exact (input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
    (runtimeSemantics input (carrierFuel input)) model).symm

/-- A checked result contains replayable certificate data together with its kernel-checked
acceptance invariant. -/
structure Evaluation (input : Input) where
  nodes : Nodes input
  facts : Facts input
  accepted : checkProposals? input nodes = some facts

/-- The generated fallback evaluation.  The node list is bound once; the facts are the
target/outcome projection of that same list, so no second production is performed. -/
def referenceEvaluation (input : Input) : Evaluation input :=
  let nodes := referenceNodes input
  { nodes
    facts := nodes.map fun node => (node.target, node.outcome)
    accepted := by
      dsimp only [nodes]
      exact reference_accepted input }

/-- The runnable fallback exposes exactly one production: its node field is that production and
its fact field is the projection of the same list. -/
theorem referenceEvaluation_production (input : Input) :
    (referenceEvaluation input).nodes = referenceNodes input ∧
      (referenceEvaluation input).facts =
        (referenceNodes input).map fun node => (node.target, node.outcome) :=
  ⟨rfl, rfl⟩

/-- The fallback facts are precisely the single node list's projection; no independent fact
computation takes place. -/
theorem referenceEvaluation_facts_eq_nodes_map (input : Input) :
    (referenceEvaluation input).facts =
      (referenceEvaluation input).nodes.map fun node => (node.target, node.outcome) :=
  rfl

theorem referenceEvaluation_facts (input : Input) :
    (referenceEvaluation input).facts = referenceFacts input := rfl

/-- The canonical report projection, with the same body as the production pipeline. -/
def report (input : Input) (facts : Facts input) : Report :=
  input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, lookup facts
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))

/-- The report projection is exactly the existing pipeline report. -/
theorem report_eq_pipeline (input : Input) (facts : Facts input) :
    report input facts = LocalizedExtendedShortCircuit.report input facts := rfl

/-- Reference evaluation with the policy executable rule. -/
def referenceReport (input : Input) : Report :=
  report input (referenceFacts input)

/-! ## Runnable checked fast path with generated fallback -/

/-- Replay the candidate; on rejection produce the single generated fallback. -/
def evaluate (input : Input) (nodes : Nodes input) : Evaluation input :=
  match accepted : checkProposals? input nodes with
  | some facts => ⟨nodes, facts, accepted⟩
  | none => referenceEvaluation input

/-- Every evaluation result, accepted or generated, computes the same unique reference state. -/
theorem evaluation_eq_reference (input : Input) (result : Evaluation input) :
    lookup result.facts = referenceState input :=
  checked_eq_reference input result.nodes result.facts result.accepted

/-- Both branches of `evaluate` produce the same unique operational state. -/
theorem evaluate_state (input : Input) (nodes : Nodes input) :
    lookup (evaluate input nodes).facts = referenceState input :=
  evaluation_eq_reference input (evaluate input nodes)

theorem evaluate_facts_accepted (input : Input) (nodes : Nodes input) (facts : Facts input)
    (accepted : checkProposals? input nodes = some facts) :
    (evaluate input nodes).facts = facts := by
  unfold evaluate
  split
  · rename_i values checked
    have valuesEq : values = facts := Option.some.inj (checked.symm.trans accepted)
    subst valuesEq
    rfl
  · rename_i checked
    rw [checked] at accepted
    simp at accepted

theorem evaluate_nodes_accepted (input : Input) (nodes : Nodes input) (facts : Facts input)
    (accepted : checkProposals? input nodes = some facts) :
    (evaluate input nodes).nodes = nodes := by
  unfold evaluate
  split
  · rename_i values checked
    have valuesEq : values = facts := Option.some.inj (checked.symm.trans accepted)
    subst valuesEq
    rfl
  · rename_i checked
    rw [checked] at accepted
    simp at accepted

/-- A rejected or incomplete candidate falls back to the single generated production. -/
theorem evaluate_rejected (input : Input) (nodes : Nodes input)
    (rejected : checkProposals? input nodes = none) :
    evaluate input nodes = referenceEvaluation input := by
  unfold evaluate
  split
  · rename_i values checked
    rw [checked] at rejected
    simp at rejected
  · rename_i checked
    rfl

theorem evaluate_rejected_facts (input : Input) (nodes : Nodes input)
    (rejected : checkProposals? input nodes = none) :
    (evaluate input nodes).facts = referenceFacts input := by
  rw [evaluate_rejected input nodes rejected]
  exact referenceEvaluation_facts input

/-- A positive outcome of any evaluation result has independent universal descriptor evidence at
the computed Rule-3 budget, relative to that result's own state.  The original computed-budget
conclusion is retained; the policy fuel does not replace it. -/
theorem evaluation_positive_sound (input : Input) (result : Evaluation input)
    (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel)
    (computed : lookup result.facts target = some descriptor) :
    ∃ (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
        (evaluationBudget : Nat),
      input.certified.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        evaluationBudget =
          (prepareUniversalRule3EvaluationOutcome input.certified base.cursors target
            (input.certified.localizedDependencyView (lookup result.facts) target)).1 ∧
          input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
            (input.certified.localizedDependencyView (lookup result.facts) target)
            evaluationBudget descriptor := by
  have equation : evaluator input (carrierFuel input) target
      (input.certified.localizedDependencyView (lookup result.facts) target) =
        lookup result.facts target :=
    checked_model input result.nodes result.facts result.accepted target
  rw [evaluator_eq_universalDescriptor_apply input (carrierFuel input) target
    (input.certified.localizedDependencyView (lookup result.facts) target)] at equation
  have universalSome : input.certified.universalDescriptor? target
      (input.certified.localizedDependencyView (lookup result.facts) target) =
        some descriptor := by
    rw [equation]
    exact computed
  obtain ⟨base, baseComputed, meaning⟩ :=
    input.certified.universalDescriptor?_sound target _ descriptor universalSome
  exact ⟨base, _, baseComputed, rfl, meaning⟩

/-! ## Executable analysis -/

/-- Candidate proposals come from a caller-supplied function; the default is empty, which takes
the generated fallback unless the carrier is empty. -/
abbrev Proposer := (input : Input) → Nodes input

def emptyProposer : Proposer := fun _ => []

/-- Executable analysis: replay the candidate and report the resulting state. -/
def analyze (input : Input) (propose : Proposer := emptyProposer) : Report :=
  report input (evaluate input (propose input)).facts

/-- Every evaluation state is the reference state, so the executable report is exactly the
reference report. -/
theorem analyze_eq_reference (input : Input) (propose : Proposer) :
    analyze input propose = referenceReport input := by
  unfold analyze referenceReport report
  rw [evaluate_state input (propose input)]
  rfl

/-- Positive outcomes of the executable analysis carry independent universal descriptor
evidence at the computed Rule-3 budget. -/
theorem analyze_positive_sound (input : Input) (propose : Proposer)
    (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel)
    (computed : lookup (evaluate input (propose input)).facts target = some descriptor) :
    ∃ (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
        (evaluationBudget : Nat),
      input.certified.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        evaluationBudget =
          (prepareUniversalRule3EvaluationOutcome input.certified base.cursors target
            (input.certified.localizedDependencyView
              (lookup (evaluate input (propose input)).facts) target)).1 ∧
          input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
            (input.certified.localizedDependencyView
              (lookup (evaluate input (propose input)).facts) target)
            evaluationBudget descriptor :=
  evaluation_positive_sound input (evaluate input (propose input)) target descriptor computed

/-! ## Source admission wrapper -/

def evaluateSource? (source : AuthoritativeChemicalInput)
    (propose : Proposer := emptyProposer) :
    Option ((input : Input) × Evaluation input) := do
  let input ← admitSource? source
  pure ⟨input, evaluate input (propose input)⟩

def analyzeSource? (source : AuthoritativeChemicalInput)
    (propose : Proposer := emptyProposer) : Option Report :=
  (evaluateSource? source propose).map fun result => report result.1 result.2.facts

/-- No admission, no evaluation. -/
theorem evaluateSource?_none_iff (source : AuthoritativeChemicalInput) (propose : Proposer) :
    evaluateSource? source propose = none ↔ admitSource? source = none := by
  unfold evaluateSource?
  cases admitted : admitSource? source with
  | none => simp
  | some input => simp

end TetraStereo.OneCenter.LocalizedUniversalReference

assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluator_eq_descriptorAt_policy
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluator_eq_universalDescriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluator_eq_universalDescriptor_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluator_eq_universalFuelEvaluator
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_eq_universalIteration
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.reference_check
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluate_state
