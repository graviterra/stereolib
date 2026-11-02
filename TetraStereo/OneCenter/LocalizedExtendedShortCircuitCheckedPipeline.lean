import TetraStereo.OneCenter.LocalizedExtendedShortCircuitPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedExtendedShortCircuit
open CertifiedLocalizedCIPInput Certificate.Dependency

def covered (input : Input) (facts : Facts input) : Bool :=
  (input.certified.localizedOccurrenceCarrier (carrierFuel input)).all fun occurrence =>
    decide (occurrence ∈ facts.map Prod.fst)

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

theorem checked_eq_reference (input : Input) (nodes : Nodes input) (facts : Facts input)
    (accepted : checkProposals? input nodes = some facts) :
    lookup facts = referenceState input := by
  have model := checked_model input nodes facts accepted
  unfold runtimeSystem localizedCertificateSystem at model
  rw [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old] at model
  rw [reference_eq_boundedIteration]
  exact (input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
    (runtimeSemantics input (carrierFuel input)) model).symm

/-- The returned result contains replayable certificate data, along with its kernel-checked
acceptance invariant. The caller supplies only ordinary molecular and configuration data. -/
structure Evaluation (input : Input) where
  nodes : Nodes input
  facts : Facts input
  accepted : checkProposals? input nodes = some facts

def referenceEvaluation (input : Input) : Evaluation input :=
  let nodes := referenceNodes input
  { nodes
    facts := nodes.map (fun (node : Node (Occurrence input) LocalizedAuxiliaryLabel) =>
      (node.target, node.outcome))
    accepted := reference_accepted input }

/-- Rejected proposals run the ranked reference fallback lazily. -/
def evaluate (input : Input) (nodes : Nodes input) : Evaluation input :=
  match accepted : checkProposals? input nodes with
  | some facts => ⟨nodes, facts, accepted⟩
  | none => referenceEvaluation input

theorem evaluation_eq_reference (input : Input) (result : Evaluation input) :
    lookup result.facts = referenceState input :=
  checked_eq_reference input result.nodes result.facts result.accepted

theorem evaluation_report_eq_reference (input : Input) (result : Evaluation input) :
    report input result.facts = analyze input := by
  unfold report analyze
  rw [evaluation_eq_reference input result]
  rfl

/-- Every positive checked result has independent rule evidence relative to its returned state.
This statement does not interpret operational refusal as independent chemical nonexistence. -/
theorem evaluation_positive_sound (input : Input) (result : Evaluation input)
    (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel)
    (computed : lookup result.facts target = some descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
      target (input.certified.localizedDependencyView (lookup result.facts) target) descriptor := by
  have equation : evaluator input (carrierFuel input) target
      (input.certified.localizedDependencyView (lookup result.facts) target) =
        lookup result.facts target :=
    checked_model input result.nodes result.facts result.accepted target
  exact input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_sound
    target _ descriptor (equation.trans computed)

abbrev Proposer := (input : Input) → Nodes input

/-- The default offers no speculative nodes. Incomplete empty proposals take the existing lazy
reference fallback; a complete empty carrier is accepted directly by the same checker. -/
def emptyProposer : Proposer := fun _ => []

def evaluateSource? (source : AuthoritativeChemicalInput)
    (propose : Proposer := emptyProposer) : Option ((input : Input) × Evaluation input) := do
  let input ← admitSource? source
  pure ⟨input, evaluate input (propose input)⟩

def analyzeSource? (source : AuthoritativeChemicalInput)
    (propose : Proposer := emptyProposer) : Option Report :=
  (evaluateSource? source propose).map fun result => report result.1 result.2.facts

theorem analyzeSource?_eq_reference (source : AuthoritativeChemicalInput) (propose : Proposer) :
    analyzeSource? source propose = (admitSource? source).map analyze := by
  unfold analyzeSource? evaluateSource?
  cases admitted : admitSource? source with
  | none => rfl
  | some input => simp only [Option.map_some,
      evaluation_report_eq_reference]; rfl

def evaluateSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) (propose : Proposer := emptyProposer) :
    Except ParserError (Option ((input : Input) × Evaluation input)) :=
  (admitSmilesSpatial? text spatial cycles).map fun admitted =>
    admitted.map fun input => ⟨input, evaluate input (propose input)⟩

end TetraStereo.OneCenter.LocalizedExtendedShortCircuit
