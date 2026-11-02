import TetraStereo.OneCenter.LocalizedNoDoubleReferencePipeline
import TetraStereo.OneCenter.LocalizedDependencyCertificate
import TetraStereo.Certificate.DependencyCheckedModel

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedNoDoubleReference

open TetraStereo.Certificate.Dependency
open TetraStereo.OneCenter.DeclarativeCIP
open CertifiedLocalizedCIPInput





































/-! ## The runtime system and dependency list -/

/-- The runtime occurrence system of the admitted input: the plain occurrence system at the direct
executable final-center root, with the repository's descriptor-bearing rule semantics. -/
def runtimeSystem (input : Input) :
    OccurrenceSystem input.certified.TetrahedralCenter
      (input.certified.LocalizedCIPOccurrence (carrierFuel input)) LocalizedAuxiliaryLabel :=
  input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot
    (runtimeSemantics input (carrierFuel input))

/-- The runtime strict-dependency enumeration: exactly the strict root-relative depth dependencies
of a target inside the executable carrier. -/
def runtimeDependencies (input : Input) :
    input.certified.LocalizedCIPOccurrence (carrierFuel input) →
      List (input.certified.LocalizedCIPOccurrence (carrierFuel input)) :=
  input.certified.localizedDependencyList (carrierFuel input)

/-! ## Complete coverage, decision procedure, and the checked wrapper -/

/-- Completeness of a proposed fact list: every carrier occurrence is recorded. -/
def CarrierCovered (input : Input)
    (facts : List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) : Prop :=
  ∀ occurrence ∈ input.certified.localizedOccurrenceCarrier (carrierFuel input),
    occurrence ∈ facts.map Prod.fst

/-- Executable coverage test.  It is phrased as a Boolean fold over the carrier so that the
otherwise undecidable whole-type quantifier is replaced by a decision over the explicit finite
enumeration; `carrierCoveredBool_eq_true_iff` records that this loses nothing. -/
def carrierCoveredBool (input : Input)
    (facts : List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) : Bool :=
  (input.certified.localizedOccurrenceCarrier (carrierFuel input)).all fun occurrence =>
    decide (occurrence ∈ facts.map Prod.fst)

theorem carrierCoveredBool_eq_true_iff (input : Input)
    (facts : List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) :
    carrierCoveredBool input facts = true ↔ CarrierCovered input facts := by
  unfold carrierCoveredBool CarrierCovered
  rw [List.all_eq_true]
  constructor
  · intro hall occurrence present
    exact of_decide_eq_true (hall occurrence present)
  · intro covered occurrence present
    exact decide_eq_true (covered occurrence present)

/-- Replay a proposed certificate and, if it is accepted with duplicate-free complete coverage,
return its facts; otherwise nothing.  This is the checked *decision* only; the fallback lives in
`evaluateCheckedOrReference`. -/
def checkProposals? (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) :
    Option (List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) :=
  Option.bind (check (runtimeSystem input) (runtimeDependencies input) nodes)
    (fun facts =>
      if (facts.map Prod.fst).Nodup ∧ carrierCoveredBool input facts = true then
        some facts
      else
        none)




def evaluateCheckedOrReference (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) :
    List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel) :=
  match checkProposals? input nodes with
  | some facts => facts
  | none => evaluatedFacts input

/-! ## Acceptance, decomposed -/

private theorem option_bind_some_iff {α β : Type*} (option : Option α) (next : α → Option β)
    (result : β) :
    option.bind next = some result ↔ ∃ value, option = some value ∧ next value = some result := by
  cases option with
  | none => simp
  | some value =>
      constructor
      · intro bound
        exact ⟨value, rfl, bound⟩
      · rintro ⟨candidate, equal, bound⟩
        injection equal with equal
        subst equal
        exact bound

/-- Exact characterization of acceptance: the checker succeeds, the recorded occurrences are
duplicate free, and the carrier is completely covered. -/
theorem checkProposals?_eq_some_iff (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (facts : List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) :
    checkProposals? input nodes = some facts ↔
      check (runtimeSystem input) (runtimeDependencies input) nodes = some facts ∧
        (facts.map Prod.fst).Nodup ∧ CarrierCovered input facts := by
  constructor
  · intro checked
    have decomposed := checked
    unfold checkProposals? at decomposed
    rw [option_bind_some_iff] at decomposed
    obtain ⟨result, checkerAccepted, guardHolds⟩ := decomposed
    by_cases accepted : (result.map Prod.fst).Nodup ∧ carrierCoveredBool input result = true
    · rw [if_pos accepted] at guardHolds
      have equal : result = facts := Option.some.inj guardHolds
      subst result
      exact ⟨checkerAccepted, accepted.1, (carrierCoveredBool_eq_true_iff input facts).mp accepted.2⟩
    · rw [if_neg accepted] at guardHolds
      exact absurd guardHolds (by simp)
  · rintro ⟨checkerAccepted, nodup, covered⟩
    unfold checkProposals?
    rw [checkerAccepted, Option.bind_some]
    rw [if_pos ⟨nodup, (carrierCoveredBool_eq_true_iff input facts).mpr covered⟩]

/-! ## The checked lookup is a runtime model -/


theorem checkProposals?_accepted (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (facts : List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (checked : checkProposals? input nodes = some facts) :
    check (runtimeSystem input) (runtimeDependencies input) nodes = some facts ∧
      (facts.map Prod.fst).Nodup ∧ CarrierCovered input facts :=
  (checkProposals?_eq_some_iff input nodes facts).mp checked

/-- The dependency relation generated by the runtime dependency lists is exactly strict
root-relative depth. -/
theorem relation_runtimeDependencies (input : Input) :
    relation (runtimeDependencies input) =
      (@input.certified.LocalizedDepthDependency (carrierFuel input)) := by
  funext inner target
  exact propext
    (input.certified.mem_localizedDependencyList_iff (carrierFuel input) target inner)

/-- The runtime evaluator is local for the runtime dependency relation. -/
theorem runtimeSystem_evaluatorLocal (input : Input) :
    (runtimeSystem input).EvaluatorLocalFor (relation (runtimeDependencies input)) := by
  unfold runtimeSystem
  rw [relation_runtimeDependencies input,
    input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old
      (runtimeSemantics input (carrierFuel input))]
  exact input.certified.localizedAuxiliaryEvaluatorLocal
    (runtimeSemantics input (carrierFuel input))

/-- The runtime system carries the independent derivation/executable correspondence. -/
theorem runtimeSystem_derivationStepCorrespondence (input : Input) :
    (runtimeSystem input).DerivationStepCorrespondence := by
  unfold runtimeSystem
  exact input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_derivationStepCorrespondence
    (runtimeSemantics input (carrierFuel input))

/-- The runtime dependency relation is well founded (strict depth grading). -/
theorem runtimeDependencies_wellFounded (input : Input) :
    WellFounded (relation (runtimeDependencies input)) := by
  rw [relation_runtimeDependencies input]
  exact input.certified.localizedDepthDependency_wellFounded (carrierFuel input)






theorem checkProposals?_lookup_cipModel (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (facts : List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (checked : checkProposals? input nodes = some facts) :
    (runtimeSystem input).CIPModel (Certificate.Dependency.lookup facts) := by
  obtain ⟨accepted, nodup, covered⟩ := checkProposals?_accepted input nodes facts checked
  refine TetraStereo.Certificate.DependencyCheckedModel.checked_lookup_cipModel
    (runtimeSystem input) (runtimeDependencies input) nodes facts accepted nodup ?_
    (runtimeSystem_evaluatorLocal input) (runtimeSystem_derivationStepCorrespondence input)
  intro occurrence
  exact covered occurrence
    (input.certified.localizedOccurrenceCarrier_complete (carrierFuel input) occurrence)

/-! ## The checked lookup equals the reference state -/

/-- **Model uniqueness across the checked and reference branches.**  Both the checked lookup and
`evaluatedState input` are complete models of the same runtime system, whose dependency relation is
well founded and for which the evaluator is local; hence they are equal.  The reference state is a
model by `cipModel_evaluatedState`, transported across the proved equality of the executable-root
system with the fixed-point interface's system. -/
theorem lookup_eq_evaluatedState_of_checkProposals? (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (facts : List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (checked : checkProposals? input nodes = some facts) :
    Certificate.Dependency.lookup facts = evaluatedState input := by
  have checkedModel := checkProposals?_lookup_cipModel input nodes facts checked
  have referenceModel : (runtimeSystem input).CIPModel (evaluatedState input) := by
    unfold runtimeSystem
    rw [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old
      (runtimeSemantics input (carrierFuel input))]
    exact cipModel_evaluatedState input
  exact (runtimeSystem input).cipModel_unique_of_wellFounded
    (runtimeSystem_derivationStepCorrespondence input)
    (relation (runtimeDependencies input)) (runtimeDependencies_wellFounded input)
    (runtimeSystem_evaluatorLocal input)
    (Certificate.Dependency.lookup facts) (evaluatedState input) checkedModel referenceModel

/-- **Exactness of the compiled checked-or-reference wrapper.**  On the accepted branch the returned
facts replay to the reference state, and on the fallback branch the returned facts are the reference
tabulation itself; both branches therefore look up to `evaluatedState input`.  The checked path
never changes the evaluated state. -/
theorem lookup_evaluateCheckedOrReference_eq_evaluatedState (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) :
    Certificate.Dependency.lookup (evaluateCheckedOrReference input nodes) =
      evaluatedState input := by
  unfold evaluateCheckedOrReference
  cases checked : checkProposals? input nodes with
  | none => rfl
  | some facts => exact lookup_eq_evaluatedState_of_checkProposals? input nodes facts checked

/-- Pointwise form at an arbitrary occurrence. -/
theorem lookup_evaluateCheckedOrReference_apply (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input)) :
    Certificate.Dependency.lookup (evaluateCheckedOrReference input nodes) target =
      evaluatedState input target :=
  congrFun (lookup_evaluateCheckedOrReference_eq_evaluatedState input nodes) target

/-- The fallback branch is the reference tabulation itself, definitionally. -/
theorem evaluateCheckedOrReference_of_rejected (input : Input)
    (nodes : List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel))
    (rejected : checkProposals? input nodes = none) :
    evaluateCheckedOrReference input nodes = evaluatedFacts input := by
  unfold evaluateCheckedOrReference
  rw [rejected]










def localizedCheckedNodes (input : Input) :=
  input.certified.localizedCertificateNodes (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))


def localizedCheckedFacts (input : Input) :=
  input.certified.localizedCertificateFacts (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))




theorem checkProposals?_localizedCheckedNodes (input : Input) :
    checkProposals? input (localizedCheckedNodes input) = some (localizedCheckedFacts input) := by
  rw [localizedCheckedNodes, localizedCheckedFacts, checkProposals?_eq_some_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact input.certified.localizedCertificate_check (carrierFuel input)
      (runtimeSemantics input (carrierFuel input))
  · rw [input.certified.localizedCertificateFacts_targets (carrierFuel input)
        (runtimeSemantics input (carrierFuel input))]
    exact input.certified.localizedCertificateOrder_nodup (carrierFuel input)
  · intro occurrence _
    rw [input.certified.localizedCertificateFacts_targets (carrierFuel input)
        (runtimeSemantics input (carrierFuel input))]
    exact input.certified.localizedCertificateOrder_complete (carrierFuel input) occurrence


theorem evaluateCheckedOrReference_localizedCheckedNodes (input : Input) :
    evaluateCheckedOrReference input (localizedCheckedNodes input) = localizedCheckedFacts input := by
  unfold evaluateCheckedOrReference
  rw [checkProposals?_localizedCheckedNodes]

/-- **The ranked fast path is exact.**  The generated ranked certificate looks up to exactly the
reference occurrence state, so building and replaying a certificate never changes the evaluated
state. -/
theorem lookup_localizedCheckedFacts_eq_evaluatedState (input : Input) :
    Certificate.Dependency.lookup (localizedCheckedFacts input) = evaluatedState input := by
  rw [localizedCheckedFacts]
  exact lookup_eq_evaluatedState_of_checkProposals? input (localizedCheckedNodes input)
    (input.certified.localizedCertificateFacts (carrierFuel input)
      (runtimeSemantics input (carrierFuel input)))
    (checkProposals?_localizedCheckedNodes input)

end TetraStereo.OneCenter.LocalizedNoDoubleReference
