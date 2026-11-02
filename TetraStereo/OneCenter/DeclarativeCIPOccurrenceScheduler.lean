import TetraStereo.OneCenter.DeclarativeCIPGlobalFixedPoint

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP
namespace OccurrenceScheduler

universe u v w

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

/-!
# A causal dependency-ready scheduler for occurrence equations

Scheduler facts contain finite evaluation proof trees.  A certificate node records outcomes for
the target's strict dependencies, certificates for those outcomes, and a direct equation showing
that the target outcome is one executable evaluation over precisely that dependency environment.
The certificate type does not mention the already-solved well-founded state.

One scheduler round retains established facts and simultaneously adds exactly the certificate
nodes whose immediate child certificates are present.  Thus leaves enter first.  A separate
well-founded argument constructs one canonical proof tree per occurrence and proves, rather than
assumes, that every certificate outcome equals the well-founded executable solution.
-/

/-- A causal proof tree for one executable occurrence outcome. -/
inductive EvaluationCertificate
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) :
    Occurrence → Option Label → Type (max v w) where
  | node (target : Occurrence)
      (dependencyOutcomes : ∀ inner, dependency inner target → Option Label)
      (dependencyCertificates : ∀ inner h,
        EvaluationCertificate system dependency inner (dependencyOutcomes inner h))
      {outcome : Option Label}
      (evaluation_eq : outcome =
        system.executableStep
          (system.dependencyEnvironment dependency target dependencyOutcomes) target) :
      EvaluationCertificate system dependency target outcome

/-- A scheduler fact packages a target, an outcome, and a causal certificate for that outcome. -/
abbrev CertifiedFact
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) :=
  Σ target, Σ outcome, EvaluationCertificate system dependency target outcome

/-- The immediate child facts required by a certificate node. -/
def DependenciesPresent
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) :
    ∀ {target outcome}, EvaluationCertificate system dependency target outcome →
      Set (CertifiedFact system dependency) → Prop
  | _, _, .node target dependencyOutcomes dependencyCertificates _, facts =>
      ∀ inner h,
        (⟨inner, dependencyOutcomes inner h, dependencyCertificates inner h⟩ :
          CertifiedFact system dependency) ∈ facts

/-- The simultaneous batch consists of exactly the causally ready certificate nodes. -/
def readyBatch
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (facts : Set (CertifiedFact system dependency)) :
    Set (CertifiedFact system dependency) :=
  { fact | DependenciesPresent system dependency fact.2.2 facts }

/-- One worklist round retains all established facts and adds the complete ready batch. -/
def stepSet
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (facts : Set (CertifiedFact system dependency)) :
    Set (CertifiedFact system dependency) :=
  facts ∪ readyBatch system dependency facts

/-- The causal worklist is a monotone, inflationary descriptor closure operator. -/
def operator
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) :
    DescriptorClosureOperator (CertifiedFact system dependency) where
  step :=
    { toFun := stepSet system dependency
      monotone' := by
        intro left right included fact member
        rcases member with old | ready
        · exact Or.inl (included old)
        · exact Or.inr (by
            cases fact with
            | mk target rest =>
                cases rest with
                | mk outcome certificate =>
                    cases certificate with
                    | node target dependencyOutcomes dependencyCertificates evaluation_eq =>
                        intro inner h
                        exact included (ready inner h)) }
  inflationary := by
    intro facts fact member
    exact Or.inl member

/-- The step is exactly an old-fact union with one simultaneous ready batch. -/
theorem operator_step_eq
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (facts : Set (CertifiedFact system dependency)) :
    (operator system dependency).step facts =
      facts ∪ readyBatch system dependency facts := rfl

theorem mem_operator_step_iff
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (facts : Set (CertifiedFact system dependency))
    (fact : CertifiedFact system dependency) :
    fact ∈ (operator system dependency).step facts ↔
      fact ∈ facts ∨ DependenciesPresent system dependency fact.2.2 facts := by
  rfl

/-- A genuinely new fact enters a round exactly when all immediate child certificates occur in
the preceding fact set. -/
theorem new_mem_operator_step_iff_dependenciesPresent
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (facts : Set (CertifiedFact system dependency))
    (fact : CertifiedFact system dependency) (not_present : fact ∉ facts) :
    fact ∈ (operator system dependency).step facts ↔
      DependenciesPresent system dependency fact.2.2 facts := by
  rw [mem_operator_step_iff]
  simp [not_present]

/-- The scheduler starts with no pre-certified outcomes. -/
def closure
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) :
    Set (CertifiedFact system dependency) :=
  (operator system dependency).closureFrom ∅

/-! ## Canonical causal certificates -/

/-- The defining equation for the well-founded executable state at one target.  This lemma is not
part of `EvaluationCertificate`; it is used only to construct the canonical causal tree. -/
theorem buildOccurrenceState_equation
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) (target : Occurrence) :
    system.buildOccurrenceState dependency wellFounded target =
      system.executableStep
        (system.dependencyEnvironment dependency target fun inner _ =>
          system.buildOccurrenceState dependency wellFounded inner) target := by
  rw [OccurrenceSystem.buildOccurrenceState, WellFounded.fix_eq]

/-- A canonical causal proof tree, constructed recursively along the dependency relation. -/
noncomputable def canonicalCertificate
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) :
    ∀ target, EvaluationCertificate system dependency target
      (system.buildOccurrenceState dependency wellFounded target) :=
  wellFounded.fix fun target recurse =>
    .node target
      (fun inner _ => system.buildOccurrenceState dependency wellFounded inner)
      (fun inner h => recurse inner h)
      (buildOccurrenceState_equation system dependency wellFounded target)

/-- The canonical tree exposes exactly the canonical trees of its immediate dependencies. -/
theorem canonicalCertificate_eq
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) (target : Occurrence) :
    canonicalCertificate system dependency wellFounded target =
      .node target
        (fun inner _ => system.buildOccurrenceState dependency wellFounded inner)
        (fun inner _ => canonicalCertificate system dependency wellFounded inner)
        (buildOccurrenceState_equation system dependency wellFounded target) := by
  rw [canonicalCertificate, WellFounded.fix_eq]

/-- The canonical fact merely packages the independently constructed causal tree. -/
noncomputable def canonicalFact
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) (target : Occurrence) :
    CertifiedFact system dependency :=
  ⟨target, system.buildOccurrenceState dependency wellFounded target,
    canonicalCertificate system dependency wellFounded target⟩

/-- Every canonical causal tree is eventually scheduled.  The well-founded induction hypothesis
puts all immediate child trees in the closure; closure fixedness then admits the parent node. -/
theorem canonicalFact_mem_closure
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) (target : Occurrence) :
    canonicalFact system dependency wellFounded target ∈ closure system dependency := by
  apply wellFounded.induction target
  intro current inductionHypothesis
  have childrenPresent : DependenciesPresent system dependency
      (canonicalCertificate system dependency wellFounded current)
      (closure system dependency) := by
    rw [canonicalCertificate_eq]
    intro inner h
    exact inductionHypothesis inner h
  have entersStep : canonicalFact system dependency wellFounded current ∈
      (operator system dependency).step (closure system dependency) := by
    rw [mem_operator_step_iff]
    exact Or.inr childrenPresent
  change canonicalFact system dependency wellFounded current ∈
    (operator system dependency).step ((operator system dependency).closureFrom ∅) at entersStep
  rw [(operator system dependency).step_closureFrom ∅] at entersStep
  exact entersStep

/-! ## Certificate soundness and explicit decoding -/

/-- Every causal proof tree computes the same outcome as the well-founded executable solution.
This is proved recursively from the node equation and the soundness of its immediate child trees;
it is not stored in the certificate. -/
theorem certificate_outcome_eq_buildOccurrenceState
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) (target : Occurrence)
    (outcome : Option Label)
    (certificate : EvaluationCertificate system dependency target outcome) :
    outcome = system.buildOccurrenceState dependency wellFounded target := by
  induction certificate with
  | node current dependencyOutcomes dependencyCertificates evaluation_eq
      inductionHypothesis =>
      have dependencyOutcomes_eq : ∀ inner h,
          dependencyOutcomes inner h =
            system.buildOccurrenceState dependency wellFounded inner := by
        intro inner h
        exact inductionHypothesis inner h
      have environments_eq :
          system.dependencyEnvironment dependency current dependencyOutcomes =
            system.dependencyEnvironment dependency current (fun inner _ =>
              system.buildOccurrenceState dependency wellFounded inner) := by
        funext inner
        by_cases h : dependency inner current
        · simp [OccurrenceSystem.dependencyEnvironment, h, dependencyOutcomes_eq inner h]
        · simp [OccurrenceSystem.dependencyEnvironment, h]
      exact evaluation_eq.trans ((congrArg
        (fun state => system.executableStep state current) environments_eq).trans
          (buildOccurrenceState_equation system dependency wellFounded current).symm)

/-- A set has a certified outcome for a target when it contains some causal proof tree rooted at
that target and outcome. -/
def HasCertifiedOutcome
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (facts : Set (CertifiedFact system dependency)) (target : Occurrence) : Prop :=
  ∃ outcome certificate, (⟨target, outcome, certificate⟩ : CertifiedFact system dependency) ∈ facts

/-- Decoding explicitly consults fact membership.  It chooses the outcome of a present causal
certificate and returns `none` only when no certificate for the target is present. -/
noncomputable def decode
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (facts : Set (CertifiedFact system dependency)) :
    OccurrenceState Occurrence Label := by
  classical
  exact fun target =>
    if h : HasCertifiedOutcome system dependency facts target then Classical.choose h else none

theorem decode_eq_buildOccurrenceState_of_hasCertifiedOutcome
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (facts : Set (CertifiedFact system dependency)) (target : Occurrence)
    (has : HasCertifiedOutcome system dependency facts target) :
    decode system dependency facts target =
      system.buildOccurrenceState dependency wellFounded target := by
  rw [decode, dif_pos has]
  let outcome : Option Label := Classical.choose has
  have hasCertificate : ∃ certificate,
      (⟨target, outcome, certificate⟩ : CertifiedFact system dependency) ∈ facts :=
    Classical.choose_spec has
  let certificate : EvaluationCertificate system dependency target outcome :=
    Classical.choose hasCertificate
  exact certificate_outcome_eq_buildOccurrenceState system dependency wellFounded target
    outcome certificate

/-- Every target has a causal proof tree in the scheduler closure. -/
theorem closure_hasCertifiedOutcome
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) (target : Occurrence) :
    HasCertifiedOutcome system dependency (closure system dependency) target := by
  exact ⟨system.buildOccurrenceState dependency wellFounded target,
    canonicalCertificate system dependency wellFounded target,
    canonicalFact_mem_closure system dependency wellFounded target⟩

/-- Membership-sensitive decoding of the empty-seed closure recovers the well-founded executable
state. -/
theorem decode_closure_eq_buildOccurrenceState
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) :
    decode system dependency (closure system dependency) =
      system.buildOccurrenceState dependency wellFounded := by
  funext target
  exact decode_eq_buildOccurrenceState_of_hasCertifiedOutcome system dependency wellFounded _ _
    (closure_hasCertifiedOutcome system dependency wellFounded target)

/-- Locality makes the decoded closure an executable fixed point; independent derivation/step
correspondence then makes it a declarative CIP model. -/
theorem decode_closure_cipModel
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency) :
    system.CIPModel (decode system dependency (closure system dependency)) := by
  rw [decode_closure_eq_buildOccurrenceState]
  rw [system.cipModel_iff_executableStateStep_fixed correspondence]
  exact system.buildOccurrenceState_fixed dependency wellFounded locality

/-- The decoded scheduler closure equals every declarative model, hence the unique model. -/
theorem decode_closure_eq_model
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency)
    {state : OccurrenceState Occurrence Label} (model : system.CIPModel state) :
    decode system dependency (closure system dependency) = state := by
  exact system.cipModel_unique_of_wellFounded correspondence dependency wellFounded locality _ _
    (decode_closure_cipModel system correspondence dependency wellFounded locality) model

/-- Existence and uniqueness, with the causally decoded closure exhibited as the witness. -/
theorem decode_closure_is_uniqueModel
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency) :
    ∃! state, system.CIPModel state := by
  refine ⟨decode system dependency (closure system dependency),
    decode_closure_cipModel system correspondence dependency wellFounded locality, ?_⟩
  intro state model
  exact (decode_closure_eq_model system correspondence dependency wellFounded locality model).symm

end OccurrenceScheduler
end DeclarativeCIP
end OneCenter
end TetraStereo
