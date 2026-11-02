import TetraStereo.OneCenter.DeclarativeCIPOccurrenceScheduler

set_option autoImplicit false

namespace TetraStereo.Certificate.Dependency

open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.DeclarativeCIP.OccurrenceScheduler

universe u v w

/-!
A finite, data-only causal certificate. Each node names its occurrence, proposed optional outcome
and indices into earlier facts. The checker verifies the complete ordered dependency list and
recomputes the actual local evaluator. It does not accept local correctness or a final model as
payload. A `none` outcome must pass that same check.

The source adapter owns the occurrence encoding, dependency enumeration, evaluator and its
independent declarative correspondence. Acceptance establishes the listed outcomes; it does not
claim that every input has a finite causal certificate or that cyclic dependencies are supported.
-/

structure Node (Occurrence : Type v) (Label : Type w) where
  target : Occurrence
  outcome : Option Label
  references : List Nat
  deriving Repr, DecidableEq

abbrev Fact (Occurrence : Type v) (Label : Type w) := Occurrence × Option Label

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

def lookup [DecidableEq Occurrence] (facts : List (Fact Occurrence Label))
    (target : Occurrence) : Option Label :=
  match facts with
  | [] => none
  | (occurrence, outcome) :: rest => if occurrence = target then outcome else lookup rest target

def referenced (facts : List (Fact Occurrence Label)) (indices : List Nat) :
    List (Fact Occurrence Label) :=
  indices.filterMap (fun index => facts[index]?)

def relation (dependencies : Occurrence → List Occurrence) :
    Occurrence → Occurrence → Prop :=
  fun inner target => inner ∈ dependencies target

/-- Structural reference checks and one local evaluation, independently of the scheduler solution. -/
def ValidNode [DecidableEq Occurrence]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (facts : List (Fact Occurrence Label)) (node : Node Occurrence Label) : Prop :=
  node.references.Nodup ∧
    (∀ index ∈ node.references, index < facts.length) ∧
    (referenced facts node.references).map Prod.fst = dependencies node.target ∧
    node.outcome = system.executableStep (lookup (referenced facts node.references)) node.target

instance [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (facts : List (Fact Occurrence Label)) (node : Node Occurrence Label) :
    Decidable (ValidNode system dependencies facts node) := by
  unfold ValidNode
  infer_instance

/-- The prefix is internal execution state; public checking always starts with the empty prefix. -/
def checkFrom [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (facts : List (Fact Occurrence Label)) :
    List (Node Occurrence Label) → Option (List (Fact Occurrence Label))
  | [] => some facts
  | node :: rest =>
      if ValidNode system dependencies facts node then
        checkFrom system dependencies (facts ++ [(node.target, node.outcome)]) rest
      else none

def check [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence) (nodes : List (Node Occurrence Label)) :
    Option (List (Fact Occurrence Label)) :=
  checkFrom system dependencies [] nodes

def Certified (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence) (facts : List (Fact Occurrence Label)) : Prop :=
  ∀ fact ∈ facts, Nonempty (EvaluationCertificate system (relation dependencies) fact.1 fact.2)

theorem lookup_none_of_not_mem [DecidableEq Occurrence]
    (facts : List (Fact Occurrence Label)) (target : Occurrence)
    (absent : target ∉ facts.map Prod.fst) : lookup facts target = none := by
  induction facts with
  | nil => rfl
  | cons fact rest ih =>
      rcases fact with ⟨occurrence, outcome⟩
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp only [lookup, if_neg (Ne.symm absent.1)]
      exact ih absent.2

theorem lookup_certified [DecidableEq Occurrence]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence) (facts : List (Fact Occurrence Label))
    (certified : Certified system dependencies facts) (target : Occurrence)
    (present : target ∈ facts.map Prod.fst) :
    Nonempty (EvaluationCertificate system (relation dependencies) target (lookup facts target)) := by
  induction facts with
  | nil => simp at present
  | cons fact rest ih =>
      rcases fact with ⟨occurrence, outcome⟩
      by_cases equal : occurrence = target
      · subst occurrence
        simpa only [lookup, if_pos rfl] using certified (target, outcome) (by simp)
      · have in_rest : target ∈ rest.map Prod.fst := by
          simpa only [List.map_cons, List.mem_cons, Ne.symm equal, false_or] using present
        have rest_certified : Certified system dependencies rest := by
          intro fact member
          exact certified fact (List.mem_cons_of_mem _ member)
        simpa only [lookup, if_neg equal] using ih rest_certified in_rest

theorem referenced_certified
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (facts : List (Fact Occurrence Label)) (indices : List Nat)
    (certified : Certified system dependencies facts) :
    Certified system dependencies (referenced facts indices) := by
  intro fact member
  obtain ⟨index, _, found⟩ := List.mem_filterMap.mp member
  exact certified fact (List.mem_of_getElem? found)

/-- Checked data can be elaborated into the existing causal proof-tree interface. -/
theorem validNode_certificate [DecidableEq Occurrence]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (facts : List (Fact Occurrence Label)) (node : Node Occurrence Label)
    (certified : Certified system dependencies facts)
    (valid : ValidNode system dependencies facts node) :
    Nonempty (EvaluationCertificate system (relation dependencies) node.target node.outcome) := by
  classical
  let inputs := referenced facts node.references
  have inputs_certified : Certified system dependencies inputs :=
    referenced_certified system dependencies facts node.references certified
  have domain : inputs.map Prod.fst = dependencies node.target := valid.2.2.1
  have child : ∀ inner, relation dependencies inner node.target →
      Nonempty (EvaluationCertificate system (relation dependencies) inner (lookup inputs inner)) := by
    intro inner depends
    apply lookup_certified system dependencies inputs inputs_certified inner
    rw [domain]
    exact depends
  have environment :
      system.dependencyEnvironment (relation dependencies) node.target
        (fun inner _ => lookup inputs inner) = lookup inputs := by
    funext inner
    by_cases depends : relation dependencies inner node.target
    · simp [OccurrenceSystem.dependencyEnvironment, depends]
    · have absent : inner ∉ inputs.map Prod.fst := by
        rw [domain]
        exact depends
      simp [OccurrenceSystem.dependencyEnvironment, depends,
        lookup_none_of_not_mem inputs inner absent]
  refine ⟨EvaluationCertificate.node node.target (fun inner _ => lookup inputs inner)
    (fun inner depends => Classical.choice (child inner depends)) ?_⟩
  rw [environment]
  exact valid.2.2.2

theorem checkFrom_certified [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (nodes : List (Node Occurrence Label))
    (facts result : List (Fact Occurrence Label))
    (certified : Certified system dependencies facts)
    (accepted : checkFrom system dependencies facts nodes = some result) :
    Certified system dependencies result := by
  induction nodes generalizing facts with
  | nil =>
      simp only [checkFrom, Option.some.injEq] at accepted
      subst result
      exact certified
  | cons node rest ih =>
      simp only [checkFrom] at accepted
      split at accepted
      · rename_i valid
        apply ih (facts ++ [(node.target, node.outcome)])
        · intro fact member
          rcases List.mem_append.mp member with old | added
          · exact certified fact old
          · have equal : fact = (node.target, node.outcome) := by simpa using added
            subst fact
            exact validNode_certificate system dependencies facts node certified valid
        · exact accepted
      · contradiction

theorem check_sound [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (nodes : List (Node Occurrence Label)) (result : List (Fact Occurrence Label))
    (accepted : check system dependencies nodes = some result) :
    Certified system dependencies result :=
  checkFrom_certified system dependencies nodes [] result (by simp [Certified]) accepted

/-- Soundness relative to a well-founded actual dependency relation. No complete model is supplied. -/
theorem checked_outcome_eq_solution [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (wellFounded : WellFounded (relation dependencies))
    (nodes : List (Node Occurrence Label)) (result : List (Fact Occurrence Label))
    (accepted : check system dependencies nodes = some result)
    (fact : Fact Occurrence Label) (member : fact ∈ result) :
    fact.2 = system.buildOccurrenceState (relation dependencies) wellFounded fact.1 := by
  obtain ⟨certificate⟩ := check_sound system dependencies nodes result accepted fact member
  exact certificate_outcome_eq_buildOccurrenceState system (relation dependencies)
    wellFounded fact.1 fact.2 certificate

/-- The chemical interpretation boundary remains explicit: a source adapter must prove both
locality of its dependency enumeration and correspondence to its independent derivation relation.
The checker supplies the outcome; no desired descriptor or completed model is an input. -/
theorem checked_outcome_declarative [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (wellFounded : WellFounded (relation dependencies))
    (locality : system.EvaluatorLocalFor (relation dependencies))
    (correspondence : system.DerivationStepCorrespondence)
    (nodes : List (Node Occurrence Label)) (result : List (Fact Occurrence Label))
    (accepted : check system dependencies nodes = some result)
    (fact : Fact Occurrence Label) (member : fact ∈ result) :
    system.DeclarativeDerivation
      (system.buildOccurrenceState (relation dependencies) wellFounded) fact.1 fact.2 := by
  have model := (system.cipModel_iff_executableStateStep_fixed correspondence
    (system.buildOccurrenceState (relation dependencies) wellFounded)).mpr
      (system.buildOccurrenceState_fixed (relation dependencies) wellFounded locality)
  rw [checked_outcome_eq_solution system dependencies wellFounded nodes result accepted fact member]
  exact model fact.1

end TetraStereo.Certificate.Dependency
