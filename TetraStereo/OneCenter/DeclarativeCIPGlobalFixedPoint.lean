import TetraStereo.OneCenter.DeclarativeCIP
import TetraStereo.OneCenter.DescriptorFixedPoint

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

universe u v w x

/-!
# Generic occurrence-level revised-CIP fixed points

This module deliberately contains no molecular occurrence discovery and no production rule
implementation.  A production integration supplies two genuinely separate objects:

* a declarative, proof-relevant derivation relation on optional outcomes; and
* an executable, total optional evaluator.

Their correspondence is an explicit theorem hypothesis.  In particular, `none` is a semantic
outcome that must itself be derived, rather than the absence of a positive derivation.
-/

/-- A complete candidate state is indexed by occurrences, never by final stereogenic units. -/
abbrev OccurrenceState (Occurrence : Type u) (Label : Type v) :=
  Occurrence → Option Label

/-- Generic data for occurrence-level revised-CIP semantics.

`FinalUnit` and `Occurrence` are intentionally unrelated types at this layer.  The sole route from
a final unit to occurrence semantics is `finalOccurrence`.  Production discovery is responsible
for constructing that map and proving its molecular meaning.

`DeclarativeDerivation` and `executableStep` are independent fields.  Merely constructing a system
does not assert that they agree; that assertion is the separate `DerivationStepCorrespondence`
proposition below. -/
structure OccurrenceSystem (FinalUnit : Type u) (Occurrence : Type v) (Label : Type w) where
  finalOccurrence : FinalUnit → Occurrence
  descriptorOf : Label → Descriptor
  DeclarativeDerivation :
    OccurrenceState Occurrence Label → Occurrence → Option Label → Prop
  executableStep : OccurrenceState Occurrence Label → Occurrence → Option Label

namespace OccurrenceSystem

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

local notation "State" => OccurrenceState Occurrence Label

/-- A declarative model derives the complete optional outcome stored at every occurrence.
The outcome is not restricted to `some label`; a model must also justify every stored `none`. -/
def CIPModel (system : OccurrenceSystem FinalUnit Occurrence Label) (state : State) : Prop :=
  ∀ occurrence, system.DeclarativeDerivation state occurrence (state occurrence)

/-- The independently executable evaluator regenerates `output` from `input` pointwise. -/
def Regenerates (system : OccurrenceSystem FinalUnit Occurrence Label)
    (input output : State) : Prop :=
  ∀ occurrence, system.executableStep input occurrence = output occurrence

/-- Simultaneous application of the independently supplied executable evaluator. -/
def executableStateStep (system : OccurrenceSystem FinalUnit Occurrence Label) : State → State :=
  fun state occurrence => system.executableStep state occurrence

/-- The substantive integration obligation: declarative derivability and executable evaluation
agree for every state, occurrence, and optional outcome. -/
def DerivationStepCorrespondence
    (system : OccurrenceSystem FinalUnit Occurrence Label) : Prop :=
  ∀ state occurrence outcome,
    system.DeclarativeDerivation state occurrence outcome ↔
      system.executableStep state occurrence = outcome

/-- Soundness and completeness of a model with respect to executable regeneration.

This theorem crosses the independently defined derivation relation and evaluator through the
explicit correspondence proof.  It is neither definitional equality nor a repacking of two model
fields. -/
theorem cipModel_iff_regenerates
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence) (state : State) :
    system.CIPModel state ↔ system.Regenerates state state := by
  constructor
  · intro model occurrence
    exact (correspondence state occurrence (state occurrence)).1 (model occurrence)
  · intro regenerated occurrence
    exact (correspondence state occurrence (state occurrence)).2 (regenerated occurrence)

/-- Executable regeneration is ordinary function equality after simultaneous application. -/
theorem regenerates_iff_executableStateStep_eq
    (system : OccurrenceSystem FinalUnit Occurrence Label) (input output : State) :
    system.Regenerates input output ↔ system.executableStateStep input = output := by
  constructor
  · intro regenerated
    funext occurrence
    exact regenerated occurrence
  · intro equation occurrence
    exact congrFun equation occurrence

theorem cipModel_iff_executableStateStep_fixed
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence) (state : State) :
    system.CIPModel state ↔ system.executableStateStep state = state := by
  rw [system.cipModel_iff_regenerates correspondence]
  exact system.regenerates_iff_executableStateStep_eq state state

/-! ## Exact semantic dependence of the executable evaluator -/

/-- Two states differ, if at all, only at one occurrence. -/
def DiffersOnlyAt (left right : State) (source : Occurrence) : Prop :=
  ∀ other, other ≠ source → left other = right other

/-- An occurrence is an essential input exactly when changing only that coordinate can change the
executable result at the target.  This is semantic dependence, not a declared overapproximation. -/
def EssentialInput (system : OccurrenceSystem FinalUnit Occurrence Label)
    (source target : Occurrence) : Prop :=
  ∃ left right : State,
    DiffersOnlyAt left right source ∧
      system.executableStep left target ≠ system.executableStep right target

/-- The exact local input view consists of precisely the evaluator's essential coordinates. -/
def EssentialScope (system : OccurrenceSystem FinalUnit Occurrence Label)
    (target : Occurrence) :=
  { source : Occurrence // system.EssentialInput source target }

def EssentialView (system : OccurrenceSystem FinalUnit Occurrence Label)
    (target : Occurrence) :=
  system.EssentialScope target → Option Label

def restrictEssential (system : OccurrenceSystem FinalUnit Occurrence Label)
    (state : State) (target : Occurrence) : system.EssentialView target :=
  fun source => state source.1

/-- Locality of the executable evaluator with respect to a proposed dependency relation. -/
def EvaluatorLocalFor (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) : Prop :=
  ∀ left right target,
    (∀ source, dependency source target → left source = right source) →
      system.executableStep left target = system.executableStep right target

section FiniteEssentialScope

variable [Fintype Occurrence] [DecidableEq Occurrence]

private def patch (left right : State) (done : Finset Occurrence) : State :=
  fun occurrence => if occurrence ∈ done then right occurrence else left occurrence

omit [Fintype Occurrence] in
@[simp] private theorem patch_empty (left right : State) :
    patch left right ∅ = left := by
  funext occurrence
  simp [patch]

@[simp] private theorem patch_univ (left right : State) :
    patch left right Finset.univ = right := by
  funext occurrence
  simp [patch]

omit [Fintype Occurrence] in
private theorem patch_insert_differsOnlyAt (left right : State)
    (done : Finset Occurrence) (source : Occurrence) :
    DiffersOnlyAt (patch left right done) (patch left right (insert source done)) source := by
  intro other hne
  simp only [patch, Finset.mem_insert]
  by_cases hdone : other ∈ done
  · simp [hdone]
  · simp [hdone, hne]

omit [Fintype Occurrence] in
private theorem executableStep_patch_eq
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (left right : State) (target : Occurrence)
    (agree : ∀ source, system.EssentialInput source target →
      left source = right source) :
    ∀ done : Finset Occurrence,
      system.executableStep left target =
        system.executableStep (patch left right done) target := by
  intro done
  induction done using Finset.induction_on with
  | empty => simp
  | @insert source done hnotmem inductionHypothesis =>
      rw [inductionHypothesis]
      by_cases hessential : system.EssentialInput source target
      · have hsource := agree source hessential
        have hpatch : patch left right (insert source done) = patch left right done := by
          funext occurrence
          simp only [patch, Finset.mem_insert]
          by_cases hoccurrence : occurrence = source
          · subst occurrence
            simp [hnotmem, hsource]
          · simp [hoccurrence]
        rw [hpatch]
      · apply Classical.byContradiction
        intro hne
        apply hessential
        exact ⟨patch left right done, patch left right (insert source done),
          patch_insert_differsOnlyAt left right done source, hne⟩

/-- Agreement on exactly the essential scope is sufficient for evaluator agreement. -/
theorem executableStep_eq_of_restrictEssential_eq
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (left right : State) (target : Occurrence)
    (viewsEqual : system.restrictEssential left target =
      system.restrictEssential right target) :
    system.executableStep left target = system.executableStep right target := by
  have agree : ∀ source, system.EssentialInput source target →
      left source = right source := by
    intro source essential
    exact congrFun viewsEqual ⟨source, essential⟩
  simpa using system.executableStep_patch_eq left right target agree Finset.univ

/-- The evaluator is local with respect to its exact semantic essential-input relation. -/
theorem evaluatorLocalFor_essential
    (system : OccurrenceSystem FinalUnit Occurrence Label) :
    system.EvaluatorLocalFor system.EssentialInput := by
  intro left right target agree
  apply system.executableStep_eq_of_restrictEssential_eq left right target
  funext source
  exact agree source.1 source.2

end FiniteEssentialScope

/-- Every relation sufficient for evaluator locality contains every semantically essential input.
Thus `EssentialInput` is minimal among all locality relations. -/
theorem essentialInput_minimal
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (locality : system.EvaluatorLocalFor dependency)
    {source target : Occurrence} (essential : system.EssentialInput source target) :
    dependency source target := by
  by_contra hnot
  rcases essential with ⟨left, right, only, changes⟩
  apply changes
  apply locality left right target
  intro other hdependency
  exact only other (fun equal => hnot (equal ▸ hdependency))

/-- On a finite occurrence carrier, `EssentialInput` is the least relation that makes the
executable evaluator local: it is itself local and is contained in every other local relation. -/
theorem essentialInput_isLeast_localityRelation
    [Fintype Occurrence] [DecidableEq Occurrence]
    (system : OccurrenceSystem FinalUnit Occurrence Label) :
    system.EvaluatorLocalFor system.EssentialInput ∧
      ∀ dependency, system.EvaluatorLocalFor dependency →
        ∀ source target, system.EssentialInput source target →
          dependency source target :=
  ⟨system.evaluatorLocalFor_essential,
    fun dependency locality _ _ essential =>
      system.essentialInput_minimal dependency locality essential⟩

/-! ## Well-founded existence and uniqueness -/

/-- A total state assembled from values already constructed at strict dependencies.  Values at
all nondependencies are explicitly `none`; no uninitialized value is silently consulted. -/
noncomputable def dependencyEnvironment
    (_system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (target : Occurrence)
    (innerValue : ∀ inner, dependency inner target → Option Label) : State := by
  classical
  exact fun inner =>
    if hinner : dependency inner target then innerValue inner hinner else none

/-- Well-founded evaluation of the executable occurrence equations. -/
noncomputable def buildOccurrenceState
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency) : State :=
  wellFounded.fix fun target innerValue =>
    system.executableStep
      (system.dependencyEnvironment dependency target innerValue) target

theorem buildOccurrenceState_fixed
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency) :
    system.executableStateStep
        (system.buildOccurrenceState dependency wellFounded) =
      system.buildOccurrenceState dependency wellFounded := by
  funext target
  let localEnvironment : State :=
    system.dependencyEnvironment dependency target fun inner _ =>
      system.buildOccurrenceState dependency wellFounded inner
  have fixedEquation : system.buildOccurrenceState dependency wellFounded target =
      system.executableStep localEnvironment target := by
    rw [buildOccurrenceState, WellFounded.fix_eq]
    rfl
  have environmentsAgree : ∀ inner, dependency inner target →
      localEnvironment inner =
        system.buildOccurrenceState dependency wellFounded inner := by
    intro inner hinner
    simp [localEnvironment, dependencyEnvironment, hinner]
  have stepEqual := locality localEnvironment
    (system.buildOccurrenceState dependency wellFounded) target environmentsAgree
  exact stepEqual.symm.trans fixedEquation.symm

theorem cipModel_unique_of_wellFounded
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency) :
    ∀ left right, system.CIPModel left → system.CIPModel right → left = right := by
  intro left right leftModel rightModel
  have leftFixed :=
    (system.cipModel_iff_executableStateStep_fixed correspondence left).1 leftModel
  have rightFixed :=
    (system.cipModel_iff_executableStateStep_fixed correspondence right).1 rightModel
  funext target
  apply wellFounded.induction target
  intro target inductionHypothesis
  have stepEqual : system.executableStep left target =
      system.executableStep right target := by
    apply locality left right target
    intro inner hinner
    exact inductionHypothesis inner hinner
  exact (congrFun leftFixed target).symm.trans
    (stepEqual.trans (congrFun rightFixed target))

/-! ## Naturality of the unique global model -/

/-- Transport an occurrence state contravariantly along an occurrence permutation and
covariantly along a label map. -/
def transportState
    (permutation : Equiv.Perm Occurrence) (relabel : Label → Label)
    (state : State) : State :=
  fun target => (state (permutation.symm target)).map relabel

/-- Pointwise naturality of the executable evaluator promotes, by well-founded uniqueness, to
naturality of every complete declarative model.  This is the global collapse theorem used by
molecular symmetries: the scheduler is proved equivariant once, without replaying its closure at
each occurrence. -/
theorem cipModel_natural_of_executableStep_natural
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency)
    (permutation : Equiv.Perm Occurrence) (relabel : Label → Label)
    (natural : ∀ candidate target,
      system.executableStep (transportState permutation relabel candidate)
          (permutation target) =
        (system.executableStep candidate target).map relabel)
    (state : State) (model : system.CIPModel state) :
    ∀ target, state (permutation target) = (state target).map relabel := by
  let transported := transportState permutation relabel state
  have stateFixed : system.executableStateStep state = state :=
    (system.cipModel_iff_executableStateStep_fixed correspondence state).mp model
  have transportedFixed : system.executableStateStep transported = transported := by
    funext transformedTarget
    let original := permutation.symm transformedTarget
    have targetEq : permutation original = transformedTarget :=
      permutation.apply_symm_apply transformedTarget
    change system.executableStep transported transformedTarget = transported transformedTarget
    rw [← targetEq]
    change system.executableStep
        (transportState permutation relabel state) (permutation original) =
      (state (permutation.symm (permutation original))).map relabel
    rw [natural state original, permutation.symm_apply_apply]
    exact congrArg (Option.map relabel) (congrFun stateFixed original)
  have transportedModel : system.CIPModel transported :=
    (system.cipModel_iff_executableStateStep_fixed correspondence transported).mpr
      transportedFixed
  have stateEq : state = transported :=
    system.cipModel_unique_of_wellFounded correspondence dependency wellFounded locality
      state transported model transportedModel
  intro target
  have atTarget := congrFun stateEq (permutation target)
  simpa [transported, transportState] using atTarget

/-- A well-founded local executable evaluator has exactly one complete occurrence model, provided
the independent declarative rules have been proved equivalent to that evaluator. -/
theorem existsUnique_cipModel_of_wellFounded
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency) :
    ∃! state, system.CIPModel state := by
  let state := system.buildOccurrenceState dependency wellFounded
  have fixed : system.executableStateStep state = state :=
    system.buildOccurrenceState_fixed dependency wellFounded locality
  have model : system.CIPModel state :=
    (system.cipModel_iff_executableStateStep_fixed correspondence state).2 fixed
  refine ⟨state, model, ?_⟩
  intro candidate candidateModel
  exact system.cipModel_unique_of_wellFounded correspondence dependency wellFounded locality
    candidate state candidateModel model

/-! ## Final projection and the state-sensitive one-way judgment -/

/-- Final descriptors exist only as a projection of the occurrence-level state. -/
def finalDescriptorProjection
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (state : State) : DescriptorMap FinalUnit :=
  fun unit => (state (system.finalOccurrence unit)).map system.descriptorOf

/-- State-sensitive descriptor judgment induced by the independently defined declarative rules at
the distinguished final occurrence.  Production integrations prove their concrete judgment
equivalent to this relation; the generic core contains no assumed soundness field. -/
def FinalDescriptorJudgment
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (state : State) (unit : FinalUnit) (descriptor : Descriptor) : Prop :=
  ∃ label,
    system.DeclarativeDerivation state (system.finalOccurrence unit) (some label) ∧
      system.descriptorOf label = descriptor

/-- A model assignment at a final occurrence automatically yields the state-sensitive descriptor
judgment.  No bridge structure or caller-supplied semantic implication is involved. -/
theorem finalDescriptorJudgment_of_model_assignment
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    {state : State} (model : system.CIPModel state)
    (unit : FinalUnit) (label : Label)
    (assigned : state (system.finalOccurrence unit) = some label) :
    system.FinalDescriptorJudgment state unit (system.descriptorOf label) := by
  refine ⟨label, ?_, rfl⟩
  simpa [assigned] using model (system.finalOccurrence unit)

theorem finalDescriptorProjection_eq_some_of_assignment
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (state : State) (unit : FinalUnit) (label : Label)
    (assigned : state (system.finalOccurrence unit) = some label) :
    system.finalDescriptorProjection state unit = some (system.descriptorOf label) := by
  simp [finalDescriptorProjection, assigned]

/-- The all-`none` state cannot satisfy the model merely because positive labels are absent: one
executable `some` outcome contradicts the required declarative derivation of `none`. -/
theorem empty_not_model_of_some_outcome
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (occurrence : Occurrence) (label : Label)
    (produces : system.executableStep (fun _ => none) occurrence = some label) :
    ¬system.CIPModel (fun _ => none) := by
  intro model
  have derivedNone := model occurrence
  have producesNone :=
    (correspondence (fun _ => none) occurrence none).1 derivedNone
  rw [produces] at producesNone
  simp at producesNone

/-! ## Monotone certified-fact scheduler simulation -/

/-- A certified-fact scheduler simulation decodes fact sets to complete occurrence states and
proves that one monotone closure step implements the actual executable state step. -/
structure SchedulerSimulation (CertifiedFact : Type x)
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (operator : DescriptorClosureOperator CertifiedFact) where
  decode : Set CertifiedFact → State
  step_commutes : ∀ facts,
    decode (operator.step facts) =
      system.executableStateStep (decode facts)

/-- The monotone scheduler closure decodes to a declarative model via both the executable-step
simulation and the independently proved derivation/step correspondence. -/
theorem schedulerClosure_cipModel
    {CertifiedFact : Type x}
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (operator : DescriptorClosureOperator CertifiedFact)
    (simulation : SchedulerSimulation CertifiedFact system operator)
    (seed : Set CertifiedFact) :
    system.CIPModel (simulation.decode (operator.closureFrom seed)) := by
  rw [system.cipModel_iff_executableStateStep_fixed correspondence]
  rw [← simulation.step_commutes]
  rw [operator.step_closureFrom]

/-- Under well-founded locality, the decoded scheduler closure is the unique occurrence model. -/
theorem schedulerClosure_eq_uniqueModel
    {CertifiedFact : Type x}
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency)
    (operator : DescriptorClosureOperator CertifiedFact)
    (simulation : SchedulerSimulation CertifiedFact system operator)
    (seed : Set CertifiedFact) {state : State} (model : system.CIPModel state) :
    simulation.decode (operator.closureFrom seed) = state :=
  system.cipModel_unique_of_wellFounded correspondence dependency wellFounded locality _ _
    (system.schedulerClosure_cipModel correspondence operator simulation seed) model

end OccurrenceSystem

end DeclarativeCIP
end OneCenter
end TetraStereo
