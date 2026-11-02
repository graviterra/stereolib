import TetraStereo.OneCenter.DeclarativeCIPGlobalFixedPoint

set_option autoImplicit false



























namespace TetraStereo
namespace UniversalProof
namespace FiniteCyclicOccurrenceModelsProofs

open TetraStereo.OneCenter.DeclarativeCIP

universe u v w

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

/-- The complete candidate state space for a finite occurrence carrier. -/
abbrev CompleteState (Occurrence : Type v) (Label : Type w) :=
  OccurrenceState Occurrence Label

section FiniteEnumeration

variable [Fintype Occurrence] [DecidableEq Occurrence]
variable [Fintype Label] [DecidableEq Label]

/-- The computable pointwise fixed-point test.  It is a `Bool` obtained from the *supplied*
decidable equality on the complete function space, not from a classical filter. -/
def isFixedState (system : OccurrenceSystem FinalUnit Occurrence Label)
    (state : CompleteState Occurrence Label) : Bool :=
  if system.executableStateStep state = state then true else false

omit [DecidableEq Occurrence] [Fintype Label] in
/-- The `Bool` fixed-point test reflects the exact executable fixed-point equation. -/
theorem isFixedState_eq_true_iff (system : OccurrenceSystem FinalUnit Occurrence Label)
    (state : CompleteState Occurrence Label) :
    isFixedState system state = true ↔ system.executableStateStep state = state := by
  by_cases fixed : system.executableStateStep state = state
  · simp [isFixedState, fixed]
  · simp [isFixedState, fixed]

/-- The finite set of complete environments left unchanged by the executable evaluator.

This is the total function space `Occurrence → Option Label` filtered pointwise.  Its cardinality
is bounded by `|Option Label| ^ |Occurrence|`; no arbitrary branching or node cap is imposed. -/
def fixedModels (system : OccurrenceSystem FinalUnit Occurrence Label) :
    Finset (CompleteState Occurrence Label) :=
  Finset.univ.filter fun state => system.executableStateStep state = state

/-- Literal membership in the enumerator is exactly the executable fixed-point equation. -/
theorem mem_fixedModels_iff (system : OccurrenceSystem FinalUnit Occurrence Label)
    (state : CompleteState Occurrence Label) :
    state ∈ fixedModels system ↔ system.executableStateStep state = state := by
  simp [fixedModels]

/-- Membership can equivalently be read off the computable `Bool` reflection. -/
theorem mem_fixedModels_iff_isFixedState (system : OccurrenceSystem FinalUnit Occurrence Label)
    (state : CompleteState Occurrence Label) :
    state ∈ fixedModels system ↔ isFixedState system state = true :=
  (mem_fixedModels_iff system state).trans (isFixedState_eq_true_iff system state).symm

/-- **Literal model membership.**  Under the explicit, independently discharged
`DerivationStepCorrespondence`, a complete environment is enumerated by the executable solver if
and only if it is a declarative `CIPModel`.  This is the bridge between the executable enumeration
and the declarative semantics; it is *not* a repackaging of definitionally equal fields. -/
theorem mem_fixedModels_iff_cipModel (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (state : CompleteState Occurrence Label) :
    state ∈ fixedModels system ↔ system.CIPModel state :=
  (mem_fixedModels_iff system state).trans
    (system.cipModel_iff_executableStateStep_fixed correspondence state).symm

/-- The enumerator is duplicate-free by construction: a `Finset` carries its own `Nodup` witness,
which we expose so no downstream consumer can silently revert to a multiset. -/
theorem fixedModels_val_nodup (system : OccurrenceSystem FinalUnit Occurrence Label) :
    (fixedModels system).val.Nodup :=
  (fixedModels system).nodup

/-- The enumerator is nonempty exactly when a declarative model exists. -/
theorem fixedModels_nonempty_iff_exists_cipModel
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence) :
    (fixedModels system).Nonempty ↔ ∃ state, system.CIPModel state := by
  constructor
  · rintro ⟨state, hmem⟩
    exact ⟨state, (mem_fixedModels_iff_cipModel system correspondence state).1 hmem⟩
  · rintro ⟨state, hmodel⟩
    exact ⟨state, (mem_fixedModels_iff_cipModel system correspondence state).2 hmodel⟩

omit [Fintype Occurrence] [DecidableEq Occurrence] [Fintype Label] [DecidableEq Label] in
/-- The well-founded construction's canonical state is a declarative model. -/
theorem buildOccurrenceState_cipModel (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency) :
    system.CIPModel (system.buildOccurrenceState dependency wellFounded) :=
  (system.cipModel_iff_executableStateStep_fixed correspondence
    (system.buildOccurrenceState dependency wellFounded)).mpr
      (system.buildOccurrenceState_fixed dependency wellFounded locality)

/-- **Agreement with the well-founded unique causal construction.**  When the executable evaluator
is local for a well-founded dependency relation, the finite enumerator is exactly the singleton of
the existing `buildOccurrenceState` model.  This connects the exhaustive solver to the prior
construction rather than replacing it. -/
theorem mem_fixedModels_iff_eq_buildOccurrenceState
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop)
    (wellFounded : WellFounded dependency)
    (locality : system.EvaluatorLocalFor dependency)
    (state : CompleteState Occurrence Label) :
    state ∈ fixedModels system ↔
      state = system.buildOccurrenceState dependency wellFounded := by
  constructor
  · intro hmem
    have hmodel : system.CIPModel state :=
      (mem_fixedModels_iff_cipModel system correspondence state).1 hmem
    exact system.cipModel_unique_of_wellFounded correspondence dependency wellFounded locality
      state _ hmodel
      (buildOccurrenceState_cipModel system correspondence dependency wellFounded locality)
  · intro heq
    rw [heq]
    exact (mem_fixedModels_iff_cipModel system correspondence _).2
      (buildOccurrenceState_cipModel system correspondence dependency wellFounded locality)

end FiniteEnumeration

end FiniteCyclicOccurrenceModelsProofs
end UniversalProof
end TetraStereo
