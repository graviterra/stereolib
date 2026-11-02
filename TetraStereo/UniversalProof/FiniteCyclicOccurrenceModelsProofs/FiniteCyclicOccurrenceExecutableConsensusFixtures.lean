import TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.FiniteCyclicOccurrenceExecutableConsensus

set_option autoImplicit false

/-! Closed finite evaluator regressions, not molecular or normative chemistry fixtures.
The relation is stated as optional-value constraints, independently of model enumeration. -/
namespace TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ExecutableConsensus.Fixtures

open TetraStereo.OneCenter.DeclarativeCIP

/-- Copy a present bit, treating absence as false. -/
def CopyDerives (input outcome : Option Bool) : Prop :=
  (input = some true ∧ outcome = some true) ∨
    (input ≠ some true ∧ outcome = some false)

/-- Negate a present bit, treating absence as false before negation. -/
def NegateDerives (input outcome : Option Bool) : Prop :=
  (input = some true ∧ outcome = some false) ∨
    (input ≠ some true ∧ outcome = some true)

theorem copy_correspondence (input outcome : Option Bool) :
    CopyDerives input outcome ↔ some (input.getD false) = outcome := by
  cases input with
  | none => simp [CopyDerives, eq_comm]
  | some bit => cases bit <;> simp [CopyDerives, eq_comm]

theorem negate_correspondence (input outcome : Option Bool) :
    NegateDerives input outcome ↔ some (!(input.getD false)) = outcome := by
  cases input with
  | none => simp [NegateDerives, eq_comm]
  | some bit => cases bit <;> simp [NegateDerives, eq_comm]

/-- A is fixed false; B/C either copy or form an inconsistent negation loop. -/
def cycleSystem (negated : Bool) : OccurrenceSystem Unit (Fin 3) Bool where
  finalOccurrence := fun _ => 0
  descriptorOf := fun bit => if bit then .R else .S
  executableStep := fun state site =>
    if site = 0 then some false else
    if site = 1 then some (if negated then !(state 2).getD false else (state 2).getD false)
    else some ((state 1).getD false)
  DeclarativeDerivation := fun state site outcome =>
    if site = 0 then outcome = some false else
    if site = 1 then
      if negated then NegateDerives (state 2) outcome else CopyDerives (state 2) outcome
    else CopyDerives (state 1) outcome

theorem cycle_correspondence (negated : Bool) :
    (cycleSystem negated).DerivationStepCorrespondence := by
  intro state site outcome
  by_cases zero : site = 0
  · simp [cycleSystem, zero, eq_comm]
  · by_cases one : site = 1
    · cases negated <;> simp [cycleSystem, one, copy_correspondence,
        negate_correspondence]
    · simp [cycleSystem, zero, one, copy_correspondence]

theorem copy_cycle_exactly_two_models : (fixedModels (cycleSystem false)).card = 2 := by
  decide +kernel

theorem copy_cycle_forced_A : compute (fixedModels (cycleSystem false)) 0 =
    .determined (some false) := by decide +kernel

theorem copy_cycle_ambiguous_B : compute (fixedModels (cycleSystem false)) 1 =
    .ambiguous := by decide +kernel

theorem copy_cycle_ambiguous_C : compute (fixedModels (cycleSystem false)) 2 =
    .ambiguous := by decide +kernel

/-- The same complete models force A while leaving B genuinely ambiguous. -/
theorem forced_coordinate_despite_multiple_models :
    (fixedModels (cycleSystem false)).card = 2 ∧
      compute (fixedModels (cycleSystem false)) 0 = .determined (some false) ∧
      compute (fixedModels (cycleSystem false)) 1 = .ambiguous :=
  ⟨copy_cycle_exactly_two_models, copy_cycle_forced_A, copy_cycle_ambiguous_B⟩

theorem negation_cycle_no_model : fixedModels (cycleSystem true) = ∅ := by decide +kernel

theorem negation_cycle_no_vacuous_A : compute (fixedModels (cycleSystem true)) 0 =
    .inconsistent := by decide +kernel

theorem negation_cycle_no_declarative_model :
    ¬ ∃ state, (cycleSystem true).CIPModel state :=
  (compute_fixedModels_inconsistent_iff (cycleSystem true) (cycle_correspondence true) 0).mp
    negation_cycle_no_vacuous_A

def absentSystem : OccurrenceSystem Unit (Fin 1) Bool where
  finalOccurrence := fun _ => 0
  descriptorOf := fun bit => if bit then .R else .S
  executableStep := fun _ _ => none
  DeclarativeDerivation := fun _ _ outcome => outcome = none

theorem absent_correspondence : absentSystem.DerivationStepCorrespondence := by
  intro state site outcome
  simp [absentSystem, eq_comm]

theorem absent_exactly_one_model : (fixedModels absentSystem).card = 1 := by decide +kernel

theorem absent_determined_none : compute (fixedModels absentSystem) 0 = .determined none := by
  decide +kernel

theorem absent_nonempty_not_inconsistent :
    compute (fixedModels absentSystem) 0 ≠ .inconsistent := by
  rw [absent_determined_none]
  decide

/-- Distinct descriptor alphabets are supported without any tetrahedral coercion. -/
def mixedSystem : OccurrenceSystem Unit (Fin 2) Bool where
  finalOccurrence := fun _ => 0
  descriptorOf := fun bit => if bit then .seqTrans else .E
  executableStep := fun _ site => some (decide (site = 0))
  DeclarativeDerivation := fun _ site outcome =>
    (site = 0 ∧ outcome = some true) ∨ (site ≠ 0 ∧ outcome = some false)

theorem mixed_correspondence : mixedSystem.DerivationStepCorrespondence := by
  intro state site outcome
  by_cases zero : site = 0 <;> simp [mixedSystem, zero, eq_comm]

theorem mixed_exactly_one_model : (fixedModels mixedSystem).card = 1 := by decide +kernel

theorem mixed_first_computed : compute (fixedModels mixedSystem) 0 = .determined (some true) := by
  decide +kernel

theorem mixed_second_computed : compute (fixedModels mixedSystem) 1 = .determined (some false) := by
  decide +kernel

theorem mixed_descriptor_preserved :
    mixedSystem.descriptorOf true = .seqTrans ∧ mixedSystem.descriptorOf false = .E := by
  decide +kernel

end TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ExecutableConsensus.Fixtures
