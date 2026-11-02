import TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.FiniteCyclicOccurrenceExecutableConsensusFixtures

set_option autoImplicit false



























namespace TetraStereo.UniversalProof.ProjectedCompleteModelConsensusProofs.ProjectedConsensus

open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs
open TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ExecutableConsensus
open TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ExecutableConsensus.Fixtures

universe u v w x

variable {FinalUnit : Type u} {Model : Type u} {Output : Type v}
variable {Occurrence : Type w} {Label : Type x}

/-- The projected result of a whole model, viewed as a single-coordinate state. -/
abbrev ResultState (Output : Type v) := Fin 1 → Option Output

/-- Image of the model set under a total projection.  Equal projected results collapse to one
element; existence of an originating model is proved relative to the original input set. Only
`DecidableEq Output` is needed — the result type is deduplicated, not required to be finite. -/
def projectedStates [DecidableEq Output] (models : Finset Model)
    (projection : Model → Option Output) : Finset (ResultState Output) :=
  models.image fun model (_ : Fin 1) => projection model

/-- Independent projected-consensus specification, stated over the *original* models and never over
the synthetic `Fin 1` image.  Determination requires a nonempty model set, so it is never vacuously
true. -/
def ClassifiesProjection (models : Finset Model) (projection : Model → Option Output) :
    Status Output → Prop
  | .inconsistent => models = ∅
  | .ambiguous => models.Nonempty ∧ ¬ ∃ value, ∀ model ∈ models, projection model = value
  | .determined value => models.Nonempty ∧ ∀ model ∈ models, projection model = value



def computeProjection [DecidableEq Output] (models : Finset Model)
    (projection : Model → Option Output) : Status Output :=
  compute (projectedStates models projection) 0

theorem projectedStates_nonempty_iff [DecidableEq Output] (models : Finset Model)
    (projection : Model → Option Output) :
    (projectedStates models projection).Nonempty ↔ models.Nonempty := by
  constructor
  · rintro ⟨state, hstate⟩
    simp only [projectedStates, Finset.mem_image] at hstate
    obtain ⟨model, hmodel, _⟩ := hstate
    exact ⟨model, hmodel⟩
  · rintro ⟨model, hmodel⟩
    refine ⟨fun _ => projection model, ?_⟩
    simp only [projectedStates, Finset.mem_image]
    exact ⟨model, hmodel, rfl⟩

theorem projectedStates_eq_empty_iff [DecidableEq Output] (models : Finset Model)
    (projection : Model → Option Output) :
    projectedStates models projection = ∅ ↔ models = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact not_congr (projectedStates_nonempty_iff models projection)

/-- Agreement of the projection image at coordinate `0` is exactly agreement of `projection` over
every *original* model. -/
theorem agree_projected_iff [DecidableEq Output] (models : Finset Model)
    (projection : Model → Option Output) (value : Option Output) :
    Agree (projectedStates models projection) 0 value ↔
      ∀ model ∈ models, projection model = value := by
  constructor
  · intro agree model hmodel
    exact agree (fun _ : Fin 1 => projection model) (by
      simp only [projectedStates, Finset.mem_image]
      exact ⟨model, hmodel, rfl⟩)
  · intro agree state hstate
    simp only [projectedStates, Finset.mem_image] at hstate
    obtain ⟨model, hmodel, hEq⟩ := hstate
    rw [← hEq]
    exact agree model hmodel

/-- Originating-model existence: every projected result in the image is produced by an original model, and
its value is that model's projection. The image and returned status do not store model IDs. -/
theorem mem_projectedStates_exists_model [DecidableEq Output] (models : Finset Model)
    (projection : Model → Option Output) (state : ResultState Output)
    (hstate : state ∈ projectedStates models projection) :
    ∃ model ∈ models, projection model = state 0 := by
  simp only [projectedStates, Finset.mem_image] at hstate
  obtain ⟨model, hmodel, hEq⟩ := hstate
  exact ⟨model, hmodel, congrFun hEq 0⟩

theorem classifies_iff_classifiesProjection [DecidableEq Output] (models : Finset Model)
    (projection : Model → Option Output) (status : Status Output) :
    Classifies (projectedStates models projection) 0 status ↔
      ClassifiesProjection models projection status := by
  cases status with
  | inconsistent =>
      change projectedStates models projection = ∅ ↔ models = ∅
      exact projectedStates_eq_empty_iff models projection
  | ambiguous =>
      change ((projectedStates models projection).Nonempty ∧
          ¬ ∃ value, Agree (projectedStates models projection) 0 value) ↔
        (models.Nonempty ∧ ¬ ∃ value, ∀ model ∈ models, projection model = value)
      exact and_congr (projectedStates_nonempty_iff models projection)
        (not_congr (exists_congr (fun value => agree_projected_iff models projection value)))
  | determined value =>
      change ((projectedStates models projection).Nonempty ∧
          Agree (projectedStates models projection) 0 value) ↔
        (models.Nonempty ∧ ∀ model ∈ models, projection model = value)
      exact and_congr (projectedStates_nonempty_iff models projection)
        (agree_projected_iff models projection value)

/-- **Main classification theorem.**  The computed projected status is exactly the independent
specification, for an arbitrary model type and only a `DecidableEq` on the output. -/
theorem computeProjection_eq_iff [DecidableEq Output] (models : Finset Model)
    (projection : Model → Option Output) (status : Status Output) :
    computeProjection models projection = status ↔
      ClassifiesProjection models projection status :=
  (compute_eq_iff (projectedStates models projection) (0 : Fin 1) status).trans
    (classifies_iff_classifiesProjection models projection status)

/-- **Wrapper over the exhaustive enumerator.**  On the finite models of an occurrence system, the
projected consensus is determined exactly when a declarative model exists and every one of them
projects to the value.  The independent `DerivationStepCorrespondence` is retained, so the bridge to
`CIPModel` is a supplied obligation rather than definitional equality. -/
theorem computeProjection_fixedModels_determined_iff
    [Fintype Occurrence] [DecidableEq Occurrence] [Fintype Label] [DecidableEq Label]
    [DecidableEq Output]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (projection : CompleteState Occurrence Label → Option Output) (value : Option Output) :
    computeProjection (fixedModels system) projection = .determined value ↔
      (∃ state, system.CIPModel state) ∧
        (∀ state, system.CIPModel state → projection state = value) := by
  rw [computeProjection_eq_iff]
  change (fixedModels system).Nonempty ∧
      (∀ state ∈ fixedModels system, projection state = value) ↔
    (∃ state, system.CIPModel state) ∧
      (∀ state, system.CIPModel state → projection state = value)
  refine and_congr (fixedModels_nonempty_iff_exists_cipModel system correspondence) ?_
  constructor
  · intro agree state model
    exact agree state ((mem_fixedModels_iff_cipModel system correspondence state).mpr model)
  · intro agree state member
    exact agree state ((mem_fixedModels_iff_cipModel system correspondence state).mp member)

/-- The projected consensus is inconsistent exactly when the system has no declarative model. -/
theorem computeProjection_fixedModels_inconsistent_iff
    [Fintype Occurrence] [DecidableEq Occurrence] [Fintype Label] [DecidableEq Label]
    [DecidableEq Output]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (projection : CompleteState Occurrence Label → Option Output) :
    computeProjection (fixedModels system) projection = .inconsistent ↔
      ¬ ∃ state, system.CIPModel state := by
  rw [computeProjection_eq_iff]
  change fixedModels system = ∅ ↔ ¬ ∃ state, system.CIPModel state
  exact (Finset.not_nonempty_iff_eq_empty).symm.trans
    (not_congr (fixedModels_nonempty_iff_exists_cipModel system correspondence))

/-- The projected consensus is ambiguous exactly when a declarative model exists but the models do
not share a common projected value. -/
theorem computeProjection_fixedModels_ambiguous_iff
    [Fintype Occurrence] [DecidableEq Occurrence] [Fintype Label] [DecidableEq Label]
    [DecidableEq Output]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (projection : CompleteState Occurrence Label → Option Output) :
    computeProjection (fixedModels system) projection = .ambiguous ↔
      (∃ state, system.CIPModel state) ∧
        (¬ ∃ value, ∀ state, system.CIPModel state → projection state = value) := by
  rw [computeProjection_eq_iff]
  change ((fixedModels system).Nonempty ∧
      (¬ ∃ value, ∀ state ∈ fixedModels system, projection state = value)) ↔
    (∃ state, system.CIPModel state) ∧
      (¬ ∃ value, ∀ state, system.CIPModel state → projection state = value)
  refine and_congr (fixedModels_nonempty_iff_exists_cipModel system correspondence) ?_
  apply not_congr
  constructor
  · rintro ⟨value, agree⟩
    exact ⟨value, fun state model =>
      agree state ((mem_fixedModels_iff_cipModel system correspondence state).mpr model)⟩
  · rintro ⟨value, agree⟩
    exact ⟨value, fun state member =>
      agree state ((mem_fixedModels_iff_cipModel system correspondence state).mp member)⟩

/-- A coordinate projection is a special case of a total projection: the specification agrees with
the coordinate `Classifies`. -/
theorem classifies_coordinate_iff (models : Finset (CompleteState Occurrence Label))
    (occ : Occurrence) (status : Status Label) :
    Classifies models occ status ↔
      ClassifiesProjection models (fun state => state occ) status := by
  cases status with
  | inconsistent => exact Iff.rfl
  | ambiguous =>
      change (models.Nonempty ∧ ¬ ∃ value, ∀ state ∈ models, state occ = value) ↔
        (models.Nonempty ∧ ¬ ∃ value, ∀ state ∈ models, state occ = value)
      exact Iff.rfl
  | determined value =>
      change (models.Nonempty ∧ ∀ state ∈ models, state occ = value) ↔
        (models.Nonempty ∧ ∀ state ∈ models, state occ = value)
      exact Iff.rfl

/-- **Algorithm reuse check.**  Projecting a single coordinate reproduces the existing coordinate
consensus exactly. -/
theorem computeProjection_coordinate_eq_compute [Fintype Occurrence] [DecidableEq Label]
    (models : Finset (CompleteState Occurrence Label)) (occ : Occurrence) :
    computeProjection models (fun state => state occ) = compute models occ :=
  (computeProjection_eq_iff models (fun state => state occ) (compute models occ)).mpr
    ((classifies_coordinate_iff models occ (compute models occ)).mp
      (compute_classifies models occ))

namespace Fixtures

/-- Whole-state projection: the projected final result is `some true` exactly when the two
coordinates `B = 1` and `C = 2` carry the same stored optional value.  It reads the *entire* state,
not a single coordinate. -/
def bEqualsCProjection : CompleteState (Fin 3) Bool → Option Bool :=
  fun state => some (decide (state 1 = state 2))

/-- Both global models of the copy cycle agree on the whole-state result, so the projected
consensus is determined. -/
theorem copy_cycle_projection_determined :
    computeProjection (fixedModels (cycleSystem false)) bEqualsCProjection =
      .determined (some true) := by
  decide +kernel

/-- The whole-state result is determined even though the individual coordinates `B` and `C` remain
ambiguous.  This is the point of projecting the whole model rather than a coordinate. -/
theorem copy_cycle_whole_state_determined_despite_coordinate_ambiguity :
    computeProjection (fixedModels (cycleSystem false)) bEqualsCProjection =
        .determined (some true) ∧
      compute (fixedModels (cycleSystem false)) 1 = .ambiguous ∧
      compute (fixedModels (cycleSystem false)) 2 = .ambiguous := by
  decide +kernel

/-- Deduplication: two distinct models collapse to a single projected result. -/
theorem copy_cycle_projection_collapses_card :
    (projectedStates (fixedModels (cycleSystem false)) bEqualsCProjection).card = 1 ∧
      (fixedModels (cycleSystem false)).card = 2 := by
  decide +kernel

/-- The empty negation cycle has no projected result and computes to `inconsistent`. -/
theorem negation_cycle_projection_inconsistent :
    computeProjection (fixedModels (cycleSystem true)) bEqualsCProjection = .inconsistent := by
  decide +kernel

/-- Nonvacuity: `inconsistent` here really means the original model set is empty, not a vacuous
"all models agree" statement. -/
theorem negation_cycle_projection_nonvacuous :
    ClassifiesProjection (fixedModels (cycleSystem true)) bEqualsCProjection Status.inconsistent :=
  (computeProjection_eq_iff (fixedModels (cycleSystem true)) bEqualsCProjection
      Status.inconsistent).mp
    negation_cycle_projection_inconsistent

/-- Determined absence is preserved: the single model storing `none` projects to `determined none`,
never to `inconsistent`. -/
theorem absent_projection_determined_none :
    computeProjection (fixedModels absentSystem) (fun state => state 0) = .determined none := by
  decide +kernel

/-- Closed check of `computeProjection_coordinate_eq_compute` on the copy cycle. -/
theorem copy_cycle_coordinate_projection_agrees :
    computeProjection (fixedModels (cycleSystem false)) (fun state => state 0) =
      compute (fixedModels (cycleSystem false)) 0 := by
  decide +kernel

end Fixtures

end TetraStereo.UniversalProof.ProjectedCompleteModelConsensusProofs.ProjectedConsensus
