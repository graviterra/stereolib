import TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.FiniteCyclicOccurrenceModels
import Mathlib.Data.Finset.Fold

set_option autoImplicit false

/-!
# Executable, nonvacuous consensus over all complete occurrence models

The fold examines every complete model and preserves the distinction between no model,
model disagreement, and agreement on an optional value (including `none`). The specification
quantifies over models independently of the fold. Production chemical correspondence and
source approval remain explicit obligations; this is finite generic solver infrastructure.
-/

namespace TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ExecutableConsensus

open TetraStereo.OneCenter.DeclarativeCIP

universe u v w
variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

inductive Status (Label : Type w) where
  | inconsistent
  | ambiguous
  | determined (value : Option Label)
  deriving DecidableEq, Repr

/-- Empty input is neutral, disagreement absorbs, and equal determined values agree. -/
def join [DecidableEq Label] : Status Label → Status Label → Status Label
  | .inconsistent, right => right
  | left, .inconsistent => left
  | .ambiguous, _ => .ambiguous
  | _, .ambiguous => .ambiguous
  | .determined left, .determined right =>
      if left = right then .determined left else .ambiguous

theorem join_comm [DecidableEq Label] (left right : Status Label) :
    join left right = join right left := by
  cases left <;> cases right <;> simp [join]
  split_ifs <;> simp_all

theorem join_assoc [DecidableEq Label] (a b c : Status Label) :
    join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> simp only [join] <;>
    split_ifs <;> simp_all only [ite_true, ite_false]

instance [DecidableEq Label] : Std.Commutative (join (Label := Label)) := ⟨join_comm⟩
instance [DecidableEq Label] : Std.Associative (join (Label := Label)) := ⟨join_assoc⟩

/-- Independent universal agreement specification. -/
def Agree (models : Finset (CompleteState Occurrence Label)) (occ : Occurrence)
    (value : Option Label) : Prop :=
  ∀ state ∈ models, state occ = value

/-- Determination requires a nonempty set; agreement alone would be vacuous on the empty set. -/
def Classifies (models : Finset (CompleteState Occurrence Label)) (occ : Occurrence) :
    Status Label → Prop
  | .inconsistent => models = ∅
  | .ambiguous => models.Nonempty ∧ ¬ ∃ value, Agree models occ value
  | .determined value => models.Nonempty ∧ Agree models occ value

/-- Computable fold; no chosen first model and no classical decision procedure. -/
def compute [DecidableEq Label] (models : Finset (CompleteState Occurrence Label))
    (occ : Occurrence) : Status Label :=
  models.fold join .inconsistent fun state => .determined (state occ)

theorem classifies_insert [DecidableEq Label] [DecidableEq (CompleteState Occurrence Label)]
    (models : Finset (CompleteState Occurrence Label)) (occ : Occurrence)
    (state : CompleteState Occurrence Label) (status : Status Label)
    (h : Classifies models occ status) :
    Classifies (insert state models) occ (join (.determined (state occ)) status) := by
  cases status with
  | inconsistent =>
      have empty : models = ∅ := h
      subst models
      simp [join, Classifies, Agree]
  | ambiguous =>
      change (insert state models).Nonempty ∧ ¬ ∃ value, Agree (insert state models) occ value
      refine ⟨⟨state, Finset.mem_insert_self _ _⟩, ?_⟩
      rintro ⟨value, agree⟩
      exact h.2 ⟨value, fun other member => agree other (Finset.mem_insert_of_mem member)⟩
  | determined value =>
      by_cases eqv : state occ = value
      · simp only [join, eqv, if_pos]
        refine ⟨⟨state, Finset.mem_insert_self _ _⟩, ?_⟩
        intro other member
        rcases Finset.mem_insert.mp member with rfl | member
        · exact eqv
        · exact h.2 other member
      · simp only [join, if_neg eqv]
        refine ⟨⟨state, Finset.mem_insert_self _ _⟩, ?_⟩
        rintro ⟨otherValue, agree⟩
        obtain ⟨old, oldMem⟩ := h.1
        have oldEq := h.2 old oldMem
        have oldNew := agree old (Finset.mem_insert_of_mem oldMem)
        have newEq := agree state (Finset.mem_insert_self _ _)
        exact eqv (newEq.trans (oldNew.symm.trans oldEq))

theorem compute_classifies [Fintype Occurrence] [DecidableEq Label]
    (models : Finset (CompleteState Occurrence Label)) (occ : Occurrence) :
    Classifies models occ (compute models occ) := by
  induction models using Finset.induction_on with
  | empty => simp [compute, Classifies]
  | @insert state models notMem ih =>
      have step := classifies_insert models occ state (compute models occ) ih
      simpa only [compute, Finset.fold_insert notMem] using step

theorem classifies_unique (models : Finset (CompleteState Occurrence Label))
    (occ : Occurrence) {left right : Status Label}
    (hl : Classifies models occ left) (hr : Classifies models occ right) : left = right := by
  cases left <;> cases right
  · rfl
  · exact False.elim (Finset.nonempty_iff_ne_empty.mp hr.1 hl)
  · exact False.elim (Finset.nonempty_iff_ne_empty.mp hr.1 hl)
  · exact False.elim (Finset.nonempty_iff_ne_empty.mp hl.1 hr)
  · rfl
  · exact False.elim (hl.2 ⟨_, hr.2⟩)
  · exact False.elim (Finset.nonempty_iff_ne_empty.mp hl.1 hr)
  · exact False.elim (hr.2 ⟨_, hl.2⟩)
  · obtain ⟨state, member⟩ := hl.1
    exact congrArg Status.determined ((hl.2 state member).symm.trans (hr.2 state member))

theorem compute_eq_iff [Fintype Occurrence] [DecidableEq Label]
    (models : Finset (CompleteState Occurrence Label)) (occ : Occurrence) (status : Status Label) :
    compute models occ = status ↔ Classifies models occ status := by
  constructor
  · intro eqv
    rw [← eqv]
    exact compute_classifies models occ
  · exact classifies_unique models occ (compute_classifies models occ)

theorem compute_fixedModels_determined_iff [Fintype Occurrence] [DecidableEq Occurrence]
    [Fintype Label] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence) (occ : Occurrence)
    (value : Option Label) :
    compute (fixedModels system) occ = .determined value ↔
      (∃ state, system.CIPModel state) ∧ ∀ state, system.CIPModel state → state occ = value := by
  rw [compute_eq_iff]
  change (fixedModels system).Nonempty ∧ Agree (fixedModels system) occ value ↔ _
  refine and_congr (fixedModels_nonempty_iff_exists_cipModel system correspondence) ?_
  constructor
  · intro agree state model
    exact agree state ((mem_fixedModels_iff_cipModel system correspondence state).mpr model)
  · intro agree state member
    exact agree state ((mem_fixedModels_iff_cipModel system correspondence state).mp member)

theorem compute_fixedModels_inconsistent_iff [Fintype Occurrence] [DecidableEq Occurrence]
    [Fintype Label] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence) (occ : Occurrence) :
    compute (fixedModels system) occ = .inconsistent ↔ ¬ ∃ state, system.CIPModel state := by
  rw [compute_eq_iff]
  change fixedModels system = ∅ ↔ _
  exact (Finset.not_nonempty_iff_eq_empty).symm.trans
    (not_congr (fixedModels_nonempty_iff_exists_cipModel system correspondence))

theorem compute_fixedModels_ambiguous_iff [Fintype Occurrence] [DecidableEq Occurrence]
    [Fintype Label] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence) (occ : Occurrence) :
    compute (fixedModels system) occ = .ambiguous ↔
      (∃ state, system.CIPModel state) ∧
      ¬ ∃ value, ∀ state, system.CIPModel state → state occ = value := by
  rw [compute_eq_iff]
  change ((fixedModels system).Nonempty ∧ (¬ ∃ value, Agree (fixedModels system) occ value)) ↔
    ((∃ state, system.CIPModel state) ∧
      (¬ ∃ value, ∀ state, system.CIPModel state → state occ = value))
  refine and_congr (fixedModels_nonempty_iff_exists_cipModel system correspondence) ?_
  apply not_congr
  constructor
  · rintro ⟨value, agree⟩
    exact ⟨value, fun state model => agree state
      ((mem_fixedModels_iff_cipModel system correspondence state).mpr model)⟩
  · rintro ⟨value, agree⟩
    exact ⟨value, fun state member => agree state
      ((mem_fixedModels_iff_cipModel system correspondence state).mp member)⟩

end TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ExecutableConsensus
