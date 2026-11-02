import TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.FiniteCyclicOccurrenceExecutableConsensusFixtures

set_option autoImplicit false

/-!
# Exact finite models of dependency-closed occurrence blocks

This is solver infrastructure, not a molecular admission or revised-CIP rule theorem. The
independent evaluator locality, dependency closure, and declarative correspondence obligations
remain explicit. No strongly connected component discovery algorithm is asserted here.

`blockModels` enumerates functions on the actual block subtype, not complete environments with
arbitrary outside coordinates. A candidate restriction is extended by `none` only to run the
supplied evaluator. Locality and closure prove that this outside choice cannot affect fixedness.
Consequently there is no artificial multiplication of a block's model count by outside labels.

The global consistency theorem requires *every* block to be consistent. A determined coordinate
in one consistent block must never be reported as globally determined while another block has no
model. The closed finite negation-loop regression exhibits precisely this failure mode.
-/

namespace TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ClosedBlocks

open TetraStereo.OneCenter.DeclarativeCIP

universe u v w x

variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w} {Block : Type x}

/-- Each declared dependency stays within its target's block. -/
def DependencyClosed (dependency : Occurrence → Occurrence → Prop)
    (blockOf : Occurrence → Block) : Prop :=
  ∀ source target, dependency source target → blockOf source = blockOf target

/-- The evaluator equation holds at every occurrence belonging to one block. -/
def IsFixedOnBlock (system : OccurrenceSystem FinalUnit Occurrence Label)
    (blockOf : Occurrence → Block) (state : CompleteState Occurrence Label) (block : Block) : Prop :=
  ∀ occurrence, blockOf occurrence = block →
    system.executableStep state occurrence = state occurrence

/-- Locality and closure make the evaluator independent of outside coordinates. -/
theorem executableStep_eq_of_agree_on_block
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf)
    {left right : CompleteState Occurrence Label} {target : Occurrence}
    (agree : ∀ source, blockOf source = blockOf target → left source = right source) :
    system.executableStep left target = system.executableStep right target :=
  locality left right target fun source depends => agree source (closed source target depends)

theorem isFixedOnBlock_congr (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf)
    {left right : CompleteState Occurrence Label} {block : Block}
    (agree : ∀ occurrence, blockOf occurrence = block → left occurrence = right occurrence) :
    IsFixedOnBlock system blockOf left block ↔ IsFixedOnBlock system blockOf right block := by
  have stepEq : ∀ occurrence, blockOf occurrence = block →
      system.executableStep left occurrence = system.executableStep right occurrence :=
    fun occurrence belongs => executableStep_eq_of_agree_on_block
      system dependency blockOf locality closed
      (fun source same => agree source (same.trans belongs))
  constructor
  · intro fixed occurrence belongs
    exact (stepEq occurrence belongs).symm.trans
      ((fixed occurrence belongs).trans (agree occurrence belongs))
  · intro fixed occurrence belongs
    exact (stepEq occurrence belongs).trans
      ((fixed occurrence belongs).trans (agree occurrence belongs).symm)

theorem regenerates_iff_fixedOnAllBlocks (system : OccurrenceSystem FinalUnit Occurrence Label)
    (blockOf : Occurrence → Block) (state : CompleteState Occurrence Label) :
    system.Regenerates state state ↔ ∀ block, IsFixedOnBlock system blockOf state block := by
  constructor
  · intro fixed block occurrence _
    exact fixed occurrence
  · intro fixed occurrence
    exact fixed (blockOf occurrence) occurrence rfl

/-- Read each coordinate from the candidate supplied for its own block. -/
def assemble (blockOf : Occurrence → Block)
    (candidates : Block → CompleteState Occurrence Label) : CompleteState Occurrence Label :=
  fun occurrence => candidates (blockOf occurrence) occurrence

/-- Constructive product reconstruction from a supplied family of block witnesses. -/
theorem assemble_regenerates (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf)
    (candidates : Block → CompleteState Occurrence Label)
    (fixed : ∀ block, IsFixedOnBlock system blockOf (candidates block) block) :
    system.Regenerates (assemble blockOf candidates) (assemble blockOf candidates) := by
  intro occurrence
  have sameStep : system.executableStep (assemble blockOf candidates) occurrence =
      system.executableStep (candidates (blockOf occurrence)) occurrence :=
    executableStep_eq_of_agree_on_block system dependency blockOf locality closed
      (fun source same => by simp only [assemble, same])
  exact sameStep.trans (fixed (blockOf occurrence) occurrence rfl)

/-- Existence, rather than an algorithm selecting witnesses: classical choice occurs only in the
proof of this proposition. `blockModels` below is fully executable without choice. -/
theorem exists_regenerates_iff_blocks_consistent
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf) :
    (∃ state, system.Regenerates state state) ↔
      ∀ block, ∃ state, IsFixedOnBlock system blockOf state block := by
  constructor
  · rintro ⟨state, fixed⟩ block
    exact ⟨state, fun occurrence _ => fixed occurrence⟩
  · intro consistent
    classical
    let candidates : Block → CompleteState Occurrence Label :=
      fun block => Classical.choose (consistent block)
    exact ⟨assemble blockOf candidates,
      assemble_regenerates system dependency blockOf locality closed candidates
        (fun block => Classical.choose_spec (consistent block))⟩

theorem not_exists_regenerates_of_block_inconsistent
    (system : OccurrenceSystem FinalUnit Occurrence Label) (blockOf : Occurrence → Block)
    (block : Block) (inconsistent : ¬ ∃ state, IsFixedOnBlock system blockOf state block) :
    ¬ ∃ state, system.Regenerates state state := by
  rintro ⟨state, fixed⟩
  exact inconsistent ⟨state, fun occurrence _ => fixed occurrence⟩

/-! ## Executable enumeration of genuine block restrictions -/

abbrev BlockState (blockOf : Occurrence → Block) (block : Block) (Label : Type w) :=
  { occurrence : Occurrence // blockOf occurrence = block } → Option Label

def restrictToBlock (blockOf : Occurrence → Block) (block : Block)
    (state : CompleteState Occurrence Label) : BlockState blockOf block Label :=
  fun occurrence => state occurrence.val

section DecidableBlocks

variable [DecidableEq Block]

/-- The `none` outside values are an evaluation aid; they are not part of a block model. -/
def extendBlock (blockOf : Occurrence → Block) (block : Block)
    (restriction : BlockState blockOf block Label) : CompleteState Occurrence Label :=
  fun occurrence => if belongs : blockOf occurrence = block then restriction ⟨occurrence, belongs⟩
    else none

@[simp] theorem extendBlock_at (blockOf : Occurrence → Block) (block : Block)
    (restriction : BlockState blockOf block Label)
    (occurrence : { occurrence : Occurrence // blockOf occurrence = block }) :
    extendBlock blockOf block restriction occurrence.val = restriction occurrence := by
  simp [extendBlock, occurrence.property]

@[simp] theorem restrict_extendBlock (blockOf : Occurrence → Block) (block : Block)
    (restriction : BlockState blockOf block Label) :
    restrictToBlock blockOf block (extendBlock blockOf block restriction) = restriction := by
  funext occurrence
  exact extendBlock_at blockOf block restriction occurrence

theorem extend_restrict_fixedOnBlock_iff
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf)
    (state : CompleteState Occurrence Label) (block : Block) :
    IsFixedOnBlock system blockOf
        (extendBlock blockOf block (restrictToBlock blockOf block state)) block ↔
      IsFixedOnBlock system blockOf state block := by
  apply isFixedOnBlock_congr system dependency blockOf locality closed
  intro occurrence belongs
  simp [extendBlock, restrictToBlock, belongs]

variable [Fintype Occurrence] [DecidableEq Occurrence] [Fintype Label] [DecidableEq Label]

/-- Exhaustive finite block restrictions satisfying the evaluator equations on that block. -/
def blockModels (system : OccurrenceSystem FinalUnit Occurrence Label)
    (blockOf : Occurrence → Block) (block : Block) : Finset (BlockState blockOf block Label) :=
  Finset.univ.filter fun restriction =>
    ∀ occurrence : { occurrence : Occurrence // blockOf occurrence = block },
      system.executableStep (extendBlock blockOf block restriction) occurrence.val =
        restriction occurrence

theorem mem_blockModels_iff (system : OccurrenceSystem FinalUnit Occurrence Label)
    (blockOf : Occurrence → Block) (block : Block) (restriction : BlockState blockOf block Label) :
    restriction ∈ blockModels system blockOf block ↔
      IsFixedOnBlock system blockOf (extendBlock blockOf block restriction) block := by
  simp only [blockModels, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro fixed occurrence belongs
    simpa [extendBlock, belongs] using fixed ⟨occurrence, belongs⟩
  · intro fixed occurrence
    simpa only [extendBlock_at] using fixed occurrence.val occurrence.property

theorem restrict_mem_blockModels_iff
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf)
    (state : CompleteState Occurrence Label) (block : Block) :
    restrictToBlock blockOf block state ∈ blockModels system blockOf block ↔
      IsFixedOnBlock system blockOf state block :=
  (mem_blockModels_iff system blockOf block _).trans
    (extend_restrict_fixedOnBlock_iff system dependency blockOf locality closed state block)

theorem blockModels_nonempty_iff
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf) (block : Block) :
    (blockModels system blockOf block).Nonempty ↔
      ∃ state, IsFixedOnBlock system blockOf state block := by
  constructor
  · rintro ⟨restriction, member⟩
    exact ⟨extendBlock blockOf block restriction,
      (mem_blockModels_iff system blockOf block restriction).mp member⟩
  · rintro ⟨state, fixed⟩
    exact ⟨restrictToBlock blockOf block state,
      (restrict_mem_blockModels_iff system dependency blockOf locality closed state block).mpr fixed⟩

/-- The complete finite model enumeration is nonempty exactly when every closed block's own
finite restriction enumeration is nonempty. No global or local uniqueness is required. -/
theorem fixedModels_nonempty_iff_all_blockModels_nonempty
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf) :
    (fixedModels system).Nonempty ↔ ∀ block, (blockModels system blockOf block).Nonempty := by
  have global : (fixedModels system).Nonempty ↔ ∃ state, system.Regenerates state state := by
    constructor
    · rintro ⟨state, member⟩
      exact ⟨state, (system.regenerates_iff_executableStateStep_eq state state).mpr
        ((mem_fixedModels_iff system state).mp member)⟩
    · rintro ⟨state, fixed⟩
      exact ⟨state, (mem_fixedModels_iff system state).mpr
        ((system.regenerates_iff_executableStateStep_eq state state).mp fixed)⟩
  rw [global, exists_regenerates_iff_blocks_consistent system dependency blockOf locality closed]
  constructor
  · intro consistent block
    exact (blockModels_nonempty_iff system dependency blockOf locality closed block).mpr
      (consistent block)
  · intro consistent block
    exact (blockModels_nonempty_iff system dependency blockOf locality closed block).mp
      (consistent block)

/-- The independent declarative model bridge keeps its correspondence gate explicit. -/
theorem exists_cipModel_iff_all_blockModels_nonempty
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf) :
    (∃ state, system.CIPModel state) ↔ ∀ block, (blockModels system blockOf block).Nonempty :=
  (fixedModels_nonempty_iff_exists_cipModel system correspondence).symm.trans
    (fixedModels_nonempty_iff_all_blockModels_nonempty system dependency blockOf locality closed)

/-- Decide global consistency using only the finite block enumerations. This function never
constructs or filters the global function space. Its correctness requires closure and locality. -/
def allBlocksConsistent? [Fintype Block]
    (system : OccurrenceSystem FinalUnit Occurrence Label) (blockOf : Occurrence → Block) : Bool :=
  decide (∀ block, (blockModels system blockOf block).Nonempty)

theorem allBlocksConsistent?_eq_true_iff [Fintype Block]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf) :
    allBlocksConsistent? system blockOf = true ↔ (fixedModels system).Nonempty := by
  simp only [allBlocksConsistent?, decide_eq_true_eq]
  exact (fixedModels_nonempty_iff_all_blockModels_nonempty
    system dependency blockOf locality closed).symm

theorem allBlocksConsistent?_eq_true_iff_exists_cipModel [Fintype Block]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (correspondence : system.DerivationStepCorrespondence)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency)
    (closed : DependencyClosed dependency blockOf) :
    allBlocksConsistent? system blockOf = true ↔ ∃ state, system.CIPModel state :=
  (allBlocksConsistent?_eq_true_iff system dependency blockOf locality closed).trans
    (fixedModels_nonempty_iff_exists_cipModel system correspondence)

end DecidableBlocks

/-! ## Closed finite cycle regressions, without chemical interpretation -/

namespace Fixtures

open ExecutableConsensus.Fixtures

/-- The actual independent partition: A is alone; B and C share the other block. -/
def cycleBlockOf (occurrence : Fin 3) : Bool := decide (occurrence ≠ 0)

/-- Exactly the declared copy/negation-loop dependencies: C→B and B→C. -/
def cycleDependency (source target : Fin 3) : Prop :=
  (source = 2 ∧ target = 1) ∨ (source = 1 ∧ target = 2)

theorem cycle_locality (negated : Bool) :
    (cycleSystem negated).EvaluatorLocalFor cycleDependency := by
  intro left right target agree
  by_cases zero : target = 0
  · simp [cycleSystem, zero]
  · by_cases one : target = 1
    · have same : left 2 = right 2 := agree 2 (Or.inl ⟨rfl, one⟩)
      simp [cycleSystem, one, same]
    · have two : target = 2 := by omega
      have same : left 1 = right 1 := agree 1 (Or.inr ⟨rfl, two⟩)
      simp [cycleSystem, zero, one, same]

theorem cycle_closed : DependencyClosed cycleDependency cycleBlockOf := by
  intro source target depends
  rcases depends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- No outside-state multiplication: the A block has one restriction model, not nine complete
states with arbitrary B/C coordinates. -/
theorem negation_Ablock_exactly_one :
    (blockModels (cycleSystem true) cycleBlockOf false).card = 1 := by decide +kernel

theorem negation_Ablock_nonempty :
    (blockModels (cycleSystem true) cycleBlockOf false).Nonempty := by decide +kernel

theorem negation_BCblock_empty : blockModels (cycleSystem true) cycleBlockOf true = ∅ := by
  decide +kernel

theorem copy_Ablock_exactly_one :
    (blockModels (cycleSystem false) cycleBlockOf false).card = 1 := by decide +kernel

theorem copy_BCblock_exactly_two :
    (blockModels (cycleSystem false) cycleBlockOf true).card = 2 := by decide +kernel

/-- The A block really has a fixed complete-state witness, yet no global model exists. -/
theorem closed_Ablock_consistent_but_global_inconsistent :
    (∃ state, IsFixedOnBlock (cycleSystem true) cycleBlockOf state false) ∧
      ¬ ∃ state, (cycleSystem true).CIPModel state :=
  ⟨(blockModels_nonempty_iff (cycleSystem true) cycleDependency cycleBlockOf
      (cycle_locality true) cycle_closed false).mp negation_Ablock_nonempty,
    negation_cycle_no_declarative_model⟩

/-- Global inconsistency follows from the actual closed BC block, through product reconstruction. -/
theorem negation_global_empty_from_closed_block : fixedModels (cycleSystem true) = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro nonempty
  have blockNonempty :=
    (fixedModels_nonempty_iff_all_blockModels_nonempty (cycleSystem true) cycleDependency
      cycleBlockOf (cycle_locality true) cycle_closed).mp nonempty true
  rw [negation_BCblock_empty] at blockNonempty
  exact Finset.not_nonempty_empty blockNonempty

/-- Even A remains globally inconsistent: its locally forced label cannot override an empty
closed block elsewhere in the system. -/
theorem negation_no_vacuous_global_determination :
    ExecutableConsensus.compute (fixedModels (cycleSystem true)) 0 = .inconsistent := by
  rw [negation_global_empty_from_closed_block]
  simp [ExecutableConsensus.compute]

/-- Actual component-only decisions: no global candidate enumeration is called here. -/
theorem copy_blocks_consistency_computed :
    allBlocksConsistent? (cycleSystem false) cycleBlockOf = true := by decide +kernel

theorem negation_blocks_consistency_computed :
    allBlocksConsistent? (cycleSystem true) cycleBlockOf = false := by decide +kernel

end Fixtures

end TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ClosedBlocks
