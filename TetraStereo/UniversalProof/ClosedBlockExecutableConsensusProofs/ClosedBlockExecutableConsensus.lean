import TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.FiniteCyclicOccurrenceClosedBlocks
import TetraStereo.UniversalProof.ProjectedCompleteModelConsensusProofs.ProjectedCompleteModelConsensus

set_option autoImplicit false

















namespace TetraStereo.UniversalProof.ClosedBlockExecutableConsensusProofs.ClosedBlockExecutableConsensus

open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs
open TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ExecutableConsensus
open TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ClosedBlocks
open TetraStereo.UniversalProof.ProjectedCompleteModelConsensusProofs.ProjectedConsensus

universe u v w x
variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w} {Block : Type x}

section ClosedBlockConsensus
variable [DecidableEq Block] [Fintype Block] [Fintype Occurrence] [DecidableEq Occurrence]
  [Fintype Label] [DecidableEq Label]

/-- Block-local projection: read the target occurrence inside its own block restriction. -/
def targetProjection (blockOf : Occurrence → Block) (target : Occurrence) :
    BlockState blockOf (blockOf target) Label → Option Label :=
  fun restriction => restriction ⟨target, rfl⟩

/-- Projected consensus over the target block's own finite restriction models. -/
def localBlockConsensus (system : OccurrenceSystem FinalUnit Occurrence Label)
    (blockOf : Occurrence → Block) (target : Occurrence) : Status Label :=
  computeProjection (blockModels system blockOf (blockOf target)) (targetProjection blockOf target)

/-- Executable answer: the block-local result when every block has a genuine model, else
`inconsistent`. -/
def globallySafeStatus (system : OccurrenceSystem FinalUnit Occurrence Label)
    (blockOf : Occurrence → Block) (target : Occurrence) : Status Label :=
  if allBlocksConsistent? system blockOf = true then localBlockConsensus system blockOf target
  else Status.inconsistent
omit [Fintype Block] in
/-- A global fixed model restricts to a genuine model of the target block. -/
theorem restrict_target_mem_blockModels (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency) (closed : DependencyClosed dependency blockOf)
    (target : Occurrence) (state : CompleteState Occurrence Label) (hmem : state ∈ fixedModels system) :
    restrictToBlock blockOf (blockOf target) state ∈ blockModels system blockOf (blockOf target) := by
  have fixed : system.Regenerates state state :=
    (system.regenerates_iff_executableStateStep_eq state state).mpr
      ((mem_fixedModels_iff system state).mp hmem)
  exact (restrict_mem_blockModels_iff system dependency blockOf locality closed state
    (blockOf target)).mpr fun occurrence _ => fixed occurrence

/-- **Extension.** Every genuine target-block restriction extends to a global fixed model (classical
witnesses in the proof only; no algorithm selects them). -/
theorem exists_mem_fixedModels_restrict_eq (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency) (closed : DependencyClosed dependency blockOf)
    (blocks : allBlocksConsistent? system blockOf = true) (target : Occurrence)
    (restriction : BlockState blockOf (blockOf target) Label)
    (member : restriction ∈ blockModels system blockOf (blockOf target)) :
    ∃ state ∈ fixedModels system, restrictToBlock blockOf (blockOf target) state = restriction := by
  classical
  have allNonempty : ∀ block, (blockModels system blockOf block).Nonempty := of_decide_eq_true blocks
  let base : Block → CompleteState Occurrence Label := fun block =>
    Classical.choose ((blockModels_nonempty_iff system dependency blockOf locality closed block).mp
      (allNonempty block))
  let candidates : Block → CompleteState Occurrence Label := fun block =>
    if block = blockOf target then extendBlock blockOf (blockOf target) restriction else base block
  have candidates_fixed : ∀ block, IsFixedOnBlock system blockOf (candidates block) block := by
    intro block
    by_cases same : block = blockOf target
    · rw [same]
      rw [show candidates (blockOf target) = extendBlock blockOf (blockOf target) restriction by
        simp only [candidates, if_pos rfl]]
      exact (mem_blockModels_iff system blockOf (blockOf target) restriction).mp member
    · rw [show candidates block = base block by simp only [candidates, if_neg same]]
      exact Classical.choose_spec
        ((blockModels_nonempty_iff system dependency blockOf locality closed block).mp
          (allNonempty block))
  have restricts : restrictToBlock blockOf (blockOf target) (assemble blockOf candidates) =
      restriction := by
    funext occurrence
    have belongs : blockOf occurrence.val = blockOf target := occurrence.property
    show (if blockOf occurrence.val = blockOf target then
        extendBlock blockOf (blockOf target) restriction else base (blockOf occurrence.val))
          occurrence.val = restriction occurrence
    rw [if_pos belongs, extendBlock_at blockOf (blockOf target) restriction occurrence]
  refine ⟨assemble blockOf candidates, ?_, restricts⟩
  rw [mem_fixedModels_iff]
  exact (system.regenerates_iff_executableStateStep_eq _ _).mp
    (assemble_regenerates system dependency blockOf locality closed candidates candidates_fixed)

/-- **Attainable-value bridge**: global models realize exactly the target block's own values. -/
theorem target_value_attainable_iff (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency) (closed : DependencyClosed dependency blockOf)
    (blocks : allBlocksConsistent? system blockOf = true) (target : Occurrence) (value : Option Label) :
    (∃ state ∈ fixedModels system, state target = value) ↔
      (∃ restriction ∈ blockModels system blockOf (blockOf target),
        restriction ⟨target, rfl⟩ = value) := by
  constructor
  · rintro ⟨state, hmem, hvalue⟩
    refine ⟨restrictToBlock blockOf (blockOf target) state,
      restrict_target_mem_blockModels system dependency blockOf locality closed target state hmem, ?_⟩
    exact (show (restrictToBlock blockOf (blockOf target) state) ⟨target, rfl⟩ = state target
      from rfl).trans hvalue
  · rintro ⟨restriction, member, hvalue⟩
    obtain ⟨state, hmem, heq⟩ := exists_mem_fixedModels_restrict_eq system dependency blockOf
      locality closed blocks target restriction member
    exact ⟨state, hmem, (congrFun heq ⟨target, rfl⟩).trans hvalue⟩

/-- Agreement at the target is exactly agreement over the target block's restriction models. -/
theorem agree_iff (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency) (closed : DependencyClosed dependency blockOf)
    (blocks : allBlocksConsistent? system blockOf = true) (target : Occurrence) (value : Option Label) :
    (∀ state ∈ fixedModels system, state target = value) ↔
      (∀ restriction ∈ blockModels system blockOf (blockOf target),
        restriction ⟨target, rfl⟩ = value) := by
  constructor
  · intro agree restriction member
    obtain ⟨state, hmem, heq⟩ := exists_mem_fixedModels_restrict_eq system dependency blockOf
      locality closed blocks target restriction member
    have hvalue : restriction ⟨target, rfl⟩ = state target := by
      rw [← heq]
      rfl
    exact hvalue.trans (agree state hmem)
  · intro agree state hmem
    exact agree (restrictToBlock blockOf (blockOf target) state)
      (restrict_target_mem_blockModels system dependency blockOf locality closed target state hmem)

/-- The three outcomes agree between the global model set and the target block's restriction set,
including nonempty, determined-`none` and ambiguous. -/
theorem classifiesProjection_iff (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency) (closed : DependencyClosed dependency blockOf)
    (blocks : allBlocksConsistent? system blockOf = true) (target : Occurrence) (status : Status Label) :
    ClassifiesProjection (fixedModels system)
        (fun state : CompleteState Occurrence Label => state target) status ↔
      ClassifiesProjection (blockModels system blockOf (blockOf target))
        (targetProjection blockOf target) status := by
  have globalNonempty : (fixedModels system).Nonempty :=
    (allBlocksConsistent?_eq_true_iff system dependency blockOf locality closed).mp blocks
  have blockNonempty : (blockModels system blockOf (blockOf target)).Nonempty :=
    of_decide_eq_true blocks (blockOf target)
  have nonempty : (fixedModels system).Nonempty ↔
      (blockModels system blockOf (blockOf target)).Nonempty := iff_of_true globalNonempty blockNonempty
  cases status with
  | inconsistent =>
      simp only [ClassifiesProjection]
      rw [← Finset.not_nonempty_iff_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
      exact not_congr nonempty
  | ambiguous =>
      simp only [ClassifiesProjection, targetProjection]
      exact and_congr nonempty (not_congr (exists_congr fun value =>
        agree_iff system dependency blockOf locality closed blocks target value))
  | determined value =>
      simp only [ClassifiesProjection, targetProjection]
      exact and_congr nonempty
        (agree_iff system dependency blockOf locality closed blocks target value)

/-- **Local/global projected-consensus equality** when every block is consistent. -/
theorem computeProjection_fixedModels_eq_localBlockConsensus
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency) (closed : DependencyClosed dependency blockOf)
    (blocks : allBlocksConsistent? system blockOf = true) (target : Occurrence) :
    computeProjection (fixedModels system)
        (fun state : CompleteState Occurrence Label => state target) =
      localBlockConsensus system blockOf target :=
  (computeProjection_eq_iff (fixedModels system)
    (fun state : CompleteState Occurrence Label => state target)
    (localBlockConsensus system blockOf target)).mpr
    ((classifiesProjection_iff system dependency blockOf locality closed blocks target
      (localBlockConsensus system blockOf target)).mpr
      ((computeProjection_eq_iff (blockModels system blockOf (blockOf target))
        (targetProjection blockOf target)
        (localBlockConsensus system blockOf target)).mp rfl))

/-- **Executable answer equals global consensus**: `globallySafeStatus` is exactly
`ExecutableConsensus.compute (fixedModels system) target`. -/
theorem globallySafeStatus_eq_executableConsensus
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependency : Occurrence → Occurrence → Prop) (blockOf : Occurrence → Block)
    (locality : system.EvaluatorLocalFor dependency) (closed : DependencyClosed dependency blockOf)
    (target : Occurrence) :
    globallySafeStatus system blockOf target = compute (fixedModels system) target := by
  by_cases blocks : allBlocksConsistent? system blockOf = true
  · simp only [globallySafeStatus, if_pos blocks]
    rw [← computeProjection_fixedModels_eq_localBlockConsensus system dependency blockOf locality
      closed blocks target]
    exact computeProjection_coordinate_eq_compute (fixedModels system) target
  · have empty : fixedModels system = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro nonempty
      exact blocks ((allBlocksConsistent?_eq_true_iff system dependency blockOf locality closed).mpr
        nonempty)
    have status : compute (fixedModels system) target = Status.inconsistent :=
      (compute_eq_iff (fixedModels system) target Status.inconsistent).mpr empty
    simp only [globallySafeStatus, if_neg blocks]
    exact status.symm
end ClosedBlockConsensus
/-! ## Closed finite cycle regressions (no chemical interpretation) -/
namespace Fixtures
open TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ExecutableConsensus.Fixtures
open TetraStereo.UniversalProof.FiniteCyclicOccurrenceModelsProofs.ClosedBlocks.Fixtures
/-- Copy cycle: A is determined by its single A-block restriction; B is genuinely ambiguous. -/
theorem copy_local_classified :
    localBlockConsensus (cycleSystem false) cycleBlockOf 0 = .determined (some false) ∧
      localBlockConsensus (cycleSystem false) cycleBlockOf 1 = .ambiguous := by
  decide +kernel

/-- Copy cycle: the executable answer equals the global consensus at both targets. -/
theorem copy_local_equals_global :
    globallySafeStatus (cycleSystem false) cycleBlockOf 0 =
        compute (fixedModels (cycleSystem false)) 0 ∧
      globallySafeStatus (cycleSystem false) cycleBlockOf 1 =
        compute (fixedModels (cycleSystem false)) 1 := by
  decide +kernel

/-- Negation cycle: A is locally determined, but the empty BC block makes the answer `inconsistent`
(while still equal to the global consensus). -/
theorem negation_local_determined_but_global_inconsistent :
    localBlockConsensus (cycleSystem true) cycleBlockOf 0 = .determined (some false) ∧
      globallySafeStatus (cycleSystem true) cycleBlockOf 0 = .inconsistent ∧
      globallySafeStatus (cycleSystem true) cycleBlockOf 0 =
        compute (fixedModels (cycleSystem true)) 0 := by
  decide +kernel

/-- The closed BC block is literally empty; this is why the negation cycle refuses A. -/
theorem negation_BC_block_empty :
    blockModels (cycleSystem true) cycleBlockOf true = ∅ := by
  decide +kernel
end Fixtures

end TetraStereo.UniversalProof.ClosedBlockExecutableConsensusProofs.ClosedBlockExecutableConsensus
