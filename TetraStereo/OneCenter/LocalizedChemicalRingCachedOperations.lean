import TetraStereo.OneCenter.LocalizedChemicalRingRootSliceCache
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations
import TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

/-! Exact cached representation of the current rule-major sparse operations. The caller
passes an exact child reader backed by a materialized carrier or selected-root slice. The
original root-specific raw lookup, stage-specific comparisons, default marker layout,
sorting, promotion count and refusals are unchanged. No molecular-domain or success
assumptions are needed for the equalities. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations

open CertifiedLocalizedCIPInput
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedPromotedKey
open LocalizedMarkedRetainedSparsePromotedKey LocalizedMarkedRetainedSparsePromotedOperations
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedCarrierLookup (lookup?)

variable (input : CertifiedLocalizedCIPInput)
abbrev Occ := input.LocalizedCIPOccurrence (retainedCarrierFuel input)
abbrev Cursor := input.LocalizedRerootCursor (retainedCarrierFuel input)
abbrev Frame := input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input)
variable (cache : input.LocalizedRerootChildReader (retainedCarrierFuel input))

def cumulative (stage : LocalizedCumulativeRule45Stage)
    (read : Cursor input → Option LocalizedAuxiliaryLabel) :
    Nat → Cursor input → Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← cache.readChildren cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
      else none
  | fuel + 1, cursor => do
      let children ← cache.readChildren cursor
      if children = [] then
        some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
      else
        let keys ← children.mapM (cumulative stage read fuel)
        some (localizedCumulativeRule45StepKey input stage cursor (read cursor)
          (input.sortRuleMajorCumulativeKeys stage keys))

theorem cumulative_eq (stage : LocalizedCumulativeRule45Stage)
    (read : Cursor input → Option LocalizedAuxiliaryLabel) (fuel : Nat) :
    cumulative input cache stage read fuel = input.buildRuleMajorCumulativeWithReadExec? stage read fuel := by
  induction fuel with
  | zero =>
      funext cursor
      simp [cumulative, buildRuleMajorCumulativeWithReadExec?, cache.readChildren_eq]
  | succ fuel ih =>
      funext cursor
      simp [cumulative, buildRuleMajorCumulativeWithReadExec?, cache.readChildren_eq, ih]

def stageCompiler (target : Occ input) (view : input.LocalizedDependencyView target)
    (read : Cursor input → Option LocalizedAuxiliaryLabel) (fuel : Nat) :
    input.RuleMajorCompoundStageCompiler (retainedCarrierFuel input) :=
  fun stage cursor => match stage with
    | .rule4a => WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
        input cache.readChildren .rule4a target view fuel cursor
    | other => cumulative input cache other read fuel cursor

theorem stageCompiler_eq (target : Occ input) (view : input.LocalizedDependencyView target)
    (read : Cursor input → Option LocalizedAuxiliaryLabel) (fuel : Nat) :
    stageCompiler input cache target view read fuel =
      input.ruleMajorCompoundStageCompilerExec target view read fuel := by
  funext stage cursor
  cases stage <;> simp only [stageCompiler, ruleMajorCompoundStageCompilerExec, cumulative_eq,
    WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?_eq_original
      input cache.readChildren cache.readChildren_eq]

def compound (target : Occ input) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : Cursor input) : Option input.LocalizedRerootCompoundRule45Key :=
  input.buildRuleMajorCompoundRule45KeyWith?
    (stageCompiler input cache target view (input.localizedDependencyLabel target view) fuel) cursor

theorem compound_eq (target : Occ input) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : Cursor input) : compound input cache target view fuel cursor =
    input.buildActualRuleMajorCompoundRule45KeyExec? target view fuel cursor := by
  unfold compound buildActualRuleMajorCompoundRule45KeyExec? buildRuleMajorCompoundRule45KeyExec?
  rw [stageCompiler_eq]

def frame (target : Occ input) : Option (Frame input) :=
  WithChildren.localizedNoDoubleFourLigandFrameExec? input cache.readChildren target

theorem frame_eq (target : Occ input) :
    frame input cache target = input.localizedNoDoubleFourLigandFrameExec? target :=
  WithChildren.localizedNoDoubleFourLigandFrameExec?_eq_original input cache.readChildren
    cache.readChildren_eq target

def before (state : OccurrenceAuxState) (target : Occ input) (base : Frame input)
    (left right : Fin 4) : Option Ordering :=
  (do
    let budget := localizedOccurrenceRerootEvaluationFuel (retainedCarrierFuel input)
    let leftKey ← compound input cache target (rawStateView input state target) budget (base.cursorAt left)
    let rightKey ← compound input cache target (rawStateView input state target) budget (base.cursorAt right)
    some (localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))).map
    ConstitutionalDescriptorHierarchyComparison.ordering

theorem before_eq (state : OccurrenceAuxState) (target : Occ input) (base : Frame input) :
    before input cache state target base = rawStateBefore input state target base := by
  funext left right
  unfold before rawStateBefore compareRuleMajorOccurrenceExecAt?
  simp only [compound_eq]

def partition (state : OccurrenceAuxState) (target : Occ input) :
    Option (List (Fin 4) × List (Option Ordering)) := do
  let base ← frame input cache target
  let sorted ← sortBy? (before input cache state target base) (List.finRange 4)
  some (sorted, adjacentBy (before input cache state target base) sorted)

theorem partition_eq (state : OccurrenceAuxState) (target : Occ input) :
    partition input cache state target = ordinaryPartition? input state target := by
  unfold partition ordinaryPartition?
  simp only [frame_eq, before_eq]

def ordinary (mol : RawMolecule) (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    Option (List Nat × List (Option Ordering)) := do
  let target ← lookup? input node
  let atoms ← LocalizedGenericMarkedRecalculation.frameAtoms? mol node
  let base ← frame input cache target
  let ranked ← partition input cache state target
  let positions ← positions? input atoms base ranked.1
  some (positions, ranked.2)

theorem ordinary_eq (mol : RawMolecule) (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    ordinary input cache mol state node = (sparseOperations input mol).ordinary state node := by
  change ordinary input cache mol state node = LocalizedMarkedRetainedOperations.ordinary input mol state node
  unfold ordinary LocalizedMarkedRetainedOperations.ordinary
  simp only [frame_eq, partition_eq]

def markedKey (target : Occ input) (view : input.LocalizedDependencyView target)
    (reference : input.Atom) (W D : Nat) : Nat → Cursor input → Option (SparseKey input)
  | 0, cursor => do
      let prior ← compound input cache target view (2 * (retainedCarrierFuel input + 1)) cursor
      let children ← cache.readChildren cursor
      if children = [] then
        some ⟨prior, LocalizedPhysicalMarkedSparseMarker.assemble W D (referenceBit input reference cursor) []⟩
      else none
  | fuel + 1, cursor => do
      let prior ← compound input cache target view (2 * (retainedCarrierFuel input + 1)) cursor
      let children ← cache.readChildren cursor
      let keys ← children.mapM (markedKey target view reference W D fuel)
      some ⟨prior, LocalizedPhysicalMarkedSparseMarker.assemble W D (referenceBit input reference cursor)
        ((sortSparse input keys).map SparseKey.marker)⟩

theorem markedKey_eq (target : Occ input) (view : input.LocalizedDependencyView target)
    (reference : input.Atom) (W D fuel : Nat) : markedKey input cache target view reference W D fuel =
    sparseBuild? input target view reference W D fuel := by
  induction fuel with
  | zero =>
      funext cursor
      simp only [markedKey, sparseBuild?, ordinaryKey?, compound_eq, cache.readChildren_eq]
  | succ fuel ih =>
      funext cursor
      simp only [markedKey, sparseBuild?, ordinaryKey?, compound_eq, cache.readChildren_eq, ih]

def markedBefore (state : OccurrenceAuxState) (target : Occ input) (reference : input.Atom)
    (W D : Nat) (base : Frame input) (left right : Fin 4) : Option Ordering := do
  let l ← markedKey input cache target (rawStateView input state target) reference W D
    (2 * (retainedCarrierFuel input + 1)) (base.cursorAt left)
  let r ← markedKey input cache target (rawStateView input state target) reference W D
    (2 * (retainedCarrierFuel input + 1)) (base.cursorAt right)
  some (compareSparse input l r)

theorem markedBefore_eq (state : OccurrenceAuxState) (target : Occ input) (reference : input.Atom)
    (W D : Nat) (base : Frame input) : markedBefore input cache state target reference W D base =
      sparseBefore input state target reference W D base := by
  funext left right
  unfold markedBefore sparseBefore sparseCompareAt?
  simp only [markedKey_eq]

def markedPartition (state : OccurrenceAuxState) (target : Occ input) (reference : input.Atom)
    (W D : Nat) : Option (List (Fin 4) × List (Option Ordering)) := do
  let base ← frame input cache target
  let sorted ← sortBy? (markedBefore input cache state target reference W D base) (List.finRange 4)
  some (sorted, adjacentBy (markedBefore input cache state target reference W D base) sorted)

theorem markedPartition_eq (state : OccurrenceAuxState) (target : Occ input) (reference : input.Atom)
    (W D : Nat) : markedPartition input cache state target reference W D =
      sparsePartition? input state target reference W D := by
  unfold markedPartition sparsePartition?
  simp only [frame_eq, markedBefore_eq]

def marked (mol : RawMolecule) (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : Option Rule6TrackedRanking := do
  if bound : mark < input.certified.input.molecule.atomCount then
    let reference : input.Atom := ⟨mark, bound⟩
    let target ← lookup? input node
    let atoms ← LocalizedGenericMarkedRecalculation.frameAtoms? mol node
    let base ← frame input cache target
    let W := retainedCarrierFuel input
    let D := 2 * (retainedCarrierFuel input + 1)
    let ranked ← markedPartition input cache state target reference W D
    let positions ← positions? input atoms base ranked.1
    let count ← LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount?
      (before input cache state target base) (markedBefore input cache state target reference W D base) ranked.1
    some { positions := positions
           unique := LocalizedGenericMarkedRecalculation.strict ranked.2
           pseudoComparisons := count }
  else none

theorem marked_eq (mol : RawMolecule) (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) : marked input cache mol state node mark = (sparseOperations input mol).marked state node mark := by
  change marked input cache mol state node mark = sparseMarked? input mol state node mark
  unfold marked sparseMarked? sparseMarkedWithLayout?
  simp only [frame_eq, markedPartition_eq, before_eq, markedBefore_eq]

def operations (mol : RawMolecule) : LocalizedMarkedOperationEvaluator.Operations :=
  ⟨ordinary input cache mol, marked input cache mol⟩

/-- Exact record equality, including all failure cases and arbitrary initial auxiliary states. -/
theorem operations_eq (mol : RawMolecule) : operations input cache mol = sparseOperations input mol := by
  have ordinarySame : ordinary input cache mol = (sparseOperations input mol).ordinary :=
    funext fun state => funext fun node => ordinary_eq input cache mol state node
  have markedSame : marked input cache mol = (sparseOperations input mol).marked :=
    funext fun state => funext fun node => funext fun mark => marked_eq input cache mol state node mark
  unfold operations
  rw [ordinarySame, markedSame]

/-- Every distant-reference descriptor, at any depth, geometry, state and inherited context. -/
theorem descriptor_eq (mol : RawMolecule) (depth : Nat)
    (geom : LocalizedGenericMarkedRecalculation.Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) :
    LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol (operations input cache mol) depth geom state ctx node =
      LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol (sparseOperations input mol) depth geom state ctx node := by
  rw [operations_eq]

end TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.cumulative_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.stageCompiler_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.compound_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.frame_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.before_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.partition_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.ordinary_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.markedKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.markedBefore_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.markedPartition_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.marked_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.operations_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.descriptor_eq
