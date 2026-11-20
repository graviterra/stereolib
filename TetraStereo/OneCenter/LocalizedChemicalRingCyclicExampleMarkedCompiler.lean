import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCompiler
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-! Exact finite representation of the marked callback for the cyclic example. The marker
window, sparse marker order, ordinary prefix and promotion count are the actual operations. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleMarkedCompiler

open CertifiedLocalizedCIPInput LocalizedChemicalRingCyclicExampleInput
open LocalizedChemicalRingCyclicExampleChildren LocalizedChemicalRingCyclicExampleCompiler
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedPromotedKey
open LocalizedMarkedRetainedSparsePromotedKey LocalizedMarkedRetainedSparsePromotedOperations

def markedKey (target : Occ) (view : certified.LocalizedDependencyView target)
    (reference : certified.Atom) (W D : Nat) : Nat → Cursor → Option (SparseKey certified)
  | 0, cursor => do
      let prior ← compound target view 22 cursor
      let children ← readChildren cursor
      if children = [] then
        some ⟨prior, LocalizedPhysicalMarkedSparseMarker.assemble W D (referenceBit certified reference cursor) []⟩
      else none
  | fuel + 1, cursor => do
      let prior ← compound target view 22 cursor
      let children ← readChildren cursor
      let keys ← children.mapM (markedKey target view reference W D fuel)
      some ⟨prior, LocalizedPhysicalMarkedSparseMarker.assemble W D (referenceBit certified reference cursor)
        ((sortSparse certified keys).map SparseKey.marker)⟩

theorem markedKey_eq (target : Occ) (view : certified.LocalizedDependencyView target)
    (reference : certified.Atom) (W D fuel : Nat) : markedKey target view reference W D fuel =
    sparseBuild? certified target view reference W D fuel := by
  induction fuel with
  | zero =>
      funext cursor
      simp only [markedKey, sparseBuild?, ordinaryKey?, compound_eq, readChildren_eq]
  | succ fuel ih =>
      funext cursor
      simp only [markedKey, sparseBuild?, ordinaryKey?, compound_eq, readChildren_eq, ih]

def markedBefore (state : OccurrenceAuxState) (target : Occ) (reference : certified.Atom)
    (W D : Nat) (base : certified.LocalizedOccurrenceFourLigandFrame 10)
    (left right : Fin 4) : Option Ordering := do
  let l ← markedKey target (rawStateView certified state target) reference W D 22 (base.cursorAt left)
  let r ← markedKey target (rawStateView certified state target) reference W D 22 (base.cursorAt right)
  some (compareSparse certified l r)

theorem markedBefore_eq (state : OccurrenceAuxState) (target : Occ) (reference : certified.Atom)
    (W D : Nat) (base : certified.LocalizedOccurrenceFourLigandFrame 10) :
    markedBefore state target reference W D base = sparseBefore certified state target reference W D base := by
  funext left right
  unfold markedBefore sparseBefore sparseCompareAt?
  simp only [markedKey_eq]
  rfl

def markedPartition (state : OccurrenceAuxState) (target : Occ) (reference : certified.Atom)
    (W D : Nat) : Option (List (Fin 4) × List (Option Ordering)) := do
  let base ← frame target
  let sorted ← sortBy? (markedBefore state target reference W D base) (List.finRange 4)
  some (sorted, adjacentBy (markedBefore state target reference W D base) sorted)

theorem markedPartition_eq (state : OccurrenceAuxState) (target : Occ) (reference : certified.Atom)
    (W D : Nat) : markedPartition state target reference W D =
      sparsePartition? certified state target reference W D := by
  unfold markedPartition sparsePartition?
  simp only [frame_eq, markedBefore_eq]
  rfl

def marked (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    Option Rule6TrackedRanking := do
  if bound : mark < 9 then
    let reference : certified.Atom := ⟨mark, bound⟩
    let target ← lookup node
    let atoms ← LocalizedGenericMarkedRecalculation.frameAtoms? mol node
    let base ← frame target
    let ranked ← markedPartition state target reference 10 22
    let positions ← positions? certified atoms base ranked.1
    let count ← LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount?
      (before state target base) (markedBefore state target reference 10 22 base) ranked.1
    some { positions := positions
           unique := LocalizedGenericMarkedRecalculation.strict ranked.2
           pseudoComparisons := count }
  else none

theorem marked_eq (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    marked state node mark = ops.marked state node mark := by
  change marked state node mark = sparseMarked? certified mol state node mark
  unfold marked sparseMarked? sparseMarkedWithLayout?
  simp only [lookup_eq, frame_eq, markedPartition_eq, before_eq, markedBefore_eq]
  rfl

def operations : LocalizedMarkedOperationEvaluator.Operations :=
  ⟨LocalizedChemicalRingCyclicExampleCompiler.ordinary, marked⟩

theorem operations_eq : operations = ops := by
  have ordinarySame : LocalizedChemicalRingCyclicExampleCompiler.ordinary = ops.ordinary :=
    funext fun state => funext fun node => ordinary_eq state node
  have markedSame : marked = ops.marked :=
    funext fun state => funext fun node => funext fun mark => marked_eq state node mark
  unfold operations
  rw [ordinarySame, markedSame]

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleMarkedCompiler

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleMarkedCompiler.markedKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleMarkedCompiler.operations_eq
