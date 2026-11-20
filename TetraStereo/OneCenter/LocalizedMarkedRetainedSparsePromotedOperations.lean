import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey
import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Executable sparse marked operations, equal to the dense retained-promoted operations

The marked callback of `LocalizedMarkedRetainedPromotedOperations.operations` with every promoted
key built by `sparseBuild?`. The ordinary callback, frame, positions, count, reference handling,
default layout and the evaluator's inherited-reference policy are unchanged.

`sparseOperations_eq` proves that the operations records are equal, for every certified input and
raw molecule. Every theorem about the dense record (generated facts, recursive descriptors, the
whole report, agreement with `independentOperations`) therefore holds for the sparse record by
rewriting. The sparse record avoids materializing `W ^ level` zero cells at the default layout.

This is an executable representation successor, not a new chemical rule or default change.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedCarrierLookup LocalizedMarkedFramePositionBridge
open LocalizedMarkedRetainedSparsePromotedKey
open LocalizedGenericMarkedRecalculation (frameAtoms? strict)

abbrev Node := RawMolecule.CanonicalBranchNode

variable (input : CertifiedLocalizedCIPInput)

def sparseBefore (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (reference : input.Atom) (W D : Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (left right : Fin 4) : Option Ordering :=
  sparseCompareAt? input target (rawStateView input state target) reference W D
    (frame.cursorAt left) (frame.cursorAt right)

def sparsePartition? (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (reference : input.Atom) (W D : Nat) :
    Option (List (Fin 4) × List (Option Ordering)) := do
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  let sorted ← sortBy? (sparseBefore input state target reference W D frame) (List.finRange 4)
  some (sorted, adjacentBy (sparseBefore input state target reference W D frame) sorted)

def sparseMarkedWithLayout? (mol : RawMolecule) (W D : Nat) (state : OccurrenceAuxState)
    (node : Node) (mark : Nat) : Option Rule6TrackedRanking := do
  if bound : mark < input.certified.input.molecule.atomCount then
    let reference : input.Atom := ⟨mark, bound⟩
    let target ← lookup? input node
    let atoms ← frameAtoms? mol node
    let frame ← input.localizedNoDoubleFourLigandFrameExec? target
    let partition ← sparsePartition? input state target reference W D
    let positions ← positions? input atoms frame partition.1
    let count ← LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount?
      (rawStateBefore input state target frame)
      (sparseBefore input state target reference W D frame)
      partition.1
    some { positions := positions, unique := strict partition.2, pseudoComparisons := count }
  else none

def sparseMarked? (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node) (mark : Nat) :
    Option Rule6TrackedRanking :=
  sparseMarkedWithLayout? input mol (retainedCarrierFuel input)
    (2 * (retainedCarrierFuel input + 1)) state node mark

def sparseOperations (mol : RawMolecule) : LocalizedMarkedOperationEvaluator.Operations where
  ordinary := ordinary input mol
  marked := sparseMarked? input mol

theorem sparseBefore_eq :
    sparseBefore input = LocalizedMarkedRetainedPromotedRanking.before input := by
  funext state target reference W D frame left right
  exact sparseCompareAt?_eq input target _ reference W D _ _

theorem sparsePartition?_eq :
    sparsePartition? input = LocalizedMarkedRetainedPromotedRanking.partition? input := by
  funext state target reference W D
  unfold sparsePartition? LocalizedMarkedRetainedPromotedRanking.partition?
  rw [sparseBefore_eq]

theorem sparseMarkedWithLayout?_eq :
    sparseMarkedWithLayout? input =
      LocalizedMarkedRetainedPromotedOperations.markedWithLayout? input := by
  funext mol W D state node mark
  unfold sparseMarkedWithLayout? LocalizedMarkedRetainedPromotedOperations.markedWithLayout?
  rw [sparsePartition?_eq, sparseBefore_eq]

/-- **The sparse record is the dense retained-promoted record.** -/
theorem sparseOperations_eq (mol : RawMolecule) :
    sparseOperations input mol = LocalizedMarkedRetainedPromotedOperations.operations input mol := by
  unfold sparseOperations LocalizedMarkedRetainedPromotedOperations.operations sparseMarked?
    LocalizedMarkedRetainedPromotedOperations.marked?
  rw [sparseMarkedWithLayout?_eq]

/-- Every generated fact, at every depth, geometry, state and inherited context. -/
theorem facts_eq (mol : RawMolecule) (depth : Nat)
    (geom : LocalizedGenericMarkedRecalculation.Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : Node) :
    LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth geom state ctx
        node =
      LocalizedMarkedOperationEvaluator.facts mol
        (LocalizedMarkedRetainedPromotedOperations.operations input mol) depth geom state ctx node := by
  rw [sparseOperations_eq]

/-- The whole detected-centre report. -/
theorem assign_eq (mol : RawMolecule) (geom : LocalizedGenericMarkedRecalculation.Geometry) :
    LocalizedMarkedOperationEvaluator.assign mol (sparseOperations input mol) geom =
      LocalizedMarkedOperationEvaluator.assign mol
        (LocalizedMarkedRetainedPromotedOperations.operations input mol) geom := by
  rw [sparseOperations_eq]

end TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations.sparseBefore_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations.sparsePartition?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations.sparseMarkedWithLayout?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations.facts_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations.assign_eq
