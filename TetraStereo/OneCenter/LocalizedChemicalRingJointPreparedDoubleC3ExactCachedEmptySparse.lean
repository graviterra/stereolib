import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse
import TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Root0-only cached execution of the absent-label scalar sparse keys. The true reader branch
never constructs other-root carriers, and every prior stage has a constant absent-label reader. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCachedEmptySparse

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice (reader)
open LocalizedMarkedRetainedStateReader (rawStateView)
open LocalizedMarkedRetainedSparsePromotedKey (SparseKey compareSparse sortSparse sparseCompareAt?)
open LocalizedMarkedRetainedPromotedKey (referenceBit)
open LocalizedPhysicalMarkedSparseMarker (assemble)

abbrev Cursor := input.LocalizedRerootCursor 26

def prior (cursor : Cursor) : Option input.LocalizedRerootCompoundRule45Key :=
  input.buildRuleMajorCompoundRule45KeyWith?
    (fun stage position => LocalizedChemicalRingCachedOperations.cumulative input reader stage
      (fun _ => none) 54 position) cursor

theorem prior_eq (cursor : Cursor) :
    prior cursor = LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.emptyPrior input cursor := by
  unfold prior LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.emptyPrior
  congr 1
  funext stage position
  exact congrFun (LocalizedChemicalRingCachedOperations.cumulative_eq input reader stage
    (fun _ => none) 54) position

def build (reference : Fin 25) (W D : Nat) : Nat → Cursor → Option (SparseKey input)
  | 0, cursor => do
      let ordinary ← prior cursor
      let children ← reader.readChildren cursor
      if children = [] then some ⟨ordinary, assemble W D (referenceBit input reference cursor) []⟩ else none
  | fuel + 1, cursor => do
      let ordinary ← prior cursor
      let children ← reader.readChildren cursor
      let keys ← children.mapM (build reference W D fuel)
      some ⟨ordinary, assemble W D (referenceBit input reference cursor)
        ((sortSparse input keys).map SparseKey.marker)⟩

theorem build_eq (reference : Fin 25) (W D : Nat) :
    ∀ fuel cursor, build reference W D fuel cursor =
      LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.build input reference W D fuel cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor
      simp only [build, LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.build,
        prior_eq, reader.readChildren_eq]
  | succ fuel ih =>
      intro cursor
      have same : build reference W D fuel =
          LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.build input reference W D fuel := funext ih
      simp only [build, LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.build,
        prior_eq, reader.readChildren_eq, same]

def compareAt (reference : Fin 25) (W D : Nat) (left right : Cursor) : Option Ordering := do
  let l ← build reference W D 54 left
  let r ← build reference W D 54 right
  some (compareSparse input l r)

theorem compareAt_eq (target : input.LocalizedCIPOccurrence 26) (reference : Fin 25)
    (W D : Nat) (left right : Cursor) :
    compareAt reference W D left right =
      sparseCompareAt? input target (rawStateView input [] target) reference W D left right := by
  rw [← LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.compareAt_eq input target]
  unfold compareAt LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.compareAt
  rw [build_eq, build_eq]

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCachedEmptySparse

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCachedEmptySparse.prior_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCachedEmptySparse.build_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCachedEmptySparse.compareAt_eq
