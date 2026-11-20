import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrdinary
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Sparse marked keys with an absent auxiliary reader. This is an exact executable
representation of the actual empty-state key, independent of its descriptor target. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse

open CertifiedLocalizedCIPInput
open LocalizedMarkedRetainedStateReader (rawStateView)
open LocalizedMarkedRetainedSparsePromotedKey (SparseKey compareSparse sortSparse sparseBuild? sparseCompareAt?)
open LocalizedMarkedRetainedPromotedKey (ordinaryKey? referenceBit)
open LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrdinary (ordinaryKey_nil)
open LocalizedPhysicalMarkedSparseMarker (assemble)

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

def emptyPrior (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key :=
  input.buildRuleMajorCompoundRule45KeyWith?
    (fun stage position => input.buildRuleMajorCumulativeWithReadExec? stage
      (fun _ => none) (2 * (carrierFuel + 1)) position) cursor

theorem emptyPrior_eq (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    emptyPrior input cursor = ordinaryKey? input target (rawStateView input [] target) cursor := by
  rw [ordinaryKey_nil]
  unfold emptyPrior
  congr 1
  funext stage position
  exact input.buildRuleMajorCumulativeWithReadExec_eq stage (fun _ => none) _ position

def build (reference : input.Atom) (W D : Nat) :
    Nat → input.LocalizedRerootCursor carrierFuel → Option (SparseKey input)
  | 0, cursor => do
      let prior ← emptyPrior input cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then some ⟨prior, assemble W D (referenceBit input reference cursor) []⟩ else none
  | fuel + 1, cursor => do
      let prior ← emptyPrior input cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      let keys ← children.mapM (build reference W D fuel)
      some ⟨prior, assemble W D (referenceBit input reference cursor)
        ((sortSparse input keys).map SparseKey.marker)⟩

theorem build_eq (target : input.LocalizedCIPOccurrence carrierFuel)
    (reference : input.Atom) (W D : Nat) :
    ∀ fuel cursor, build input reference W D fuel cursor =
      sparseBuild? input target (rawStateView input [] target) reference W D fuel cursor := by
  intro fuel
  induction fuel with
  | zero => intro cursor; simp only [build, sparseBuild?, emptyPrior_eq input target]
  | succ fuel ih =>
      intro cursor
      have same : build input reference W D fuel =
          sparseBuild? input target (rawStateView input [] target) reference W D fuel := funext ih
      simp only [build, sparseBuild?, emptyPrior_eq input target, same]

def compareAt (reference : input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel) : Option Ordering := do
  let l ← build input reference W D (2 * (carrierFuel + 1)) left
  let r ← build input reference W D (2 * (carrierFuel + 1)) right
  some (compareSparse input l r)

theorem compareAt_eq (target : input.LocalizedCIPOccurrence carrierFuel)
    (reference : input.Atom) (W D : Nat) (left right : input.LocalizedRerootCursor carrierFuel) :
    compareAt input reference W D left right =
      sparseCompareAt? input target (rawStateView input [] target) reference W D left right := by
  unfold compareAt sparseCompareAt?
  rw [build_eq input target, build_eq input target]

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.emptyPrior
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.emptyPrior_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.build
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.build_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.compareAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptySparse.compareAt_eq
