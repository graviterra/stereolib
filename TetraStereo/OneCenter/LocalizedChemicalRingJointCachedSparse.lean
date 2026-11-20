import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse
import TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Reuse one certified occurrence child reader throughout every ordinary and joint sparse
subbuild. The complete ordered reference vector and single shared child ordering are unchanged.
All equalities hold for every cursor, including failures; no valid-cursor or output premise is
required. The public caller constructs the cache once and captures it in its operations. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointCachedSparse

open CertifiedLocalizedCIPInput
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedPromotedKey (ordinaryKey?)
open LocalizedChemicalRingJointMarkerSparse (SparseKey sparseMarkers sortSparse compareSparse
  sparseBuild? sparseCompareAt?)
open LocalizedChemicalRingCachedOperations (compound compound_eq)

variable (input : CertifiedLocalizedCIPInput)
  (cache : input.LocalizedRerootChildReader (retainedCarrierFuel input))

def build? (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat) :
    Nat → input.LocalizedRerootCursor (retainedCarrierFuel input) → Option (SparseKey input)
  | 0, cursor => do
      let prior ← compound input cache target view (2 * (retainedCarrierFuel input + 1)) cursor
      let children ← cache.readChildren cursor
      if children = [] then some ⟨prior, sparseMarkers input references W D [] cursor⟩ else none
  | fuel + 1, cursor => do
      let prior ← compound input cache target view (2 * (retainedCarrierFuel input + 1)) cursor
      let children ← cache.readChildren cursor
      let keys ← children.mapM (build? target view references W D fuel)
      some ⟨prior, sparseMarkers input references W D (sortSparse input keys) cursor⟩

theorem build?_eq (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D fuel : Nat) :
    build? input cache target view references W D fuel =
      sparseBuild? input target view references W D fuel := by
  induction fuel with
  | zero =>
    funext cursor
    simp only [build?, sparseBuild?, ordinaryKey?, compound_eq, cache.readChildren_eq]
  | succ fuel ih =>
    funext cursor
    simp only [build?, sparseBuild?, ordinaryKey?, compound_eq, cache.readChildren_eq, ih]

def compareAt? (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor (retainedCarrierFuel input)) : Option Ordering := do
  let l ← build? input cache target view references W D (2 * (retainedCarrierFuel input + 1)) left
  let r ← build? input cache target view references W D (2 * (retainedCarrierFuel input + 1)) right
  some (compareSparse input l r)

theorem compareAt?_eq (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor (retainedCarrierFuel input)) :
    compareAt? input cache target view references W D left right =
      sparseCompareAt? input target view references W D left right := by
  simp only [compareAt?, sparseCompareAt?, build?_eq]

end TetraStereo.OneCenter.LocalizedChemicalRingJointCachedSparse

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedSparse.build?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedSparse.build?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedSparse.compareAt?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedSparse.compareAt?_eq
