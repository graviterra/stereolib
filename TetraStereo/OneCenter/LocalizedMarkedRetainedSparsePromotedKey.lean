import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey
import TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Sparse promoted keys: the dense builder with zero-free marker rows

`sparseBuild?` is the recursive promoted-key builder of `LocalizedMarkedRetainedPromotedKey`
with every marker stored as zero-free `(index, value)` rows (`LocalizedPhysicalMarkedSparseMarker`)
and compared by `compareMarker`. The ordinary prefix, its comparator, the child order, the
reference bit, fuel and layout are unchanged.

`sparseBuild?_eq` proves, for every target, view, reference, layout, fuel and cursor, that the
sparse builder is the dense builder mapped through `toSparse` (same prior, `encode` of the dense
marker). The marker shape needed by `compareMarker_encode_shaped` is derived from assembly
(`build?_shaped`); no arbitrary-row normalization or encoder agreement is assumed. Consequently
`sparseCompareAt?` equals the dense `compareAt?`.

This is a representation successor for execution: the dense padding `W ^ level` is not
materialized. It is not a new chemical rule.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey

open CertifiedLocalizedCIPInput DeclarativeCIP.PromotedCanonical
open LocalizedMarkedRetainedPromotedKey
open LocalizedPhysicalMarkedSparseMarker (SparseMarker assemble encode compareMarker
  assemble_eq_encode compareMarker_encode_shaped)
private theorem mapM_option_map {α β γ : Type} (h : α → Option β) (s : β → γ) :
    ∀ l : List α, l.mapM (fun p => (h p).map s) = (l.mapM h).map (List.map s)
  | [] => rfl
  | a :: l => by
      simp only [List.mapM_cons, mapM_option_map h s l]
      cases h a <;> cases l.mapM h <;> rfl

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

/-- Complete ordinary priority followed by the sparse promoted observation column. -/
structure SparseKey where
  prior : input.LocalizedRerootCompoundRule45Key
  marker : SparseMarker

def compareSparse (left right : SparseKey input) : Ordering :=
  (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering.then
    (compareMarker left.marker right.marker)

def sortSparse (keys : List (SparseKey input)) : List (SparseKey input) :=
  keys.insertionSort fun a b => compareSparse input a b ≠ .lt

/-- The dense recursion with sparse marker assembly. -/
def sparseBuild? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat) :
    Nat → input.LocalizedRerootCursor carrierFuel → Option (SparseKey input)
  | 0, cursor => do
      let prior ← ordinaryKey? input target view cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some ⟨prior, assemble W D (referenceBit input reference cursor) []⟩
      else none
  | fuel + 1, cursor => do
      let prior ← ordinaryKey? input target view cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      let keys ← children.mapM (sparseBuild? target view reference W D fuel)
      some ⟨prior, assemble W D (referenceBit input reference cursor)
        ((sortSparse input keys).map SparseKey.marker)⟩

def sparseCompareAt? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel) : Option Ordering := do
  let l ← sparseBuild? input target view reference W D (2 * (carrierFuel + 1)) left
  let r ← sparseBuild? input target view reference W D (2 * (carrierFuel + 1)) right
  some (compareSparse input l r)

def toSparse (key : PromotedKey input) : SparseKey input := ⟨key.prior, encode key.marker⟩

theorem compareSparse_toSparse {W D : Nat} (left right : PromotedKey input)
    (leftShape : MarkerWellShaped W D left.marker) (rightShape : MarkerWellShaped W D right.marker) :
    compareSparse input (toSparse input left) (toSparse input right) =
      compareKeys input left right := by
  unfold compareSparse compareKeys toSparse
  rw [compareMarker_encode_shaped left.marker right.marker leftShape rightShape]

private theorem mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      simp
  | x :: xs, ys, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨y, hy, rest, hrest, rfl⟩ := h
      intro z member
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨x, List.mem_cons_self, hy⟩
      · obtain ⟨w, wMem, hw⟩ := mapM_mem f xs rest hrest z tail
        exact ⟨w, List.mem_cons_of_mem _ wMem, hw⟩

section Builder

variable (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)

/-- Every dense build has a well-shaped marker; derived from assembly, not assumed. -/
theorem build?_shaped : ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : PromotedKey input), build? input target view reference W D fuel cursor = some key →
      MarkerWellShaped W D key.marker
  | 0, cursor, key, built => by
      simp only [build?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨prior, _, children, _, rest⟩ := built
      split at rest
      · cases Option.some.inj rest
        exact assembleMarker_wellShaped W D _ [] (by simp)
      · cases rest
  | fuel + 1, cursor, key, built => by
      simp only [build?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨prior, _, children, _, keys, hkeys, same⟩ := built
      cases Option.some.inj same
      apply assembleMarker_wellShaped
      intro marker member
      obtain ⟨sortedKey, sortedMember, rfl⟩ := List.mem_map.mp member
      have original : sortedKey ∈ keys := (List.perm_insertionSort _ keys).mem_iff.mp sortedMember
      obtain ⟨child, _, childBuilt⟩ := mapM_mem _ children keys hkeys sortedKey original
      exact build?_shaped fuel child sortedKey childBuilt

/-- **Sparse builder = dense builder** with the marker encoded, for every input, view,
reference, layout, fuel and cursor. -/
theorem sparseBuild?_eq : ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
    sparseBuild? input target view reference W D fuel cursor =
      (build? input target view reference W D fuel cursor).map (toSparse input)
  | 0, cursor => by
      cases hp : ordinaryKey? input target view cursor with
      | none => simp [sparseBuild?, build?, hp]
      | some prior =>
          cases hc : input.executableLocalizedRerootChildren? cursor with
          | none => simp [sparseBuild?, build?, hp, hc]
          | some children =>
              by_cases empty : children = []
              · subst empty
                have leaf := assemble_eq_encode W D (referenceBit input reference cursor) []
                  (by simp)
                simp only [List.map_nil] at leaf
                simp [sparseBuild?, build?, hp, hc, toSparse, leaf]
              · simp [sparseBuild?, build?, hp, hc, empty]
  | fuel + 1, cursor => by
      cases hp : ordinaryKey? input target view cursor with
      | none => simp [sparseBuild?, build?, hp]
      | some prior =>
          cases hc : input.executableLocalizedRerootChildren? cursor with
          | none => simp [sparseBuild?, build?, hp, hc]
          | some children =>
              have children_eq : children.mapM (sparseBuild? input target view reference W D fuel) =
                  (children.mapM (build? input target view reference W D fuel)).map
                    (List.map (toSparse input)) := by
                rw [← mapM_option_map]
                congr 1
                funext child
                exact sparseBuild?_eq fuel child
              cases hk : children.mapM (build? input target view reference W D fuel) with
              | none =>
                  rw [hk] at children_eq
                  simp [sparseBuild?, build?, hp, hc, hk, children_eq]
              | some keys =>
                  rw [hk] at children_eq
                  have shaped : ∀ key ∈ keys, MarkerWellShaped W D key.marker := by
                    intro key member
                    obtain ⟨child, _, childBuilt⟩ := mapM_mem _ children keys hk key member
                    exact build?_shaped input target view reference W D fuel child key childBuilt
                  have sorted : sortSparse input (keys.map (toSparse input)) =
                      (sortKeys input keys).map (toSparse input) :=
                    (List.map_insertionSort (fun a b => compareKeys input a b ≠ .lt)
                      (fun a b => compareSparse input a b ≠ .lt) (toSparse input) keys
                      fun a ha b hb => by
                        dsimp only
                        rw [compareSparse_toSparse input a b (shaped a ha) (shaped b hb)]).symm
                  have markersShaped : ∀ marker ∈ (sortKeys input keys).map PromotedKey.marker,
                      MarkerWellShaped W D marker := by
                    intro marker member
                    obtain ⟨key, keyMember, rfl⟩ := List.mem_map.mp member
                    exact shaped key ((List.perm_insertionSort _ keys).mem_iff.mp keyMember)
                  have assembled := assemble_eq_encode W D (referenceBit input reference cursor)
                    ((sortKeys input keys).map PromotedKey.marker) markersShaped
                  rw [List.map_map] at assembled
                  simp only [sparseBuild?, build?, hp, hc, hk, children_eq, Option.bind_eq_bind,
                    Option.bind_some, Option.map_some, sorted, List.map_map]
                  exact congrArg (fun marker => some (⟨prior, marker⟩ : SparseKey input)) assembled

/-- The sparse branch comparison is the dense one. -/
theorem sparseCompareAt?_eq (left right : input.LocalizedRerootCursor carrierFuel) :
    sparseCompareAt? input target view reference W D left right =
      compareAt? input target view reference W D left right := by
  unfold sparseCompareAt? compareAt?
  rw [sparseBuild?_eq, sparseBuild?_eq]
  cases hl : build? input target view reference W D (2 * (carrierFuel + 1)) left with
  | none => rfl
  | some l =>
      cases hr : build? input target view reference W D (2 * (carrierFuel + 1)) right with
      | none => rfl
      | some r =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
          rw [compareSparse_toSparse input l r (build?_shaped input target view reference W D _ _ l hl)
            (build?_shaped input target view reference W D _ _ r hr)]

end Builder

end TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey.compareSparse_toSparse
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey.build?_shaped
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey.sparseBuild?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey.sparseCompareAt?_eq
