import TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5
import TetraStereo.OneCenter.DeclarativeCIPPromotedCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Full ordinary-prefix promoted keys on retained occurrences

Every recursive child is ordered by its complete Rules-1–5 compound key, then by its
promotion column. The original target and dependency view stay fixed throughout recursion.
Ordinary builds always use the adequate carrier budget; marker traversal has separate fuel.
This replaces the unfinished Rule-4a-only draft, which could let promotion override Rule 4b.

Success is derived for every path-valid carrier cursor. A successful build reads back the
actual full ordinary key, and a strict ordinary decision survives every promotion observation.
These are executable/operational results. Independent canonical marker agreement and the
chemical meaning of generated auxiliary labels are separate obligations.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey

open CertifiedLocalizedCIPInput DeclarativeCIP.PromotedCanonical

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

/-- Complete ordinary priority followed by the promoted observation column. -/
structure PromotedKey where
  prior : input.LocalizedRerootCompoundRule45Key
  marker : MarkerKey

/-- An earlier ordinary decision is immutable, at every recursive child as well as the root. -/
def compareKeys (left right : PromotedKey input) : Ordering :=
  (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering.then
    (compare left.marker right.marker)

def sortKeys (keys : List (PromotedKey input)) : List (PromotedKey input) :=
  keys.insertionSort fun a b => compareKeys input a b ≠ .lt

/-- Reference membership, including actual duplicate occurrences bearing that atom. -/
def referenceBit (reference : input.Atom) (cursor : input.LocalizedRerootCursor carrierFuel) : Nat :=
  if cursor.occurrence.1.node.current? = some reference then 1 else 0

/-- Ordinary fuel is independent of the remaining marker traversal fuel. -/
def ordinaryKey? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key :=
  input.buildActualRuleMajorCompoundRule45KeyExec? target view (2 * (carrierFuel + 1)) cursor

/-- Actual children are sorted by full earlier priority, then the recursively promoted marker.
Neither the original target nor the dependency view is changed at an interior node. -/
def build? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat) :
    Nat → input.LocalizedRerootCursor carrierFuel → Option (PromotedKey input)
  | 0, cursor => do
      let prior ← ordinaryKey? input target view cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some ⟨prior, assembleMarker W D (referenceBit input reference cursor) []⟩
      else none
  | fuel + 1, cursor => do
      let prior ← ordinaryKey? input target view cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      let keys ← children.mapM (build? target view reference W D fuel)
      some ⟨prior, assembleMarker W D (referenceBit input reference cursor)
        ((sortKeys input keys).map PromotedKey.marker)⟩

/-- Comparison of two actual promoted branches. -/
def compareAt? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel) : Option Ordering := do
  let l ← build? input target view reference W D (2 * (carrierFuel + 1)) left
  let r ← build? input target view reference W D (2 * (carrierFuel + 1)) right
  some (compareKeys input l r)

theorem compareKeys_of_prior_ne (left right : PromotedKey input)
    (strict : (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering
      ≠ .eq) :
    compareKeys input left right =
      (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering := by
  unfold compareKeys
  cases h : (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering
    <;> simp_all

theorem compareKeys_of_prior_eq (left right : PromotedKey input)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering
      = .eq) :
    compareKeys input left right = compare left.marker right.marker := by
  simp [compareKeys, tie]

theorem ordinaryKey?_exists (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, ordinaryKey? input target view cursor = some key := by
  unfold ordinaryKey?
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq]
  exact input.exists_buildActualRuleMajorCompoundRule45Key_at_twice target view cursor valid

private theorem mapM_exists {α β : Type} (f : α → Option β) :
    ∀ xs : List α, (∀ x ∈ xs, ∃ y, f x = some y) → ∃ ys, xs.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, available => by
      obtain ⟨y, hy⟩ := available x List.mem_cons_self
      obtain ⟨ys, hys⟩ := mapM_exists f xs
        (fun z hz => available z (List.mem_cons_of_mem x hz))
      exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- Adequate marker budget derives success, including rings and all reference populations. -/
theorem build?_exists_of_budget (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ fuel →
      ∃ key, build? input target view reference W D fuel cursor = some key := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor valid covered
      obtain ⟨prior, priorEq⟩ := ordinaryKey?_exists input target view cursor valid
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      have empty : input.executableLocalizedRerootChildren cursor = [] := by
        by_contra nonempty
        obtain ⟨child, member⟩ := List.exists_mem_of_ne_nil _ nonempty
        have less := input.localizedRerootChild_budget_lt cursor child _ valid derived member
        omega
      refine ⟨⟨prior, assembleMarker W D (referenceBit input reference cursor) []⟩, ?_⟩
      simp [build?, priorEq, input.executableLocalizedRerootChildren?_eq_some, empty]
  | succ fuel ih =>
      intro cursor valid covered
      obtain ⟨prior, priorEq⟩ := ordinaryKey?_exists input target view cursor valid
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      have childComplete : ∀ child ∈ input.executableLocalizedRerootChildren cursor,
          ∃ key, build? input target view reference W D fuel child = some key := by
        intro child member
        have childValid := input.localizedRerootChild_valid cursor child _ derived member
        have less := input.localizedRerootChild_budget_lt cursor child _ valid derived member
        exact ih child childValid (by omega)
      obtain ⟨keys, keysEq⟩ := mapM_exists
        (build? input target view reference W D fuel) _ childComplete
      refine ⟨⟨prior, assembleMarker W D (referenceBit input reference cursor)
        ((sortKeys input keys).map PromotedKey.marker)⟩, ?_⟩
      simp [build?, priorEq, input.executableLocalizedRerootChildren?_eq_some, keysEq]

theorem build?_exists (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, build? input target view reference W D (2 * (carrierFuel + 1)) cursor = some key :=
  build?_exists_of_budget input target view reference W D _ cursor valid
    (input.localizedRerootCursorBudget_le_twice cursor)

/-- Every successful result retains exactly the actual full ordinary key at that cursor. -/
theorem build?_prior (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D fuel : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : PromotedKey input)
    (built : build? input target view reference W D fuel cursor = some key) :
    ordinaryKey? input target view cursor = some key.prior := by
  cases fuel <;>
    simp only [build?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
  · obtain ⟨prior, hp, children, _, rest⟩ := built
    split at rest
    · cases Option.some.inj rest
      exact hp
    · cases rest
  · obtain ⟨prior, hp, children, _, keys, _, same⟩ := built
    cases Option.some.inj same
    exact hp

/-- Comparison succeeds without assuming successful child builds or sorting. -/
theorem compareAt?_exists (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid left)
    (rightValid : input.LocalizedRerootCursorValid right) :
    ∃ order, compareAt? input target view reference W D left right = some order := by
  obtain ⟨l, hl⟩ := build?_exists input target view reference W D left leftValid
  obtain ⟨r, hr⟩ := build?_exists input target view reference W D right rightValid
  exact ⟨compareKeys input l r, by simp [compareAt?, hl, hr]⟩

/-- At every valid recursive cursor, a strict complete ordinary decision survives promotion.
The original target/view are fixed; ordinary keys are the actual full compound builds. -/
theorem compareAt?_preserves_ordinary (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid left)
    (rightValid : input.LocalizedRerootCursorValid right)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftBuilt : ordinaryKey? input target view left = some leftKey)
    (rightBuilt : ordinaryKey? input target view right = some rightKey)
    (strict : (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey).ordering ≠ .eq) :
    compareAt? input target view reference W D left right =
      some (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey).ordering := by
  obtain ⟨l, hl⟩ := build?_exists input target view reference W D left leftValid
  obtain ⟨r, hr⟩ := build?_exists input target view reference W D right rightValid
  have lp : l.prior = leftKey := Option.some.inj
    ((build?_prior input target view reference W D _ left l hl).symm.trans leftBuilt)
  have rp : r.prior = rightKey := Option.some.inj
    ((build?_prior input target view reference W D _ right r hr).symm.trans rightBuilt)
  simp only [compareAt?, hl, hr, Option.bind_eq_bind, Option.bind_some]
  congr 1
  have strict' : (input.compareLocalizedRerootCompoundThroughRule5 l.prior r.prior).ordering ≠ .eq := by
    simpa only [lp, rp] using strict
  rw [compareKeys_of_prior_ne input l r strict', lp, rp]

end TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey.ordinaryKey?_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey.build?_exists_of_budget
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey.build?_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey.build?_prior
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey.compareAt?_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey.compareAt?_preserves_ordinary
