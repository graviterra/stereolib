import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys
import TetraStereo.Certificate.CanonicalSphereKey
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The actual occurrence sorter under an independent key

Pointwise comparison correspondence suffices to derive sorting success and the exact stable
key order, including ties. The authoritative child ranker then has precisely that order followed
by its specified phantom padding. Neither successful sorting nor a selected output is a premise.

The terminal corollary discharges comparison correspondence for the actual promoted comparator:
real, auxiliary-silent terminal children with equal constitutional observations are ordered by
their reference-membership bits. The general nonterminal correspondence is still a separate
obligation; this module does not establish the chemical meaning of recursively generated labels.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedIndependentKeySort

open LocalizedMarkedTerminalGaugeKeys LocalizedMarkedTerminalComparison

abbrev Cursor := CanonicalRerootCursor

section KeySort

variable {K : Type} [LinearOrder K] (key : Cursor → K)

private theorem insert_key (candidate : Cursor) (entries : List Cursor) :
    insertCursorBy? (fun a b => some (compare (key a) (key b))) candidate entries =
      some (entries.orderedInsert (fun a b => key b ≤ key a) candidate) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      by_cases order : key head ≤ key candidate
      · have notLt : compare (key candidate) (key head) ≠ .lt := by
          intro contrary
          exact not_lt_of_ge order (compare_lt_iff_lt.mp contrary)
        cases compared : compare (key candidate) (key head) <;>
          simp_all [insertCursorBy?, List.orderedInsert]
      · have lt : compare (key candidate) (key head) = .lt :=
          compare_lt_iff_lt.mpr (lt_of_not_ge order)
        simp [insertCursorBy?, lt, List.orderedInsert, order, ih]

theorem sort_key (entries : List Cursor) :
    sortCursorsBy? (fun a b => some (compare (key a) (key b))) entries =
      some (entries.insertionSort (fun a b => key b ≤ key a)) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      simp only [sortCursorsBy?, ih, List.insertionSort_cons]
      exact insert_key key head _

/-- The actual sorter is the stable independent key order. Only comparisons on input members
need correspondence, and sorting success is a conclusion. -/
theorem sort_eq_key_sort
    (before : Cursor → Cursor → Option Ordering) (entries : List Cursor)
    (corresponds : ∀ a ∈ entries, ∀ b ∈ entries,
      before a b = some (compare (key a) (key b))) :
    sortCursorsBy? before entries =
      some (entries.insertionSort (fun a b => key b ≤ key a)) := by
  rw [sortCursorsBy?_congr before (fun a b => some (compare (key a) (key b)))
    entries corresponds]
  exact sort_key key entries

/-- The observed output keys are the canonical descending list, even when multiple input
cursors have equal keys. -/
theorem sorted_keys (entries : List Cursor) :
    (entries.insertionSort (fun a b => key b ≤ key a)).map key =
      Certificate.CanonicalSphereKey.sortDesc (entries.map key) := by
  exact List.map_insertionSort (fun a b => key b ≤ key a) (fun a b => b ≤ a)
    key entries (by intros; rfl)

/-- Exact authoritative padding after a derived successful key sort. -/
theorem ranked_children_eq_key_sort (mol : RawMolecule)
    (before : Cursor → Cursor → Option Ordering) (cursor : Cursor)
    (width : (cursor.children mol).length ≤ RawMolecule.authoritativeChildSlots)
    (corresponds : ∀ a ∈ cursor.children mol, ∀ b ∈ cursor.children mol,
      before a b = some (compare (key a) (key b))) :
    rankedCursorChildrenAuthoritative? mol before cursor =
      some ((cursor.children mol).insertionSort (fun a b => key b ≤ key a) ++
        List.replicate (RawMolecule.authoritativeChildSlots - (cursor.children mol).length)
          { node := mol.canonicalPhantom cursor.node.atom
              (cursor.node.rule1bRootDistance + 1) }) := by
  simp [rankedCursorChildrenAuthoritative?, Nat.not_lt.mpr width,
    sort_eq_key_sort key before _ corresponds, List.length_insertionSort]

end KeySort

/-- Independent observation at a real terminal child: does it represent the chosen reference? -/
def promotionBit (reference : Nat) (cursor : Cursor) : Nat :=
  if cursor.node.atom = reference then 1 else 0

/-- A fully discharged runtime instance. Arbitrary fuel, reference, number of children and
auxiliary state are allowed, subject to the explicit terminal/silence/constitutional conditions.
There is no comparison, ordering, or sorting-success assumption. -/
theorem promoted_terminal_children_sort
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat) (cursor : Cursor)
    (terminal : ∀ c ∈ cursor.children mol, cursorTerminal mol c = true)
    (real : ∀ c ∈ cursor.children mol, c.node.provenance = .realAtom)
    (silent : ∀ c ∈ cursor.children mol, state.factAt? c.node = none)
    (sameZ : ∀ a ∈ cursor.children mol, ∀ b ∈ cursor.children mol,
      mol.atomZAt a.node.atom = mol.atomZAt b.node.atom)
    (sameDepth : ∀ a ∈ cursor.children mol, ∀ b ∈ cursor.children mol,
      a.node.depth = b.node.depth)
    (sameMass : ∀ a ∈ cursor.children mol, ∀ b ∈ cursor.children mol,
      mol.atomMassAt a.node.atom = mol.atomMassAt b.node.atom) :
    sortCursorsBy?
        (fun a b => (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          mol state reference fuel a b).map Rule6TrackedDecision.ordering)
        (cursor.children mol) =
      some ((cursor.children mol).insertionSort
        (fun a b => promotionBit reference b ≤ promotionBit reference a)) := by
  apply sort_eq_key_sort
  intro a ha b hb
  rw [promoted_bits mol state fuel reference a b (terminal a ha) (terminal b hb)
    (real a ha) (real b hb) (sameZ a ha b hb) (sameDepth a ha b hb)
    (sameMass a ha b hb) (silent a ha) (silent b hb)]
  rfl

end TetraStereo.OneCenter.LocalizedMarkedIndependentKeySort

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedIndependentKeySort.sort_eq_key_sort
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedIndependentKeySort.sorted_keys
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedIndependentKeySort.ranked_children_eq_key_sort
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedIndependentKeySort.promoted_terminal_children_sort
