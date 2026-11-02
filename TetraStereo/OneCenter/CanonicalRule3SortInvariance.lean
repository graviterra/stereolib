import TetraStereo.OneCenter.CanonicalRule3Hierarchy
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

/-!
# Sort invariance of the addressed Rule-3 hierarchy

The core module `TetraStereo.OneCenter.CanonicalRule3Hierarchy` compiles recursive Rules-1a--3
keys, sorts sibling keys with the structural descending insertion sort `sortCanonicalRule3Keys`,
and proves that the comparator decides equality exactly when the comparison-visible observables
agree (`compareCanonicalRule3Keys_eq_iff_observable_eq`) and that the comparator is transitive
(`compareCanonicalRule3Keys_transCmp`).  It also proves that the sort is a permutation
(`sortCanonicalRule3Keys_perm`).

This leaf module supplies the missing combinatorial step used by the recursive permutation
theorem: two sibling lists whose comparison-visible observables are permutations of each other
have exactly the same sorted observable list,

`(sortCanonicalRule3Keys xs).map canonicalRule3Observable =
  (sortCanonicalRule3Keys ys).map canonicalRule3Observable`.

Only the comparison-visible projection is claimed.  Keys that differ in the retained observation
provenance, or in `constitutional.sourceNodes` / `sourceOccurrences` / `sourceTree?`, are never
required to be equal.  The argument is the standard uniqueness of sorted lists: the structural
insertion sort produces a list that is descending-sorted with respect to the observable comparator,
and two descending-sorted permutations of a total antisymmetric comparator must coincide.

The result is purely structural: no stereo-perception or physical-chemistry claim is made.
-/

/-! ## The descending comparison relations -/

/-- Descending relation on comparison-visible observables: `left` may appear before `right`
whenever the observable comparator does not report `left < right`. -/
private def descendingObservable
    (left right : CanonicalRule3Observable) : Prop :=
  compareCanonicalRule3Observable left right ≠ Ordering.lt

/-- Descending relation on recursive keys, induced by the key comparator. -/
private def descendingKey (left right : CanonicalRule3Key) : Prop :=
  compareCanonicalRule3Keys left right ≠ Ordering.lt

/-! ## Elementwise transitivity of the descending relations -/

/-- The complement of `Ordering.lt` is transitive for any transitive comparator. -/
private theorem orderingNotLessTrans {α : Type*} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    {a b c : α} (leftNotLess : cmp a b ≠ Ordering.lt)
    (rightNotLess : cmp b c ≠ Ordering.lt) : cmp a c ≠ Ordering.lt := by
  cases first : cmp a b with
  | lt => exact absurd first leftNotLess
  | eq =>
      rw [Std.TransCmp.congr_left first]
      exact rightNotLess
  | gt =>
      cases second : cmp b c with
      | lt => exact absurd second rightNotLess
      | eq =>
          rw [Std.TransCmp.gt_of_gt_of_eq first second]
          intro impossible
          cases impossible
      | gt =>
          rw [Std.TransCmp.gt_trans first second]
          intro impossible
          cases impossible

/-- Two observables that are mutually not strictly less are equal.  This is the antisymmetry step
used to identify descending-sorted permutations. -/
private theorem compareCanonicalRule3Observable_eq_of_not_lt_of_not_lt
    (left right : CanonicalRule3Observable)
    (leftNotLess : compareCanonicalRule3Observable left right ≠ Ordering.lt)
    (rightNotLess : compareCanonicalRule3Observable right left ≠ Ordering.lt) :
    left = right := by
  haveI : Std.TransCmp compareCanonicalRule3Observable :=
    compareCanonicalRule3Observable_transCmp
  have equal : compareCanonicalRule3Observable left right = Ordering.eq := by
    cases comparison : compareCanonicalRule3Observable left right with
    | lt => exact absurd comparison leftNotLess
    | eq => rfl
    | gt =>
        have opposite : compareCanonicalRule3Observable right left = Ordering.lt :=
          Std.OrientedCmp.lt_of_gt comparison
        exact absurd opposite rightNotLess
  exact (compareCanonicalRule3Observable_eq_iff left right).mp equal

/-! ## The structural insertion sort is descending-sorted -/

/-- Every member of an insertion result is either the inserted key or a member of the original
list.  This is the membership induction used to transport the sortedness invariant across the
recursive insertion step. -/
private theorem forall_mem_insertCanonicalRule3Key {property : CanonicalRule3Key → Prop}
    (key : CanonicalRule3Key) :
    ∀ keys : List CanonicalRule3Key,
      property key → (∀ item ∈ keys, property item) →
        ∀ item ∈ insertCanonicalRule3Key key keys, property item
  | [], keyProperty, _ => by
      intro item member
      have itemEq : item = key := by
        simpa [insertCanonicalRule3Key] using member
      rw [itemEq]
      exact keyProperty
  | head :: tail, keyProperty, keysProperty => by
      unfold insertCanonicalRule3Key
      cases comparison : compareCanonicalRule3Keys key head with
      | lt =>
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact keysProperty _ List.mem_cons_self
          · exact forall_mem_insertCanonicalRule3Key (property := property) key tail
              keyProperty
              (fun item itemMember =>
                keysProperty item (List.mem_cons_of_mem head itemMember))
              item member
      | eq =>
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact keyProperty
          · exact keysProperty item member
      | gt =>
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact keyProperty
          · exact keysProperty item member

/-- The structural descending insertion preserves the descending-sorted invariant. -/
private theorem pairwise_insertCanonicalRule3Key (key : CanonicalRule3Key) :
    ∀ keys : List CanonicalRule3Key,
      keys.Pairwise descendingKey →
        (insertCanonicalRule3Key key keys).Pairwise descendingKey
  | [], _ => by
      simp only [insertCanonicalRule3Key]
      exact List.pairwise_singleton descendingKey key
  | head :: tail, sorted => by
      haveI : Std.TransCmp compareCanonicalRule3Keys :=
        compareCanonicalRule3Keys_transCmp
      obtain ⟨headBeforeTail, tailSorted⟩ := List.pairwise_cons.mp sorted
      have insertedSorted := pairwise_insertCanonicalRule3Key key tail tailSorted
      unfold insertCanonicalRule3Key
      cases comparison : compareCanonicalRule3Keys key head with
      | lt =>
          have keyNotLess : compareCanonicalRule3Keys head key ≠ Ordering.lt := by
            have orientation : compareCanonicalRule3Keys head key = Ordering.gt :=
              Std.OrientedCmp.gt_of_lt comparison
            rw [orientation]
            intro impossible
            cases impossible
          rw [List.pairwise_cons]
          refine ⟨?_, insertedSorted⟩
          intro item member
          refine forall_mem_insertCanonicalRule3Key
            (property := fun item => descendingKey head item) key tail ?_ ?_ item member
          · exact keyNotLess
          · intro item itemMember
            exact headBeforeTail item itemMember
      | eq =>
          have keyNotLess : compareCanonicalRule3Keys key head ≠ Ordering.lt := by
            rw [comparison]
            intro impossible
            cases impossible
          rw [List.pairwise_cons]
          refine ⟨?_, List.pairwise_cons.mpr ⟨headBeforeTail, tailSorted⟩⟩
          intro item member
          rcases List.mem_cons.mp member with rfl | itemMember
          · exact keyNotLess
          · exact orderingNotLessTrans keyNotLess (headBeforeTail item itemMember)
      | gt =>
          have keyNotLess : compareCanonicalRule3Keys key head ≠ Ordering.lt := by
            rw [comparison]
            intro impossible
            cases impossible
          rw [List.pairwise_cons]
          refine ⟨?_, List.pairwise_cons.mpr ⟨headBeforeTail, tailSorted⟩⟩
          intro item member
          rcases List.mem_cons.mp member with rfl | itemMember
          · exact keyNotLess
          · exact orderingNotLessTrans keyNotLess (headBeforeTail item itemMember)

/-- The structural descending sort produces a descending-sorted key list. -/
private theorem pairwise_sortCanonicalRule3Keys (keys : List CanonicalRule3Key) :
    (sortCanonicalRule3Keys keys).Pairwise descendingKey := by
  induction keys with
  | nil => exact List.Pairwise.nil
  | cons key keys inductionHypothesis =>
      exact pairwise_insertCanonicalRule3Key key (sortCanonicalRule3Keys keys)
        inductionHypothesis

/-! ## Transport to the comparison-visible projection -/

/-- Mapping the comparison-visible projection over the sorted key list yields a
descending-sorted observable list. -/
private theorem pairwise_map_observable_sortCanonicalRule3Keys
    (keys : List CanonicalRule3Key) :
    ((sortCanonicalRule3Keys keys).map canonicalRule3Observable).Pairwise
      descendingObservable := by
  refine List.Pairwise.map canonicalRule3Observable ?_ (pairwise_sortCanonicalRule3Keys keys)
  intro left right relation
  simp only [descendingKey] at relation
  simp only [descendingObservable]
  simpa only [compareCanonicalRule3Keys_eq_compareObservable] using relation

/-! ## Sort invariance -/

/-- Two lists of recursive keys whose comparison-visible observables are permutations of each
other have the same sorted observable projection.

No equality of keys is required: the retained observation provenance and the constitutional
provenance fields may differ arbitrarily.  The proof uses only (i) the exactness of the observable
comparator on equality, (ii) its transitivity, and (iii) the fact that the structural insertion
sort is descending-sorted. -/
theorem map_sortCanonicalRule3Keys_observable_eq_of_perm
    {xs ys : List CanonicalRule3Key}
    (permutation : (xs.map canonicalRule3Observable).Perm
      (ys.map canonicalRule3Observable)) :
    (sortCanonicalRule3Keys xs).map canonicalRule3Observable =
      (sortCanonicalRule3Keys ys).map canonicalRule3Observable := by
  refine List.Perm.eq_of_pairwise (le := descendingObservable) ?_
    (pairwise_map_observable_sortCanonicalRule3Keys xs)
    (pairwise_map_observable_sortCanonicalRule3Keys ys)
    (((sortCanonicalRule3Keys_perm xs).map canonicalRule3Observable).trans
      (permutation.trans
        ((sortCanonicalRule3Keys_perm ys).map canonicalRule3Observable).symm))
  intro left right _ _ leftNotLess rightNotLess
  simp only [descendingObservable] at leftNotLess rightNotLess
  exact compareCanonicalRule3Observable_eq_of_not_lt_of_not_lt left right
    leftNotLess rightNotLess

/- Kernel trust checks for every theorem in this module. -/
assert_kernel_only orderingNotLessTrans
assert_kernel_only compareCanonicalRule3Observable_eq_of_not_lt_of_not_lt
assert_kernel_only forall_mem_insertCanonicalRule3Key
assert_kernel_only pairwise_insertCanonicalRule3Key
assert_kernel_only pairwise_sortCanonicalRule3Keys
assert_kernel_only pairwise_map_observable_sortCanonicalRule3Keys
assert_kernel_only map_sortCanonicalRule3Keys_observable_eq_of_perm

end RawMolecule
end OneCenter
end TetraStereo
