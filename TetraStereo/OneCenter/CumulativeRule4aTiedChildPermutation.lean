import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Cumulative Rule-4a child-permutation invariance and the flat-projection regression

The executable cumulative Rules-4a--5 compiler in
`TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key` sorts the independently compiled child
keys with the structural descending insertion sort `sortLocalizedRerootCumulativeRule45Keys` and
only then assigns final sibling slots.  The comparator
`compareLocalizedRerootCumulativeRule45Keys` reads exactly two components of a key: the
constitutional Rules-1a/1b/2 projection and the cumulative descriptor projection.  Rule 4a is the
first component of that cumulative descriptor, with priority `chiral = 2 > pseudoasymmetric = 1 >
none = 0` (`localizedRule4aPriority`).

This module proves the following, entirely for the actual definitions above (no comparator or
sorter is redefined for the positive results):

* **Staged sort invariance.**  For arbitrary child lists `left` and `right` related by `List.Perm`,
  the sorted child sequences have the same comparison-visible observable projection.  This is a
  direct composition of the existing permutation lemma, the existing descending-sortedness lemma,
  and the existing uniqueness of descending representatives.
* **Rule-4a separation of an earlier-rule tie.**  Two keys that share the same constitutional
  projection (`localizedRule4aWitness_constitutional_tie`, the Rules-1a/1b/2 component visible
  inside this key; Rule 3 is a separate top-level key that this sibling permutation does not touch)
  but carry the `chiral` and `pseudoasymmetric` Rule-4a labels are compared strictly (`Ordering.gt`)
  by the cumulative comparator.  A general "later rule refines an earlier tie" lemma
  (`compareLocalizedRerootCumulativeRule45Keys_of_constitutional_eq`) reduces the comparison to the
  descriptor, and a one-sphere reduction lemma
  (`compareSparseLayers_singleton_priority`) exposes the Rule-4a priority vector.
* **The concrete regression.**  On the two-child lists `[chiral, pseudoasymmetric]` and
  `[pseudoasymmetric, chiral]`, the actual cumulative sort returns the *same* key list in both
  orders (`sortLocalizedRerootCumulativeRule45Keys_rule4aTiedChildPermutation`), and that list is a
  permutation of the input with length two.  Hence no child is dropped or duplicated by the
  refinement.  The older flat projection that compares only the constitutional component
  (`compareLocalizedRerootFlatConstitutionalKeys`) ties the two children; its structural sort
  returns the two different input orders unchanged, so it is not order-invariant on this pair.
* **Assembler-facing consequence.**  The actual assembler consumes the sorted children through
  `OfficialRuleMajorKey.assemble` and the three `mergeLocalizedReroot*Children` functions.  Since
  the sorted child lists coincide, the assembled constitutional projection and all three merged
  child contributions coincide as well.

The results are structural statements about the comparator and sorter.  No chemical-fidelity claim
is made beyond the source ordering already encoded by `localizedRule4aPriority`; in particular a
comparator tie is never upgraded to equality of the retained labels or provenance.

Namespace note: this file places the flat-projection sorter in the same namespace as the actual
one only so that the regression can be stated on the same key type.  It is not used by the compile
pipeline.
-/

/-! ## One-sphere descriptor reduction -/

/-- After a constitutional tie, a cumulative key whose descriptor is one sphere with one addressed
entry compares exactly by that entry's cumulative priority vector.  This is the reduction that
exposes Rule 4a in the concrete child pair below. -/
theorem compareSparseLayers_singleton_priority (left right : List Nat) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      [[([], left)]] [[([], right)]] =
      compareLocalizedCumulativeRule45Priority left right := by
  simp only [OfficialRuleMajorKey.compareSparseLayers,
    OfficialRuleMajorKey.compareSparseLayer,
    OfficialRuleMajorKey.compareSparseEntry,
    compareLex, Ordering.byKey, flip,
    List.compareLex_cons_cons, List.compareLex_nil_nil,
    Ordering.eq_then]
  generalize h : compareLocalizedCumulativeRule45Priority left right = outcome
  cases outcome <;> rfl

/-- **Later rules refine an earlier tie.**  When two keys tie under the constitutional Rules
1a/1b/2, the cumulative comparator returns exactly the comparison of the cumulative descriptor
projections.  No later descriptor stage is observed before the earlier constitutional tie has been
exhausted. -/
theorem compareLocalizedRerootCumulativeRule45Keys_of_constitutional_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (constitutionalTie :
      OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.descriptor right.descriptor := by
  simp [compareLocalizedRerootCumulativeRule45Keys, compareLex, Ordering.byKey,
    constitutionalTie]

/-! ## Staged sort invariance under a permutation of the child keys -/

/-- **Staged sort invariance.**  The actual cumulative Rules-4a--5 sibling sort returns the same
comparison-visible child sequence for any permutation of the input child keys.  The conclusion is
the observable projection: the constitutional Rules-1a/1b/2 layers and the cumulative descriptor
layers.  Retained labels and provenance are deliberately not required to agree, because the
comparator never reads them.

The proof composes the actual sorter's permutation lemma, its descending-sortedness lemma, and the
existing theorem that two descending permutations have equal observable projections. -/
theorem map_sortLocalizedRerootCumulativeRule45Keys_observable_eq_of_perm
    (input : CertifiedLocalizedCIPInput)
    {left right : List input.LocalizedRerootCumulativeRule45Key}
    (permutation : left.Perm right) :
    (input.sortLocalizedRerootCumulativeRule45Keys left).map
        (input.localizedRerootCumulativeRule45Observable) =
      (input.sortLocalizedRerootCumulativeRule45Keys right).map
        (input.localizedRerootCumulativeRule45Observable) := by
  exact map_localizedRerootCumulativeRule45Observable_eq_of_perm_of_descending
    input
    (input.sortLocalizedRerootCumulativeRule45Keys left)
    (input.sortLocalizedRerootCumulativeRule45Keys right)
    ((input.sortLocalizedRerootCumulativeRule45Keys_perm left).trans
      (permutation.trans
        (input.sortLocalizedRerootCumulativeRule45Keys_perm right).symm))
    (input.sortLocalizedRerootCumulativeRule45Keys_descending left)
    (input.sortLocalizedRerootCumulativeRule45Keys_descending right)

/-! ## Rule-4a priority: chiral over pseudoasymmetric -/

/-- The Rule-4a priority vector places every chiral label strictly above every pseudoasymmetric
label, independently of the concrete `R`/`S` and `r`/`s` payloads. -/
theorem cumulativeRule4a_chiral_over_pseudoasymmetric
    (descriptor : RS) (pseudo : PseudoRS) :
    compareLocalizedCumulativeRule45Priority
      (localizedCumulativeRule45Priority .rule4a (some (.chiral descriptor)))
      (localizedCumulativeRule45Priority .rule4a (some (.pseudoasymmetric pseudo))) =
      Ordering.gt := by
  cases descriptor <;> cases pseudo <;> rfl

/-- The same priority vector read in the opposite argument order. -/
theorem cumulativeRule4a_pseudoasymmetric_lt_chiral
    (descriptor : RS) (pseudo : PseudoRS) :
    compareLocalizedCumulativeRule45Priority
      (localizedCumulativeRule45Priority .rule4a (some (.pseudoasymmetric pseudo)))
      (localizedCumulativeRule45Priority .rule4a (some (.chiral descriptor))) =
      Ordering.lt := by
  cases descriptor <;> cases pseudo <;> rfl

/-! ## A concrete child-key pair tied before Rule 4a -/

/-- A key with a prescribed constitutional root, a single cumulative descriptor sphere carrying
one addressed priority vector, and empty observation state.  The empty `labels` and `rankedLabels`
are intentional: this witness is used only for comparator and sorter statements, and the
comparator does not inspect those fields. -/
def localizedCumulativeLabelWitness
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel) :
    input.LocalizedRerootCumulativeRule45Key where
  constitutional := root
  descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
  labels := []
  rankedLabels := []

/-- The cumulative comparator on two one-sphere witnesses is exactly the comparison of their
priority vectors. -/
theorem compareLocalizedRerootCumulativeRule45Keys_labelWitness
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (stage : LocalizedCumulativeRule45Stage)
    (leftLabel rightLabel : Option LocalizedAuxiliaryLabel) :
    input.compareLocalizedRerootCumulativeRule45Keys
        (localizedCumulativeLabelWitness input root stage leftLabel)
        (localizedCumulativeLabelWitness input root stage rightLabel) =
      compareLocalizedCumulativeRule45Priority
        (localizedCumulativeRule45Priority stage leftLabel)
        (localizedCumulativeRule45Priority stage rightLabel) := by
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  have tied :
      OfficialRuleMajorKey.compare
        (localizedCumulativeLabelWitness input root stage leftLabel).constitutional
        (localizedCumulativeLabelWitness input root stage rightLabel).constitutional =
      Ordering.eq := by
    show OfficialRuleMajorKey.compare root root = Ordering.eq
    exact Std.ReflCmp.compare_self
  rw [compareLocalizedRerootCumulativeRule45Keys_of_constitutional_eq input _ _ tied]
  simp only [localizedCumulativeLabelWitness]
  exact compareSparseLayers_singleton_priority _ _

/-- On the concrete Rule-4a child pair with the same constitutional root, the actual cumulative
comparator strictly prefers the chiral child over the pseudoasymmetric child. -/
theorem compareLocalizedRerootCumulativeRule45Keys_rule4a_chiral_gt_pseudoasymmetric
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    input.compareLocalizedRerootCumulativeRule45Keys
        (localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)))
        (localizedCumulativeLabelWitness input root .rule4a
          (some (.pseudoasymmetric pseudo))) =
      Ordering.gt := by
  rw [compareLocalizedRerootCumulativeRule45Keys_labelWitness
    input root .rule4a (some (.chiral descriptor)) (some (.pseudoasymmetric pseudo))]
  exact cumulativeRule4a_chiral_over_pseudoasymmetric descriptor pseudo

/-- The same pair read in the opposite order compares strictly the other way. -/
theorem compareLocalizedRerootCumulativeRule45Keys_rule4a_pseudoasymmetric_lt_chiral
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    input.compareLocalizedRerootCumulativeRule45Keys
        (localizedCumulativeLabelWitness input root .rule4a
          (some (.pseudoasymmetric pseudo)))
        (localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor))) =
      Ordering.lt := by
  rw [compareLocalizedRerootCumulativeRule45Keys_labelWitness
    input root .rule4a (some (.pseudoasymmetric pseudo)) (some (.chiral descriptor))]
  exact cumulativeRule4a_pseudoasymmetric_lt_chiral descriptor pseudo

/-- The two witnesses used throughout the regression are tied under the constitutional Rules
1a/1b/2: they share the same `constitutional` field, so the constitutional comparator reports a
tie.  This is the earlier-rule tie that Rule 4a is required to refine; the separate Rule-3 key is
not part of `LocalizedRerootCumulativeRule45Key` and is unaffected by the sibling order. -/
theorem localizedRule4aWitness_constitutional_tie
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    OfficialRuleMajorKey.compare
        (localizedCumulativeLabelWitness input root .rule4a
          (some (.chiral descriptor))).constitutional
        (localizedCumulativeLabelWitness input root .rule4a
          (some (.pseudoasymmetric pseudo))).constitutional =
      Ordering.eq := by
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  show OfficialRuleMajorKey.compare root root = Ordering.eq
  exact Std.ReflCmp.compare_self

/-- The chiral and pseudoasymmetric witnesses are distinct keys, because the cumulative comparator
separates them strictly while it is reflexive.  This is the key-inequality fact behind the flat
projection's order dependence. -/
theorem localizedCumulativeLabelWitness_rule4a_chiral_ne_pseudoasymmetric
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)) ≠
      localizedCumulativeLabelWitness input root .rule4a (some (.pseudoasymmetric pseudo)) := by
  intro same
  have strict :=
    compareLocalizedRerootCumulativeRule45Keys_rule4a_chiral_gt_pseudoasymmetric
      input root descriptor pseudo
  rw [same] at strict
  have selfEqual :
      input.compareLocalizedRerootCumulativeRule45Keys
        (localizedCumulativeLabelWitness input root .rule4a
          (some (.pseudoasymmetric pseudo)))
        (localizedCumulativeLabelWitness input root .rule4a
          (some (.pseudoasymmetric pseudo))) =
      Ordering.eq := by
    letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
      input.compareLocalizedRerootCumulativeRule45Keys_transCmp
    exact Std.ReflCmp.compare_self
  rw [selfEqual] at strict
  cases strict

/-! ## The two-child structural sort -/

/-- A strictly greater key sorts ahead of the other key in either input order.  This is the
two-child normal form of the structural descending insertion sort. -/
theorem sortLocalizedRerootCumulativeRule45Keys_pair_of_gt
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (comparison :
      input.compareLocalizedRerootCumulativeRule45Keys left right = Ordering.gt) :
    input.sortLocalizedRerootCumulativeRule45Keys [left, right] = [left, right] ∧
      input.sortLocalizedRerootCumulativeRule45Keys [right, left] =
        [left, right] := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  have reverseLt :
      input.compareLocalizedRerootCumulativeRule45Keys right left = Ordering.lt :=
    Std.OrientedCmp.lt_of_gt comparison
  constructor
  · change input.insertLocalizedRerootCumulativeRule45Key left
        (input.sortLocalizedRerootCumulativeRule45Keys [right]) = [left, right]
    change input.insertLocalizedRerootCumulativeRule45Key left
        (input.insertLocalizedRerootCumulativeRule45Key right
          (input.sortLocalizedRerootCumulativeRule45Keys [])) = [left, right]
    change input.insertLocalizedRerootCumulativeRule45Key left
        (input.insertLocalizedRerootCumulativeRule45Key right []) = [left, right]
    simp [insertLocalizedRerootCumulativeRule45Key, comparison]
  · change input.insertLocalizedRerootCumulativeRule45Key right
        (input.sortLocalizedRerootCumulativeRule45Keys [left]) = [left, right]
    change input.insertLocalizedRerootCumulativeRule45Key right
        (input.insertLocalizedRerootCumulativeRule45Key left
          (input.sortLocalizedRerootCumulativeRule45Keys [])) = [left, right]
    change input.insertLocalizedRerootCumulativeRule45Key right
        (input.insertLocalizedRerootCumulativeRule45Key left []) = [left, right]
    simp [insertLocalizedRerootCumulativeRule45Key, reverseLt]

/-- **Cumulative Rule-4a refinement removes the input-order dependence.**  The actual cumulative
staged sort returns identical key lists for the two physical input orders of the Rule-4a-separated
child pair. -/
theorem sortLocalizedRerootCumulativeRule45Keys_rule4a_chiral_pseudoasymmetric_commute
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    input.sortLocalizedRerootCumulativeRule45Keys
        [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
         localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo))] =
      input.sortLocalizedRerootCumulativeRule45Keys
        [localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo)),
         localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor))] := by
  have sorted := sortLocalizedRerootCumulativeRule45Keys_pair_of_gt input
    (localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)))
    (localizedCumulativeLabelWitness input root .rule4a (some (.pseudoasymmetric pseudo)))
    (compareLocalizedRerootCumulativeRule45Keys_rule4a_chiral_gt_pseudoasymmetric
      input root descriptor pseudo)
  exact sorted.1.trans sorted.2.symm

/-- The cumulative sort of the chiral-first witness list is a permutation of that list: the
refinement preserves every child with its multiplicity. -/
theorem sortLocalizedRerootCumulativeRule45Keys_rule4a_witness_perm
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    (input.sortLocalizedRerootCumulativeRule45Keys
        [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
         localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo))]).Perm
      [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
       localizedCumulativeLabelWitness input root .rule4a
         (some (.pseudoasymmetric pseudo))] :=
  input.sortLocalizedRerootCumulativeRule45Keys_perm
    [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
     localizedCumulativeLabelWitness input root .rule4a (some (.pseudoasymmetric pseudo))]

/-- Multiplicity preservation, counted: the cumulative sort of the two-child witness list still
has exactly two children. -/
theorem sortLocalizedRerootCumulativeRule45Keys_rule4a_witness_length
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    (input.sortLocalizedRerootCumulativeRule45Keys
        [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
         localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo))]).length = 2 := by
  simpa using
    (input.sortLocalizedRerootCumulativeRule45Keys_perm
      [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
       localizedCumulativeLabelWitness input root .rule4a
         (some (.pseudoasymmetric pseudo))]).length_eq

/-! ## The older flat projection and its regression -/

/-- The older flat projection: compare only the constitutional Rules-1a/1b/2 component and ignore
the entire cumulative descriptor, including Rule 4a.  It is introduced here solely to make the
regression precise; the actual compile pipeline uses
`compareLocalizedRerootCumulativeRule45Keys` instead. -/
def compareLocalizedRerootFlatConstitutionalKeys
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootCumulativeRule45Key →
      input.LocalizedRerootCumulativeRule45Key → Ordering :=
  Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare

/-- Structural insertion under the flat constitutional projection. -/
def insertLocalizedRerootFlatConstitutionalKey
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    List input.LocalizedRerootCumulativeRule45Key →
      List input.LocalizedRerootCumulativeRule45Key
  | [] => [key]
  | head :: tail =>
      match compareLocalizedRerootFlatConstitutionalKeys input key head with
      | .lt => head ::
          insertLocalizedRerootFlatConstitutionalKey input key tail
      | .eq | .gt => key :: head :: tail

/-- Structural descending sort under the flat constitutional projection. -/
def sortLocalizedRerootFlatConstitutionalKeys
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedRerootCumulativeRule45Key →
      List input.LocalizedRerootCumulativeRule45Key
  | [] => []
  | key :: keys =>
      insertLocalizedRerootFlatConstitutionalKey input key
        (sortLocalizedRerootFlatConstitutionalKeys input keys)

/-- Under the flat projection, a tied two-child list is returned unchanged.  The `.eq` branch of
the structural insertion sort is precisely the branch that leaves the incoming order in place. -/
theorem sortLocalizedRerootFlatConstitutionalKeys_pair_of_eq
    (input : CertifiedLocalizedCIPInput)
    (key head : input.LocalizedRerootCumulativeRule45Key)
    (tied : compareLocalizedRerootFlatConstitutionalKeys input key head = Ordering.eq) :
    sortLocalizedRerootFlatConstitutionalKeys input [key, head] = [key, head] := by
  change insertLocalizedRerootFlatConstitutionalKey input key
      (sortLocalizedRerootFlatConstitutionalKeys input [head]) = [key, head]
  change insertLocalizedRerootFlatConstitutionalKey input key
      (insertLocalizedRerootFlatConstitutionalKey input head
        (sortLocalizedRerootFlatConstitutionalKeys input [])) = [key, head]
  change insertLocalizedRerootFlatConstitutionalKey input key
      (insertLocalizedRerootFlatConstitutionalKey input head []) = [key, head]
  simp [insertLocalizedRerootFlatConstitutionalKey, tied]

/-- The flat constitutional projection ties any two one-sphere witnesses with the same root. -/
theorem compareLocalizedRerootFlatConstitutionalKeys_labelWitness
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (stage : LocalizedCumulativeRule45Stage)
    (leftLabel rightLabel : Option LocalizedAuxiliaryLabel) :
    compareLocalizedRerootFlatConstitutionalKeys input
        (localizedCumulativeLabelWitness input root stage leftLabel)
        (localizedCumulativeLabelWitness input root stage rightLabel) =
      Ordering.eq := by
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  simp only [compareLocalizedRerootFlatConstitutionalKeys, Ordering.byKey,
    localizedCumulativeLabelWitness]
  exact Std.ReflCmp.compare_self

/-- Under the flat projection the two witness orders are left unchanged, because the comparator
ties and the structural insertion sort keeps the incoming order on an `.eq` branch. -/
theorem sortLocalizedRerootFlatConstitutionalKeys_rule4a_chiral_pseudoasymmetric
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    sortLocalizedRerootFlatConstitutionalKeys input
        [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
         localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo))] =
      [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
       localizedCumulativeLabelWitness input root .rule4a
         (some (.pseudoasymmetric pseudo))] ∧
      sortLocalizedRerootFlatConstitutionalKeys input
        [localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo)),
         localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor))] =
      [localizedCumulativeLabelWitness input root .rule4a
         (some (.pseudoasymmetric pseudo)),
       localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor))] := by
  constructor
  · exact sortLocalizedRerootFlatConstitutionalKeys_pair_of_eq input _ _
      (compareLocalizedRerootFlatConstitutionalKeys_labelWitness input root .rule4a
        (some (.chiral descriptor)) (some (.pseudoasymmetric pseudo)))
  · exact sortLocalizedRerootFlatConstitutionalKeys_pair_of_eq input _ _
      (compareLocalizedRerootFlatConstitutionalKeys_labelWitness input root .rule4a
        (some (.pseudoasymmetric pseudo)) (some (.chiral descriptor)))

/-- **The older flat projection is wrong on the Rule-4a-separated pair.**  Its structural sort
returns the two physical input orders unchanged, so it distinguishes inputs that the actual
cumulative sort identifies. -/
theorem sortLocalizedRerootFlatConstitutionalKeys_rule4a_not_invariant
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    sortLocalizedRerootFlatConstitutionalKeys input
        [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
         localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo))] ≠
      sortLocalizedRerootFlatConstitutionalKeys input
        [localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo)),
         localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor))] := by
  have sorted :=
    sortLocalizedRerootFlatConstitutionalKeys_rule4a_chiral_pseudoasymmetric
      input root descriptor pseudo
  rw [sorted.1, sorted.2]
  intro sameList
  have sameHead :
      localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)) =
        localizedCumulativeLabelWitness input root .rule4a
          (some (.pseudoasymmetric pseudo)) := by
    have heads := congrArg List.head? sameList
    simpa using heads
  exact localizedCumulativeLabelWitness_rule4a_chiral_ne_pseudoasymmetric
    input root descriptor pseudo sameHead

/-! ## The packaged deliverable statement -/

/-- **Cumulative Rule-4a tied-child permutation invariance, with the flat-projection regression.**
For the concrete child pair that is tied under the constitutional Rules 1a/1b/2 but separated by
Rule 4a:

* the flat constitutional projection ties the pair;
* the actual cumulative comparator strictly prefers the chiral child;
* the actual cumulative staged sort returns the same list for both physical input orders;
* that sorted list is `[chiral, pseudoasymmetric]` itself;
* it is a permutation of the input, of length two, so multiplicity is preserved.

This is the complete statement requested for the cumulative Rule-4a refinement.  No equality of
retained labels or provenance is asserted, and no chemical conclusion beyond the source Rule-4a
ordering is drawn. -/
theorem sortLocalizedRerootCumulativeRule45Keys_rule4aTiedChildPermutation
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    compareLocalizedRerootFlatConstitutionalKeys input
        (localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)))
        (localizedCumulativeLabelWitness input root .rule4a
          (some (.pseudoasymmetric pseudo))) =
        Ordering.eq ∧
      input.compareLocalizedRerootCumulativeRule45Keys
        (localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)))
        (localizedCumulativeLabelWitness input root .rule4a
          (some (.pseudoasymmetric pseudo))) =
        Ordering.gt ∧
      input.sortLocalizedRerootCumulativeRule45Keys
          [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
           localizedCumulativeLabelWitness input root .rule4a
             (some (.pseudoasymmetric pseudo))] =
        input.sortLocalizedRerootCumulativeRule45Keys
          [localizedCumulativeLabelWitness input root .rule4a
             (some (.pseudoasymmetric pseudo)),
           localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor))] ∧
      input.sortLocalizedRerootCumulativeRule45Keys
          [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
           localizedCumulativeLabelWitness input root .rule4a
             (some (.pseudoasymmetric pseudo))] =
        [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
         localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo))] ∧
      (input.sortLocalizedRerootCumulativeRule45Keys
          [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
           localizedCumulativeLabelWitness input root .rule4a
             (some (.pseudoasymmetric pseudo))]).Perm
        [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
         localizedCumulativeLabelWitness input root .rule4a
           (some (.pseudoasymmetric pseudo))] ∧
      (input.sortLocalizedRerootCumulativeRule45Keys
          [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
           localizedCumulativeLabelWitness input root .rule4a
             (some (.pseudoasymmetric pseudo))]).length = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact compareLocalizedRerootFlatConstitutionalKeys_labelWitness input root .rule4a
      (some (.chiral descriptor)) (some (.pseudoasymmetric pseudo))
  · exact compareLocalizedRerootCumulativeRule45Keys_rule4a_chiral_gt_pseudoasymmetric
      input root descriptor pseudo
  · exact sortLocalizedRerootCumulativeRule45Keys_rule4a_chiral_pseudoasymmetric_commute
      input root descriptor pseudo
  · exact (sortLocalizedRerootCumulativeRule45Keys_pair_of_gt input
      (localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)))
      (localizedCumulativeLabelWitness input root .rule4a
        (some (.pseudoasymmetric pseudo)))
      (compareLocalizedRerootCumulativeRule45Keys_rule4a_chiral_gt_pseudoasymmetric
        input root descriptor pseudo)).1
  · exact sortLocalizedRerootCumulativeRule45Keys_rule4a_witness_perm
      input root descriptor pseudo
  · exact sortLocalizedRerootCumulativeRule45Keys_rule4a_witness_length
      input root descriptor pseudo

/-! ## Assembler-facing consequence -/

/-- **Assembler-facing invariance.**  The actual assembler consumes the sorted child list through
`OfficialRuleMajorKey.assemble` (for the constitutional projection) and the three
`mergeLocalizedReroot*Children` functions.  Since the cumulative sort returns the same child list
in either physical order, all four assembled child components agree.  This is the exact interface
used in the `descriptor` and `labels` fields of `buildLocalizedRerootCumulativeRule45Key?`. -/
theorem assembledChildComponents_rule4aTiedChildPermutation
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptor : RS) (pseudo : PseudoRS) :
    OfficialRuleMajorKey.assemble root
        ((input.sortLocalizedRerootCumulativeRule45Keys
          [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
           localizedCumulativeLabelWitness input root .rule4a
             (some (.pseudoasymmetric pseudo))]).map
          (fun key => key.constitutional)) =
      OfficialRuleMajorKey.assemble root
        ((input.sortLocalizedRerootCumulativeRule45Keys
          [localizedCumulativeLabelWitness input root .rule4a
             (some (.pseudoasymmetric pseudo)),
           localizedCumulativeLabelWitness input root .rule4a
             (some (.chiral descriptor))]).map
          (fun key => key.constitutional)) ∧
      input.mergeLocalizedRerootDescriptorChildren
          (input.sortLocalizedRerootCumulativeRule45Keys
            [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
             localizedCumulativeLabelWitness input root .rule4a
               (some (.pseudoasymmetric pseudo))]) =
        input.mergeLocalizedRerootDescriptorChildren
          (input.sortLocalizedRerootCumulativeRule45Keys
            [localizedCumulativeLabelWitness input root .rule4a
               (some (.pseudoasymmetric pseudo)),
             localizedCumulativeLabelWitness input root .rule4a
               (some (.chiral descriptor))]) ∧
      input.mergeLocalizedRerootLabelChildren
          (input.sortLocalizedRerootCumulativeRule45Keys
            [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
             localizedCumulativeLabelWitness input root .rule4a
               (some (.pseudoasymmetric pseudo))]) =
        input.mergeLocalizedRerootLabelChildren
          (input.sortLocalizedRerootCumulativeRule45Keys
            [localizedCumulativeLabelWitness input root .rule4a
               (some (.pseudoasymmetric pseudo)),
             localizedCumulativeLabelWitness input root .rule4a
               (some (.chiral descriptor))]) ∧
      input.mergeLocalizedRerootRankedLabelChildren
          (input.sortLocalizedRerootCumulativeRule45Keys
            [localizedCumulativeLabelWitness input root .rule4a (some (.chiral descriptor)),
             localizedCumulativeLabelWitness input root .rule4a
               (some (.pseudoasymmetric pseudo))]) =
        input.mergeLocalizedRerootRankedLabelChildren
          (input.sortLocalizedRerootCumulativeRule45Keys
            [localizedCumulativeLabelWitness input root .rule4a
               (some (.pseudoasymmetric pseudo)),
             localizedCumulativeLabelWitness input root .rule4a
               (some (.chiral descriptor))]) := by
  rw [sortLocalizedRerootCumulativeRule45Keys_rule4a_chiral_pseudoasymmetric_commute]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Kernel trust checks -/

assert_kernel_only compareSparseLayers_singleton_priority
assert_kernel_only compareLocalizedRerootCumulativeRule45Keys_of_constitutional_eq
assert_kernel_only map_sortLocalizedRerootCumulativeRule45Keys_observable_eq_of_perm
assert_kernel_only cumulativeRule4a_chiral_over_pseudoasymmetric
assert_kernel_only cumulativeRule4a_pseudoasymmetric_lt_chiral
assert_kernel_only compareLocalizedRerootCumulativeRule45Keys_labelWitness
assert_kernel_only compareLocalizedRerootCumulativeRule45Keys_rule4a_chiral_gt_pseudoasymmetric
assert_kernel_only compareLocalizedRerootCumulativeRule45Keys_rule4a_pseudoasymmetric_lt_chiral
assert_kernel_only localizedRule4aWitness_constitutional_tie
assert_kernel_only localizedCumulativeLabelWitness_rule4a_chiral_ne_pseudoasymmetric
assert_kernel_only sortLocalizedRerootCumulativeRule45Keys_pair_of_gt
assert_kernel_only sortLocalizedRerootCumulativeRule45Keys_rule4a_chiral_pseudoasymmetric_commute
assert_kernel_only sortLocalizedRerootCumulativeRule45Keys_rule4a_witness_perm
assert_kernel_only sortLocalizedRerootCumulativeRule45Keys_rule4a_witness_length
assert_kernel_only sortLocalizedRerootFlatConstitutionalKeys_pair_of_eq
assert_kernel_only compareLocalizedRerootFlatConstitutionalKeys_labelWitness
assert_kernel_only sortLocalizedRerootFlatConstitutionalKeys_rule4a_chiral_pseudoasymmetric
assert_kernel_only sortLocalizedRerootFlatConstitutionalKeys_rule4a_not_invariant
assert_kernel_only sortLocalizedRerootCumulativeRule45Keys_rule4aTiedChildPermutation
assert_kernel_only assembledChildComponents_rule4aTiedChildPermutation

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
