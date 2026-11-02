import TetraStereo.OneCenter.ExactOfficialRuleMajorKey
import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.OneCenter.PublicParametricCumulativeRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

/-!
# Exact public constitutional observables

The public exact compiler `ExactOfficialRuleMajorKey` retains a finite addressed provenance tree
(`sourceNodes`) and reads Rules 1a, 1b and 2 freshly from it.  Its comparison therefore never
consults cached projections, but it does consult the *representation* of a Rule-1a observation:
`DeclarativeCIP.ExactAtomicNumber` is deliberately unreduced (`1/2` and `2/4` are different
records), while the exact Rule-1a comparison reads only the rational `.value`.

This module isolates the comparison-visible projection of an exact public key as an
`ExactConstitutionalObservable` whose Rule-1a column stores rational **values**, so that
representationally different but numerically equal Rule-1a observations become identical.  Rules
1b and 2 stay addressed natural-number columns.

The main results are

* `compareObserved_eq_compareExactConstitutionalObservable` — the public exact comparator
  `compareObserved` is literally the observable comparator applied to the projection, for an
  arbitrary observation reader;
* `compare_eq_compareExactConstitutionalObservable` — the semantic compiler comparator `compare`
  factors the same way;
* `compareExactConstitutionalObservable_eq_iff` — the observable comparator decides equality
  exactly;
* `compareExactConstitutionalObservable_transCmp` — the observable comparator is oriented and
  transitive, hence usable in `List.Perm.eq_of_pairwise`.

Nothing here assumes the desired observable equality or a sort order; both are derived from the
comparator laws and the compiler's structural invariants.
-/

/-! ## Exact rational comparison -/

/-- Comparison of the rational values carried by exact Rule-1a observations.  This is the
canonical `LinearOrder` comparison of `ℚ`, written in the `compareOfLessAndEq` form whose laws are
available in the core library. -/
def compareExactRational (left right : ℚ) : Ordering :=
  compareOfLessAndEq left right

/-- The rational comparator decides equality exactly. -/
theorem compareExactRational_eq_iff (left right : ℚ) :
    compareExactRational left right = Ordering.eq ↔ left = right := by
  unfold compareExactRational compareOfLessAndEq
  by_cases lower : left < right
  · rw [if_pos lower]
    constructor
    · intro impossible
      cases impossible
    · intro same
      exact absurd same (ne_of_lt lower)
  · by_cases equal : left = right
    · simp [equal]
    · simp [lower, equal]

/-- The canonical `ℚ` comparison and the `compareOfLessAndEq` presentation agree.  The ambient
`Ord ℚ` instance is the computational linear-order comparison, so this is a definitional
unfolding plus the trichotomy laws. -/
theorem compare_rational_eq_compareExactRational (left right : ℚ) :
    compare left right = compareExactRational left right := by
  unfold compareExactRational compareOfLessAndEq
  change (if left ≤ right then (if right ≤ left then Ordering.eq else Ordering.lt)
      else Ordering.gt) =
    (if left < right then Ordering.lt
      else if left = right then Ordering.eq else Ordering.gt)
  by_cases lower : left ≤ right
  · rw [if_pos lower]
    by_cases upper : right ≤ left
    · rw [if_pos upper]
      have same : left = right := le_antisymm lower upper
      subst same
      simp
    · rw [if_neg upper]
      have strict : left < right := lt_of_le_not_ge lower upper
      rw [if_pos strict]
  · rw [if_neg lower]
    have strict : right < left := lt_of_not_ge lower
    have notStrict : ¬ left < right := not_lt_of_gt strict
    rw [if_neg notStrict]
    have different : left ≠ right := by
      intro same
      subst same
      exact lower (le_refl left)
    rw [if_neg different]

/-- The rational comparator is oriented and transitive. -/
theorem compareExactRational_transCmp : Std.TransCmp compareExactRational := by
  unfold compareExactRational
  exact Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    (α := ℚ)
    (fun {_ _} h₁ h₂ => le_antisymm h₁ h₂)
    (fun {_ _ _} h₁ h₂ => le_trans h₁ h₂)
    (fun left right => le_total left right)
    (fun {_ _} => not_le)

/-- Exact Rule-1a comparison reads exactly the rational values of the two observations. -/
theorem compareExactAtomicNumber_eq_value
    (left right : DeclarativeCIP.ExactAtomicNumber) :
    ExactOfficialRuleMajorKey.compareExactAtomicNumber left right =
      compareExactRational left.value right.value := by
  unfold ExactOfficialRuleMajorKey.compareExactAtomicNumber compareExactRational Ordering.byKey
  exact compare_rational_eq_compareExactRational left.value right.value

/-! ## The exact constitutional observable -/

/-- The comparison-visible projection of one exact public key.

`rule1a` stores rational **values**, not `ExactAtomicNumber` records: two representations of the
same rational observation become the same observable entry.  `rule1b` and `rule2` are the addressed
natural-number columns the public comparator reads. -/
structure ExactConstitutionalObservable where
  /-- Addressed Rule-1a observations, projected to exact rational values. -/
  rule1a : List (List (OfficialSparseEntry ℚ))
  /-- Addressed Rule-1b duplicate-atom observations. -/
  rule1b : List (List (OfficialSparseEntry ℕ))
  /-- Addressed Rule-2 isotope-mass observations. -/
  rule2 : List (List (OfficialSparseEntry ℕ))
  deriving DecidableEq

/-- Observable comparison in the public exact rule order: Rule 1a, then Rule 1b, then Rule 2. -/
def compareExactConstitutionalObservable :
    ExactConstitutionalObservable → ExactConstitutionalObservable → Ordering :=
  compareLex
    (Ordering.byKey ExactConstitutionalObservable.rule1a
      (OfficialRuleMajorKey.compareSparseLayers compareExactRational))
    (compareLex
      (Ordering.byKey ExactConstitutionalObservable.rule1b
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      (Ordering.byKey ExactConstitutionalObservable.rule2
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))

/-- Comparison-visible projection of a public exact key, relative to an arbitrary observation
reader.  The reader is used only through its rational value, so reader representations that agree
in value produce the same observable. -/
def exactConstitutionalObservableObserved {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (key : ExactOfficialRuleMajorKey V) : ExactConstitutionalObservable where
  rule1a := OfficialRuleMajorKey.mapSourceLayers
    (fun node => (observe node).value) key.sourceNodes
  rule1b := ExactOfficialRuleMajorKey.rule1bLayers key.sourceNodes
  rule2 := ExactOfficialRuleMajorKey.rule2Layers m key.sourceNodes

/-- Comparison-visible projection of a public exact key under the independent semantic Rule-1a
observation. -/
def exactConstitutionalObservable {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (key : ExactOfficialRuleMajorKey V) :
    ExactConstitutionalObservable :=
  exactConstitutionalObservableObserved m m.exactOfficialRule1aObservation key

/-! ## Pointwise value projection of addressed layers -/

/-- One addressed sphere commutes with the exact rational-value projection. -/
theorem mapObservation_value_comp {V : Type*}
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (layer : List (OfficialSparseEntry (OfficialCIPNode V))) :
    (layer.map (OfficialRuleMajorKey.mapObservation observe)).map
        (OfficialRuleMajorKey.mapObservation DeclarativeCIP.ExactAtomicNumber.value) =
      layer.map (OfficialRuleMajorKey.mapObservation (fun node => (observe node).value)) := by
  induction layer with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      obtain ⟨address, node⟩ := head
      simp only [List.map_cons, inductionHypothesis]
      rfl

/-- Projection of an addressed source layer through the exact rational value of every Rule-1a
observation. -/
theorem mapSourceLayers_value_comp {V : Type*}
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (layers : OfficialRuleMajorKey.AddressedSourceLayers V) :
    OfficialRuleMajorKey.mapSourceLayers DeclarativeCIP.ExactAtomicNumber.value
        (OfficialRuleMajorKey.mapSourceLayers observe layers) =
      OfficialRuleMajorKey.mapSourceLayers (fun node => (observe node).value) layers := by
  unfold OfficialRuleMajorKey.mapSourceLayers
  rw [List.map_map]
  exact List.map_congr_left (fun layer _ => mapObservation_value_comp observe layer)

/-- One exact addressed entry compares through `compareExactAtomicNumber` exactly as its rational
value compares through `compareExactRational`. -/
theorem compareSparseEntry_map_value
    (left right : OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber) :
    OfficialRuleMajorKey.compareSparseEntry
        ExactOfficialRuleMajorKey.compareExactAtomicNumber left right =
      OfficialRuleMajorKey.compareSparseEntry compareExactRational
        (OfficialRuleMajorKey.mapObservation DeclarativeCIP.ExactAtomicNumber.value left)
        (OfficialRuleMajorKey.mapObservation DeclarativeCIP.ExactAtomicNumber.value right) := by
  simp only [OfficialRuleMajorKey.compareSparseEntry,
    OfficialRuleMajorKey.mapObservation, Ordering.byKey, compareLex,
    compareExactAtomicNumber_eq_value]

/-- One addressed exact sphere compares identically after projecting every entry to its rational
value. -/
theorem compareSparseLayer_map_value :
    ∀ (left right : List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber)),
      OfficialRuleMajorKey.compareSparseLayer
          ExactOfficialRuleMajorKey.compareExactAtomicNumber left right =
        OfficialRuleMajorKey.compareSparseLayer compareExactRational
          (left.map (OfficialRuleMajorKey.mapObservation
            DeclarativeCIP.ExactAtomicNumber.value))
          (right.map (OfficialRuleMajorKey.mapObservation
            DeclarativeCIP.ExactAtomicNumber.value)) := by
  unfold OfficialRuleMajorKey.compareSparseLayer
  intro left
  induction left with
  | nil =>
      intro right
      cases right <;> rfl
  | cons head tail inductionHypothesis =>
      intro right
      cases right with
      | nil => rfl
      | cons otherHead otherTail =>
          rw [List.map_cons, List.map_cons, List.compareLex_cons_cons,
            List.compareLex_cons_cons]
          rw [compareSparseEntry_map_value head otherHead]
          cases OfficialRuleMajorKey.compareSparseEntry compareExactRational
            (OfficialRuleMajorKey.mapObservation DeclarativeCIP.ExactAtomicNumber.value head)
            (OfficialRuleMajorKey.mapObservation DeclarativeCIP.ExactAtomicNumber.value
              otherHead) with
          | lt => rfl
          | gt => rfl
          | eq => simpa using inductionHypothesis otherTail

/-- Exhaustive exact Rule-1a sphere comparison is exactly rational-value sphere comparison. -/
theorem compareSparseLayers_map_value :
    ∀ (left right : List (List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber))),
      OfficialRuleMajorKey.compareSparseLayers
          ExactOfficialRuleMajorKey.compareExactAtomicNumber left right =
        OfficialRuleMajorKey.compareSparseLayers compareExactRational
          (OfficialRuleMajorKey.mapSourceLayers
            DeclarativeCIP.ExactAtomicNumber.value left)
          (OfficialRuleMajorKey.mapSourceLayers
            DeclarativeCIP.ExactAtomicNumber.value right) := by
  unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.mapSourceLayers
  intro left
  induction left with
  | nil =>
      intro right
      cases right <;> rfl
  | cons head tail inductionHypothesis =>
      intro right
      cases right with
      | nil => rfl
      | cons otherHead otherTail =>
          simp only [List.map_cons]
          rw [List.compareLex_cons_cons, List.compareLex_cons_cons]
          rw [compareSparseLayer_map_value head otherHead]
          cases OfficialRuleMajorKey.compareSparseLayer compareExactRational
            (head.map (OfficialRuleMajorKey.mapObservation
              DeclarativeCIP.ExactAtomicNumber.value))
            (otherHead.map (OfficialRuleMajorKey.mapObservation
              DeclarativeCIP.ExactAtomicNumber.value)) with
          | lt => rfl
          | gt => rfl
          | eq => simpa using inductionHypothesis otherTail

/-- Rule-1a sphere comparison of an arbitrary observation reader is exactly rational-value
comparison of the projected observations. -/
theorem compareSparseLayers_observed_value {V : Type*}
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (left right : OfficialRuleMajorKey.AddressedSourceLayers V) :
    OfficialRuleMajorKey.compareSparseLayers
        ExactOfficialRuleMajorKey.compareExactAtomicNumber
        (OfficialRuleMajorKey.mapSourceLayers observe left)
        (OfficialRuleMajorKey.mapSourceLayers observe right) =
      OfficialRuleMajorKey.compareSparseLayers compareExactRational
        (OfficialRuleMajorKey.mapSourceLayers (fun node => (observe node).value) left)
        (OfficialRuleMajorKey.mapSourceLayers (fun node => (observe node).value) right) := by
  rw [compareSparseLayers_map_value]
  rw [mapSourceLayers_value_comp observe left, mapSourceLayers_value_comp observe right]

/-! ## Factorization through the observable -/

/-- The public exact comparator with an arbitrary observation reader is exactly the observable
comparator applied to the reader-relative projection. -/
theorem compareObserved_eq_compareExactConstitutionalObservable
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (left right : ExactOfficialRuleMajorKey V) :
    ExactOfficialRuleMajorKey.compareObserved m observe left right =
      compareExactConstitutionalObservable
        (exactConstitutionalObservableObserved m observe left)
        (exactConstitutionalObservableObserved m observe right) := by
  simp only [ExactOfficialRuleMajorKey.compareObserved,
    ExactOfficialRuleMajorKey.compareAddressedSourcesObserved,
    ExactOfficialRuleMajorKey.observedRule1aLayers,
    ExactOfficialRuleMajorKey.rule1bLayers, ExactOfficialRuleMajorKey.rule2Layers,
    compareExactConstitutionalObservable, exactConstitutionalObservableObserved,
    Ordering.byKey, compareLex, compareSparseLayers_observed_value]

/-- The semantic public exact comparator is exactly the observable comparator applied to the
semantic projection. -/
theorem compare_eq_compareExactConstitutionalObservable
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V) :
    ExactOfficialRuleMajorKey.compare m left right =
      compareExactConstitutionalObservable
        (exactConstitutionalObservable m left)
        (exactConstitutionalObservable m right) := by
  have factored := compareObserved_eq_compareExactConstitutionalObservable m
    m.exactOfficialRule1aObservation left right
  rw [ExactOfficialRuleMajorKey.compareObserved_eq_exact m m.exactOfficialRule1aObservation
    (fun _ => rfl)] at factored
  unfold exactConstitutionalObservable
  exact factored

/-- Readers that agree on every rational Rule-1a value induce the same observable on every key. -/
theorem exactConstitutionalObservableObserved_congr
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    {left right : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber}
    (agree : ∀ node, (left node).value = (right node).value)
    (key : ExactOfficialRuleMajorKey V) :
    exactConstitutionalObservableObserved m left key =
      exactConstitutionalObservableObserved m right key := by
  unfold exactConstitutionalObservableObserved
  rw [show (fun node => (left node).value) = fun node => (right node).value from
    funext agree]

/-- Readers that agree on every rational Rule-1a value induce the same public exact comparator. -/
theorem compareObserved_congr_of_value
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    {left right : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber}
    (agree : ∀ node, (left node).value = (right node).value)
    (first second : ExactOfficialRuleMajorKey V) :
    ExactOfficialRuleMajorKey.compareObserved m left first second =
      ExactOfficialRuleMajorKey.compareObserved m right first second := by
  rw [compareObserved_eq_compareExactConstitutionalObservable m left first second,
    compareObserved_eq_compareExactConstitutionalObservable m right first second,
    exactConstitutionalObservableObserved_congr m agree first,
    exactConstitutionalObservableObserved_congr m agree second]

/-! ## Exactness and ordering laws of the observable comparator -/

/-- The observable comparator decides equality exactly. -/
theorem compareExactConstitutionalObservable_eq_iff
    (left right : ExactConstitutionalObservable) :
    compareExactConstitutionalObservable left right = Ordering.eq ↔ left = right := by
  have rule1aCompare : OfficialRuleMajorKey.compareSparseLayers compareExactRational
      left.rule1a right.rule1a = Ordering.eq ↔ left.rule1a = right.rule1a :=
    CertifiedLocalizedCIPInput.compareSparseLayers_eq_iff compareExactRational
      compareExactRational_eq_iff left.rule1a right.rule1a
  have rule1bCompare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      left.rule1b right.rule1b = Ordering.eq ↔ left.rule1b = right.rule1b :=
    CertifiedLocalizedCIPInput.compareSparseLayers_compareRule1b_eq_iff left.rule1b right.rule1b
  have rule2Compare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule2 right.rule2 = Ordering.eq ↔ left.rule2 = right.rule2 :=
    CertifiedLocalizedCIPInput.compareSparseLayers_compareNat_eq_iff left.rule2 right.rule2
  rw [compareExactConstitutionalObservable, compareLex_eq_eq, compareLex_eq_eq]
  simp only [Ordering.byKey, rule1aCompare, rule1bCompare, rule2Compare]
  constructor
  · rintro ⟨h1a, h1b, h2⟩
    cases left
    cases right
    simp_all
  · intro equal
    rw [equal]
    exact ⟨rfl, rfl, rfl⟩

/-- The observable comparator is oriented and transitive. -/
theorem compareExactConstitutionalObservable_transCmp :
    Std.TransCmp compareExactConstitutionalObservable := by
  letI : Std.TransCmp compareExactRational := compareExactRational_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat :=
    inferInstanceAs (Std.TransCmp (compare : ℕ → ℕ → Ordering))
  letI : Std.TransCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  have rule1aLayersTrans :
      Std.TransCmp (OfficialRuleMajorKey.compareSparseLayers compareExactRational) := by
    unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
      OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  have rule1bLayersTrans :
      Std.TransCmp (OfficialRuleMajorKey.compareSparseLayers
        OfficialRuleMajorKey.compareRule1b) := by
    unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
      OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  have rule2LayersTrans :
      Std.TransCmp (OfficialRuleMajorKey.compareSparseLayers
        OfficialRuleMajorKey.compareNat) := by
    unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
      OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  letI : Std.TransCmp
      (OfficialRuleMajorKey.compareSparseLayers compareExactRational) := rule1aLayersTrans
  letI : Std.TransCmp
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b) :=
    rule1bLayersTrans
  letI : Std.TransCmp
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat) := rule2LayersTrans
  rw [show compareExactConstitutionalObservable =
      compareLex
        (Ordering.byKey ExactConstitutionalObservable.rule1a
          (OfficialRuleMajorKey.compareSparseLayers compareExactRational))
        (compareLex
          (Ordering.byKey ExactConstitutionalObservable.rule1b
            (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
          (Ordering.byKey ExactConstitutionalObservable.rule2
            (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))
      from rfl]
  infer_instance

/-! ## Sorted permutation uniqueness -/

/-- A descending list of exact public keys has a descending list of observables.  No order is
assumed here: the implication is derived from the factorization of `compareObserved` through the
observable. -/
theorem exactObservable_pairwise_of_descending
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    {keys : List (ExactOfficialRuleMajorKey V)}
    (descending : keys.Pairwise fun left right =>
      ExactOfficialRuleMajorKey.compareObserved m observe left right ≠ Ordering.lt) :
    (keys.map (exactConstitutionalObservableObserved m observe)).Pairwise
      fun left right => compareExactConstitutionalObservable left right ≠ Ordering.lt := by
  induction keys with
  | nil => exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.pairwise_cons]
      rw [List.pairwise_cons] at descending
      refine ⟨?_, inductionHypothesis descending.2⟩
      intro other present
      rw [List.mem_map] at present
      obtain ⟨child, _, same⟩ := present
      subst same
      rw [← compareObserved_eq_compareExactConstitutionalObservable m observe head child]
      exact descending.1 child ‹child ∈ tail›

/-- **Sorted permutation uniqueness.**  Two sibling lists that are both descending for the public
exact comparator and that are permutations of one another have *equal* observable lists.  This is
the multiset-to-sequence step: the sorted sequence of constitutional observables is determined by
the multiset of sibling observables, independently of tie order, provenance representation or the
auxiliary observation reader. -/
theorem exactConstitutionalObservables_eq_of_perm
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    {first second : List (ExactOfficialRuleMajorKey V)}
    (firstDescending : first.Pairwise fun left right =>
      ExactOfficialRuleMajorKey.compareObserved m observe left right ≠ Ordering.lt)
    (secondDescending : second.Pairwise fun left right =>
      ExactOfficialRuleMajorKey.compareObserved m observe left right ≠ Ordering.lt)
    (permutation : first.Perm second) :
    first.map (exactConstitutionalObservableObserved m observe) =
      second.map (exactConstitutionalObservableObserved m observe) := by
  haveI : Std.TransCmp compareExactConstitutionalObservable :=
    compareExactConstitutionalObservable_transCmp
  refine List.Perm.eq_of_pairwise
    (le := fun left right => compareExactConstitutionalObservable left right ≠ Ordering.lt)
    ?_ ?_ ?_ (permutation.map (exactConstitutionalObservableObserved m observe))
  · intro left right _ _ leftLe rightLe
    exact (compareExactConstitutionalObservable_eq_iff left right).mp (by
      refine Ordering.eq_eq_of_isLE_of_isGE ?_ (Ordering.ne_lt_iff_isGE.mp leftLe)
      rw [← Std.OrientedCmp.isGE_eq_isLE]
      exact Ordering.ne_lt_iff_isGE.mp rightLe)
  · exact exactObservable_pairwise_of_descending m observe firstDescending
  · exact exactObservable_pairwise_of_descending m observe secondDescending

/-! ## Addressed merge and assembly of observables -/

/-- Maximum sphere count of a sibling list of addressed layer bundles, for an arbitrary
observation type. -/
def addressedLayerCount {α : Type*}
    (children : List (List (List (OfficialSparseEntry α)))) : ℕ :=
  children.foldl (fun longest child => max longest child.length) 0

/-- Parent-slot-addressed merge of sibling layer bundles, for an arbitrary observation type. -/
def mergeAddressedLayers {α : Type*}
    (children : List (List (List (OfficialSparseEntry α)))) :
    List (List (OfficialSparseEntry α)) :=
  let count := addressedLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.getD depth [])

/-- The maximum sphere count is unchanged by projecting every observation. -/
theorem addressedLayerCount_mapSourceLayers {V α : Type*}
    (observe : V → α)
    (children : List (List (List (OfficialSparseEntry V)))) :
    addressedLayerCount (children.map (OfficialRuleMajorKey.mapSourceLayers observe)) =
      addressedLayerCount children := by
  unfold addressedLayerCount
  have generalized : ∀ initial,
      List.foldl (fun longest child => max longest child.length) initial
          (children.map (OfficialRuleMajorKey.mapSourceLayers observe)) =
        List.foldl (fun longest child => max longest child.length) initial children := by
    induction children with
    | nil => intro initial; rfl
    | cons head tail inductionHypothesis =>
        intro initial
        simp only [List.map_cons, List.foldl_cons,
          OfficialRuleMajorKey.mapSourceLayers, List.length_map]
        exact inductionHypothesis _
  exact generalized 0

/-- Projecting an addressed merge is the addressed merge of the projected children. -/
theorem mapSourceLayers_mergeAddressedLayers {V α : Type*}
    (observe : V → α)
    (children : List (List (List (OfficialSparseEntry V)))) :
    OfficialRuleMajorKey.mapSourceLayers observe (mergeAddressedLayers children) =
      mergeAddressedLayers (children.map (OfficialRuleMajorKey.mapSourceLayers observe)) := by
  have perDepth : ∀ depth : ℕ,
      (children.zipIdx.flatMap fun child =>
          OfficialRuleMajorKey.prefixLayer child.2 (child.1.getD depth [])).map
        (OfficialRuleMajorKey.mapObservation observe) =
      (children.map (OfficialRuleMajorKey.mapSourceLayers observe)).zipIdx.flatMap
        fun child => OfficialRuleMajorKey.prefixLayer child.2 (child.1.getD depth []) := by
    intro depth
    rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr ?_
    intro child _
    obtain ⟨source, slot⟩ := child
    rw [← OfficialRuleMajorKey.prefixLayer_mapObservation,
      ← OfficialRuleMajorKey.mapSourceLayers_getD]
    rfl
  unfold mergeAddressedLayers
  rw [addressedLayerCount_mapSourceLayers observe children]
  unfold OfficialRuleMajorKey.mapSourceLayers
  rw [List.map_map]
  exact List.map_congr_left (fun depth _ => perDepth depth)

/-- The compiler's provenance-tree merge projects exactly as the addressed observable merge. -/
theorem mapSourceLayers_mergeAddressedChildren {V α : Type*}
    (observe : OfficialCIPNode V → α)
    (children : List (OfficialRuleMajorKey.AddressedSourceLayers V)) :
    OfficialRuleMajorKey.mapSourceLayers observe
        (OfficialRuleMajorKey.mergeAddressedChildren children) =
      mergeAddressedLayers
        (children.map (OfficialRuleMajorKey.mapSourceLayers observe)) :=
  mapSourceLayers_mergeAddressedLayers observe children

/-- Assembly of observables: the root observable followed by the parent-slot-addressed merge of
the child observables. -/
def assembleConstitutionalObservable (root : ExactConstitutionalObservable)
    (children : List ExactConstitutionalObservable) : ExactConstitutionalObservable where
  rule1a := root.rule1a ++ mergeAddressedLayers
    (children.map ExactConstitutionalObservable.rule1a)
  rule1b := root.rule1b ++ mergeAddressedLayers
    (children.map ExactConstitutionalObservable.rule1b)
  rule2 := root.rule2 ++ mergeAddressedLayers
    (children.map ExactConstitutionalObservable.rule2)

/-- **Assembly factorization.**  The constitutional observable of an assembled exact public key is
the assembly of the root observable with the observable sequence of the sorted children.  It
depends on the children only through their observables. -/
theorem exactConstitutionalObservableObserved_assemble
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (root : ExactOfficialRuleMajorKey V)
    (children : List (ExactOfficialRuleMajorKey V)) :
    exactConstitutionalObservableObserved m observe
        (ExactOfficialRuleMajorKey.assemble root children) =
      assembleConstitutionalObservable
        (exactConstitutionalObservableObserved m observe root)
        (children.map (exactConstitutionalObservableObserved m observe)) := by
  unfold exactConstitutionalObservableObserved ExactOfficialRuleMajorKey.assemble
    ExactOfficialRuleMajorKey.rule1bLayers ExactOfficialRuleMajorKey.rule2Layers
    assembleConstitutionalObservable
  simp only [OfficialRuleMajorKey.mapSourceLayers_append,
    mapSourceLayers_mergeAddressedChildren, List.map_map, Function.comp_def]

/-- Assembled observables depend only on the root observable and the child observable sequence. -/
theorem assembleConstitutionalObservable_congr
    {root root' : ExactConstitutionalObservable}
    {children children' : List ExactConstitutionalObservable}
    (rootEq : root = root') (childrenEq : children = children') :
    assembleConstitutionalObservable root children =
      assembleConstitutionalObservable root' children' := by
  rw [rootEq, childrenEq]

/-- Two sorted sibling lists with equal observable sequences assemble to equal observables. -/
theorem exactConstitutionalObserved_assemble_of_observables_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (root : ExactOfficialRuleMajorKey V)
    {first second : List (ExactOfficialRuleMajorKey V)}
    (observablesEq :
      first.map (exactConstitutionalObservableObserved m observe) =
        second.map (exactConstitutionalObservableObserved m observe)) :
    exactConstitutionalObservableObserved m observe
        (ExactOfficialRuleMajorKey.assemble root first) =
      exactConstitutionalObservableObserved m observe
        (ExactOfficialRuleMajorKey.assemble root second) := by
  rw [exactConstitutionalObservableObserved_assemble m observe root first,
    exactConstitutionalObservableObserved_assemble m observe root second, observablesEq]

/-! ## Sorted permutation uniqueness on observables -/

/-- **Sorted permutation uniqueness on observables.**  Two descending lists of constitutional
observables that are permutations of one another are equal.  This is stated directly on
observables so that sibling lists whose *keys* differ but whose observables agree can be compared. -/
theorem exactConstitutionalObservable_eq_of_perm
    {first second : List ExactConstitutionalObservable}
    (firstDescending : first.Pairwise fun left right =>
      compareExactConstitutionalObservable left right ≠ Ordering.lt)
    (secondDescending : second.Pairwise fun left right =>
      compareExactConstitutionalObservable left right ≠ Ordering.lt)
    (permutation : first.Perm second) : first = second := by
  haveI : Std.TransCmp compareExactConstitutionalObservable :=
    compareExactConstitutionalObservable_transCmp
  refine List.Perm.eq_of_pairwise
    (le := fun left right => compareExactConstitutionalObservable left right ≠ Ordering.lt)
    ?_ firstDescending secondDescending permutation
  intro left right _ _ leftLe rightLe
  exact (compareExactConstitutionalObservable_eq_iff left right).mp (by
    refine Ordering.eq_eq_of_isLE_of_isGE ?_ (Ordering.ne_lt_iff_isGE.mp leftLe)
    rw [← Std.OrientedCmp.isGE_eq_isLE]
    exact Ordering.ne_lt_iff_isGE.mp rightLe)

/-- Changing the sibling ordering among keys with the same public exact comparison data leaves the
assembled constitutional observable unchanged. -/
theorem exactConstitutionalObservableObserved_assemble_eq_of_perm
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (root : ExactOfficialRuleMajorKey V)
    {first second : List (ExactOfficialRuleMajorKey V)}
    (firstDescending : first.Pairwise fun left right =>
      ExactOfficialRuleMajorKey.compareObserved m observe left right ≠ Ordering.lt)
    (secondDescending : second.Pairwise fun left right =>
      ExactOfficialRuleMajorKey.compareObserved m observe left right ≠ Ordering.lt)
    (permutation : first.Perm second) :
    exactConstitutionalObservableObserved m observe
        (ExactOfficialRuleMajorKey.assemble root first) =
      exactConstitutionalObservableObserved m observe
        (ExactOfficialRuleMajorKey.assemble root second) :=
  exactConstitutionalObserved_assemble_of_observables_eq m observe root
    (exactConstitutionalObservables_eq_of_perm m observe
      firstDescending secondDescending permutation)

namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-- The exact public constitutional observable of a standalone exact public key, read through the
semantic exact Rule-1a observation used by the public cumulative comparator. -/
def exactOfficialRuleMajorConstitutionalObservable
    (source : AuthoritativeChemicalInput)
    (key : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom) :
    ExactConstitutionalObservable :=
  exactConstitutionalObservableObserved source.molecule.toLocalizedMoleculeGraph
    source.molecule.semanticExactOfficialRule1aObservation key

/-- The exact public constitutional observable of a source-canonical cumulative Rules-4a--5 key,
read through the semantic exact Rule-1a observation used by the public cumulative comparator. -/
def cumulativeRule45ConstitutionalObservable
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalCumulativeRule45Key) : ExactConstitutionalObservable :=
  exactConstitutionalObservableObserved source.molecule.toLocalizedMoleculeGraph
    source.molecule.semanticExactOfficialRule1aObservation key.constitutional

/-- The constitutional component of the public cumulative comparator read as an observable
comparison. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_constitutional_not_lt
    (source : AuthoritativeChemicalInput)
    {left right : source.AromaticCanonicalCumulativeRule45Key}
    (notLt : source.compareAromaticCanonicalCumulativeRule45Keys left right ≠ Ordering.lt) :
    ExactOfficialRuleMajorKey.compareObserved source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      left.constitutional right.constitutional ≠ Ordering.lt := by
  intro constitutionalLt
  apply notLt
  unfold compareAromaticCanonicalCumulativeRule45Keys compareLex
  rw [show Ordering.byKey (fun key => key.constitutional)
        (ExactOfficialRuleMajorKey.compareObserved
          source.molecule.toLocalizedMoleculeGraph
          source.molecule.semanticExactOfficialRule1aObservation) left right = Ordering.lt
      from constitutionalLt]
  rfl

/-- A cumulative key comparison that is not `lt` gives a constitutional observable comparison that
is not `lt`.  Equal constitutional components therefore have equal observables. -/
theorem cumulativeRule45ConstitutionalObservable_not_lt
    (source : AuthoritativeChemicalInput)
    {left right : source.AromaticCanonicalCumulativeRule45Key}
    (notLt : source.compareAromaticCanonicalCumulativeRule45Keys left right ≠ Ordering.lt) :
    compareExactConstitutionalObservable
        (cumulativeRule45ConstitutionalObservable source left)
        (cumulativeRule45ConstitutionalObservable source right) ≠ Ordering.lt := by
  intro observableLt
  apply compareAromaticCanonicalCumulativeRule45Keys_constitutional_not_lt source notLt
  rw [compareObserved_eq_compareExactConstitutionalObservable]
  exact observableLt

/-- Assembly factorization for the exact public observable: assembly of exact keys projects to
assembly of the root observable with the child observable sequence. -/
theorem exactOfficialRuleMajorConstitutionalObservable_assemble
    (source : AuthoritativeChemicalInput)
    (root : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom)
    (children : List (ExactOfficialRuleMajorKey source.AromaticCanonicalAtom)) :
    exactOfficialRuleMajorConstitutionalObservable source
        (ExactOfficialRuleMajorKey.assemble root children) =
      assembleConstitutionalObservable
        (exactOfficialRuleMajorConstitutionalObservable source root)
        (children.map (exactOfficialRuleMajorConstitutionalObservable source)) :=
  exactConstitutionalObservableObserved_assemble _ _ root children

universe u

/-- The `Bind`-class syntactic form of `Option.bind_some`.  `do`-notation elaborates through the
`Bind` instance projection, so core's `Option.bind_some` (stated for `Option.bind`) does not match
the elaborated term syntactically even though the two are definitionally equal. -/
private theorem bind_some_option {α β : Type u} (value : α) (next : α → Option β) :
    Bind.bind (some value) next = next value := rfl

/-- The `Bind`-class syntactic form of `Option.bind_none`. -/
private theorem bind_none_option {α β : Type u} (next : α → Option β) :
    Bind.bind (none : Option α) next = none := rfl

/-- Pointwise agreement of the projected options lifts through `List.mapM`. -/
private theorem list_mapM_map_projection {α β γ : Type*}
    (first second : α → Option β) (project : β → γ)
    (agrees : ∀ value, (first value).map project = (second value).map project) :
    ∀ values : List α,
      (values.mapM first).map (List.map project) =
        (values.mapM second).map (List.map project)
  | [] => rfl
  | value :: values => by
      rw [List.mapM_cons, List.mapM_cons]
      have inner : ∀ chosen : β,
          Option.map (List.map project)
              ((values.mapM first).bind (fun rest => some (chosen :: rest))) =
            Option.map (List.map project)
              ((values.mapM second).bind (fun rest => some (chosen :: rest))) := by
        intro chosen
        rw [Option.map_bind, Option.map_bind]
        show (values.mapM first).bind
              (fun rest => some (project chosen :: List.map project rest)) =
            (values.mapM second).bind
              (fun rest => some (project chosen :: List.map project rest))
        have firstNormalized :
            (values.mapM first).bind
                (fun rest => some (project chosen :: List.map project rest)) =
              (values.mapM first).map
                (fun rest => project chosen :: List.map project rest) := by
          cases List.mapM first values <;> rfl
        have secondNormalized :
            (values.mapM second).bind
                (fun rest => some (project chosen :: List.map project rest)) =
              (values.mapM second).map
                (fun rest => project chosen :: List.map project rest) := by
          cases List.mapM second values <;> rfl
        rw [firstNormalized, secondNormalized]
        have combined := congrArg
          (Option.map (fun rest : List γ => project chosen :: rest))
          (list_mapM_map_projection first second project agrees values)
        rw [Option.map_map, Option.map_map] at combined
        exact combined
      cases firstComputed : first value with
      | none =>
          have secondComputed : second value = none := by
            have pointwise := agrees value
            rw [firstComputed] at pointwise
            cases secondValue : second value with
            | none => rfl
            | some _ => simp [secondValue] at pointwise
          rw [secondComputed]
          rfl
      | some head =>
          have secondValue :
              ∃ other, second value = some other ∧ project head = project other := by
            have pointwise := agrees value
            rw [firstComputed] at pointwise
            cases secondComputed : second value with
            | none => simp [secondComputed] at pointwise
            | some other =>
                simp [secondComputed] at pointwise
                exact ⟨other, rfl, pointwise⟩
          obtain ⟨other, secondComputed, projectionEq⟩ := secondValue
          rw [secondComputed]
          show Option.map (List.map project)
                ((values.mapM first).bind (fun rest => some (head :: rest))) =
              Option.map (List.map project)
                ((values.mapM second).bind (fun rest => some (other :: rest)))
          rw [inner head]
          rw [Option.map_bind, Option.map_bind]
          show (values.mapM second).bind
                (fun rest => some (project head :: List.map project rest)) =
              (values.mapM second).bind
                (fun rest => some (project other :: List.map project rest))
          rw [projectionEq]

/-- **Observable independence from the auxiliary label reader.**  Two actual public cumulative
Rules-4a--5 builds at the same fuel and cursor, driven by *arbitrary* label readers, have the same
exact constitutional observable.  Sibling order may differ between the readers, because the
recursive sort uses the later-rule descriptor as a tie-break; the proof passes through sorted
permutation uniqueness of observables and the addressed-merge factorization, and never assumes
that the sorted orders agree. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage first fuel cursor).map
          (cumulativeRule45ConstitutionalObservable source) =
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage second fuel cursor).map
          (cumulativeRule45ConstitutionalObservable source)
  | 0, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      simp only [aromaticCanonicalRerootChildren?]
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal, cumulativeRule45ConstitutionalObservable]
      · simp [children, terminal]
  | fuel + 1, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      simp only [aromaticCanonicalRerootChildren?]
      by_cases terminal : source.aromaticCanonicalRerootChildren cursor = []
      · simp only [bind_some_option, if_pos terminal, Option.map_some,
          cumulativeRule45ConstitutionalObservable]
      · simp only [bind_some_option, if_neg terminal]
        have mapProjectionEq :
            ((source.aromaticCanonicalRerootChildren cursor).mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  stage first fuel)).map
                (List.map (cumulativeRule45ConstitutionalObservable source)) =
              ((source.aromaticCanonicalRerootChildren cursor).mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  stage second fuel)).map
                (List.map (cumulativeRule45ConstitutionalObservable source)) :=
          list_mapM_map_projection
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage first fuel)
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage second fuel)
            (cumulativeRule45ConstitutionalObservable source)
            (fun child =>
              buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq
                source stage first second fuel child)
            (source.aromaticCanonicalRerootChildren cursor)
        cases firstComputed : (source.aromaticCanonicalRerootChildren cursor).mapM
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage first fuel) with
        | none =>
            have secondComputed : (source.aromaticCanonicalRerootChildren cursor).mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage second fuel) =
                  none := by
              cases secondValue : (source.aromaticCanonicalRerootChildren cursor).mapM
                  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                    stage second fuel) with
              | none => rfl
              | some _ => simp [firstComputed, secondValue] at mapProjectionEq
            simp only [secondComputed, bind_none_option]
        | some firstKeys =>
            cases secondComputed : (source.aromaticCanonicalRerootChildren cursor).mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage second fuel) with
            | none => simp [firstComputed, secondComputed] at mapProjectionEq
            | some secondKeys =>
                have observablesEq :
                    firstKeys.map (cumulativeRule45ConstitutionalObservable source) =
                      secondKeys.map (cumulativeRule45ConstitutionalObservable source) := by
                  simp [firstComputed, secondComputed] at mapProjectionEq
                  exact mapProjectionEq
                have sortedMapEq :
                    (sortAromaticCanonicalCumulativeRule45Keys
                        source.compareAromaticCanonicalCumulativeRule45Keys firstKeys).map
                        (cumulativeRule45ConstitutionalObservable source) =
                      (sortAromaticCanonicalCumulativeRule45Keys
                        source.compareAromaticCanonicalCumulativeRule45Keys secondKeys).map
                        (cumulativeRule45ConstitutionalObservable source) := by
                  haveI : Std.TransCmp source.compareAromaticCanonicalCumulativeRule45Keys :=
                    source.compareAromaticCanonicalCumulativeRule45Keys_transCmp
                  have firstPerm :=
                    (sortAromaticCanonicalCumulativeRule45Keys_perm
                      source.compareAromaticCanonicalCumulativeRule45Keys firstKeys).map
                      (cumulativeRule45ConstitutionalObservable source)
                  have secondPerm :=
                    (sortAromaticCanonicalCumulativeRule45Keys_perm
                      source.compareAromaticCanonicalCumulativeRule45Keys secondKeys).map
                      (cumulativeRule45ConstitutionalObservable source)
                  refine exactConstitutionalObservable_eq_of_perm ?_ ?_ ?_
                  · exact (sortAromaticCanonicalCumulativeRule45Keys_descending
                        source.compareAromaticCanonicalCumulativeRule45Keys firstKeys).map
                      (cumulativeRule45ConstitutionalObservable source)
                      (fun left right notLt =>
                        cumulativeRule45ConstitutionalObservable_not_lt source notLt)
                  · exact (sortAromaticCanonicalCumulativeRule45Keys_descending
                        source.compareAromaticCanonicalCumulativeRule45Keys secondKeys).map
                      (cumulativeRule45ConstitutionalObservable source)
                      (fun left right notLt =>
                        cumulativeRule45ConstitutionalObservable_not_lt source notLt)
                  · refine firstPerm.trans ?_
                    rw [observablesEq]
                    exact secondPerm.symm
                simp only [bind_some_option, Option.map_some, Option.some.injEq,
                  cumulativeRule45ConstitutionalObservable]
                rw [exactConstitutionalObservableObserved_assemble,
                  exactConstitutionalObservableObserved_assemble]
                have mapRewrite : ∀ (keys : List source.AromaticCanonicalCumulativeRule45Key),
                    (keys.map (fun child => child.constitutional)).map
                        (exactConstitutionalObservableObserved
                          source.molecule.toLocalizedMoleculeGraph
                          source.molecule.semanticExactOfficialRule1aObservation) =
                      keys.map (cumulativeRule45ConstitutionalObservable source) := by
                  intro keys
                  rw [List.map_map]
                  rfl
                rw [mapRewrite, mapRewrite, sortedMapEq]

/-- **Successful-shape observable independence from the auxiliary label reader.**  If two actual
public cumulative Rules-4a--5 builds driven by arbitrary readers both succeed at the same fuel and
cursor, the resulting keys have the same exact constitutional observable.  This is the
success-form companion of
`buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq`, which also covers
the fail-closed `none` outcomes. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq_of_success
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey : source.AromaticCanonicalCumulativeRule45Key}
    (firstComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      stage first fuel cursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      stage second fuel cursor = some secondKey) :
    cumulativeRule45ConstitutionalObservable source firstKey =
      cumulativeRule45ConstitutionalObservable source secondKey := by
  have combined :=
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq
      source stage first second fuel cursor
  rw [firstComputed, secondComputed] at combined
  simpa using combined

end AuthoritativeChemicalInput

end

assert_kernel_only compareExactRational_eq_iff
assert_kernel_only compare_rational_eq_compareExactRational
assert_kernel_only compareExactRational_transCmp
assert_kernel_only compareExactAtomicNumber_eq_value
assert_kernel_only mapObservation_value_comp
assert_kernel_only mapSourceLayers_value_comp
assert_kernel_only compareSparseEntry_map_value
assert_kernel_only compareSparseLayer_map_value
assert_kernel_only compareSparseLayers_map_value
assert_kernel_only compareSparseLayers_observed_value
assert_kernel_only compareObserved_eq_compareExactConstitutionalObservable
assert_kernel_only compare_eq_compareExactConstitutionalObservable
assert_kernel_only exactConstitutionalObservableObserved_congr
assert_kernel_only compareObserved_congr_of_value
assert_kernel_only compareExactConstitutionalObservable_eq_iff
assert_kernel_only compareExactConstitutionalObservable_transCmp
assert_kernel_only exactConstitutionalObservable_eq_of_perm
assert_kernel_only exactConstitutionalObservableObserved_assemble_eq_of_perm
assert_kernel_only AuthoritativeChemicalInput.exactOfficialRuleMajorConstitutionalObservable
assert_kernel_only AuthoritativeChemicalInput.cumulativeRule45ConstitutionalObservable
assert_kernel_only AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_constitutional_not_lt
assert_kernel_only AuthoritativeChemicalInput.cumulativeRule45ConstitutionalObservable_not_lt
assert_kernel_only AuthoritativeChemicalInput.exactOfficialRuleMajorConstitutionalObservable_assemble
assert_kernel_only AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq
assert_kernel_only AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq_of_success
assert_kernel_only exactConstitutionalObservable
assert_kernel_only compareExactConstitutionalObservable
assert_kernel_only exactConstitutionalObservableObserved
assert_kernel_only exactObservable_pairwise_of_descending
assert_kernel_only addressedLayerCount
assert_kernel_only mergeAddressedLayers
assert_kernel_only addressedLayerCount_mapSourceLayers
assert_kernel_only mapSourceLayers_mergeAddressedLayers
assert_kernel_only mapSourceLayers_mergeAddressedChildren
assert_kernel_only assembleConstitutionalObservable
assert_kernel_only exactConstitutionalObservableObserved_assemble
assert_kernel_only assembleConstitutionalObservable_congr
assert_kernel_only exactConstitutionalObserved_assemble_of_observables_eq

end TetraStereo.OneCenter
