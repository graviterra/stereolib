import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

/-!
# Recursive Rules-1a--3 hierarchy with addressed Rule-3 observations

This module extends the existing constitutional compiled-key assembly
(`canonicalRootKeyAuthoritative?` / `assembleCanonicalBranchKey`) with Rule-3 geometry
observations.  It does not define a second constitutional solver and does not inspect stereo
perception: the caller supplies the child enumerator and the node observation function.

The comparison-visible projection is the address-aligned Rule-1a, Rule-1b, Rule-2 and Rule-3
table plus the completeness flag.  Rule-1a labels are projected from `CIPAtomicLabel` to `Rat`
along the exact comparator, so syntactically different representatives of one rational label
(`6/2` and `3/1`) become identical in the projection.  Rule-1b uses the existing reversed root
distance order, Rule-2 and Rule-3 use natural-number comparison.  Constitutional rules are
exhausted before Rule 3 is consulted.

This core module provides the concrete observation type, key type, comparison projection,
comparators and their equality/transitivity laws, the addressed merge/assembly, the recursive
builder, and the completeness and observation/priority alignment laws for successful builds.
The general theorem that arbitrary pointwise child permutations with identical observations
produce identical comparison projections is developed in the separate
`CanonicalRule3HierarchyPermutation.lean` module on top of this API.  Provenance fields
(`sourceNodes`, `sourceOccurrences`, `sourceTree?`) are not part of the comparison projection.
-/

/-! ## Evidence retained by the Rule-3 hierarchy -/

/-- One addressed Rule-3 geometry observation.  The physical unit is an unordered atom pair; it is
evidence only and never a priority key. -/
structure CanonicalRule3Observation where
  /-- Unordered endpoints of the physical double-bond unit. -/
  unit : ℕ × ℕ
  /-- Endpoint through which the branch enters the unit. -/
  near : ℕ
  /-- Opposite endpoint of the unit. -/
  far : ℕ
  /-- Optional real incoming occurrence entry. -/
  entry? : Option ℕ
  /-- Official Rule-3 geometry class of the unit.  The existing authoritative enum is reused. -/
  geometry : OfficialRule3Geometry
  deriving DecidableEq, Repr

namespace CanonicalRule3Observation

/-- Numeric Rule-3 priority of an observation. -/
def priority (observation : CanonicalRule3Observation) : ℕ :=
  observation.geometry.priority

end CanonicalRule3Observation

/-- Compiled recursive Rules-1a--3 key.

`constitutional` is exactly the existing compiled constitutional key.  `observations` records the
addressed geometry evidence; `rule3` is its natural-number priority projection.  Only `rule3` is
read by the comparator. -/
structure CanonicalRule3Key where
  constitutional : CanonicalBranchKey
  observations : List (List (List ℕ × CanonicalRule3Observation)) := []
  rule3 : List (List CanonicalNatEntry) := []
  deriving DecidableEq, Repr

/-! ## Rational projection of Rule-1a labels -/

/-- Exact rational value of a Rule-1a label.  The effective denominator is positive by
construction. -/
def canonicalLabelValue (label : CIPAtomicLabel) : ℚ :=
  (label.numerator : ℚ) / (label.effectiveDenominator : ℚ)

/-- Comparison-visible Rule-1a entry. -/
def canonicalAtomicEntryValue (entry : CanonicalAtomicEntry) : List ℕ × ℚ :=
  (entry.1, canonicalLabelValue entry.2)

/-- Rational comparison used by the Rule-1a projection. -/
def compareRule1aValue (left right : ℚ) : Ordering :=
  compareOfLessAndEq left right

private local instance rule1aValueCompareTrans : Std.TransCmp compareRule1aValue := by
  unfold compareRule1aValue
  exact Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
    (fun value => lt_irrefl value)
    (fun {_ _ _} leftMiddle middleRight => lt_trans leftMiddle middleRight)
    (fun notLeftRight notRightLeft =>
      le_antisymm (le_of_not_gt notRightLeft) (le_of_not_gt notLeftRight))

/-- The rational label projection computes the same comparison as `compareCIPAtomicLabel`. -/
theorem compareCIPAtomicLabel_eq_compare_labelValue (left right : CIPAtomicLabel) :
    compareCIPAtomicLabel left right =
      compareRule1aValue (canonicalLabelValue left) (canonicalLabelValue right) := by
  unfold compareCIPAtomicLabel compareRule1aValue canonicalLabelValue
  rw [LinearOrder.compare_eq_compareOfLessAndEq]
  unfold compareOfLessAndEq
  have leftPositive : (0 : ℚ) < left.effectiveDenominator := by
    have positive : 0 < left.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast positive
  have rightPositive : (0 : ℚ) < right.effectiveDenominator := by
    have positive : 0 < right.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast positive
  simp only [div_lt_div_iff₀ leftPositive rightPositive,
    div_eq_div_iff leftPositive.ne' rightPositive.ne']
  norm_cast

/-- The rational comparator decides equality exactly. -/
theorem compareRule1aValue_eq_iff (left right : ℚ) :
    compareRule1aValue left right = Ordering.eq ↔ left = right := by
  unfold compareRule1aValue compareOfLessAndEq
  by_cases lower : left < right
  · rw [if_pos lower]
    constructor
    · intro impossible
      cases impossible
    · intro same
      exact absurd same (ne_of_lt lower)
  · rw [if_neg lower]
    by_cases equal : left = right
    · rw [if_pos equal]
      constructor
      · intro _
        exact equal
      · intro _
        rfl
    · rw [if_neg equal]
      constructor
      · intro impossible
        cases impossible
      · intro same
        exact absurd same equal

/-! ## Comparison-visible observable and projection -/

/-- Project one Rule-1a layer to rational labels. -/
def mapCanonicalAtomicLayer (layer : List CanonicalAtomicEntry) : List (List ℕ × ℚ) :=
  layer.map canonicalAtomicEntryValue

/-- Project all Rule-1a layers to rational labels. -/
def mapCanonicalAtomicLayers (layers : List (List CanonicalAtomicEntry)) :
    List (List (List ℕ × ℚ)) :=
  layers.map mapCanonicalAtomicLayer

/-- The comparison-visible projection of one recursive Rules-1a--3 key. -/
structure CanonicalRule3Observable where
  rule1a : List (List (List ℕ × ℚ))
  rule1b : List (List CanonicalNatEntry)
  rule2 : List (List CanonicalNatEntry)
  rule3 : List (List CanonicalNatEntry)
  deriving DecidableEq, Repr

/-- Project the recursive key to its comparison-visible form. -/
def canonicalRule3Observable (key : CanonicalRule3Key) : CanonicalRule3Observable :=
  { rule1a := mapCanonicalAtomicLayers key.constitutional.rule1a
    rule1b := key.constitutional.rule1b
    rule2 := key.constitutional.rule2
    rule3 := key.rule3 }

/-- The comparison projection requested by the integration contract: the four addressed rule
layers plus successful-key completeness. -/
structure CanonicalRule3ComparisonProjection where
  observable : CanonicalRule3Observable
  complete : Bool
  deriving DecidableEq, Repr

/-- Forget a compiled key down to its comparison projection. -/
def canonicalRule3ComparisonProjection (key : CanonicalRule3Key) :
    CanonicalRule3ComparisonProjection :=
  { observable := canonicalRule3Observable key
    complete := key.constitutional.complete }

/-! ## Comparators -/

/-- Constitutional comparison of observables: Rule 1a, then Rule 1b, then Rule 2, exactly as
`compareCanonicalBranchKeys`. -/
def compareConstitutionalObservable
    (left right : CanonicalRule3Observable) : Ordering :=
  compareLex
    (Ordering.byKey CanonicalRule3Observable.rule1a
      (compareSparseCanonicalLayers compareRule1aValue))
    (compareLex
      (Ordering.byKey CanonicalRule3Observable.rule1b
        (compareSparseCanonicalLayers compareRule1bRootDistance))
      (Ordering.byKey CanonicalRule3Observable.rule2
        (compareSparseCanonicalLayers compare))) left right

/-- Complete observable comparison: the constitutional rules dominate; Rule 3 is consulted only
after an exhaustive constitutional tie. -/
def compareCanonicalRule3Observable
    (left right : CanonicalRule3Observable) : Ordering :=
  compareLex compareConstitutionalObservable
    (Ordering.byKey CanonicalRule3Observable.rule3
      (compareSparseCanonicalLayers compare)) left right

/-- Comparison of recursive Rule-1a--3 keys through their comparison-visible projection. -/
def compareCanonicalRule3Keys (left right : CanonicalRule3Key) : Ordering :=
  Ordering.byKey canonicalRule3Observable compareCanonicalRule3Observable left right

@[simp] theorem compareCanonicalRule3Keys_eq_compareObservable
    (left right : CanonicalRule3Key) :
    compareCanonicalRule3Keys left right =
      compareCanonicalRule3Observable
        (canonicalRule3Observable left) (canonicalRule3Observable right) :=
  rfl

/-- Once the constitutional prefix decides, Rule 3 is never consulted. -/
theorem compareCanonicalRule3Observable_eq_constitutional_of_ne
    (left right : CanonicalRule3Observable)
    (different : compareConstitutionalObservable left right ≠ Ordering.eq) :
    compareCanonicalRule3Observable left right =
      compareConstitutionalObservable left right := by
  unfold compareCanonicalRule3Observable compareLex
  cases constitutional : compareConstitutionalObservable left right with
  | eq => exact absurd constitutional different
  | lt => rfl
  | gt => rfl

/-- After an exhaustive constitutional tie, the complete comparison is exactly the Rule-3
comparison of the addressed priority layers. -/
theorem compareCanonicalRule3Observable_eq_rule3_of_constitutional_eq
    (left right : CanonicalRule3Observable)
    (tie : compareConstitutionalObservable left right = Ordering.eq) :
    compareCanonicalRule3Observable left right =
      compareSparseCanonicalLayers compare left.rule3 right.rule3 := by
  unfold compareCanonicalRule3Observable compareLex Ordering.byKey
  rw [tie]
  rfl

/-! ## Exactness of the addressed comparators -/

private theorem nat_compare_eq_iff (left right : ℕ) :
    compare left right = Ordering.eq ↔ left = right :=
  Std.LawfulEqOrd.compare_eq_iff_eq

private theorem flip_compare_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ a b : α, flip cmp a b = Ordering.eq ↔ a = b := by
  intro a b
  show cmp b a = Ordering.eq ↔ a = b
  exact (hcmp b a).trans eq_comm

private theorem listCompareLex_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : List α, List.compareLex cmp left right = Ordering.eq ↔ left = right := by
  intro left
  induction left with
  | nil =>
      intro right
      exact List.compareLex_nil_left_eq_eq.trans eq_comm
  | cons head tail inductionHypothesis =>
      intro right
      cases right with
      | nil => exact List.compareLex_nil_right_eq_eq
      | cons otherHead otherTail =>
          rw [List.compareLex_cons_cons, Ordering.then_eq_eq]
          constructor
          · rintro ⟨headEq, tailEq⟩
            rw [(hcmp head otherHead).mp headEq,
              (inductionHypothesis otherTail).mp tailEq]
          · intro equal
            injection equal with headEq tailEq
            exact ⟨(hcmp head otherHead).mpr headEq,
              (inductionHypothesis otherTail).mpr tailEq⟩

private theorem compareCanonicalPath_eq_iff (left right : List ℕ) :
    compareCanonicalPath left right = Ordering.eq ↔ left = right := by
  unfold compareCanonicalPath
  exact listCompareLex_eq_iff compare nat_compare_eq_iff left right

private theorem compareSparseCanonicalEntry_eq_iff {α : Type*}
    (cmp : α → α → Ordering) (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : List ℕ × α,
      compareSparseCanonicalEntry cmp left right = Ordering.eq ↔ left = right := by
  have position : ∀ (left right : List ℕ),
      flip compareCanonicalPath left right = Ordering.eq ↔ left = right :=
    flip_compare_eq_iff compareCanonicalPath compareCanonicalPath_eq_iff
  intro left right
  unfold compareSparseCanonicalEntry
  rw [compareLex_eq_eq]
  simp only [Ordering.byKey, position left.1 right.1, hcmp left.2 right.2]
  exact ⟨fun equal => Prod.ext equal.1 equal.2,
    fun equal => ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩⟩

private theorem compareSparseCanonicalLayer_eq_iff {α : Type*}
    (cmp : α → α → Ordering) (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : List (List ℕ × α),
      compareSparseCanonicalLayer cmp left right = Ordering.eq ↔ left = right := by
  intro left right
  unfold compareSparseCanonicalLayer
  exact listCompareLex_eq_iff (compareSparseCanonicalEntry cmp)
    (compareSparseCanonicalEntry_eq_iff cmp hcmp) left right

private theorem compareSparseCanonicalLayers_eq_iff {α : Type*}
    (cmp : α → α → Ordering) (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : List (List (List ℕ × α)),
      compareSparseCanonicalLayers cmp left right = Ordering.eq ↔ left = right := by
  intro left right
  unfold compareSparseCanonicalLayers
  exact listCompareLex_eq_iff (compareSparseCanonicalLayer cmp)
    (compareSparseCanonicalLayer_eq_iff cmp hcmp) left right

private theorem compareRule1bRootDistance_eq_iff (left right : ℕ) :
    compareRule1bRootDistance left right = Ordering.eq ↔ left = right := by
  unfold compareRule1bRootDistance
  exact flip_compare_eq_iff compare nat_compare_eq_iff left right

theorem compareSparseCanonicalLayers_rat_eq_iff
    (left right : List (List (List ℕ × ℚ))) :
    compareSparseCanonicalLayers compareRule1aValue left right = Ordering.eq ↔
      left = right :=
  compareSparseCanonicalLayers_eq_iff compareRule1aValue compareRule1aValue_eq_iff left right

theorem compareSparseCanonicalLayers_nat_eq_iff
    (left right : List (List (List ℕ × ℕ))) :
    compareSparseCanonicalLayers compare left right = Ordering.eq ↔ left = right :=
  compareSparseCanonicalLayers_eq_iff compare nat_compare_eq_iff left right

theorem compareSparseCanonicalLayers_rule1b_eq_iff
    (left right : List (List (List ℕ × ℕ))) :
    compareSparseCanonicalLayers compareRule1bRootDistance left right = Ordering.eq ↔
      left = right :=
  compareSparseCanonicalLayers_eq_iff compareRule1bRootDistance
    compareRule1bRootDistance_eq_iff left right

/-- The observable comparator decides equality exactly on equal observables. -/
theorem compareCanonicalRule3Observable_eq_iff
    (left right : CanonicalRule3Observable) :
    compareCanonicalRule3Observable left right = Ordering.eq ↔ left = right := by
  have rule1aCompare : compareSparseCanonicalLayers compareRule1aValue
      left.rule1a right.rule1a = Ordering.eq ↔ left.rule1a = right.rule1a :=
    compareSparseCanonicalLayers_rat_eq_iff left.rule1a right.rule1a
  have rule1bCompare : compareSparseCanonicalLayers compareRule1bRootDistance
      left.rule1b right.rule1b = Ordering.eq ↔ left.rule1b = right.rule1b :=
    compareSparseCanonicalLayers_rule1b_eq_iff left.rule1b right.rule1b
  have rule2Compare : compareSparseCanonicalLayers compare
      left.rule2 right.rule2 = Ordering.eq ↔ left.rule2 = right.rule2 :=
    compareSparseCanonicalLayers_nat_eq_iff left.rule2 right.rule2
  have rule3Compare : compareSparseCanonicalLayers compare
      left.rule3 right.rule3 = Ordering.eq ↔ left.rule3 = right.rule3 :=
    compareSparseCanonicalLayers_nat_eq_iff left.rule3 right.rule3
  simp only [compareCanonicalRule3Observable, compareConstitutionalObservable,
    compareLex_eq_eq, Ordering.byKey]
  rw [rule1aCompare, rule1bCompare, rule2Compare, rule3Compare]
  constructor
  · rintro ⟨⟨h1a, h1b, h2⟩, h3⟩
    cases left
    cases right
    simp_all
  · intro equal
    rw [equal]
    simp

/-- Two recursive keys compare equal exactly when their comparison-visible observables agree. -/
theorem compareCanonicalRule3Keys_eq_iff_observable_eq
    (left right : CanonicalRule3Key) :
    compareCanonicalRule3Keys left right = Ordering.eq ↔
      canonicalRule3Observable left = canonicalRule3Observable right := by
  rw [compareCanonicalRule3Keys_eq_compareObservable]
  exact compareCanonicalRule3Observable_eq_iff _ _

/-! ## Comparator transitivity -/

/-- The observable comparator is oriented and transitive. -/
theorem compareCanonicalRule3Observable_transCmp :
    Std.TransCmp compareCanonicalRule3Observable := by
  haveI : Std.TransCmp compareRule1aValue := rule1aValueCompareTrans
  unfold compareCanonicalRule3Observable compareConstitutionalObservable
    compareSparseCanonicalLayers compareSparseCanonicalLayer compareSparseCanonicalEntry
    compareCanonicalPath compareRule1bRootDistance
  infer_instance

/-- The key comparator is oriented and transitive. -/
theorem compareCanonicalRule3Keys_transCmp :
    Std.TransCmp compareCanonicalRule3Keys := by
  haveI : Std.TransCmp compareCanonicalRule3Observable :=
    compareCanonicalRule3Observable_transCmp
  unfold compareCanonicalRule3Keys
  infer_instance

/-! ## Descending child ordering -/

/-- Structural descending insertion by the complete cumulative Rules-1a--3 comparator. -/
def insertCanonicalRule3Key (key : CanonicalRule3Key) :
    List CanonicalRule3Key → List CanonicalRule3Key
  | [] => [key]
  | head :: tail =>
      match compareCanonicalRule3Keys key head with
      | .lt => head :: insertCanonicalRule3Key key tail
      | .eq | .gt => key :: head :: tail

/-- Structural descending sort used before a parent assigns sibling addresses. -/
def sortCanonicalRule3Keys : List CanonicalRule3Key → List CanonicalRule3Key
  | [] => []
  | key :: keys => insertCanonicalRule3Key key (sortCanonicalRule3Keys keys)

theorem insertCanonicalRule3Key_perm (key : CanonicalRule3Key) :
    ∀ keys, (insertCanonicalRule3Key key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertCanonicalRule3Key
      cases comparison : compareCanonicalRule3Keys key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head (insertCanonicalRule3Key_perm key tail)).trans
            (List.Perm.swap key head tail)

theorem sortCanonicalRule3Keys_perm (keys : List CanonicalRule3Key) :
    (sortCanonicalRule3Keys keys).Perm keys := by
  induction keys with
  | nil => exact List.Perm.refl []
  | cons key keys inductionHypothesis =>
      exact (insertCanonicalRule3Key_perm key (sortCanonicalRule3Keys keys)).trans
        (List.Perm.cons key inductionHypothesis)

/-! ## Addressed merge and assembly -/

/-- Prefix one Rule-3 observation layer with its final sibling slot. -/
def prefixCanonicalObservationLayer (slot : ℕ)
    (layer : List (List ℕ × CanonicalRule3Observation)) :
    List (List ℕ × CanonicalRule3Observation) :=
  layer.map fun entry => (slot :: entry.1, entry.2)

/-- Prefix one rational Rule-1a layer with its final sibling slot. -/
def prefixCanonicalAtomicValueLayer (slot : ℕ) (layer : List (List ℕ × ℚ)) :
    List (List ℕ × ℚ) :=
  layer.map fun entry => (slot :: entry.1, entry.2)

/-- Child-agnostic addressed merge of Rule-1a entry layers. -/
def mergeAtomicObserved (children : List (List (List CanonicalAtomicEntry))) :
    List (List CanonicalAtomicEntry) :=
  let count := children.foldl (fun longest child => max longest child.length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixCanonicalAtomicLayer child.2 (child.1.getD depth [])

/-- Child-agnostic addressed merge of rational Rule-1a entry layers. -/
def mergeAtomicValueObserved (children : List (List (List (List ℕ × ℚ)))) :
    List (List (List ℕ × ℚ)) :=
  let count := children.foldl (fun longest child => max longest child.length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixCanonicalAtomicValueLayer child.2 (child.1.getD depth [])

/-- Child-agnostic addressed merge of natural-number layers. -/
def mergeNatObserved (children : List (List (List CanonicalNatEntry))) :
    List (List CanonicalNatEntry) :=
  let count := children.foldl (fun longest child => max longest child.length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixCanonicalNatLayer child.2 (child.1.getD depth [])

/-- Child-agnostic addressed merge of observation layers. -/
def mergeObservationObserved
    (children : List (List (List (List ℕ × CanonicalRule3Observation)))) :
    List (List (List ℕ × CanonicalRule3Observation)) :=
  let count := children.foldl (fun longest child => max longest child.length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixCanonicalObservationLayer child.2 (child.1.getD depth [])

/-- The existing constitutional Rule-1a merge is the observation-only merge of child layers. -/
theorem mergeCanonicalAtomicChildren_eq_observed (children : List CanonicalBranchKey) :
    mergeCanonicalAtomicChildren children =
      mergeAtomicObserved (children.map fun child => child.rule1a) := by
  unfold mergeCanonicalAtomicChildren canonicalChildLayerCount mergeAtomicObserved
  rw [List.foldl_map]
  apply List.map_congr_left
  intro depth _
  rw [List.zipIdx_map, List.flatMap_map]
  rfl

/-- The existing constitutional natural-number merge is the observation-only merge of child
layers. -/
theorem mergeCanonicalNatChildren_eq_observed
    (layers : CanonicalBranchKey → List (List CanonicalNatEntry))
    (children : List CanonicalBranchKey) :
    mergeCanonicalNatChildren layers children = mergeNatObserved (children.map layers) := by
  unfold mergeCanonicalNatChildren canonicalChildLayerCount mergeNatObserved
  rw [List.foldl_map]
  apply List.map_congr_left
  intro depth _
  rw [List.zipIdx_map, List.flatMap_map]
  rfl

/-- The addressed Rule-3 priority merge is the observation-only merge of child layers. -/
def mergeCanonicalRule3NatChildren
    (layers : CanonicalRule3Key → List (List CanonicalNatEntry))
    (children : List CanonicalRule3Key) : List (List CanonicalNatEntry) :=
  mergeNatObserved (children.map layers)

/-- The addressed observation merge is the observation-only merge of child layers. -/
def mergeCanonicalRule3ObservationChildren (children : List CanonicalRule3Key) :
    List (List (List ℕ × CanonicalRule3Observation)) :=
  mergeObservationObserved (children.map fun child => child.observations)

@[simp] theorem mergeCanonicalRule3NatChildren_eq_observed
    (layers : CanonicalRule3Key → List (List CanonicalNatEntry))
    (children : List CanonicalRule3Key) :
    mergeCanonicalRule3NatChildren layers children = mergeNatObserved (children.map layers) :=
  rfl

@[simp] theorem mergeCanonicalRule3ObservationChildren_eq_observed
    (children : List CanonicalRule3Key) :
    mergeCanonicalRule3ObservationChildren children =
      mergeObservationObserved (children.map fun child => child.observations) :=
  rfl

/-- Addressed root observation layer. -/
def rule3ObservationRoot (observation : Option CanonicalRule3Observation) :
    List (List (List ℕ × CanonicalRule3Observation)) :=
  match observation with
  | none => [[]]
  | some value => [[([], value)]]

/-- Addressed root Rule-3 priority layer. -/
def rule3PriorityRoot (observation : Option CanonicalRule3Observation) :
    List (List CanonicalNatEntry) :=
  match observation with
  | none => [[]]
  | some value => [[([], value.priority)]]

/-- Assemble a parent key from the existing constitutional root and merge, prefixing the same
sorted child slots into the observation and Rule-3 projections. -/
def assembleCanonicalRule3Key (root : CanonicalBranchKey)
    (rootObservation : Option CanonicalRule3Observation)
    (sorted : List CanonicalRule3Key) : CanonicalRule3Key :=
  { constitutional := assembleCanonicalBranchKey root
      (sorted.map fun child => child.constitutional)
    observations := rule3ObservationRoot rootObservation ++
      mergeCanonicalRule3ObservationChildren sorted
    rule3 := rule3PriorityRoot rootObservation ++
      mergeCanonicalRule3NatChildren (fun child => child.rule3) sorted }

/-! ## Projection commutation for the merged observable -/

/-- Project one observation layer to its numeric Rule-3 priority. -/
def mapObservationPriorityLayer (layer : List (List ℕ × CanonicalRule3Observation)) :
    List CanonicalNatEntry :=
  layer.map fun entry => (entry.1, entry.2.priority)

/-- Project every observation layer to its numeric Rule-3 priority. -/
def mapObservationPriorityLayers
    (layers : List (List (List ℕ × CanonicalRule3Observation))) :
    List (List CanonicalNatEntry) :=
  layers.map mapObservationPriorityLayer

/-- Elementwise projection of one Rule-1a layer. -/
@[simp] theorem mapCanonicalAtomicLayer_eq_map (layer : List CanonicalAtomicEntry) :
    mapCanonicalAtomicLayer layer = layer.map canonicalAtomicEntryValue :=
  rfl

/-- Elementwise projection of one observation layer. -/
@[simp] theorem mapObservationPriorityLayer_eq_map
    (layer : List (List ℕ × CanonicalRule3Observation)) :
    mapObservationPriorityLayer layer =
      layer.map fun entry => (entry.1, entry.2.priority) :=
  rfl

theorem prefixCanonicalAtomicLayer_map (slot : ℕ) (layer : List CanonicalAtomicEntry) :
    (prefixCanonicalAtomicLayer slot layer).map canonicalAtomicEntryValue =
      prefixCanonicalAtomicValueLayer slot (layer.map canonicalAtomicEntryValue) := by
  simp only [prefixCanonicalAtomicLayer, prefixCanonicalAtomicValueLayer, List.map_map]
  apply List.map_congr_left
  intro entry _
  rfl

theorem prefixCanonicalObservationLayer_map (slot : ℕ)
    (layer : List (List ℕ × CanonicalRule3Observation)) :
    (prefixCanonicalObservationLayer slot layer).map
        (fun entry => (entry.1, entry.2.priority)) =
      prefixCanonicalNatLayer slot (mapObservationPriorityLayer layer) := by
  simp only [prefixCanonicalObservationLayer, prefixCanonicalNatLayer,
    mapObservationPriorityLayer, List.map_map]
  apply List.map_congr_left
  intro entry _
  rfl

theorem mapCanonicalAtomicLayer_getD (layers : List (List CanonicalAtomicEntry))
    (depth : ℕ) :
    (layers.map mapCanonicalAtomicLayer).getD depth [] =
      (layers.getD depth []).map canonicalAtomicEntryValue := by
  unfold List.getD
  rw [List.getElem?_map]
  cases layers[depth]? <;> rfl

theorem mapObservationPriorityLayer_getD
    (layers : List (List (List ℕ × CanonicalRule3Observation))) (depth : ℕ) :
    (layers.map mapObservationPriorityLayer).getD depth [] =
      mapObservationPriorityLayer (layers.getD depth []) := by
  unfold List.getD
  rw [List.getElem?_map]
  cases layers[depth]? <;> rfl

private theorem list_flatMap_congr {α β : Type*} {l₁ l₂ : List α} (equal : l₁ = l₂)
    {f g : α → List β} (pointwise : ∀ a ∈ l₁, f a = g a) :
    l₁.flatMap f = l₂.flatMap g := by
  subst l₂
  induction l₁ with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.flatMap_cons, List.flatMap_cons,
        ← pointwise head (by simp),
        inductionHypothesis (fun a member => pointwise a (List.mem_cons_of_mem head member))]

private theorem foldl_max_length_rule1a_eq_aux (children : List CanonicalBranchKey)
    (init : ℕ) :
    (children.map (fun child => child.rule1a)).foldl
        (fun longest layer => max longest layer.length) init =
      (children.map (fun child => mapCanonicalAtomicLayers child.rule1a)).foldl
        (fun longest layer => max longest layer.length) init := by
  induction children generalizing init with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map, List.foldl]
      rw [inductionHypothesis]
      have lengths : head.rule1a.length =
          (mapCanonicalAtomicLayers head.rule1a).length := by
        simp only [mapCanonicalAtomicLayers, List.length_map]
      rw [lengths]

private theorem foldl_max_length_observations_eq_aux
    (children : List (List (List (List ℕ × CanonicalRule3Observation)))) (init : ℕ) :
    children.foldl (fun longest layer => max longest layer.length) init =
      (children.map mapObservationPriorityLayers).foldl
        (fun longest layer => max longest layer.length) init := by
  induction children generalizing init with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map, List.foldl]
      rw [inductionHypothesis]
      have lengths : head.length = (mapObservationPriorityLayers head).length := by
        simp only [mapObservationPriorityLayers, List.length_map]
      rw [lengths]

/-- Mapping Rule-1a entries to rational values commutes with the addressed child merge. -/
theorem mapCanonicalAtomicLayers_mergeCanonicalAtomicChildren
    (children : List CanonicalBranchKey) :
    mapCanonicalAtomicLayers (mergeCanonicalAtomicChildren children) =
      mergeAtomicValueObserved
        (children.map fun child => mapCanonicalAtomicLayers child.rule1a) := by
  rw [mergeCanonicalAtomicChildren_eq_observed]
  unfold mergeAtomicObserved mergeAtomicValueObserved mapCanonicalAtomicLayers
  rw [foldl_max_length_rule1a_eq_aux, List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply, mapCanonicalAtomicLayer_eq_map, List.map_flatMap,
    List.zipIdx_map, List.flatMap_map]
  apply list_flatMap_congr rfl
  intro child _
  cases child with
  | mk key slot =>
      show (prefixCanonicalAtomicLayer slot (key.rule1a.getD depth [])).map
          canonicalAtomicEntryValue =
        prefixCanonicalAtomicValueLayer slot
          ((key.rule1a.map mapCanonicalAtomicLayer).getD depth [])
      rw [mapCanonicalAtomicLayer_getD]
      exact prefixCanonicalAtomicLayer_map slot (key.rule1a.getD depth [])

/-- Projecting observations to priorities commutes with the addressed child merge. -/
theorem mapObservationPriorityLayers_mergeObservationObserved
    (children : List (List (List (List ℕ × CanonicalRule3Observation)))) :
    mapObservationPriorityLayers (mergeObservationObserved children) =
      mergeNatObserved (children.map mapObservationPriorityLayers) := by
  unfold mergeObservationObserved mergeNatObserved mapObservationPriorityLayers
  rw [foldl_max_length_observations_eq_aux, List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply, mapObservationPriorityLayer_eq_map, List.map_flatMap,
    List.zipIdx_map, List.flatMap_map]
  apply list_flatMap_congr rfl
  intro child _
  cases child with
  | mk key slot =>
      show (prefixCanonicalObservationLayer slot (key.getD depth [])).map
          (fun entry => (entry.1, entry.2.priority)) =
        prefixCanonicalNatLayer slot
          ((key.map mapObservationPriorityLayer).getD depth [])
      rw [mapObservationPriorityLayer_getD]
      exact prefixCanonicalObservationLayer_map slot (key.getD depth [])

/-! ## Observation/priority alignment -/

namespace CanonicalRule3Key

/-- The stored observation evidence and the compared Rule-3 priority layers are address aligned:
projecting every observation entry to its geometry priority recovers exactly `rule3`. -/
def Rule3Aligned (key : CanonicalRule3Key) : Prop :=
  mapObservationPriorityLayers key.observations = key.rule3

end CanonicalRule3Key

theorem rule3PriorityRoot_eq_map (observation : Option CanonicalRule3Observation) :
    rule3PriorityRoot observation =
      mapObservationPriorityLayers (rule3ObservationRoot observation) := by
  cases observation with
  | none =>
      simp only [rule3PriorityRoot, rule3ObservationRoot, mapObservationPriorityLayers,
        mapObservationPriorityLayer, List.map]
  | some value =>
      simp only [rule3PriorityRoot, rule3ObservationRoot, mapObservationPriorityLayers,
        mapObservationPriorityLayer, List.map]

theorem mergeCanonicalRule3NatChildren_eq_map_observations
    (children : List CanonicalRule3Key)
    (aligned : ∀ child ∈ children,
      mapObservationPriorityLayers child.observations = child.rule3) :
    mergeCanonicalRule3NatChildren (fun child => child.rule3) children =
      mapObservationPriorityLayers (mergeCanonicalRule3ObservationChildren children) := by
  rw [mergeCanonicalRule3NatChildren_eq_observed,
    mergeCanonicalRule3ObservationChildren_eq_observed]
  have mapped : children.map (fun child => child.rule3) =
      (children.map fun child => child.observations).map
        mapObservationPriorityLayers := by
    rw [List.map_map]
    apply List.map_congr_left
    intro child member
    simp only [Function.comp_apply]
    exact (aligned child member).symm
  rw [mapped]
  exact (mapObservationPriorityLayers_mergeObservationObserved
    (children.map fun child => child.observations)).symm

theorem assembleCanonicalRule3Key_complete (root : CanonicalBranchKey)
    (rootObservation : Option CanonicalRule3Observation)
    (sorted : List CanonicalRule3Key) :
    (assembleCanonicalRule3Key root rootObservation sorted).constitutional.complete =
      root.complete :=
  rfl

theorem assembleCanonicalRule3Key_rule3Aligned
    (root : CanonicalBranchKey) (rootObservation : Option CanonicalRule3Observation)
    (sorted : List CanonicalRule3Key)
    (aligned : ∀ child ∈ sorted,
      mapObservationPriorityLayers child.observations = child.rule3) :
    (assembleCanonicalRule3Key root rootObservation sorted).Rule3Aligned := by
  unfold CanonicalRule3Key.Rule3Aligned
  change (rule3ObservationRoot rootObservation ++
      mergeCanonicalRule3ObservationChildren sorted).map mapObservationPriorityLayer =
    rule3PriorityRoot rootObservation ++
      mergeCanonicalRule3NatChildren (fun child => child.rule3) sorted
  rw [List.map_append, rule3PriorityRoot_eq_map,
    mergeCanonicalRule3NatChildren_eq_map_observations sorted aligned]
  rfl

/-! ## Bottom-up compilation -/

/-- Compile every enumerated child once, failing if any child fails. -/
def compileRule3Children (compile : CanonicalBranchNode → Option CanonicalRule3Key) :
    List CanonicalBranchNode → Option (List CanonicalRule3Key)
  | [] => some []
  | node :: nodes => do
      let key ← compile node
      let keys ← compileRule3Children compile nodes
      some (key :: keys)

/-- Every key produced by `compileRule3Children` comes from a node of the enumerated child
list. -/
theorem compileRule3Children_member
    {compile : CanonicalBranchNode → Option CanonicalRule3Key}
    {nodes : List CanonicalBranchNode} :
    ∀ {keys : List CanonicalRule3Key},
      compileRule3Children compile nodes = some keys →
      ∀ {key : CanonicalRule3Key}, key ∈ keys →
        ∃ node ∈ nodes, compile node = some key := by
  induction nodes with
  | nil =>
      intro keys computed key member
      unfold compileRule3Children at computed
      simp only [Option.some.injEq] at computed
      cases computed
      simp at member
  | cons node nodes inductionHypothesis =>
      intro keys computed key member
      unfold compileRule3Children at computed
      cases nodeComputed : compile node with
      | none =>
          rw [nodeComputed] at computed
          dsimp at computed
          cases computed
      | some nodeKey =>
          rw [nodeComputed] at computed
          dsimp at computed
          cases restComputed : compileRule3Children compile nodes with
          | none =>
              rw [restComputed] at computed
              dsimp at computed
              cases computed
          | some restKeys =>
              rw [restComputed] at computed
              dsimp at computed
              cases computed
              rcases List.mem_cons.mp member with same | later
              · exact ⟨node, List.mem_cons_self, by simpa [same] using nodeComputed⟩
              · obtain ⟨found, foundMember, foundComputed⟩ :=
                  inductionHypothesis restComputed (key := key) later
                exact ⟨found, List.mem_cons_of_mem node foundMember, foundComputed⟩

/-- Compile a branch tree bottom-up with an explicit fuel bound.

`observe node = none` is an unresolved required observation and fails.  The inner `some none`
form is a justified structural non-unit or a precomputed exclusion.  Zero fuel succeeds exactly at
terminal nodes; every nonterminal node needs positive fuel.  There is no hidden width or total-node
cap, no atom-identifier or depth flattening, and no desired-key equality test. -/
def buildCanonicalRule3Key? (mol : RawMolecule)
    (children : CanonicalBranchNode → List CanonicalBranchNode)
    (observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)) :
    ℕ → CanonicalBranchNode → Option CanonicalRule3Key
  | 0, node =>
      match observe node with
      | none => none
      | some rootObservation =>
          match children node with
          | [] =>
              match mol.canonicalRootKeyAuthoritative? node true with
              | none => none
              | some root => some (assembleCanonicalRule3Key root rootObservation [])
          | _ => none
  | fuel + 1, node =>
      match observe node with
      | none => none
      | some rootObservation =>
          match children node with
          | [] =>
              match mol.canonicalRootKeyAuthoritative? node true with
              | none => none
              | some root => some (assembleCanonicalRule3Key root rootObservation [])
          | child :: rest =>
              match compileRule3Children
                  (fun childNode =>
                    buildCanonicalRule3Key? mol children observe fuel childNode)
                  (child :: rest) with
              | none => none
              | some childKeys =>
                  match mol.canonicalRootKeyAuthoritative? node true with
                  | none => none
                  | some root =>
                      some (assembleCanonicalRule3Key root rootObservation
                        (sortCanonicalRule3Keys childKeys))

/-! ## Basic builder facts -/

/-- An unresolved required observation refuses at every fuel. -/
theorem buildCanonicalRule3Key?_observe_none
    {mol : RawMolecule} {children : CanonicalBranchNode → List CanonicalBranchNode}
    {observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)}
    {node : CanonicalBranchNode} (unresolved : observe node = none) (fuel : ℕ) :
    buildCanonicalRule3Key? mol children observe fuel node = none := by
  cases fuel with
  | zero =>
      unfold buildCanonicalRule3Key?
      simp [unresolved]
  | succ fuel =>
      unfold buildCanonicalRule3Key?
      simp [unresolved]

/-- The authoritative root key records exactly the requested completeness flag. -/
theorem canonicalRootKeyAuthoritative?_complete {mol : RawMolecule}
    {node : CanonicalBranchNode} {complete : Bool} {root : CanonicalBranchKey}
    (computed : mol.canonicalRootKeyAuthoritative? node complete = some root) :
    root.complete = complete := by
  unfold canonicalRootKeyAuthoritative? at computed
  cases label : mol.canonicalRule1aLabelAuthoritative? node with
  | none =>
      rw [label] at computed
      dsimp at computed
      cases computed
  | some rule1a =>
      rw [label] at computed
      dsimp at computed
      cases computed
      rfl

/-- Zero fuel succeeds only at terminal nodes. -/
theorem buildCanonicalRule3Key?_zero_terminal {mol : RawMolecule}
    {children : CanonicalBranchNode → List CanonicalBranchNode}
    {observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)}
    {node : CanonicalBranchNode} {key : CanonicalRule3Key}
    (computed : buildCanonicalRule3Key? mol children observe 0 node = some key) :
    (children node).isEmpty = true := by
  unfold buildCanonicalRule3Key? at computed
  cases observed : observe node with
  | none =>
      rw [observed] at computed
      dsimp at computed
      cases computed
  | some rootObservation =>
      rw [observed] at computed
      dsimp at computed
      cases childNodes : children node with
      | nil => simp
      | cons child rest =>
          rw [childNodes] at computed
          dsimp at computed
          cases computed

/-- Zero fuel refuses every nonterminal node. -/
theorem buildCanonicalRule3Key?_zero_of_nonterminal {mol : RawMolecule}
    {children : CanonicalBranchNode → List CanonicalBranchNode}
    {observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)}
    {node : CanonicalBranchNode} (nonterminal : (children node).isEmpty = false) :
    buildCanonicalRule3Key? mol children observe 0 node = none := by
  unfold buildCanonicalRule3Key?
  cases observed : observe node with
  | none => rfl
  | some rootObservation =>
      cases childNodes : children node with
      | nil => simp [childNodes] at nonterminal
      | cons child rest => rfl

/-- Every successful compiled key is complete. -/
theorem buildCanonicalRule3Key?_complete {mol : RawMolecule}
    {children : CanonicalBranchNode → List CanonicalBranchNode}
    {observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)} :
    ∀ (fuel : ℕ) (node : CanonicalBranchNode) (key : CanonicalRule3Key),
      buildCanonicalRule3Key? mol children observe fuel node = some key →
      key.constitutional.complete = true
  | 0, node, key, computed => by
      unfold buildCanonicalRule3Key? at computed
      cases observed : observe node with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childNodes : children node with
          | cons child rest =>
              rw [childNodes] at computed
              dsimp at computed
              cases computed
          | nil =>
              rw [childNodes] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  rw [assembleCanonicalRule3Key_complete]
                  exact canonicalRootKeyAuthoritative?_complete rootComputed
  | fuel + 1, node, key, computed => by
      unfold buildCanonicalRule3Key? at computed
      cases observed : observe node with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childNodes : children node with
          | nil =>
              rw [childNodes] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  rw [assembleCanonicalRule3Key_complete]
                  exact canonicalRootKeyAuthoritative?_complete rootComputed
          | cons child rest =>
              rw [childNodes] at computed
              dsimp at computed
              cases childKeysComputed : compileRule3Children
                  (fun childNode =>
                    buildCanonicalRule3Key? mol children observe fuel childNode)
                  (child :: rest) with
              | none =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases computed
              | some childKeys =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
                  | none =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                  | some root =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                      rw [assembleCanonicalRule3Key_complete]
                      exact canonicalRootKeyAuthoritative?_complete rootComputed

/-- Every successfully built key keeps its stored observation evidence aligned with the compared
Rule-3 priority projection, at every fuel. -/
theorem buildCanonicalRule3Key?_rule3Aligned (mol : RawMolecule)
    (children : CanonicalBranchNode → List CanonicalBranchNode)
    (observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)) :
    ∀ (fuel : ℕ) (node : CanonicalBranchNode) (key : CanonicalRule3Key),
      buildCanonicalRule3Key? mol children observe fuel node = some key →
      key.Rule3Aligned := by
  intro fuel
  induction fuel with
  | zero =>
      intro node key computed
      unfold buildCanonicalRule3Key? at computed
      cases observed : observe node with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childNodes : children node with
          | cons child rest =>
              rw [childNodes] at computed
              dsimp at computed
              cases computed
          | nil =>
              rw [childNodes] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  exact assembleCanonicalRule3Key_rule3Aligned root rootObservation []
                    (by intro child member; simp at member)
  | succ fuel inductionHypothesis =>
      intro node key computed
      unfold buildCanonicalRule3Key? at computed
      cases observed : observe node with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childNodes : children node with
          | nil =>
              rw [childNodes] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  exact assembleCanonicalRule3Key_rule3Aligned root rootObservation []
                    (by intro child member; simp at member)
          | cons child rest =>
              rw [childNodes] at computed
              dsimp at computed
              cases childKeysComputed : compileRule3Children
                  (fun childNode =>
                    buildCanonicalRule3Key? mol children observe fuel childNode)
                  (child :: rest) with
              | none =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases computed
              | some childKeys =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
                  | none =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                  | some root =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                      apply assembleCanonicalRule3Key_rule3Aligned
                      intro builtChild member
                      have sortedMember : builtChild ∈ childKeys :=
                        (sortCanonicalRule3Keys_perm childKeys).mem_iff.mp member
                      obtain ⟨sourceNode, sourceMember, sourceComputed⟩ :=
                        compileRule3Children_member childKeysComputed sortedMember
                      exact inductionHypothesis sourceNode builtChild sourceComputed

/- Kernel trust checks for every theorem in this module. -/
assert_kernel_only compareCIPAtomicLabel_eq_compare_labelValue
assert_kernel_only compareRule1aValue_eq_iff
assert_kernel_only compareCanonicalRule3Keys_eq_compareObservable
assert_kernel_only compareCanonicalRule3Observable_eq_constitutional_of_ne
assert_kernel_only compareCanonicalRule3Observable_eq_rule3_of_constitutional_eq
assert_kernel_only nat_compare_eq_iff
assert_kernel_only flip_compare_eq_iff
assert_kernel_only listCompareLex_eq_iff
assert_kernel_only compareCanonicalPath_eq_iff
assert_kernel_only compareSparseCanonicalEntry_eq_iff
assert_kernel_only compareSparseCanonicalLayer_eq_iff
assert_kernel_only compareSparseCanonicalLayers_eq_iff
assert_kernel_only compareRule1bRootDistance_eq_iff
assert_kernel_only compareSparseCanonicalLayers_rat_eq_iff
assert_kernel_only compareSparseCanonicalLayers_nat_eq_iff
assert_kernel_only compareSparseCanonicalLayers_rule1b_eq_iff
assert_kernel_only compareCanonicalRule3Observable_eq_iff
assert_kernel_only compareCanonicalRule3Keys_eq_iff_observable_eq
assert_kernel_only compareCanonicalRule3Observable_transCmp
assert_kernel_only compareCanonicalRule3Keys_transCmp
assert_kernel_only insertCanonicalRule3Key_perm
assert_kernel_only sortCanonicalRule3Keys_perm
assert_kernel_only mergeCanonicalAtomicChildren_eq_observed
assert_kernel_only mergeCanonicalNatChildren_eq_observed
assert_kernel_only mergeCanonicalRule3NatChildren_eq_observed
assert_kernel_only mergeCanonicalRule3ObservationChildren_eq_observed
assert_kernel_only mapCanonicalAtomicLayer_eq_map
assert_kernel_only mapObservationPriorityLayer_eq_map
assert_kernel_only prefixCanonicalAtomicLayer_map
assert_kernel_only prefixCanonicalObservationLayer_map
assert_kernel_only mapCanonicalAtomicLayer_getD
assert_kernel_only mapObservationPriorityLayer_getD
assert_kernel_only list_flatMap_congr
assert_kernel_only foldl_max_length_rule1a_eq_aux
assert_kernel_only foldl_max_length_observations_eq_aux
assert_kernel_only mapCanonicalAtomicLayers_mergeCanonicalAtomicChildren
assert_kernel_only mapObservationPriorityLayers_mergeObservationObserved
assert_kernel_only rule3PriorityRoot_eq_map
assert_kernel_only mergeCanonicalRule3NatChildren_eq_map_observations
assert_kernel_only assembleCanonicalRule3Key_complete
assert_kernel_only assembleCanonicalRule3Key_rule3Aligned
assert_kernel_only compileRule3Children_member
assert_kernel_only buildCanonicalRule3Key?_observe_none
assert_kernel_only canonicalRootKeyAuthoritative?_complete
assert_kernel_only buildCanonicalRule3Key?_zero_terminal
assert_kernel_only buildCanonicalRule3Key?_zero_of_nonterminal
assert_kernel_only buildCanonicalRule3Key?_complete
assert_kernel_only buildCanonicalRule3Key?_rule3Aligned

end RawMolecule
end OneCenter
end TetraStereo
