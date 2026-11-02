import TetraStereo.OneCenter.LocalizedActualParentComparisonSeparation
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedConstitutionalExecutable
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Whole-state label noninterference for the parent-versus-outward comparison

`LocalizedActualParentComparisonSeparation` proves that the *restricted* dependency read
`localizedDependencyLabel target (localizedDependencyView s target)` gives a strict
parent-versus-outward constitutional comparison, decided before the cumulative descriptor is
consulted.  The restricted read is `none` at every cursor that is not a strict depth dependency of
the target; in particular it is `none` at the actual parent cursor, which is *shallower* than the
target.  Thus the existing theorem says nothing about an evaluator that reads the whole state
`s cursor.occurrence` without a dependency guard.

This module supplies that missing comparison.  It builds directly on the shared parametric
compiler `buildLocalizedRerootCumulativeRule45KeyWithRead?` of
`LocalizedParametricCumulativeLabels`, whose only difference from the shipped cumulative compiler
is that the per-cursor label comes from an arbitrary total callback
`readLabel : cursor → Option LocalizedAuxiliaryLabel`.  The shared module already supplies the
same-recursion builder, the exact restricted-reader bridge
(`buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel`), and the
label-independent constitutional derivation
(`buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative`).  This module adds
what is still missing for the comparison theorem:

* `exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_of_budget_le` and its twice-depth
  corollary: path-valid cursors compile at the proved finite budgets for *every* label reader, so
  both parent and child keys are constructed rather than assumed;
* `buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_rule1b_head`: the derived
  Rule-1b root head of a parametric build, also for every label reader.

On top of those, `wholeStateLabel input state` is the unrestricted read
`fun cursor => state cursor.occurrence`, which at the actual parent cursor returns the arbitrary
stored parent label rather than `none`, while `restrictedLabel input target view` is the shipped
restricted read packaged as a callback.

The main theorem `parentSide_outwardChild_comparison_independent_of_labels` states, for every
`readLabel` and every outward actual child of the target, that the parent-versus-child comparison
compiled from that reader is strict, that its full cumulative value equals the shipped restricted
comparison, and that this value is its own constitutional component -- with the constitutional
component itself equal to the executable pure constitutional comparison at the same cursor.  Key
existence at the proved finite budget `2 * (carrierFuel + 1)` is constructed, not assumed; both
Rule-1b head observations are derived from the successful builds.

The whole-state corollary instantiates `readLabel := wholeStateLabel input state` and the
dependency view induced by the same state.  A final corollary compares two arbitrary whole states
and shows the parent-versus-outward comparison is literally the same `Ordering`.

## Scope and honesty

* This is a statement about the strict parent-versus-outward **comparison** only.  It does not
  assert invariance of the whole cumulative key, of the descriptor projection, or of Rules-4b
  reference selection: on the outward side the restricted and unrestricted reads do agree
  (`restrictedLabel_eq_wholeStateLabel_of_outwardChild`), while only the parent read is replaced
  by an arbitrary value, and the comparison is proved insensitive to that replacement through the
  strict first Rule-1b sphere.
* No direction of the Rule-1b separation is asserted; only `≠` is used, exactly as supplied by
  `outwardChild_rule1bRootDistance_ne_parent`.
* No claim is made about normative 2013 chemistry or about the source profile beyond the
  implemented total `rule1bRootDistance`.
* No successful build, strict comparison, or comparison equality is assumed: all keys are
  constructed at `2 * (carrierFuel + 1)`, the pure comparisons at
  `2 * (carrierFuel + 1) + 1`, and every equality is derived from the existing uniqueness and
  projection theorems.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput
namespace WholeStateCumulativeLabels

/-! ## Two label readers

The shipped compiler reads `localizedDependencyLabel target view cursor`, which is `none` unless
the cursor occurrence is a strict depth dependency of the target.  The whole-state reader ignores
that guard and returns the stored state value at the cursor occurrence.  Both are total functions
of the cursor into `Option LocalizedAuxiliaryLabel`. -/

/-- The unrestricted whole-state read: `s cursor.occurrence`.  No dependency guard is applied. -/
def wholeStateLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option LocalizedAuxiliaryLabel :=
  state cursor.occurrence

/-- The shipped restricted read, packaged as a label function. -/
def restrictedLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option LocalizedAuxiliaryLabel :=
  input.localizedDependencyLabel target view cursor

/-! ## Finite-budget totality for arbitrary labels

The shared parametric compiler reads labels only after the frame and fuel conditions have been
decided, so labels never affect success.  The next two results are the parametric counterparts of
`exists_buildLocalizedRerootCumulativeRule45Key?_of_budget_le` and its twice-depth corollary, and
are the key-construction facts the comparison theorem needs. -/

private theorem exists_mapM_buildWithRead?_of_forall
    (input : CertifiedLocalizedCIPInput) {carrierFuel evaluationFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          stage readLabel evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        stage readLabel evaluationFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        exists_mapM_buildWithRead?_of_forall input stage readLabel cursors
          (fun child present => complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- **Arbitrary-label fuel completeness.**  For any label reader, a path-valid cursor compiles
successfully at any budget covering its structural budget.  In particular, no assumption about
the labels -- not even that the parent label is defined -- is needed. -/
theorem exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_of_budget_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ evaluationFuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        stage readLabel evaluationFuel cursor = some key
  | 0, cursor, valid, covered => by
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      by_cases empty : children = []
      · let label := readLabel cursor
        refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }, ?_⟩
        simp [buildLocalizedRerootCumulativeRule45KeyWithRead?,
          childrenComputed, empty, label]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := input.localizedRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | evaluationFuel + 1, cursor, valid, covered => by
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      by_cases empty : children = []
      · let label := readLabel cursor
        refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }, ?_⟩
        simp [buildLocalizedRerootCumulativeRule45KeyWithRead?,
          childrenComputed, empty, label]
      · have childComplete : ∀ child ∈ children, ∃ key,
            input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              stage readLabel evaluationFuel child = some key := by
          intro child present
          have childValid := input.localizedRerootChild_valid
            cursor child children childrenDerived present
          have decreases := input.localizedRerootChild_budget_lt
            cursor child children valid childrenDerived present
          exact exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_of_budget_le
            input stage readLabel evaluationFuel child childValid (by omega)
        obtain ⟨childKeys, childKeysComputed⟩ :=
          exists_mapM_buildWithRead?_of_forall input stage readLabel children childComplete
        let label := readLabel cursor
        let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
        refine ⟨
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
              input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }, ?_⟩
        simp [buildLocalizedRerootCumulativeRule45KeyWithRead?,
          childrenComputed, empty, childKeysComputed, label, sorted]

/-- Twice the carrier depth suffices for every path-valid cursor and every label reader. -/
theorem exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage readLabel (2 * (carrierFuel + 1)) cursor = some key := by
  apply exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_of_budget_le
    input stage readLabel (2 * (carrierFuel + 1)) cursor valid
  exact input.localizedRerootCursorBudget_le_twice cursor

/-! ## The derived Rule-1b root head of a parametric build

The label reader is not part of the constitutional recursion: the left spine of the assembled key
is exactly the ordinary rule-major reroot derivation.  The shared module already derives this
observation (`buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative`); the
next result reads off its Rule-1b head, which is what the strict cumulative comparison consumes. -/

/-- **Rule-1b root head of an arbitrary-label build.**  Independently of the label reader, the
first addressed sphere of the constitutional component is the cursor node's Rule-1b root
distance. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_rule1b_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        stage readLabel fuel cursor = some key →
      key.constitutional.rule1b.head? =
        some [([], cursor.occurrence.1.node.rule1bRootDistance)]
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            simp [MoleculeGraph.officialRuleMajorRootKey]
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            simp [MoleculeGraph.officialRuleMajorRootKey]
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  stage readLabel fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                simp [OfficialRuleMajorKey.assemble,
                  MoleculeGraph.officialRuleMajorRootKey]

/-! ## Where restricted and unrestricted reads agree -- and where they do not

The actual parent cursor is *shallower* than the target, so it is not a strict depth dependency
and the restricted read is `none` there.  Every outward child cursor, by contrast, is strictly
deeper and the two reads coincide.  This is exactly why the shipped theorem does not cover an
unrestricted parent read, and why the arbitrary reader in the parametric compiler is the right
generalization. -/

/-- The actual parent occurrence is not a strict depth dependency of the target. -/
theorem parentCursor_not_depthDependency
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedParentFrameHistory target) :
    ¬ input.LocalizedDepthDependency certificate.parent target := by
  intro dependency
  have longer := dependency.2
  have step := certificate.parent_address_length input
  omega

/-- At the actual parent cursor, the restricted read returns `none`, while the whole-state read
returns the arbitrary stored value `state certificate.parent`. -/
theorem restrictedLabel_parentCursor_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (certificate : input.LocalizedParentFrameHistory target) :
    restrictedLabel input target view
      { occurrence := certificate.parent, previous? := some target } = none := by
  unfold restrictedLabel localizedDependencyLabel
  change (if dependency : input.LocalizedDepthDependency certificate.parent target then
      view certificate.parent dependency else none) = none
  rw [dif_neg (parentCursor_not_depthDependency input target certificate)]

/-- At the actual parent cursor the whole-state reader returns exactly the stored parent value. -/
theorem wholeStateLabel_parentCursor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedParentFrameHistory target)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    wholeStateLabel input state
      { occurrence := certificate.parent, previous? := some target } =
        state certificate.parent :=
  rfl

/-- Every actual outward child of the target cursor is a strict depth dependency of the target. -/
theorem outwardChild_depthDependency
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedParentFrameHistory target) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      input.LocalizedDepthDependency child.occurrence target := by
  let targetCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := some certificate.parent }
  intro child slot childPresent childAddress
  refine ⟨?root, ?depth⟩
  · simpa [targetCursor] using
      input.localizedRerootChildren_root_eq targetCursor child
        (input.executableLocalizedRerootChildren targetCursor)
        (input.executableLocalizedRerootChildren_declarative targetCursor) childPresent
  · have lengths : child.occurrence.1.address.length =
        target.1.address.length + 1 := by
      rw [childAddress, List.length_append]
      simp
    omega

/-- On every actual outward child cursor, the restricted read and the whole-state read agree. -/
theorem restrictedLabel_eq_wholeStateLabel_of_outwardChild
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedParentFrameHistory target)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      restrictedLabel input target (input.localizedDependencyView state target) child =
        wholeStateLabel input state child := by
  intro child slot childPresent childAddress
  unfold restrictedLabel wholeStateLabel
  exact input.localizedDependencyLabel_eq_state_of_dependency target state child
    (outwardChild_depthDependency input target certificate child slot
      childPresent childAddress)

/-! ## The comparison witness and the noninterference theorem -/

/-- A completed strict parent-versus-outward comparison together with every key used to compute it.

`parentKey`/`childKey` are compiled by the shared parametric compiler from an arbitrary label
reader; the `actual*` keys are compiled by the shipped restricted-view compiler at the same
budget; `pureParent`/`pureChild` are the executable pure constitutional compiler.  The fields
state comparison *equalities*, not merely their truth. -/
structure ParentOutwardComparisonWitness
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (parentCursor childCursor : input.LocalizedRerootCursor carrierFuel) where
  /-- Parent-side key compiled from the arbitrary reader. -/
  parentKey : input.LocalizedRerootCumulativeRule45Key
  /-- Outward-child key compiled from the arbitrary reader. -/
  childKey : input.LocalizedRerootCumulativeRule45Key
  /-- Parent-side key compiled by the shipped restricted-view compiler. -/
  actualParentKey : input.LocalizedRerootCumulativeRule45Key
  /-- Outward-child key compiled by the shipped restricted-view compiler. -/
  actualChildKey : input.LocalizedRerootCumulativeRule45Key
  /-- Parent-side pure constitutional key. -/
  pureParent : OfficialRuleMajorKey input.Atom
  /-- Outward-child pure constitutional key. -/
  pureChild : OfficialRuleMajorKey input.Atom
  parentBuilt :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage readLabel
      (2 * (carrierFuel + 1)) parentCursor = some parentKey
  childBuilt :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage readLabel
      (2 * (carrierFuel + 1)) childCursor = some childKey
  actualParentBuilt :
    input.buildLocalizedRerootCumulativeRule45Key? stage target view
      (2 * (carrierFuel + 1)) parentCursor = some actualParentKey
  actualChildBuilt :
    input.buildLocalizedRerootCumulativeRule45Key? stage target view
      (2 * (carrierFuel + 1)) childCursor = some actualChildKey
  pureParentBuilt :
    input.buildLocalizedRerootRuleMajorKeyExec?
      (2 * (carrierFuel + 1) + 1) parentCursor = some pureParent
  pureChildBuilt :
    input.buildLocalizedRerootRuleMajorKeyExec?
      (2 * (carrierFuel + 1) + 1) childCursor = some pureChild
  parentHead :
    parentKey.constitutional.rule1b.head? =
      some [([], parentCursor.occurrence.1.node.rule1bRootDistance)]
  childHead :
    childKey.constitutional.rule1b.head? =
      some [([], childCursor.occurrence.1.node.rule1bRootDistance)]
  constitutionalCompare_eq_actual :
    OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional =
      OfficialRuleMajorKey.compare actualParentKey.constitutional
        actualChildKey.constitutional
  constitutionalCompare_eq_pure :
    OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional =
      OfficialRuleMajorKey.compare pureParent pureChild
  constitutionalCompare_ne_eq :
    OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional ≠
      Ordering.eq
  fullCompare_eq_actual :
    input.compareLocalizedRerootCumulativeRule45Keys parentKey childKey =
      input.compareLocalizedRerootCumulativeRule45Keys actualParentKey actualChildKey
  fullCompare_eq_constitutional :
    input.compareLocalizedRerootCumulativeRule45Keys parentKey childKey =
      OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional
  actualFullCompare_eq_constitutional :
    input.compareLocalizedRerootCumulativeRule45Keys actualParentKey actualChildKey =
      OfficialRuleMajorKey.compare actualParentKey.constitutional
        actualChildKey.constitutional

/-- **Parent-versus-outward comparison is independent of the label reader.**

For an active-simple target with an actual parent-frame certificate, an arbitrary cumulative
stage, an arbitrary dependency view, and an *arbitrary* label reader `readLabel`, every outward
actual child cursor admits, as a `Nonempty` of the `Type`-valued witness package, the following
at the proved finite budget `2 * (carrierFuel + 1)`:

* a parent-side and child-side key compiled from `readLabel` by the shared parametric compiler;
* the shipped restricted-view keys at the same budget;
* the executable pure constitutional keys at `2 * (carrierFuel + 1) + 1`;
* the derived Rule-1b root heads of the arbitrary-label keys;
* equality of the constitutional comparison with the shipped restricted comparison and with the
  pure constitutional comparison;
* strictness of the arbitrary-label constitutional comparison;
* equality of the full cumulative comparison with the shipped restricted comparison and with its
  own constitutional component (the descriptor is not reached).

Nothing about the reader's values -- including the parent's value -- is assumed. -/
theorem parentSide_outwardChild_comparison_independent_of_labels
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (stage : LocalizedCumulativeRule45Stage)
    (view : input.LocalizedDependencyView target)
    (readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      Nonempty (ParentOutwardComparisonWitness input stage readLabel target view
        { occurrence := certificate.parent, previous? := some target } child) := by
  let parentCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := certificate.parent, previous? := some target }
  let targetCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := some certificate.parent }
  intro child slot childPresent childAddress
  have parentValid : input.LocalizedRerootCursorValid
      { occurrence := certificate.parent, previous? := some target } := by
    change certificate.parent.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1
    exact certificate.parent_mem_neighborFrames input
  have childrenDerived := input.executableLocalizedRerootChildren_declarative targetCursor
  have childValid : input.LocalizedRerootCursorValid child :=
    input.localizedRerootChild_valid targetCursor child
      (input.executableLocalizedRerootChildren targetCursor) childrenDerived childPresent
  obtain ⟨parentKey, parentBuilt⟩ :=
    exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input stage readLabel parentCursor parentValid
  obtain ⟨childKey, childBuilt⟩ :=
    exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input stage readLabel child childValid
  obtain ⟨actualParentKey, actualParentBuilt⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      stage target view parentCursor parentValid
  obtain ⟨actualChildKey, actualChildBuilt⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      stage target view child childValid
  obtain ⟨pureParent, pureParentBuilt⟩ :=
    input.exists_constitutionalKey_at_linear_bound parentCursor parentValid
  obtain ⟨pureChild, pureChildBuilt⟩ :=
    input.exists_constitutionalKey_at_linear_bound child childValid
  have parentHead :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_rule1b_head
      input stage readLabel (2 * (carrierFuel + 1)) parentCursor parentKey parentBuilt
  have childHead :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_rule1b_head
      input stage readLabel (2 * (carrierFuel + 1)) child childKey childBuilt
  have actualParentHead :=
    input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
      stage target view (2 * (carrierFuel + 1)) parentCursor actualParentKey
      actualParentBuilt
  have actualChildHead :=
    input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
      stage target view (2 * (carrierFuel + 1)) child actualChildKey
      actualChildBuilt
  have distanceNe := input.outwardChild_rule1bRootDistance_ne_parent
    target targetActive certificate child slot childPresent childAddress
  have compareResult := input.builtCumulativeKeys_constitutionalCompare_ne_eq
    parentKey childKey parentHead childHead distanceNe
  have actualCompareResult := input.builtCumulativeKeys_constitutionalCompare_ne_eq
    actualParentKey actualChildKey actualParentHead actualChildHead distanceNe
  have paramParentObservable :
      constitutionalObservable parentKey.constitutional =
        constitutionalObservable pureParent :=
    input.declarative_constitutional_observable_unique
      (2 * (carrierFuel + 1)) (2 * (carrierFuel + 1) + 1) parentCursor
      parentKey.constitutional pureParent
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
        stage readLabel (2 * (carrierFuel + 1)) parentCursor parentKey parentBuilt)
      (input.buildLocalizedRerootRuleMajorKeyExec?_sound
        (2 * (carrierFuel + 1) + 1) parentCursor pureParent pureParentBuilt)
  have paramChildObservable :
      constitutionalObservable childKey.constitutional =
        constitutionalObservable pureChild :=
    input.declarative_constitutional_observable_unique
      (2 * (carrierFuel + 1)) (2 * (carrierFuel + 1) + 1) child
      childKey.constitutional pureChild
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
        stage readLabel (2 * (carrierFuel + 1)) child childKey childBuilt)
      (input.buildLocalizedRerootRuleMajorKeyExec?_sound
        (2 * (carrierFuel + 1) + 1) child pureChild pureChildBuilt)
  have actualParentObservable :
      constitutionalObservable actualParentKey.constitutional =
        constitutionalObservable pureParent :=
    input.declarative_constitutional_observable_unique
      (2 * (carrierFuel + 1)) (2 * (carrierFuel + 1) + 1) parentCursor
      actualParentKey.constitutional pureParent
      (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
        stage target view (2 * (carrierFuel + 1)) parentCursor actualParentKey
        actualParentBuilt)
      (input.buildLocalizedRerootRuleMajorKeyExec?_sound
        (2 * (carrierFuel + 1) + 1) parentCursor pureParent pureParentBuilt)
  have actualChildObservable :
      constitutionalObservable actualChildKey.constitutional =
        constitutionalObservable pureChild :=
    input.declarative_constitutional_observable_unique
      (2 * (carrierFuel + 1)) (2 * (carrierFuel + 1) + 1) child
      actualChildKey.constitutional pureChild
      (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
        stage target view (2 * (carrierFuel + 1)) child actualChildKey
        actualChildBuilt)
      (input.buildLocalizedRerootRuleMajorKeyExec?_sound
        (2 * (carrierFuel + 1) + 1) child pureChild pureChildBuilt)
  have compareEqActual :
      OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional =
        OfficialRuleMajorKey.compare actualParentKey.constitutional
          actualChildKey.constitutional :=
    ruleMajor_compare_congr parentKey.constitutional childKey.constitutional
      actualParentKey.constitutional actualChildKey.constitutional
      (paramParentObservable.trans actualParentObservable.symm)
      (paramChildObservable.trans actualChildObservable.symm)
  have compareEqPure :
      OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional =
        OfficialRuleMajorKey.compare pureParent pureChild :=
    ruleMajor_compare_congr parentKey.constitutional childKey.constitutional
      pureParent pureChild paramParentObservable paramChildObservable
  have fullCompareEqActual :
      input.compareLocalizedRerootCumulativeRule45Keys parentKey childKey =
        input.compareLocalizedRerootCumulativeRule45Keys
          actualParentKey actualChildKey := by
    calc
      input.compareLocalizedRerootCumulativeRule45Keys parentKey childKey =
          OfficialRuleMajorKey.compare parentKey.constitutional
            childKey.constitutional :=
        compareResult.2
      _ = OfficialRuleMajorKey.compare actualParentKey.constitutional
            actualChildKey.constitutional :=
        compareEqActual
      _ = input.compareLocalizedRerootCumulativeRule45Keys
            actualParentKey actualChildKey :=
        actualCompareResult.2.symm
  exact
    ⟨{ parentKey := parentKey,
       childKey := childKey,
       actualParentKey := actualParentKey,
       actualChildKey := actualChildKey,
       pureParent := pureParent,
       pureChild := pureChild,
       parentBuilt := parentBuilt,
       childBuilt := childBuilt,
       actualParentBuilt := actualParentBuilt,
       actualChildBuilt := actualChildBuilt,
       pureParentBuilt := pureParentBuilt,
       pureChildBuilt := pureChildBuilt,
       parentHead := parentHead,
       childHead := childHead,
       constitutionalCompare_eq_actual := compareEqActual,
       constitutionalCompare_eq_pure := compareEqPure,
       constitutionalCompare_ne_eq := compareResult.1,
       fullCompare_eq_actual := fullCompareEqActual,
       fullCompare_eq_constitutional := compareResult.2,
       actualFullCompare_eq_constitutional := actualCompareResult.2 }⟩

/-! ## Whole-state instantiation

The dependency view and the unrestricted read are induced by the same whole state `s`.  The
restricted side is therefore the shipped actual comparator; the arbitrary side reads
`s cursor.occurrence`, in particular an arbitrary parent label at the actual parent cursor. -/

/-- **Whole-state label noninterference.**  Instantiating the parametric theorem at the
unrestricted reader `s cursor.occurrence` and the view induced by `s` gives the same strict
comparison, equal to the shipped restricted comparison and to the pure constitutional comparison,
with the full cumulative value decided at the constitutional component.  The conclusion is a
`Nonempty` of the `Type`-valued witness package, so the package itself is not asserted as a
theorem result; the witnesses are eliminated in the state-independence corollary. -/
theorem wholeState_parentSide_outwardChild_comparison_noninterference
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (stage : LocalizedCumulativeRule45Stage)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      Nonempty (ParentOutwardComparisonWitness input stage
        (wholeStateLabel input state) target
        (input.localizedDependencyView state target)
        { occurrence := certificate.parent, previous? := some target } child) :=
  parentSide_outwardChild_comparison_independent_of_labels input target targetActive
    certificate stage (input.localizedDependencyView state target)
    (wholeStateLabel input state)

/-- **The comparison is the same for two arbitrary whole states.**  The parent labels, and indeed
every label of the two states, may differ; the strict parent-versus-outward `Ordering` is
literally equal.  This is the state-level form of parent-label noninterference: specialising the
two states to agree everywhere except at the actual parent coordinate yields the statement that
changing only the unrestricted parent label cannot change the comparison. -/
theorem wholeState_parentSide_outwardChild_comparison_state_independent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (stage : LocalizedCumulativeRule45Stage)
    (firstState secondState : input.LocalizedAuxiliaryState carrierFuel) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      ∃ firstParentKey firstChildKey secondParentKey secondChildKey,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?
            stage (wholeStateLabel input firstState) (2 * (carrierFuel + 1))
            { occurrence := certificate.parent, previous? := some target } =
          some firstParentKey ∧
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?
            stage (wholeStateLabel input firstState) (2 * (carrierFuel + 1))
            child = some firstChildKey ∧
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?
            stage (wholeStateLabel input secondState) (2 * (carrierFuel + 1))
            { occurrence := certificate.parent, previous? := some target } =
          some secondParentKey ∧
        input.buildLocalizedRerootCumulativeRule45KeyWithRead?
            stage (wholeStateLabel input secondState) (2 * (carrierFuel + 1))
            child = some secondChildKey ∧
        input.compareLocalizedRerootCumulativeRule45Keys
            firstParentKey firstChildKey =
          input.compareLocalizedRerootCumulativeRule45Keys
            secondParentKey secondChildKey := by
  intro child slot childPresent childAddress
  obtain ⟨firstWitness⟩ :=
    wholeState_parentSide_outwardChild_comparison_noninterference input target
      targetActive certificate stage firstState child slot childPresent childAddress
  obtain ⟨secondWitness⟩ :=
    wholeState_parentSide_outwardChild_comparison_noninterference input target
      targetActive certificate stage secondState child slot childPresent childAddress
  have samePureParent : firstWitness.pureParent = secondWitness.pureParent := by
    have injected := firstWitness.pureParentBuilt.symm.trans secondWitness.pureParentBuilt
    simpa only [Option.some.injEq] using injected
  have samePureChild : firstWitness.pureChild = secondWitness.pureChild := by
    have injected := firstWitness.pureChildBuilt.symm.trans secondWitness.pureChildBuilt
    simpa only [Option.some.injEq] using injected
  refine
    ⟨firstWitness.parentKey, firstWitness.childKey,
      secondWitness.parentKey, secondWitness.childKey,
      firstWitness.parentBuilt, firstWitness.childBuilt,
      secondWitness.parentBuilt, secondWitness.childBuilt, ?_⟩
  calc
    input.compareLocalizedRerootCumulativeRule45Keys
        firstWitness.parentKey firstWitness.childKey =
        OfficialRuleMajorKey.compare firstWitness.parentKey.constitutional
          firstWitness.childKey.constitutional :=
      firstWitness.fullCompare_eq_constitutional
    _ = OfficialRuleMajorKey.compare firstWitness.pureParent
          firstWitness.pureChild :=
      firstWitness.constitutionalCompare_eq_pure
    _ = OfficialRuleMajorKey.compare secondWitness.pureParent
          secondWitness.pureChild := by
      simp only [samePureParent, samePureChild]
    _ = OfficialRuleMajorKey.compare secondWitness.parentKey.constitutional
          secondWitness.childKey.constitutional :=
      secondWitness.constitutionalCompare_eq_pure.symm
    _ = input.compareLocalizedRerootCumulativeRule45Keys
          secondWitness.parentKey secondWitness.childKey :=
      secondWitness.fullCompare_eq_constitutional.symm

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.wholeStateLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.restrictedLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_of_budget_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_rule1b_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.parentCursor_not_depthDependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.restrictedLabel_parentCursor_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.wholeStateLabel_parentCursor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.outwardChild_depthDependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.restrictedLabel_eq_wholeStateLabel_of_outwardChild
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.parentSide_outwardChild_comparison_independent_of_labels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.wholeState_parentSide_outwardChild_comparison_noninterference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.wholeState_parentSide_outwardChild_comparison_state_independent

end WholeStateCumulativeLabels
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
