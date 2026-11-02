import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.KernelOnly

set_option autoImplicit false



























































namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput
namespace WholeStateCompoundLabels

/-! ## The built compound comparison witness -/

/-- A completed parent-versus-outward Rule-45 compound comparison together with the *actual* keys
returned by the two compound builders, at the proved budget `2 * (carrierFuel + 1)`.

`parentKey`/`childKey` are compiled from an arbitrary reader by the shared parametric compiler;
`actualParentKey`/`actualChildKey` are compiled by the shipped restricted-view compiler;
`pureParent`/`pureChild` are the executable pure constitutional keys.  The two remaining fields
state the reduction of each side's through-Rule-5 record to the *same* strict non-pseudo
constitutional ordering. -/
structure CompoundParentOutwardComparisonWitness
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (parentCursor childCursor : input.LocalizedRerootCursor carrierFuel) where
  /-- Parent-side key compiled from the arbitrary reader. -/
  parentKey : input.LocalizedRerootCompoundRule45Key
  /-- Outward-child key compiled from the arbitrary reader. -/
  childKey : input.LocalizedRerootCompoundRule45Key
  /-- Parent-side key compiled by the shipped restricted-view compiler. -/
  actualParentKey : input.LocalizedRerootCompoundRule45Key
  /-- Outward-child key compiled by the shipped restricted-view compiler. -/
  actualChildKey : input.LocalizedRerootCompoundRule45Key
  /-- Parent-side pure constitutional key. -/
  pureParent : OfficialRuleMajorKey input.Atom
  /-- Outward-child pure constitutional key. -/
  pureChild : OfficialRuleMajorKey input.Atom
  parentBuilt :
    input.buildLocalizedRerootCompoundRule45KeyWithRead? read
      (2 * (carrierFuel + 1)) parentCursor = some parentKey
  childBuilt :
    input.buildLocalizedRerootCompoundRule45KeyWithRead? read
      (2 * (carrierFuel + 1)) childCursor = some childKey
  actualParentBuilt :
    input.buildLocalizedRerootCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) parentCursor = some actualParentKey
  actualChildBuilt :
    input.buildLocalizedRerootCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) childCursor = some actualChildKey
  pureParentBuilt :
    input.buildLocalizedRerootRuleMajorKeyExec?
      (2 * (carrierFuel + 1) + 1) parentCursor = some pureParent
  pureChildBuilt :
    input.buildLocalizedRerootRuleMajorKeyExec?
      (2 * (carrierFuel + 1) + 1) childCursor = some pureChild
  /-- The arbitrary-reader through-Rule-5 record is the pure constitutional ordering, non-pseudo. -/
  wholeRecord_eq_pure :
    input.compareLocalizedRerootCompoundThroughRule5 parentKey childKey =
      { ordering := OfficialRuleMajorKey.compare pureParent pureChild, pseudo := false }
  /-- The shipped restricted-reader through-Rule-5 record is the same pure ordering, non-pseudo. -/
  actualRecord_eq_pure :
    input.compareLocalizedRerootCompoundThroughRule5 actualParentKey actualChildKey =
      { ordering := OfficialRuleMajorKey.compare pureParent pureChild, pseudo := false }

/-! ## The built compound parent-versus-outward noninterference theorem -/

/-- **Built compound parent-versus-outward comparison is independent of the label reader.**

For an active-simple target with an actual parent-frame certificate, an arbitrary dependency view,
and an *arbitrary* label reader `read`, every outward actual child cursor admits, as a `Nonempty`
of the `Type`-valued witness package, at the proved finite budget `2 * (carrierFuel + 1)`:

* the parent-side and child-side complete through-Rule-5 keys actually compiled from `read`;
* the shipped restricted-view keys actually compiled at the same budget;
* the executable pure constitutional keys at `2 * (carrierFuel + 1) + 1`;
* and the fact that both complete through-Rule-5 records equal the *same* strict non-pseudo
  constitutional ordering.

No value of `read` on the parent side or on the parent subtree is assumed equal to the restricted
read; only the strict Rule-1b constitutional short-circuit is used. -/
theorem compoundParentSide_outwardChild_comparison_independent_of_labels
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      Nonempty (CompoundParentOutwardComparisonWitness input read target view
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
    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
      read parentCursor parentValid
  obtain ⟨childKey, childBuilt⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
      read child childValid
  obtain ⟨actualParentKey, actualParentBuiltParam⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
      (fun cursor => input.localizedDependencyLabel target view cursor)
      parentCursor parentValid
  obtain ⟨actualChildKey, actualChildBuiltParam⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
      (fun cursor => input.localizedDependencyLabel target view cursor)
      child childValid
  have actualParentBuilt : input.buildLocalizedRerootCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) parentCursor = some actualParentKey := by
    rw [← input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
      target view (2 * (carrierFuel + 1)) parentCursor]
    exact actualParentBuiltParam
  have actualChildBuilt : input.buildLocalizedRerootCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) child = some actualChildKey := by
    rw [← input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
      target view (2 * (carrierFuel + 1)) child]
    exact actualChildBuiltParam
  obtain ⟨cumWitness⟩ :=
    WholeStateCumulativeLabels.parentSide_outwardChild_comparison_independent_of_labels
      input target targetActive certificate .rule4a view read child slot
      childPresent childAddress
  have cumParent_eq : cumWitness.parentKey = parentKey.prior.rule4aKey := by
    exact Option.some.inj (cumWitness.parentBuilt.symm.trans
      (input.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
        read (2 * (carrierFuel + 1)) parentCursor parentKey parentBuilt))
  have cumChild_eq : cumWitness.childKey = childKey.prior.rule4aKey := by
    exact Option.some.inj (cumWitness.childBuilt.symm.trans
      (input.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
        read (2 * (carrierFuel + 1)) child childKey childBuilt))
  obtain ⟨actualParentRule4aKey, actualParentRule4aBuilt, actualParentRule4aEq⟩ :=
    input.buildLocalizedRerootCompoundRule45Key?_rule4a_built
      target view (2 * (carrierFuel + 1)) parentCursor actualParentKey actualParentBuilt
  have actualParentRule4aKey_eq_cum :
      actualParentRule4aKey = cumWitness.actualParentKey :=
    Option.some.inj (actualParentRule4aBuilt.symm.trans cumWitness.actualParentBuilt)
  have actualParentRule4a_eq :
      actualParentKey.prior.rule4aKey = cumWitness.actualParentKey := by
    rw [actualParentRule4aEq, actualParentRule4aKey_eq_cum]
  obtain ⟨actualChildRule4aKey, actualChildRule4aBuilt, actualChildRule4aEq⟩ :=
    input.buildLocalizedRerootCompoundRule45Key?_rule4a_built
      target view (2 * (carrierFuel + 1)) child actualChildKey actualChildBuilt
  have actualChildRule4aKey_eq_cum :
      actualChildRule4aKey = cumWitness.actualChildKey :=
    Option.some.inj (actualChildRule4aBuilt.symm.trans cumWitness.actualChildBuilt)
  have actualChildRule4a_eq :
      actualChildKey.prior.rule4aKey = cumWitness.actualChildKey := by
    rw [actualChildRule4aEq, actualChildRule4aKey_eq_cum]
  have rule4aCompare_ne_eq : input.compareLocalizedRerootCumulativeRule45Keys
      parentKey.prior.rule4aKey childKey.prior.rule4aKey ≠ Ordering.eq := by
    rw [← cumParent_eq, ← cumChild_eq, cumWitness.fullCompare_eq_constitutional]
    exact cumWitness.constitutionalCompare_ne_eq
  have actualRule4aCompare_ne_eq : input.compareLocalizedRerootCumulativeRule45Keys
      actualParentKey.prior.rule4aKey actualChildKey.prior.rule4aKey ≠ Ordering.eq := by
    rw [actualParentRule4a_eq, actualChildRule4a_eq,
      cumWitness.actualFullCompare_eq_constitutional]
    intro h
    exact cumWitness.constitutionalCompare_ne_eq
      (cumWitness.constitutionalCompare_eq_actual.trans h)
  have wholeRecord : input.compareLocalizedRerootCompoundThroughRule5
      parentKey childKey =
    { ordering := input.compareLocalizedRerootCumulativeRule45Keys
        parentKey.prior.rule4aKey childKey.prior.rule4aKey, pseudo := false } :=
    input.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
      parentKey childKey rule4aCompare_ne_eq
  have actualRecord : input.compareLocalizedRerootCompoundThroughRule5
      actualParentKey actualChildKey =
    { ordering := input.compareLocalizedRerootCumulativeRule45Keys
        actualParentKey.prior.rule4aKey actualChildKey.prior.rule4aKey, pseudo := false } :=
    input.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
      actualParentKey actualChildKey actualRule4aCompare_ne_eq
  have wholeRecord_eq_pure : input.compareLocalizedRerootCompoundThroughRule5
      parentKey childKey =
    { ordering := OfficialRuleMajorKey.compare cumWitness.pureParent cumWitness.pureChild,
      pseudo := false } := by
    rw [wholeRecord, ← cumParent_eq, ← cumChild_eq,
      cumWitness.fullCompare_eq_constitutional, cumWitness.constitutionalCompare_eq_pure]
  have actualRecord_eq_pure : input.compareLocalizedRerootCompoundThroughRule5
      actualParentKey actualChildKey =
    { ordering := OfficialRuleMajorKey.compare cumWitness.pureParent cumWitness.pureChild,
      pseudo := false } := by
    rw [actualRecord, actualParentRule4a_eq, actualChildRule4a_eq,
      cumWitness.actualFullCompare_eq_constitutional, ← cumWitness.constitutionalCompare_eq_actual,
      cumWitness.constitutionalCompare_eq_pure]
  exact
    ⟨{ parentKey := parentKey,
       childKey := childKey,
       actualParentKey := actualParentKey,
       actualChildKey := actualChildKey,
       pureParent := cumWitness.pureParent,
       pureChild := cumWitness.pureChild,
       parentBuilt := parentBuilt,
       childBuilt := childBuilt,
       actualParentBuilt := actualParentBuilt,
       actualChildBuilt := actualChildBuilt,
       pureParentBuilt := cumWitness.pureParentBuilt,
       pureChildBuilt := cumWitness.pureChildBuilt,
       wholeRecord_eq_pure := wholeRecord_eq_pure,
       actualRecord_eq_pure := actualRecord_eq_pure }⟩

/-! ## Whole-state instantiation -/

/-- **Whole-state built compound label noninterference.**  Instantiating the parametric theorem at
the unrestricted reader `state cursor.occurrence` and the view induced by `state` gives the same
strict through-Rule-5 comparison, equal to the shipped restricted comparison, with the result
decided at the Rule-1b constitutional component and never marked pseudo. -/
theorem wholeState_compoundParentSide_outwardChild_comparison_noninterference
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      Nonempty (CompoundParentOutwardComparisonWitness input
        (WholeStateCumulativeLabels.wholeStateLabel input state) target
        (input.localizedDependencyView state target)
        { occurrence := certificate.parent, previous? := some target } child) :=
  compoundParentSide_outwardChild_comparison_independent_of_labels
    input target targetActive certificate
    (input.localizedDependencyView state target)
    (WholeStateCumulativeLabels.wholeStateLabel input state)

/-- **The built compound parent-versus-outward comparison is the same for two arbitrary whole
states.**  The parent labels, and indeed every label of the two states, may differ; the strict
through-Rule-5 `Ordering` is literally equal.  The two witnesses reduce to the *same* pure
constitutional comparison, which is independent of the state. -/
theorem wholeState_compoundParentSide_outwardChild_comparison_state_independent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (firstState secondState : input.LocalizedAuxiliaryState carrierFuel) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      ∃ firstParentKey firstChildKey secondParentKey secondChildKey,
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
            (WholeStateCumulativeLabels.wholeStateLabel input firstState)
            (2 * (carrierFuel + 1))
            { occurrence := certificate.parent, previous? := some target } =
          some firstParentKey ∧
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
            (WholeStateCumulativeLabels.wholeStateLabel input firstState)
            (2 * (carrierFuel + 1)) child = some firstChildKey ∧
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
            (WholeStateCumulativeLabels.wholeStateLabel input secondState)
            (2 * (carrierFuel + 1))
            { occurrence := certificate.parent, previous? := some target } =
          some secondParentKey ∧
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
            (WholeStateCumulativeLabels.wholeStateLabel input secondState)
            (2 * (carrierFuel + 1)) child = some secondChildKey ∧
        input.compareLocalizedRerootCompoundThroughRule5
            firstParentKey firstChildKey =
          input.compareLocalizedRerootCompoundThroughRule5
            secondParentKey secondChildKey := by
  intro child slot childPresent childAddress
  obtain ⟨firstWitness⟩ :=
    wholeState_compoundParentSide_outwardChild_comparison_noninterference input target
      targetActive certificate firstState child slot childPresent childAddress
  obtain ⟨secondWitness⟩ :=
    wholeState_compoundParentSide_outwardChild_comparison_noninterference input target
      targetActive certificate secondState child slot childPresent childAddress
  have samePureParent : firstWitness.pureParent = secondWitness.pureParent := by
    exact Option.some.inj (firstWitness.pureParentBuilt.symm.trans secondWitness.pureParentBuilt)
  have samePureChild : firstWitness.pureChild = secondWitness.pureChild := by
    exact Option.some.inj (firstWitness.pureChildBuilt.symm.trans secondWitness.pureChildBuilt)
  refine
    ⟨firstWitness.parentKey, firstWitness.childKey,
      secondWitness.parentKey, secondWitness.childKey,
      firstWitness.parentBuilt, firstWitness.childBuilt,
      secondWitness.parentBuilt, secondWitness.childBuilt, ?_⟩
  calc
    input.compareLocalizedRerootCompoundThroughRule5
        firstWitness.parentKey firstWitness.childKey =
        { ordering := OfficialRuleMajorKey.compare
            firstWitness.pureParent firstWitness.pureChild, pseudo := false } :=
      firstWitness.wholeRecord_eq_pure
    _ = { ordering := OfficialRuleMajorKey.compare
            secondWitness.pureParent secondWitness.pureChild, pseudo := false } := by
      simp only [samePureParent, samePureChild]
    _ = input.compareLocalizedRerootCompoundThroughRule5
          secondWitness.parentKey secondWitness.childKey :=
      secondWitness.wholeRecord_eq_pure.symm

/-! ## The source-level comparison-record bridge -/

/-- **Exact source-level bridge to the occurrence Rule-45 comparator.**  On every
parent-versus-outward ligand pair, the whole-state reader and the shipped restricted reader build
complete through-Rule-5 keys whose `localizedOccurrenceRule45ComparisonRecord` -- the exact value
`compareLocalizedOccurrenceThroughRule5At?` consumes -- is identical.  This is the step that turns
the reader-independence of the comparison into reader-independence of the tracked pairwise Rule-45
record. -/
theorem wholeState_parentSide_outwardChild_comparisonRecord_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      ∃ wholeParent wholeChild restrictedParent restrictedChild,
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
            (WholeStateCumulativeLabels.wholeStateLabel input state)
            (2 * (carrierFuel + 1))
            { occurrence := certificate.parent, previous? := some target } =
          some wholeParent ∧
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
            (WholeStateCumulativeLabels.wholeStateLabel input state)
            (2 * (carrierFuel + 1)) child = some wholeChild ∧
        input.buildLocalizedRerootCompoundRule45Key? target
            (input.localizedDependencyView state target)
            (2 * (carrierFuel + 1))
            { occurrence := certificate.parent, previous? := some target } =
          some restrictedParent ∧
        input.buildLocalizedRerootCompoundRule45Key? target
            (input.localizedDependencyView state target)
            (2 * (carrierFuel + 1)) child = some restrictedChild ∧
        localizedOccurrenceRule45ComparisonRecord
            (input.compareLocalizedRerootCompoundThroughRule5 wholeParent wholeChild) =
          localizedOccurrenceRule45ComparisonRecord
            (input.compareLocalizedRerootCompoundThroughRule5
              restrictedParent restrictedChild) := by
  intro child slot childPresent childAddress
  obtain ⟨witness⟩ :=
    wholeState_compoundParentSide_outwardChild_comparison_noninterference input target
      targetActive certificate state child slot childPresent childAddress
  refine ⟨witness.parentKey, witness.childKey,
    witness.actualParentKey, witness.actualChildKey,
    witness.parentBuilt, witness.childBuilt,
    witness.actualParentBuilt, witness.actualChildBuilt, ?_⟩
  exact congrArg localizedOccurrenceRule45ComparisonRecord
    (witness.wholeRecord_eq_pure.trans witness.actualRecord_eq_pure.symm)

end WholeStateCompoundLabels
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the built compound parent-versus-outward noninterference theorem, its
two whole-state corollaries, and the comparison-record bridge.  `assert_kernel_only` permits exactly
`propext`, `Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and
native/compiler trust.  The short-circuit and projection ingredients are already guarded in
`LocalizedCompoundParentNoninterference`, and the parametric totality/projection ingredients in
`LocalizedParametricCompoundRule45Key`. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCompoundLabels.compoundParentSide_outwardChild_comparison_independent_of_labels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCompoundLabels.wholeState_compoundParentSide_outwardChild_comparison_noninterference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCompoundLabels.wholeState_compoundParentSide_outwardChild_comparison_state_independent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCompoundLabels.wholeState_parentSide_outwardChild_comparisonRecord_eq
