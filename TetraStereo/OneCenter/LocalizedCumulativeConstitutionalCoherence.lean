import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Constitutional coherence of cumulative Rules-4a--5 keys

A cumulative Rules-4a--5 reroot key carries a complete constitutional `OfficialRuleMajorKey` ahead
of its cumulative descriptor projection.  This module proves that this constitutional component is
exactly the ordinary rule-major reroot derivation, and therefore that the constitutional observable
of a successful cumulative build depends only on the cursor and the recursion budget -- never on the
descriptor stage, the dependency target, the restricted state view, or the descriptor observations.

The results here are the constitutional half of the parent-dependency noninterference argument:
descriptor-selecting stages may be varied freely without moving the Rules-1a--2 comparison used to
assign sibling order.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## Descending cumulative order transports to the constitutional component -/

/-- Descending cumulative sibling order projects to descending rule-major order on the
constitutional components. -/
theorem cumulative_descending_constitutional
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending keys) :
    OfficialRuleMajorKey.Descending (keys.map (·.constitutional)) := by
  apply List.Pairwise.map (fun key => key.constitutional) _ descending
  intro left right ordered lower
  apply ordered
  simp [compareLocalizedRerootCumulativeRule45Keys, compareLex, Ordering.byKey, lower]

/-! ## Projecting cumulative derivations to pure constitutional derivations -/

/-- Pointwise projection of a cumulative child-derivation list to the existing rule-major list
relation, given a projection of the single-key relation at the same recursion budget. -/
theorem projected_cumulative_constitutional_key_list
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (project : ∀ cursor key,
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        stage target view fuel cursor key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional) :
    ∀ cursors keys,
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList
        stage target view fuel cursors keys →
      input.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors
        (keys.map (·.constitutional))
  | [], keys, derived => by
      cases derived
      exact .nil fuel
  | cursor :: cursors, keys, derived => by
      cases derived with
      | cons head tail =>
          exact .cons (project cursor _ head)
            (projected_cumulative_constitutional_key_list
              input stage target view project cursors _ tail)

/-- Every independent cumulative Rules-4a--5 derivation contains a pure constitutional derivation.
Only the descriptor observation is discarded; the exact reroot frame, the child recursion, the
permutation, and the descending order all survive. -/
theorem DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        stage target view fuel cursor key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key meaning
      cases meaning with
      | terminal frame empty _ => exact .terminal frame empty
  | succ fuel ih =>
      intro cursor key meaning
      cases meaning with
      | terminal frame empty _ => exact .terminal frame empty
      | branch frame nonempty _ childDerivations ranking descending =>
          exact .branch frame nonempty
            (projected_cumulative_constitutional_key_list
              input stage target view ih _ _ childDerivations)
            (ranking.map (·.constitutional))
            (input.cumulative_descending_constitutional _ descending)

/-- Pointwise projection of every cumulative child derivation to the existing rule-major list
relation. -/
theorem DeclarativeLocalizedRerootCumulativeRule45KeyList_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursors keys,
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList
        stage target view fuel cursors keys →
      input.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors
        (keys.map (·.constitutional))
  | fuel, [], keys, derived => by
      cases derived
      exact .nil fuel
  | fuel, cursor :: cursors, keys, derived => by
      cases derived with
      | cons head tail =>
          exact .cons
            (DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
              input stage target view fuel cursor _ head)
            (DeclarativeLocalizedRerootCumulativeRule45KeyList_constitutional_derived
              input stage target view fuel cursors _ tail)

/-- Every successful cumulative compilation carries a pure constitutional derivation of its
constitutional component. -/
theorem buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional := by
  intro fuel cursor key computed
  exact input.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
    stage target view fuel cursor key
    (input.buildLocalizedRerootCumulativeRule45Key?_sound
      stage target view fuel cursor key computed)

/-! ## Constitutional observable coherence across cumulative builds -/

/-- Two successful cumulative builds at the same cursor have equal constitutional observables,
regardless of descriptor stage, dependency target, restricted state view, or recursion budget. -/
theorem cumulative_builds_constitutional_observable_equal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {leftFuel rightFuel : Nat}
    {leftStage rightStage : LocalizedCumulativeRule45Stage}
    {leftTarget rightTarget : input.LocalizedCIPOccurrence carrierFuel}
    {leftView : input.LocalizedDependencyView leftTarget}
    {rightView : input.LocalizedDependencyView rightTarget}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftComputed : input.buildLocalizedRerootCumulativeRule45Key?
      leftStage leftTarget leftView leftFuel cursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45Key?
      rightStage rightTarget rightView rightFuel cursor = some rightKey) :
    constitutionalObservable leftKey.constitutional =
      constitutionalObservable rightKey.constitutional :=
  input.declarative_constitutional_observable_unique leftFuel rightFuel cursor
    leftKey.constitutional rightKey.constitutional
    (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
      leftStage leftTarget leftView leftFuel cursor leftKey leftComputed)
    (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
      rightStage rightTarget rightView rightFuel cursor rightKey rightComputed)

/-- A successful plain rule-major build and a successful cumulative build at the same cursor have
equal constitutional observables.  No equality of the cumulative descriptor is required. -/
theorem plain_and_cumulative_constitutional_observable_equal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (plainFuel cumulativeFuel : Nat)
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (plainKey : OfficialRuleMajorKey input.Atom)
    (cumulativeKey : input.LocalizedRerootCumulativeRule45Key)
    (plainComputed : input.buildLocalizedRerootRuleMajorKey?
      plainFuel cursor = some plainKey)
    (cumulativeComputed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view cumulativeFuel cursor = some cumulativeKey) :
    constitutionalObservable plainKey =
      constitutionalObservable cumulativeKey.constitutional :=
  input.compiled_constitutional_observable_eq_derived
    plainFuel cumulativeFuel cursor plainKey cumulativeKey.constitutional
    plainComputed
    (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
      stage target view cumulativeFuel cursor cumulativeKey cumulativeComputed)

/-- The constitutional comparator is insensitive to the descriptor stage, target, and view of a
cumulative build on each side independently: comparing the constitutional components of two
cumulative keys built at independent cursors equals comparing the corresponding plain rule-major
builds at those same cursors.  Left cumulative and left plain builds share the left cursor; right
cumulative and right plain builds share the right cursor.  Only observables are identified;
provenance metadata and cumulative descriptors need not agree, and the two sides need not share a
cursor. -/
theorem cumulative_constitutional_compare_congr
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    {leftCumulativeFuel rightCumulativeFuel : Nat}
    {leftPlainFuel rightPlainFuel : Nat}
    {leftStage rightStage : LocalizedCumulativeRule45Stage}
    {leftTarget rightTarget : input.LocalizedCIPOccurrence carrierFuel}
    {leftView : input.LocalizedDependencyView leftTarget}
    {rightView : input.LocalizedDependencyView rightTarget}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    {leftPlain rightPlain : OfficialRuleMajorKey input.Atom}
    (leftComputed : input.buildLocalizedRerootCumulativeRule45Key?
      leftStage leftTarget leftView leftCumulativeFuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45Key?
      rightStage rightTarget rightView rightCumulativeFuel rightCursor = some rightKey)
    (leftPlainComputed : input.buildLocalizedRerootRuleMajorKey?
      leftPlainFuel leftCursor = some leftPlain)
    (rightPlainComputed : input.buildLocalizedRerootRuleMajorKey?
      rightPlainFuel rightCursor = some rightPlain) :
    OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
      OfficialRuleMajorKey.compare leftPlain rightPlain :=
  ruleMajor_compare_congr
    leftKey.constitutional rightKey.constitutional leftPlain rightPlain
    ((input.compiled_constitutional_observable_eq_derived
        leftPlainFuel leftCumulativeFuel leftCursor leftPlain leftKey.constitutional
        leftPlainComputed
        (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
          leftStage leftTarget leftView leftCumulativeFuel leftCursor leftKey leftComputed)).symm)
    ((input.compiled_constitutional_observable_eq_derived
        rightPlainFuel rightCumulativeFuel rightCursor rightPlain rightKey.constitutional
        rightPlainComputed
        (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
          rightStage rightTarget rightView rightCumulativeFuel rightCursor rightKey rightComputed)).symm)

/-! ## Kernel-authority guards

Every exported theorem above combines existing kernel-safe theorems and reductions; each is closed
by kernel reduction and must pass the project-wide kernel-only check. -/

assert_kernel_only cumulative_descending_constitutional
assert_kernel_only projected_cumulative_constitutional_key_list
assert_kernel_only DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
assert_kernel_only DeclarativeLocalizedRerootCumulativeRule45KeyList_constitutional_derived
assert_kernel_only buildLocalizedRerootCumulativeRule45Key?_constitutional_derived
assert_kernel_only cumulative_builds_constitutional_observable_equal
assert_kernel_only plain_and_cumulative_constitutional_observable_equal
assert_kernel_only cumulative_constitutional_compare_congr

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
