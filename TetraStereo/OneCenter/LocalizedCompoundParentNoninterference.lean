import TetraStereo.OneCenter.FullStateParentNoninterference
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key
import TetraStereo.OneCenter.OfficialRuleMajorCompilerProjectionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Compound through-Rule-5 noninterference for the parent/outward pair

`LocalizedRerootCompoundRule45Key` compares two complete through-Rule-5 keys by first comparing
the cumulative Rules-4a--5 key of the compound Rules-4b/4c prefix, and only after an exact tie
does it inspect criterion (c)(i)'s reference count, the Rule-4b/4c readings and the two common
Rule-5 readings.  Consequently, whenever the Rule-4a key comparison is strict, the full
`ConstitutionalRule5Comparison` record is the strict constitutional decision with `pseudo = false`;
nothing downstream -- references, reference count, Rule-4b/4c readings, common-R/common-S readings
or any descriptor component carried inside them -- can change it.

The first part of this module proves that short circuit directly from the actual comparator, in
both directions.  No key equality, no sorting hypothesis and no final comparison equation is
assumed: the record is *derived* from the definition of `compareLocalizedRerootCompoundThroughRule5`
and the already-proved source-ordered Rule-4a gate of the compound comparator.  The same section
records reflexivity of the compound comparator: a key compared with itself yields
`{ ordering := .eq, pseudo := false }`, so the `eq` branch of the downstream reader and of the
sorting comparator is covered rather than assumed absent.

The second part specializes the result to the parent-versus-outward cumulative keys supplied by
`FullStateParentNoninterference`.  That module constructs, at the proved budget
`2 * (carrierFuel + 1)`, a `ParentOutwardComparisonWitness` whose parent-side and outward-side
keys have a strict constitutional comparison and whose full cumulative comparator is already
decided at that constitutional component.  Rebuilding a through-Rule-5 compound key around those
cumulative components with *arbitrary* remaining fields therefore yields the exact record
`{ ordering := constitutional, pseudo := false }`, independently of every remaining field.  In
particular the stored parent labels (and hence the parent's Rule-4b references and readings) are
irrelevant to the pair output even though the two compound keys are not equal and are never proved
equal.

The final endpoints package this as a whole-state theorem: for a real active-simple target with an
explicit parent-frame certificate and an explicit outward child membership, there is a witness for
which the whole-state-reader pair record literally equals the restricted-reader pair record.  The
remaining fields of all four compound keys may be chosen independently.  A further endpoint feeds
the shipped actual compound builder `buildLocalizedRerootCompoundRule45Key?` into the same short
circuit, exposing its `.rule4a` projection; that is the composition seam a parametric compound
builder can reuse.

## Scope

* The source profile is the implemented original-root proposed-2018 `rule1bRootDistance` used by
  the repository; nothing here asserts a public rebased runtime or a 2013 duplicate-only claim.
* The theorem is about the through-Rule-5 comparison record only.  It does not claim equality of
  the underlying cumulative keys, of descriptors, or of Rule-4b reference selections.
* All successes are supplied either by the existing GREEN witness theorems or by explicit
  `buildLocalizedRerootCompoundRule45Key?` certificates; no build is postulated without evidence.
-/

namespace CertifiedLocalizedCIPInput

open WholeStateCumulativeLabels

/-! ## Rebuilding a compound key around a prescribed Rule-4a cumulative component

The through-Rule-5 comparator reads only `key.prior.rule4aKey` before the short circuit fires.  The
constructor below makes that independence explicit: the cumulative Rules-4a--5 key is prescribed,
while the reference list, reference-count priority, Rule-4b/4c readings and both common Rule-5
readings are arbitrary. -/

/-- A through-Rule-5 compound key with a prescribed cumulative Rules-4a--5 component and arbitrary
remaining fields. -/
def compoundRule45KeyOfRule4a
    (input : CertifiedLocalizedCIPInput)
    (rule4aKey : input.LocalizedRerootCumulativeRule45Key)
    (references : List RS)
    (referenceCountPriority : Nat)
    (readings : List input.LocalizedRerootRule4bcReading)
    (rule5Readings : List input.LocalizedRerootRule5Reading) :
    input.LocalizedRerootCompoundRule45Key :=
  { prior :=
      { rule4aKey := rule4aKey
        references := references
        referenceCountPriority := referenceCountPriority
        readings := readings }
    rule5Readings := rule5Readings }

/-! ## The Rule-4a short circuit -/

/-- **Exact through-Rule-5 record at a strict Rule-4a decision.**

If the cumulative Rules-4a--5 components of the compound prefixes compare non-equal, the source
order already forbids the reference count, readings and Rule-5 layers from being inspected.  The
full record is exactly the Rule-4a comparison with `pseudo := false`; no hypothesis is placed on
any remaining field. -/
theorem compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (rule4aNe : input.compareLocalizedRerootCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := input.compareLocalizedRerootCumulativeRule45Keys
          left.prior.rule4aKey right.prior.rule4aKey
        pseudo := false } := by
  have priorEq :=
    input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      left.prior right.prior rule4aNe
  unfold compareLocalizedRerootCompoundThroughRule5
  dsimp only
  rw [priorEq]
  rw [if_pos (bne_iff_ne.mpr rule4aNe)]

/-- The `lt` orientation of the Rule-4a short circuit. -/
theorem compareLocalizedRerootCompoundThroughRule5_eq_lt_of_rule4a_lt
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (rule4aLt : input.compareLocalizedRerootCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey = Ordering.lt) :
    input.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := Ordering.lt, pseudo := false } := by
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
    left right (by rw [rule4aLt]; decide), rule4aLt]

/-- The `gt` orientation of the Rule-4a short circuit. -/
theorem compareLocalizedRerootCompoundThroughRule5_eq_gt_of_rule4a_gt
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (rule4aGt : input.compareLocalizedRerootCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey = Ordering.gt) :
    input.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := Ordering.gt, pseudo := false } := by
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
    left right (by rw [rule4aGt]; decide), rule4aGt]

/-- The same short circuit with the two orientations of the pair exchanged. -/
theorem compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq_swap
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (rule4aNe : input.compareLocalizedRerootCumulativeRule45Keys
      right.prior.rule4aKey left.prior.rule4aKey ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5 right left =
      { ordering := input.compareLocalizedRerootCumulativeRule45Keys
          right.prior.rule4aKey left.prior.rule4aKey
        pseudo := false } :=
  input.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
    right left rule4aNe

/-- **Exact through-Rule-5 record at a strict constitutional Rule-4a decision.**

This is the form consumed by the whole-state witness: the cumulative Rule-4a comparison is known
to be decided at its constitutional component and to be strict.  The record is exactly that
constitutional ordering with `pseudo := false`. -/
theorem compareLocalizedRerootCompoundThroughRule5_eq_constitutional_of_rule4a
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (rule4aConstitutional : input.compareLocalizedRerootCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey =
        OfficialRuleMajorKey.compare left.prior.rule4aKey.constitutional
          right.prior.rule4aKey.constitutional)
    (constitutionalNe : OfficialRuleMajorKey.compare
      left.prior.rule4aKey.constitutional right.prior.rule4aKey.constitutional ≠
        Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := OfficialRuleMajorKey.compare left.prior.rule4aKey.constitutional
          right.prior.rule4aKey.constitutional
        pseudo := false } := by
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
    left right (by rw [rule4aConstitutional]; exact constitutionalNe),
    rule4aConstitutional]

/-! ## Reflexivity of every layer the short circuit reads

The strict branch above is only half of the comparator contract: the structural sibling sort also
takes the `eq` branch, where two syntactically identical keys meet.  The following self-comparison
results construct those `eq` facts from the actual comparators, so no caller needs to assume that
only distinct keys are ever compared. -/

/-- The cumulative Rule-4a--5 priority vector comparator is reflexive. -/
theorem compareLocalizedCumulativeRule45Priority_self
    (values : List Nat) :
    compareLocalizedCumulativeRule45Priority values values = Ordering.eq :=
  CompilerProjectionFidelity.list_compareLex_self OfficialRuleMajorKey.compareNat
    CompilerProjectionFidelity.compareNat_self values

/-- The full constitutional rule-major comparator is reflexive. -/
theorem compareOfficialRuleMajorKey_self {V : Type*}
    (key : OfficialRuleMajorKey V) :
    OfficialRuleMajorKey.compare key key = Ordering.eq := by
  rw [CompilerProjectionFidelity.compare_eq_compareTriple]
  exact CompilerProjectionFidelity.compareTriple_self _

/-- The cumulative Rules-4a--5 key comparator is reflexive. -/
theorem compareLocalizedRerootCumulativeRule45Keys_self
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    input.compareLocalizedRerootCumulativeRule45Keys key key = Ordering.eq := by
  unfold compareLocalizedRerootCumulativeRule45Keys
  rw [compareLex_eq_eq]
  refine ⟨?_, ?_⟩
  · exact compareOfficialRuleMajorKey_self key.constitutional
  · exact CompilerProjectionFidelity.compareSparseLayers_self
      compareLocalizedCumulativeRule45Priority
      (fun value => compareLocalizedCumulativeRule45Priority_self value)
      key.descriptor

/-- The Rule-4b projection comparison of one alternative is reflexive. -/
theorem compareLocalizedRerootRule4bcReadingsByRule4b_self
    (input : CertifiedLocalizedCIPInput)
    (reading : input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b reading reading = Ordering.eq :=
  CompilerProjectionFidelity.compareSparseLayers_self
    compareLocalizedCumulativeRule45Priority
    (fun value => compareLocalizedCumulativeRule45Priority_self value)
    reading.rule4bKey.descriptor

/-- The canonical Rule-4b reading-list comparator is reflexive. -/
theorem compareLocalizedRerootCompoundRule4bReadings_self
    (input : CertifiedLocalizedCIPInput)
    (readings : List input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootCompoundRule4bReadings readings readings = Ordering.eq :=
  CompilerProjectionFidelity.list_compareLex_self
    input.compareLocalizedRerootRule4bcReadingsByRule4b
    (fun reading => compareLocalizedRerootRule4bcReadingsByRule4b_self input reading)
    readings

/-- The canonical cumulative Rule-4c reading-list comparator is reflexive. -/
theorem compareLocalizedRerootCompoundRule4cReadings_self
    (input : CertifiedLocalizedCIPInput)
    (readings : List input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootCompoundRule4cReadings readings readings = Ordering.eq :=
  CompilerProjectionFidelity.list_compareLex_self
    (Ordering.byKey (fun reading : input.LocalizedRerootRule4bcReading =>
        reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
    (fun reading => CompilerProjectionFidelity.compareSparseLayers_self
      compareLocalizedCumulativeRule45Priority
      (fun value => compareLocalizedCumulativeRule45Priority_self value)
      reading.rule4cKey.descriptor)
    readings

/-- The compound Rules-4b/4c comparator is reflexive, including its reference-count layer. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_self
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCompoundRule4bcKey) :
    input.compareLocalizedRerootCompoundRule4bcKeys key key = Ordering.eq := by
  rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff]
  exact ⟨compareLocalizedRerootCumulativeRule45Keys_self input key.rule4aKey,
    Std.ReflOrd.compare_self,
    compareLocalizedRerootCompoundRule4bReadings_self input key.readings,
    compareLocalizedRerootCompoundRule4cReadings_self input key.readings⟩

/-- The common-reference Rule-5 reading-list comparator is reflexive. -/
theorem compareLocalizedRerootCompoundRule5Readings_self
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    (readings : List input.LocalizedRerootRule5Reading) :
    input.compareLocalizedRerootCompoundRule5Readings
      commonReference readings readings = Ordering.eq :=
  CompilerProjectionFidelity.list_compareLex_self
    (Ordering.byKey (input.localizedRerootRule5Descriptor commonReference)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
    (fun reading => CompilerProjectionFidelity.compareSparseLayers_self
      compareLocalizedCumulativeRule45Priority
      (fun value => compareLocalizedCumulativeRule45Priority_self value)
      (input.localizedRerootRule5Descriptor commonReference reading))
    readings

/-- **A compound key compared with itself is exactly `eq` and non-pseudo.**

Every layer read by `compareLocalizedRerootCompoundThroughRule5` is reflexive, so the `eq` branch
of the Rule-4a gate and of the common-R reading is taken; the record is
`{ ordering := .eq, pseudo := false }`.  This is independent of the sorter's assumption that only
distinct keys are compared. -/
theorem compareLocalizedRerootCompoundThroughRule5_self
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCompoundRule45Key) :
    input.compareLocalizedRerootCompoundThroughRule5 key key =
      { ordering := Ordering.eq, pseudo := false } := by
  have priorSelf := compareLocalizedRerootCompoundRule4bcKeys_self input key.prior
  have cmpRSelf :=
    compareLocalizedRerootCompoundRule5Readings_self input .R key.rule5Readings
  unfold compareLocalizedRerootCompoundThroughRule5
  dsimp only
  rw [priorSelf]
  rw [if_neg (by decide)]
  rw [cmpRSelf]

/-- **Remaining compound components are irrelevant.**

Two compound pairs with the same prescribed Rule-4a cumulative components have literally the same
through-Rule-5 record, whatever their references, reference-count priorities, Rule-4b/4c readings,
common-R/common-S Rule-5 readings or embedded descriptor components are.  The cumulative keys are
not assumed equal; only the strict constitutional comparison of the two prescribed components is
used. -/
theorem compareLocalizedRerootCompoundThroughRule5_rule4a_components_irrelevant
    (input : CertifiedLocalizedCIPInput)
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
    (leftReferences rightReferences leftReferences' rightReferences' : List RS)
    (leftCount rightCount leftCount' rightCount' : Nat)
    (leftReadings rightReadings leftReadings' rightReadings' :
      List input.LocalizedRerootRule4bcReading)
    (leftRule5 rightRule5 leftRule5' rightRule5' :
      List input.LocalizedRerootRule5Reading)
    (rule4aConstitutional : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey rightKey =
        OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional)
    (constitutionalNe : OfficialRuleMajorKey.compare
      leftKey.constitutional rightKey.constitutional ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5
        (compoundRule45KeyOfRule4a input leftKey leftReferences leftCount
          leftReadings leftRule5)
        (compoundRule45KeyOfRule4a input rightKey rightReferences rightCount
          rightReadings rightRule5) =
      input.compareLocalizedRerootCompoundThroughRule5
        (compoundRule45KeyOfRule4a input leftKey leftReferences' leftCount'
          leftReadings' leftRule5')
        (compoundRule45KeyOfRule4a input rightKey rightReferences' rightCount'
          rightReadings' rightRule5') := by
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_constitutional_of_rule4a
    _ _ rule4aConstitutional constitutionalNe]
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_constitutional_of_rule4a
    _ _ rule4aConstitutional constitutionalNe]
  rfl

/-! ## Specialization to the GREEN parent/outward witness -/

/-- **The whole parent-side record of the witness, with arbitrary remaining fields.**

The parent-side and outward-side cumulative components of a `ParentOutwardComparisonWitness`
determine the whole through-Rule-5 record.  Nothing about the parent's stored label, its Rule-4b
references, the reference count, the Rule-4b/4c readings or the common Rule-5 readings is read. -/
theorem parentOutwardWitness_compoundThroughRule5_record
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {parentCursor childCursor : input.LocalizedRerootCursor carrierFuel}
    (witness : ParentOutwardComparisonWitness input stage readLabel target view
      parentCursor childCursor)
    (parentReferences childReferences : List RS)
    (parentCount childCount : Nat)
    (parentReadings childReadings : List input.LocalizedRerootRule4bcReading)
    (parentRule5 childRule5 : List input.LocalizedRerootRule5Reading) :
    input.compareLocalizedRerootCompoundThroughRule5
        (compoundRule45KeyOfRule4a input witness.parentKey parentReferences parentCount
          parentReadings parentRule5)
        (compoundRule45KeyOfRule4a input witness.childKey childReferences childCount
          childReadings childRule5) =
      { ordering := OfficialRuleMajorKey.compare witness.parentKey.constitutional
          witness.childKey.constitutional
        pseudo := false } :=
  input.compareLocalizedRerootCompoundThroughRule5_eq_constitutional_of_rule4a
    (compoundRule45KeyOfRule4a input witness.parentKey parentReferences parentCount
      parentReadings parentRule5)
    (compoundRule45KeyOfRule4a input witness.childKey childReferences childCount
      childReadings childRule5)
    witness.fullCompare_eq_constitutional
    witness.constitutionalCompare_ne_eq

/-- **The restricted-reader record of the witness, with arbitrary remaining fields.**

The witness also carries the shipped restricted-view keys `actualParentKey`/`actualChildKey`.  The
same short circuit applies to them, with its own arbitrary remaining fields. -/
theorem parentOutwardWitness_compoundThroughRule5_actualRecord
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {parentCursor childCursor : input.LocalizedRerootCursor carrierFuel}
    (witness : ParentOutwardComparisonWitness input stage readLabel target view
      parentCursor childCursor)
    (parentReferences childReferences : List RS)
    (parentCount childCount : Nat)
    (parentReadings childReadings : List input.LocalizedRerootRule4bcReading)
    (parentRule5 childRule5 : List input.LocalizedRerootRule5Reading) :
    input.compareLocalizedRerootCompoundThroughRule5
        (compoundRule45KeyOfRule4a input witness.actualParentKey parentReferences
          parentCount parentReadings parentRule5)
        (compoundRule45KeyOfRule4a input witness.actualChildKey childReferences
          childCount childReadings childRule5) =
      { ordering := OfficialRuleMajorKey.compare
          witness.actualParentKey.constitutional
          witness.actualChildKey.constitutional
        pseudo := false } :=
  input.compareLocalizedRerootCompoundThroughRule5_eq_constitutional_of_rule4a
    (compoundRule45KeyOfRule4a input witness.actualParentKey parentReferences
      parentCount parentReadings parentRule5)
    (compoundRule45KeyOfRule4a input witness.actualChildKey childReferences
      childCount childReadings childRule5)
    witness.actualFullCompare_eq_constitutional
    (fun h => witness.constitutionalCompare_ne_eq
      (witness.constitutionalCompare_eq_actual.trans h))

/-- **Whole-reader and restricted-reader pair records are literally equal.**

Within one witness, the arbitrary-reader parent/outward pair and the shipped restricted-view pair
have the same through-Rule-5 record, despite being built from different cumulative components and
despite carrying independently chosen remaining fields.  This is the record-level form of parent
reference noninterference; no equality of the underlying keys is asserted. -/
theorem parentOutwardWitness_compoundThroughRule5_actual_eq_arbitrary
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {parentCursor childCursor : input.LocalizedRerootCursor carrierFuel}
    (witness : ParentOutwardComparisonWitness input stage readLabel target view
      parentCursor childCursor)
    (parentReferences childReferences : List RS)
    (parentCount childCount : Nat)
    (parentReadings childReadings : List input.LocalizedRerootRule4bcReading)
    (parentRule5 childRule5 : List input.LocalizedRerootRule5Reading)
    (actualParentReferences actualChildReferences : List RS)
    (actualParentCount actualChildCount : Nat)
    (actualParentReadings actualChildReadings :
      List input.LocalizedRerootRule4bcReading)
    (actualParentRule5 actualChildRule5 : List input.LocalizedRerootRule5Reading) :
    input.compareLocalizedRerootCompoundThroughRule5
        (compoundRule45KeyOfRule4a input witness.parentKey parentReferences parentCount
          parentReadings parentRule5)
        (compoundRule45KeyOfRule4a input witness.childKey childReferences childCount
          childReadings childRule5) =
      input.compareLocalizedRerootCompoundThroughRule5
        (compoundRule45KeyOfRule4a input witness.actualParentKey actualParentReferences
          actualParentCount actualParentReadings actualParentRule5)
        (compoundRule45KeyOfRule4a input witness.actualChildKey actualChildReferences
          actualChildCount actualChildReadings actualChildRule5) := by
  rw [parentOutwardWitness_compoundThroughRule5_record input witness
        parentReferences childReferences parentCount childCount parentReadings
        childReadings parentRule5 childRule5,
      parentOutwardWitness_compoundThroughRule5_actualRecord input witness
        actualParentReferences actualChildReferences actualParentCount actualChildCount
        actualParentReadings actualChildReadings actualParentRule5 actualChildRule5,
      witness.constitutionalCompare_eq_actual]

/-! ## Projection of the shipped actual compound builder

`buildLocalizedRerootCompoundRule45Key?` builds its Rules-4b/4c prefix with the shipped
`buildLocalizedRerootCompoundRule4bcKey?`, whose first step is exactly
`buildLocalizedRerootCumulativeRule45Key? .rule4a`.  The next two lemmas expose that projection so
that a successfully built compound key can be fed to the short circuit above.  Success of the
compound build is an explicit certificate, not an assumption that the builder is total. -/

/-- A successful compound Rules-4b/4c build has its Rule-4a component built by the shipped
`.rule4a` cumulative builder at the same fuel and cursor. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_rule4a_built
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    ∃ rule4aKey,
      input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target view fuel cursor = some rule4aKey ∧
        key.rule4aKey = rule4aKey := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
      let alternatives := localizedRule4bcReferenceAlternatives references
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor alternatives with
      | none =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
          subst key
          exact ⟨rule4aKey, rfl, rfl⟩

/-- A successful through-Rule-5 compound build exposes its Rule-4a component as the shipped
`.rule4a` cumulative build at the same fuel and cursor. -/
theorem buildLocalizedRerootCompoundRule45Key?_rule4a_built
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel cursor = some key) :
    ∃ rule4aKey,
      input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target view fuel cursor = some rule4aKey ∧
        key.prior.rule4aKey = rule4aKey := by
  unfold buildLocalizedRerootCompoundRule45Key? at computed
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      cases readingsComputed : input.buildLocalizedRerootRule5Readings?
          target view fuel cursor prior.readings with
      | none => simp [priorComputed, readingsComputed] at computed
      | some readings =>
          simp [priorComputed, readingsComputed] at computed
          subst key
          exact buildLocalizedRerootCompoundRule4bcKey?_rule4a_built input target
            view fuel cursor prior priorComputed

/-- **The shipped actual compound builder at the parent/outward pair is strict and non-pseudo.**

For a witness whose cumulative keys were compiled at the canonical Rules-4a stage (the stage the
compound builder itself uses), any two successfully built compound keys at the same
`2 * (carrierFuel + 1)` budget reduce to the witness's strict constitutional comparison with
`pseudo := false`.  The remaining Rule-4b/4c and Rule-5 readings produced by the builder are
irrelevant. -/
theorem builtCompoundKeys_throughRule5_constitutional_record
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {readLabel : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {parentCursor childCursor : input.LocalizedRerootCursor carrierFuel}
    (witness : ParentOutwardComparisonWitness input .rule4a readLabel target view
      parentCursor childCursor)
    (parentKey childKey : input.LocalizedRerootCompoundRule45Key)
    (parentComputed : input.buildLocalizedRerootCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) parentCursor = some parentKey)
    (childComputed : input.buildLocalizedRerootCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) childCursor = some childKey) :
    input.compareLocalizedRerootCompoundThroughRule5 parentKey childKey =
      { ordering := OfficialRuleMajorKey.compare
          witness.actualParentKey.constitutional
          witness.actualChildKey.constitutional
        pseudo := false } := by
  obtain ⟨parentRule4aKey, parentRule4aBuilt, parentRule4aEq⟩ :=
    buildLocalizedRerootCompoundRule45Key?_rule4a_built input target view
      (2 * (carrierFuel + 1)) parentCursor parentKey parentComputed
  obtain ⟨childRule4aKey, childRule4aBuilt, childRule4aEq⟩ :=
    buildLocalizedRerootCompoundRule45Key?_rule4a_built input target view
      (2 * (carrierFuel + 1)) childCursor childKey childComputed
  have parentSame : parentRule4aKey = witness.actualParentKey :=
    Option.some.inj (parentRule4aBuilt.symm.trans witness.actualParentBuilt)
  have childSame : childRule4aKey = witness.actualChildKey :=
    Option.some.inj (childRule4aBuilt.symm.trans witness.actualChildBuilt)
  have rule4aEq : input.compareLocalizedRerootCumulativeRule45Keys
      parentKey.prior.rule4aKey childKey.prior.rule4aKey =
      input.compareLocalizedRerootCumulativeRule45Keys
        witness.actualParentKey witness.actualChildKey := by
    rw [parentRule4aEq, childRule4aEq, parentSame, childSame]
  have rule4aNe : input.compareLocalizedRerootCumulativeRule45Keys
      parentKey.prior.rule4aKey childKey.prior.rule4aKey ≠ Ordering.eq := by
    rw [rule4aEq, witness.actualFullCompare_eq_constitutional]
    intro h
    exact witness.constitutionalCompare_ne_eq
      (witness.constitutionalCompare_eq_actual.trans h)
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
    parentKey childKey rule4aNe, rule4aEq,
    witness.actualFullCompare_eq_constitutional]

/-! ## Whole-state endpoint -/

/-- **Whole-state versus restricted-reader compound pair: full record equality.**

For an active-simple carrier occurrence with an explicit parent-frame certificate and an explicit
outward executable child, there is a `ParentOutwardComparisonWitness` for the whole-state reader
`wholeStateLabel input state` and the dependency view induced by `state`.  For that witness the
whole-reader compound pair and the shipped restricted-reader compound pair have exactly the same
`ConstitutionalRule5Comparison` record.  All four compound keys may carry arbitrary remaining
references, reference counts, Rule-4b/4c readings, Rule-5 readings and embedded descriptors; no key
equality is used or asserted.  In particular the arbitrary parent label stored in `state` cannot
change the pair output. -/
theorem wholeState_compoundThroughRule5_whole_restricted_record_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (stage : LocalizedCumulativeRule45Stage)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat)
    (childPresent : child ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := some certificate.parent })
    (childAddress : child.occurrence.1.address = target.1.address ++ [slot])
    (parentReferences childReferences : List RS)
    (parentCount childCount : Nat)
    (parentReadings childReadings : List input.LocalizedRerootRule4bcReading)
    (parentRule5 childRule5 : List input.LocalizedRerootRule5Reading)
    (actualParentReferences actualChildReferences : List RS)
    (actualParentCount actualChildCount : Nat)
    (actualParentReadings actualChildReadings :
      List input.LocalizedRerootRule4bcReading)
    (actualParentRule5 actualChildRule5 : List input.LocalizedRerootRule5Reading) :
    ∃ witness : ParentOutwardComparisonWitness input stage
        (wholeStateLabel input state) target
        (input.localizedDependencyView state target)
        { occurrence := certificate.parent, previous? := some target } child,
      input.compareLocalizedRerootCompoundThroughRule5
          (compoundRule45KeyOfRule4a input witness.parentKey parentReferences
            parentCount parentReadings parentRule5)
          (compoundRule45KeyOfRule4a input witness.childKey childReferences
            childCount childReadings childRule5) =
        input.compareLocalizedRerootCompoundThroughRule5
          (compoundRule45KeyOfRule4a input witness.actualParentKey
            actualParentReferences actualParentCount actualParentReadings
            actualParentRule5)
          (compoundRule45KeyOfRule4a input witness.actualChildKey
            actualChildReferences actualChildCount actualChildReadings
            actualChildRule5) := by
  obtain ⟨witness⟩ :=
    wholeState_parentSide_outwardChild_comparison_noninterference input target
      targetActive certificate stage state child slot childPresent childAddress
  exact ⟨witness,
    parentOutwardWitness_compoundThroughRule5_actual_eq_arbitrary input witness
      parentReferences childReferences parentCount childCount parentReadings
      childReadings parentRule5 childRule5 actualParentReferences
      actualChildReferences actualParentCount actualChildCount actualParentReadings
      actualChildReadings actualParentRule5 actualChildRule5⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundRule45KeyOfRule4a
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_lt_of_rule4a_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_gt_of_rule4a_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq_swap
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_constitutional_of_rule4a
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareOfficialRuleMajorKey_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootRule4bcReadingsByRule4b_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bReadings_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4cReadings_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule5Readings_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_rule4a_components_irrelevant
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentOutwardWitness_compoundThroughRule5_record
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentOutwardWitness_compoundThroughRule5_actualRecord
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentOutwardWitness_compoundThroughRule5_actual_eq_arbitrary
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_rule4a_built
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45Key?_rule4a_built
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.builtCompoundKeys_throughRule5_constitutional_record
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeState_compoundThroughRule5_whole_restricted_record_eq
