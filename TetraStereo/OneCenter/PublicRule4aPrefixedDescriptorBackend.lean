import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule45
import TetraStereo.OneCenter.PublicParametricRule3Through5Descriptor
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Public Rule-4a-prefixed compound Rules-4a--5 backend

The shipped public compound comparator
`compareAromaticCanonicalRerootCompoundRule4bcKeys` starts with the Rule-4b reference-count
priority and never inspects `rule4aKey`:

```
reference-count priority  ->  Rule-4b readings  ->  Rule-4c readings
```

The localized comparator orders the same data as

```
Rule-4a cumulative key  ->  reference-count priority  ->  Rule-4b readings  ->  Rule-4c readings
```

P-92.5.1 (chiral precedes pseudoasymmetric precedes nonstereogenic) precedes
P-92.5.2.1(c)(i) (one reference descriptor precedes two), and Hanson 2018 states that the purpose of
Rule 4a is to exhaust the unit-kind comparison so that every later Rule-4b comparison is of the same
general type and the compared ranked-descriptor lists have equal length.  This module adds the
*smallest corrected public backend*: it reuses every existing key, builder, reading, point reader
and descriptor routine unchanged and prefixes the Rule-4a cumulative gate to the existing, unmodified
compound suffix.

## What is new here

* `compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys` — the corrected compound Rules-4a--4c
  comparator.  It uses the *actual* `compareAromaticCanonicalCumulativeRule45Keys` on `rule4aKey`
  before invoking the *actual* legacy suffix comparator.
* `AromaticCanonicalRule4aPrefixedCompoundRule4bcSemantics` and
  `...ThroughRule5Semantics` — named source semantics that expressly place Rule 4a before the
  reference count, with an explicit branch for the Rule-4a tie.
* `compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys` — the corresponding through-Rule-5
  ordering.
* `compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5` — the descriptor-facing record: a
  strict Rule-4a comparison returns its ordering with `pseudo := false`; an exact Rule-4a tie
  invokes the unchanged legacy through-Rule-5 record.

## Agreement and scope

Agreement with the legacy public backend is proved exactly where it holds: when the Rule-4a
comparison of the relevant actual pair ties, the corrected comparator, the corrected ordering and
the corrected record are literally the legacy ones.  No global equality is claimed, because on key
data with a strict Rule-4a comparison and a conflicting count suffix the two orders genuinely
differ.  Nothing here asserts that a builder-state witness is chemically realizable; the results are
statements about the actual existing builders and their actual comparison functions.
-/

/-! ## Corrected compound Rules-4a--4c comparison -/

/-- Corrected public compound Rules-4a--4c comparator.

The Rule-4a cumulative comparison is exhausted first; only an exact tie falls through to the
unchanged legacy suffix `referenceCountPriority -> Rule-4b readings -> Rule-4c readings`.  Every
projection and every suffix comparator is an existing definition. -/
def compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalRerootCompoundRule4bcKey →
      source.AromaticCanonicalRerootCompoundRule4bcKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.rule4aKey)
      source.compareAromaticCanonicalCumulativeRule45Keys)
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys

/-- Named source semantics of the corrected compound Rules-4a--4c comparison.

The result is the Rule-4a cumulative outcome whenever that outcome is strict, and the legacy
reference-count/Rule-4b/Rule-4c outcome only on an exact Rule-4a tie.  This is the schedule
required by P-92.5.1 before P-92.5.2.1(c)(i) and by the Hanson-2018 exhaust-Rule-4a-first
rationale. -/
def AromaticCanonicalRule4aPrefixedCompoundRule4bcSemantics
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (result : Ordering) : Prop :=
  result =
    match source.compareAromaticCanonicalCumulativeRule45Keys
        left.rule4aKey right.rule4aKey with
    | Ordering.eq => source.compareAromaticCanonicalRerootCompoundRule4bcKeys left right
    | other => other

/-- The corrected comparator satisfies its named semantics definitionally. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_semantics
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey) :
    source.AromaticCanonicalRule4aPrefixedCompoundRule4bcSemantics left right
      (source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys left right) := by
  unfold AromaticCanonicalRule4aPrefixedCompoundRule4bcSemantics
    compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
  generalize rule4aComparison :
      source.compareAromaticCanonicalCumulativeRule45Keys
        left.rule4aKey right.rule4aKey = outcome
  cases outcome <;> simp [rule4aComparison, compareLex, Ordering.byKey]

/-- **Strict Rule-4a prefix.**  A strict Rule-4a cumulative comparison decides the corrected
compound comparison outright; the count and the readings are never consulted. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_rule4a_of_ne
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (decisive : source.compareAromaticCanonicalCumulativeRule45Keys
      left.rule4aKey right.rule4aKey ≠ Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys left right =
      source.compareAromaticCanonicalCumulativeRule45Keys left.rule4aKey right.rule4aKey := by
  unfold compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
  generalize rule4aComparison :
      source.compareAromaticCanonicalCumulativeRule45Keys
        left.rule4aKey right.rule4aKey = outcome at decisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

/-- **Exact tie compatibility with the legacy public backend.**  When the Rule-4a cumulative
comparison ties, the corrected comparator is literally the shipped count-first comparator. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_legacy_of_rule4a_tie
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (tie : source.compareAromaticCanonicalCumulativeRule45Keys
      left.rule4aKey right.rule4aKey = Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys left right =
      source.compareAromaticCanonicalRerootCompoundRule4bcKeys left right := by
  unfold compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
  simp [compareLex, Ordering.byKey, tie]

/-- The corrected compound Rules-4a--4c comparator is transitive. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys := by
  letI : Std.TransCmp source.compareAromaticCanonicalCumulativeRule45Keys :=
    source.compareAromaticCanonicalCumulativeRule45Keys_transCmp
  letI : Std.TransCmp source.compareAromaticCanonicalRerootCompoundRule4bcKeys :=
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys_transCmp
  unfold compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
  infer_instance

/-- Comparator self-comparison: the corrected comparator ties every key with itself. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_self
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys key key = Ordering.eq := by
  letI : Std.TransCmp source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys :=
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_transCmp
  exact Std.ReflCmp.compare_self

/-- Comparator orientation: swapping the arguments swaps the corrected outcome. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_swap
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys left right =
      (source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys right left).swap := by
  letI : Std.TransCmp source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys :=
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_transCmp
  exact Std.OrientedCmp.eq_swap

/-- **Reflection compatibility.**  If the actual Rule-4a cumulative keys tie and the legacy public
reflection hypotheses hold (reflected ranked labels and pointwise reflected readings), then the
corrected comparator ties.  This is the existing public reflection result transported across the
new Rule-4a prefix. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_of_reflection
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (rule4aTie : source.compareAromaticCanonicalCumulativeRule45Keys
      left.rule4aKey right.rule4aKey = Ordering.eq)
    (leftExact : left.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels left.rule4aKey.rankedLabels))
    (rightExact : right.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels right.rule4aKey.rankedLabels))
    (rankedReflected : right.rule4aKey.rankedLabels =
      reflectUppercaseRankedLabels left.rule4aKey.rankedLabels)
    (readingsReflected : List.Forall₂
      source.AromaticCanonicalRule4bcReadingUppercaseReflection
        left.readings right.readings) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys left right = Ordering.eq := by
  rw [source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_legacy_of_rule4a_tie
    left right rule4aTie]
  exact source.compareAromaticCanonicalRerootCompoundRule4bcKeys_eq_of_reflection
    left right leftExact rightExact rankedReflected readingsReflected

/-- **Agreement on relevant actual pairs.**  For any pair of keys whose actual Rule-4a cumulative
comparison ties, the corrected comparison equals the legacy public comparison.  This is the exact
form used for frame pairs; it is not a global equality of the two comparators. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_agrees_of_rule4a_tie
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (tie : source.compareAromaticCanonicalCumulativeRule45Keys
      left.rule4aKey right.rule4aKey = Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys left right =
      source.compareAromaticCanonicalRerootCompoundRule4bcKeys left right :=
  source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_legacy_of_rule4a_tie
    left right tie

/-! ## Corresponding through-Rule-5 order -/

/-- Corrected through-Rule-5 ordering.  The prior gate is the corrected compound Rules-4a--4c
comparator; the Rule-5 reading comparator is the existing one unchanged. -/
def compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalRerootCompoundRule45Key →
      source.AromaticCanonicalRerootCompoundRule45Key → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.prior)
      source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys)
    (Ordering.byKey (fun key => key.rule5Readings)
      (source.compareAromaticCanonicalRerootCompoundRule5Readings .R))

/-- A strict corrected prior comparison decides the corrected through-Rule-5 ordering. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_eq_prior_of_prior_ne
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (decisive : source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
      left.prior right.prior ≠ Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys left right =
      source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys left.prior right.prior := by
  unfold compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys
  generalize priorComparison :
      source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
        left.prior right.prior = outcome at decisive ⊢
  cases outcome <;> simp_all [compareLex, Ordering.byKey]

/-- After a complete corrected prior tie, the corrected through-Rule-5 ordering is exactly the
existing common-R Rule-5 reading comparison. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_eq_rule5_of_prior_tie
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (priorTie : source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys left right =
      source.compareAromaticCanonicalRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings := by
  simp [compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys, compareLex,
    Ordering.byKey, priorTie]

/-- **Exact tie compatibility through Rule 5.**  If the actual Rule-4a cumulative comparison of the
two prior keys ties, the corrected through-Rule-5 ordering is literally the shipped ordering. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_eq_legacy_of_rule4a_tie
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (tie : source.compareAromaticCanonicalCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey = Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys left right =
      source.compareAromaticCanonicalRerootCompoundRule45Keys left right := by
  unfold compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys
    compareAromaticCanonicalRerootCompoundRule45Keys compareLex Ordering.byKey
  rw [source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_legacy_of_rule4a_tie
    left.prior right.prior tie]

/-- The corrected through-Rule-5 ordering is transitive. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys := by
  letI : Std.TransCmp
      source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys :=
    source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_transCmp
  letI : Std.TransCmp
      (source.compareAromaticCanonicalRerootCompoundRule5Readings .R) :=
    source.compareAromaticCanonicalRerootCompoundRule5Readings_transCmp .R
  unfold compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys
  infer_instance

/-! ## Descriptor-facing through-Rule-5 record -/

/-- Corrected descriptor-facing through-Rule-5 record.

A strict Rule-4a cumulative comparison returns that ordering with `pseudo := false`; an exact
Rule-4a tie invokes the unchanged legacy `compareAromaticCanonicalRerootCompoundThroughRule5`
record (which then starts from the legacy count gate and may reach the Rule-5 readings). -/
def compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key) :
    ConstitutionalRule5Comparison :=
  let rule4a := source.compareAromaticCanonicalCumulativeRule45Keys
    left.prior.rule4aKey right.prior.rule4aKey
  if rule4a != Ordering.eq then { ordering := rule4a, pseudo := false }
  else source.compareAromaticCanonicalRerootCompoundThroughRule5 left right

/-- Named source semantics of the corrected through-Rule-5 record: strict Rule 4a decides with an
ordinary (non-pseudoasymmetric) ordering, and only an exact Rule-4a tie reaches the unchanged
legacy record. -/
def AromaticCanonicalRule4aPrefixedCompoundThroughRule5Semantics
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (result : ConstitutionalRule5Comparison) : Prop :=
  result =
    match source.compareAromaticCanonicalCumulativeRule45Keys
        left.prior.rule4aKey right.prior.rule4aKey with
    | Ordering.eq => source.compareAromaticCanonicalRerootCompoundThroughRule5 left right
    | other => { ordering := other, pseudo := false }

/-- The corrected record satisfies its named semantics definitionally. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_semantics
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key) :
    source.AromaticCanonicalRule4aPrefixedCompoundThroughRule5Semantics left right
      (source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5 left right) := by
  unfold AromaticCanonicalRule4aPrefixedCompoundThroughRule5Semantics
    compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
  generalize rule4aComparison :
      source.compareAromaticCanonicalCumulativeRule45Keys
        left.prior.rule4aKey right.prior.rule4aKey = outcome
  cases outcome <;> simp [rule4aComparison]

/-- **Strict Rule-4a behavior of the record.**  A strict Rule-4a comparison returns its ordering
with `pseudo := false`. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_ne
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (decisive : source.compareAromaticCanonicalCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey ≠ Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5 left right =
      { ordering := source.compareAromaticCanonicalCumulativeRule45Keys
          left.prior.rule4aKey right.prior.rule4aKey
        pseudo := false } := by
  simp [compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5, decisive]

/-- **Tie behavior of the record.**  An exact Rule-4a tie invokes the unchanged legacy
through-Rule-5 record. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_tie
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (tie : source.compareAromaticCanonicalCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey = Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5 left right =
      source.compareAromaticCanonicalRerootCompoundThroughRule5 left right := by
  simp [compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5, tie]

/-- The corrected record's ordering is the corrected through-Rule-5 ordering, so descriptor-facing
consumers and ordering-only consumers cannot diverge. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_ordering
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key) :
    (source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5 left right).ordering =
      source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys left right := by
  generalize rule4aComparison :
      source.compareAromaticCanonicalCumulativeRule45Keys
        left.prior.rule4aKey right.prior.rule4aKey = outcome
  cases outcome with
  | lt =>
      have strict : source.compareAromaticCanonicalCumulativeRule45Keys
          left.prior.rule4aKey right.prior.rule4aKey ≠ Ordering.eq := by
        rw [rule4aComparison]; simp
      have priorEq :
          source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
              left.prior right.prior =
            source.compareAromaticCanonicalCumulativeRule45Keys
              left.prior.rule4aKey right.prior.rule4aKey :=
        source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_rule4a_of_ne
          left.prior right.prior strict
      have priorNe :
          source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
              left.prior right.prior ≠ Ordering.eq := by
        rw [priorEq]; exact strict
      rw [source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_ne
          left right strict,
        source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_eq_prior_of_prior_ne
          left right priorNe]
      exact priorEq.symm
  | gt =>
      have strict : source.compareAromaticCanonicalCumulativeRule45Keys
          left.prior.rule4aKey right.prior.rule4aKey ≠ Ordering.eq := by
        rw [rule4aComparison]; simp
      have priorEq :
          source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
              left.prior right.prior =
            source.compareAromaticCanonicalCumulativeRule45Keys
              left.prior.rule4aKey right.prior.rule4aKey :=
        source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_rule4a_of_ne
          left.prior right.prior strict
      have priorNe :
          source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
              left.prior right.prior ≠ Ordering.eq := by
        rw [priorEq]; exact strict
      rw [source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_ne
          left right strict,
        source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_eq_prior_of_prior_ne
          left right priorNe]
      exact priorEq.symm
  | eq =>
      have recordEq :
          source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5 left right =
            source.compareAromaticCanonicalRerootCompoundThroughRule5 left right :=
        source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_tie
          left right rule4aComparison
      have priorEq :
          source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
              left.prior right.prior =
            source.compareAromaticCanonicalRerootCompoundRule4bcKeys
              left.prior right.prior :=
        source.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_legacy_of_rule4a_tie
          left.prior right.prior rule4aComparison
      rw [recordEq, source.compareAromaticCanonicalRerootCompoundThroughRule5_ordering]
      unfold compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys
        compareAromaticCanonicalRerootCompoundRule45Keys compareLex Ordering.byKey
      rw [priorEq]

/-- A strict Rule-4a decision is always ordinary: the pseudoasymmetry flag is `false`. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_pseudo_false_of_rule4a_ne
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (decisive : source.compareAromaticCanonicalCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey ≠ Ordering.eq) :
    (source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5 left right).pseudo =
      false := by
  rw [source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_ne
    left right decisive]

/-- **Exact record compatibility.**  On an actual Rule-4a tie the corrected record is literally the
legacy record, not merely an ordering-equal one. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_eq_legacy_of_rule4a_tie
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (tie : source.compareAromaticCanonicalCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey = Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5 left right =
      source.compareAromaticCanonicalRerootCompoundThroughRule5 left right :=
  source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_tie
    left right tie

/-! ## Corrected actual Rule-3--5 frame backend

The frame comparator keeps the shipped reader-free Rule-3 gate (Rule 3 genuinely precedes Rule 4a
in the public source order; see the Rule-3 frame in `AuthoritativeSemanticMancudeOccurrenceRule3Through5`).
When Rule 3 ties, however, it calls the Rule-4a-prefixed Through-5 record: Rule 4a is decided before
the compound reference-count prefix, and the pseudoasymmetry flag remains `false` on every strict
Rule-4a decision.  The safe tracked sorter, point retrieval and descriptor then reuse the existing
actual frame builder, the existing actual coordinate lookup and the existing descriptor
classification; only the ordering relation is corrected. -/

/-- Corrected Rule-3--5 key ordering: reader-free Rule 3 first (unchanged source rule order), then
the Rule-4a-prefixed Rules-4a--5 key ordering instead of the legacy Rule-4a-free suffix. -/
noncomputable def compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Keys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalOccurrenceRule3Through5Key →
      source.AromaticCanonicalOccurrenceRule3Through5Key → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.rule3)
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys)
    (Ordering.byKey (fun key => key.rule45)
      source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys)

/-- Corrected actual frame comparison.  A strict Rule-3 decision is ordinary; a Rule-3 tie falls
through to the corrected Through-5 record, which exhausts Rule 4a before reference counts. -/
noncomputable def compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : ConstitutionalRule5Comparison :=
  let leftKey := frame.keyAt left
  let rightKey := frame.keyAt right
  match source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      leftKey.rule3 rightKey.rule3 with
  | .lt => { ordering := .lt, pseudo := false }
  | .gt => { ordering := .gt, pseudo := false }
  | .eq => source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
      leftKey.rule45 rightKey.rule45

/-- The frame record ordering is exactly the corrected Rule-3--5 key ordering. -/
theorem compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_ordering
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) :
    (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
      frame left right).ordering =
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Keys
        (frame.keyAt left) (frame.keyAt right) := by
  unfold compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
    compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Keys
  generalize rule3Comparison :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (frame.keyAt left).rule3 (frame.keyAt right).rule3 = outcome
  cases outcome <;>
    simp [compareLex, Ordering.byKey, rule3Comparison,
      source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_ordering]

/-- A strict Rule-3 decision is returned directly and is never pseudoasymmetric. -/
theorem compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_of_rule3_gt
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.gt) :
    source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        frame left right =
      { ordering := Ordering.gt, pseudo := false } := by
  simp [compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At, strict]

/-- On a Rule-3 tie the record is exactly the corrected Rule-4a-prefixed Through-5 record. -/
theorem compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_of_rule3_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (tied : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        frame left right =
      source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
        (frame.keyAt left).rule45 (frame.keyAt right).rule45 := by
  simp [compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At, tied]

/-- A pseudoasymmetric frame comparison can only arise after Rule 3 ties; in particular it can
only arise from the corrected Rule-4a-prefixed Through-5 suffix. -/
theorem compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_pseudo_implies_rule3_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (pseudo : (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
      frame left right).pseudo = true) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.eq := by
  unfold compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At at pseudo
  generalize compared : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = outcome at pseudo
  cases outcome <;> simp_all

/-- Transitivity of the corrected frame ordering, inherited from the corrected key ordering. -/
theorem compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_transCmp
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Std.TransCmp (fun left right =>
      (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        frame left right).ordering) := by
  letI : Std.TransCmp
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Keys := by
    letI : Std.TransCmp source.compareAromaticCanonicalUncancelledRule3SpatialKeys :=
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
    letI : Std.TransCmp
        source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys :=
      source.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_transCmp
    unfold compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Keys
    infer_instance
  have same : (fun left right =>
      (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        frame left right).ordering) =
      Ordering.byKey frame.keyAt
        source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Keys := by
    funext left right
    exact source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_ordering
      frame left right
  rw [same]
  infer_instance

/-- **Exact frame-record tie compatibility.**  For an actual pair whose Rule-4a keys tie, the
corrected frame record is literally the shipped legacy record.  When Rule 3 is strict both sides
are the same strict record; when Rule 3 ties the corrected and legacy Through-5 records coincide
by the Rule-4a tie lemma.  No comparison outside the tie hypothesis is identified. -/
theorem compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_legacy_of_rule4a_tie
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (tie : source.compareAromaticCanonicalCumulativeRule45Keys
      (frame.keyAt left).rule45.prior.rule4aKey
      (frame.keyAt right).rule45.prior.rule4aKey = Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        frame left right =
      source.compareAromaticCanonicalOccurrenceRule3Through5At frame left right := by
  unfold compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
    compareAromaticCanonicalOccurrenceRule3Through5At
  dsimp only
  generalize rule3Comparison :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (frame.keyAt left).rule3 (frame.keyAt right).rule3 = outcome
  cases outcome <;>
    simp [rule3Comparison,
      source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_tie
        (frame.keyAt left).rule45 (frame.keyAt right).rule45 tie]

/-- Pointwise equality of the actual frame keys transports the corrected frame comparison.  This
is the factorization hook for a future corrected-reader locality proof: it needs only the actual
slot keys of the two frames, not a re-derivation of the sorter or of any builder. -/
theorem compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_of_keyAt_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (keysEq : ∀ index, left.keyAt index = right.keyAt index)
    (leftIndex rightIndex : Fin 4) :
    source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        left leftIndex rightIndex =
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        right leftIndex rightIndex := by
  unfold compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
  rw [keysEq leftIndex, keysEq rightIndex]

/-! ### Corrected tracked sorter over the actual frame -/

/-- Corrected descriptor-facing comparison record, reusing the shipped conversion. -/
noncomputable def compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : Option ConstitutionalDescriptorHierarchyComparison :=
  some (aromaticCanonicalRule3Through5DescriptorComparison
    (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At frame left right))

/-- Corrected tracked sort, reusing the repository's `sortFourLocalizedLigandsTracked`. -/
noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder :=
  sortFourLocalizedLigandsTracked
    (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At? frame)

noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : Bool :=
  (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
    frame left right).ordering == Ordering.gt

noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    List (Fin 4) → Bool
  | [] => true
  | left :: rest =>
      rest.all
          (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict
            frame left) &&
        source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
          frame rest

theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent_eq_true_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    ∀ order,
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
          frame order = true ↔
        order.Pairwise fun left right =>
          (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
            frame left right).ordering = Ordering.gt
  | [] => by
      simp [aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent]
  | left :: rest => by
      rw [aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent,
        Bool.and_eq_true, List.all_eq_true, List.pairwise_cons,
        aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent_eq_true_iff]
      simp [aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict]

/-- Corrected safe sorter: the tracked order is accepted only when its descending order is
coherent for the corrected comparator. -/
noncomputable def safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder := do
  let tracked ←
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? frame
  if source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
      frame tracked.highestFirst then some tracked else none

/-- The corrected safe sorter is extensional in the corrected pairwise comparison. -/
theorem safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_compare
    (source : AuthoritativeChemicalInput) {carrierFuel : ℕ}
    (original mapped : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (compareNatural : ∀ left right,
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
          mapped left right =
        source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
          original left right) :
    source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
        mapped =
      source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
        original := by
  have compareAtEq :
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At? mapped =
        source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At? original := by
    funext left right
    simp [compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At?,
      compareNatural left right]
  have trackedEq :
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? mapped =
        source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? original := by
    unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
    rw [compareAtEq]
  have coherentEq : ∀ order,
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
          mapped order =
        source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
          original order := by
    intro order
    induction order with
    | nil => rfl
    | cons left rest inductionHypothesis =>
        unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
        have predicateEq :
            source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict
                mapped left =
              source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict
                original left := by
          funext right
          simp [aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict,
            compareNatural left right]
        rw [predicateEq, inductionHypothesis]
  unfold safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
  rw [trackedEq]
  cases source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? original with
  | none => rfl
  | some tracked =>
      simp
      rw [coherentEq tracked.highestFirst]

/-- **Actual-frame sorter factorization.**  Pointwise equality of the actual slot keys is enough
to transport the complete safe tracked order, including the exact pseudo-comparison count stored
in `TrackedLocalizedLigandOrder`.  No builder or reader replay is involved. -/
theorem safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_keyAt_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (keysEq : ∀ index, left.keyAt index = right.keyAt index) :
    source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? left =
      source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? right := by
  apply source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_compare
    (original := right)
  intro leftIndex rightIndex
  exact source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_of_keyAt_eq
    keysEq leftIndex rightIndex

/-- The pseudo-comparison count is transported by actual slot-key equality. -/
theorem safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_pseudoComparisons_eq_of_keyAt_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (keysEq : ∀ index, left.keyAt index = right.keyAt index)
    {leftTracked rightTracked : TrackedLocalizedLigandOrder}
    (leftComputed :
      source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
        left = some leftTracked)
    (rightComputed :
      source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
        right = some rightTracked) :
    leftTracked.pseudoComparisons = rightTracked.pseudoComparisons := by
  rw [source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_keyAt_eq
    keysEq] at leftComputed
  rw [leftComputed] at rightComputed
  injection rightComputed with trackedEq
  rw [trackedEq]

/-- Under Rule-4a ties on every actual pair, the corrected safe sorter computes literally the
legacy safe order (same ligand order and same pseudo count). -/
theorem safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_legacy_of_rule4a_ties
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (tie : ∀ left right : Fin 4,
      source.compareAromaticCanonicalCumulativeRule45Keys
        (frame.keyAt left).rule45.prior.rule4aKey
        (frame.keyAt right).rule45.prior.rule4aKey = Ordering.eq) :
    source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? frame =
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? frame := by
  have compareAtEq :
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At? frame =
        source.compareAromaticCanonicalOccurrenceRule3Through5At? frame := by
    funext left right
    simp only [compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At?,
      compareAromaticCanonicalOccurrenceRule3Through5At?]
    rw [source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_legacy_of_rule4a_tie
      frame left right (tie left right)]
  have trackedEq :
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? frame =
        source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? frame := by
    unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?
    rw [compareAtEq]
  have coherentEq : ∀ order,
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
          frame order =
        source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent frame order := by
    intro order
    induction order with
    | nil => rfl
    | cons left rest inductionHypothesis =>
        unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
          aromaticCanonicalOccurrenceRule3Through5OrderCoherent
        have predicateEq :
            source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict
                frame left =
              source.aromaticCanonicalOccurrenceRule3Through5OrderPairStrict frame left := by
          funext right
          simp [aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict,
            aromaticCanonicalOccurrenceRule3Through5OrderPairStrict,
            source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_legacy_of_rule4a_tie
              frame left right (tie left right)]
        rw [predicateEq, inductionHypothesis]
  unfold safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
    safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
  rw [trackedEq]
  cases source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? frame with
  | none => rfl
  | some tracked =>
      simp
      rw [coherentEq tracked.highestFirst]

/-! ### Corrected descriptor over actual points -/

/-- Corrected frame descriptor.  The tracked order comes from the corrected safe sorter; point
retrieval and classification are the shipped actual operations, so no coordinate or label is
fabricated. -/
noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel := do
  let tracked ←
    source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? frame
  let points ← tracked.highestFirst.mapM fun index =>
    source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)
  let raw ← CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? points
  some (classifyTetrahedralRSPseudo raw tracked.pseudoComparisons)

/-- Actual-frame descriptor factorization: identical slot keys and the same base give the same
corrected descriptor.  This is the descriptor-level hook for corrected-reader locality. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?_eq_of_keyAt_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (keysEq : ∀ index, left.keyAt index = right.keyAt index)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
        left base =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
        right base := by
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
  rw [source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_keyAt_eq
    keysEq]

/-- Under Rule-4a ties on every actual pair, the corrected frame descriptor is literally the
shipped legacy frame descriptor. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?_eq_legacy_of_rule4a_ties
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (tie : ∀ left right : Fin 4,
      source.compareAromaticCanonicalCumulativeRule45Keys
        (frame.keyAt left).rule45.prior.rule4aKey
        (frame.keyAt right).rule45.prior.rule4aKey = Ordering.eq) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
        frame base =
      source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? frame base := by
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
    aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?
  rw [source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_legacy_of_rule4a_ties
    frame tie]

/-- The corrected frame descriptor agrees with the shipped evidence descriptor whenever the
evidence record stores the actual outputs of the corrected safe sorter and the actual point read. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?_eq_evidenceDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (trackedComputed :
      source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
        evidence.keys = some evidence.tracked)
    (pointsComputed :
      evidence.tracked.highestFirst.mapM (fun index =>
        source.aromaticCanonicalRerootSpatialPoint? (evidence.base.cursorAt index)) =
        some evidence.points) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
        evidence.keys evidence.base =
      source.aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor evidence := by
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
    aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor
  simp [trackedComputed, pointsComputed]

/-- Corrected actual spatial evidence.  Every field comes from the shipped actual builder or the
shipped actual point retrieval; only the safe tracked order uses the corrected comparator. -/
noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) :
    Option (source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let base ← source.aromaticCanonicalOccurrenceFourLigandFrame? target
  let keys ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    target view ruleFuel base.roots
  let tracked ←
    source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? keys
  let points ← tracked.highestFirst.mapM fun index =>
    source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

/-- **Reachable corrected computation.**  Any evidence returned by the corrected actual builder is
assembled from the actual center, actual four-ligand frame, actual frame keys, the corrected safe
sort of those keys, and the actual priority-ordered point read.  In particular the keys are not
fabricated by the corrected backend. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?_computed
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (computed : source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
      target view ruleFuel = some evidence) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some evidence.center ∧
    source.aromaticCanonicalOccurrenceFourLigandFrame? target = some evidence.base ∧
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target view ruleFuel evidence.base.roots = some evidence.keys ∧
    source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
        evidence.keys = some evidence.tracked ∧
    evidence.tracked.highestFirst.mapM (fun index =>
        source.aromaticCanonicalRerootSpatialPoint?
          (evidence.base.cursorAt index)) = some evidence.points := by
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence? at computed
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target with
      | none => simp [centerComputed, baseComputed] at computed
      | some base =>
          cases keysComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
              target view ruleFuel base.roots with
          | none => simp [centerComputed, baseComputed, keysComputed] at computed
          | some keys =>
              cases trackedComputed :
                  source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
                    keys with
              | none =>
                  simp [centerComputed, baseComputed, keysComputed, trackedComputed] at computed
              | some tracked =>
                  cases pointsComputed : tracked.highestFirst.mapM (fun index =>
                      source.aromaticCanonicalRerootSpatialPoint?
                        (base.cursorAt index)) with
                  | none =>
                      simp [centerComputed, baseComputed, keysComputed, trackedComputed,
                        pointsComputed] at computed
                  | some points =>
                      simp [centerComputed, baseComputed, keysComputed, trackedComputed,
                        pointsComputed] at computed
                      subst evidence
                      refine ⟨?_, ?_, ?_, ?_, ?_⟩
                      · simp [centerComputed]
                      · simp [baseComputed]
                      · simpa using keysComputed
                      · simpa using trackedComputed
                      · simpa using pointsComputed

/-- The actual frame keys stored by the corrected evidence satisfy the shipped declarative frame
predicate, via the shipped builder soundness theorem. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?_keys_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (computed : source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
      target view ruleFuel = some evidence) :
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyFrame
      target view ruleFuel evidence.base.roots evidence.keys := by
  have computedParts :=
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?_computed
      target view ruleFuel evidence computed
  exact source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
    target view ruleFuel evidence.base.roots evidence.keys computedParts.2.2.1

/-- Corrected public descriptor.  It is the corrected actual evidence builder followed by the
shipped descriptor classification. -/
noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) : Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ←
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
      target view ruleFuel
  let raw ← CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- The corrected descriptor is exactly its actual evidence builder composed with the shipped
evidence descriptor. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_evidenceDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target view ruleFuel =
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
        target view ruleFuel).bind
        (source.aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor
          (carrierFuel := carrierFuel)) :=
  rfl

/-- The corrected whole descriptor at an actual computed evidence record is the corrected frame
descriptor on that evidence's actual keys and base.  This lets the frame-level tie and key
factorization theorems be applied to the public entrypoint. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_frameDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (computed : source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
      target view ruleFuel = some evidence)
    (trackedComputed :
      source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
        evidence.keys = some evidence.tracked)
    (pointsComputed :
      evidence.tracked.highestFirst.mapM (fun index =>
        source.aromaticCanonicalRerootSpatialPoint? (evidence.base.cursorAt index)) =
        some evidence.points) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target view ruleFuel =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
        evidence.keys evidence.base := by
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
    aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
  rw [computed]
  simp [trackedComputed, pointsComputed]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalRule4aPrefixedCompoundRule4bcSemantics
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_semantics
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_rule4a_of_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_legacy_of_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_transCmp
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_self
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_swap
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_eq_of_reflection
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule4bcKeys_agrees_of_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_eq_prior_of_prior_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_eq_rule5_of_prior_tie
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_eq_legacy_of_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundRule45Keys_transCmp
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalRule4aPrefixedCompoundThroughRule5Semantics
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_semantics
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_ordering
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_pseudo_false_of_rule4a_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_eq_legacy_of_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Keys
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_ordering
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_of_rule3_gt
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_of_rule3_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_pseudo_implies_rule3_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_transCmp
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_legacy_of_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_of_keyAt_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderPairStrict
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5OrderCoherent_eq_true_iff
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_compare
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_keyAt_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_pseudoComparisons_eq_of_keyAt_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_legacy_of_rule4a_ties
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?_eq_of_keyAt_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?_eq_legacy_of_rule4a_ties
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?_eq_evidenceDescriptor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?_computed
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?_keys_sound
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_evidenceDescriptor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_frameDescriptor
