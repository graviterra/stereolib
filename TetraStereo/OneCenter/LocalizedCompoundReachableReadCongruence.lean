import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Read-support congruence for the parametric compound Rules-4b/4c/5 builder

`LocalizedParametricCompoundRule45Key` builds the complete compound through-Rule-5 key from an
arbitrary total label callback `read : cursor → Option LocalizedAuxiliaryLabel`, using the actual
production cumulative builder, the actual P-92.5.2.1 reference selection, the actual no/one/two
reference alternatives, the actual R/S Rule-5 readings and the actual sibling sort/merge
construction.  `LocalizedOutwardWholeStateKeyAgreement` already proves the underlying generic
congruence for the *cumulative* builder: two readers that agree on every executable-reroot cursor
reachable from a starting cursor (through `E`, the actual
`executableLocalizedRerootChildren` membership edge) build the same full `Option` cumulative key at
that cursor, for every fuel and stage.

This module lifts that cumulative congruence through every compound layer and therefore proves
the read-support lemma needed by the Rule-3 endpoint: if two label readers agree on every
executable-reroot cursor reachable from `start`, then the complete parametric compound builders
produce *exactly equal full* `Option` results at every reachable cursor and every fuel, including
the fail-closed `none` outcome:

* `buildLocalizedRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees` (and the generic
  reading-list, compound Rule-4b/4c, one-reading Rule-5 and Rule-5-list congruences);
* `buildLocalizedRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable` — the full
  compound through-Rule-5 equality at any cursor reachable from `start`;
* `buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable` — the same
  equality at `start` itself, which is the form the endpoint consumes.

The agreement hypothesis is deliberately the honest *unbounded* executable reachability relation
`Relation.ReflTransGen (E input) start ·`: it is stronger than the bounded "descendants up to the
fuel" premise and is exactly the shape already established by the shipped outward whole-state
support.  No geometry, depth grading, path validity or label semantics is used here, and no key
equality, comparison outcome or compiled result is assumed: every layer is derived by case analysis
on the actual `Option`/`List.mapM` recursions.  In particular the readers are arbitrary total
functions and `none` is an ordinary observed value, so agreement at `none` observations is covered
exactly like any other.

## Scope

Pure runtime congruence of the existing builders.  This module adds no solver, evaluator or
production path, and makes no source-policy claim.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Reader agreement and cumulative agreement at one cursor -/

/-- The honest read-support premise: two label readers agree on every cursor reachable from
`start` along the actual executable reroot edge `E`.  `start` itself is reachable by reflexivity,
so its label observation is included.  Arbitrary total readers and arbitrary `Option` outcomes
(including `none`) are allowed. -/
abbrev LocalizedRerootReadersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∀ cursor : input.LocalizedRerootCursor carrierFuel,
    Relation.ReflTransGen (E input) start cursor → read1 cursor = read2 cursor

/-- Pointwise agreement of the two readers at one fixed fuel and cursor across *all* cumulative
stages.  This is exactly what every compound layer consumes: each layer only ever compiles
cumulative keys at the same cursor and fuel, differing only in the stage. -/
abbrev LocalizedRerootCumulativeAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∀ stage : LocalizedCumulativeRule45Stage,
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read1 fuel cursor =
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read2 fuel cursor

/-! ## Compound-layer congruence from cumulative agreement -/

/-- One-reference Rule-4b/4c reading congruence: at a cursor where the two readers build the same
cumulative key at every stage, both readings are the same full `Option`. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (cumul : input.LocalizedRerootCumulativeAgrees read1 read2 fuel cursor) :
    ∀ reference : Option RS,
      input.buildLocalizedRerootRule4bcReadingWithRead? read1 fuel cursor reference =
      input.buildLocalizedRerootRule4bcReadingWithRead? read2 fuel cursor reference := by
  intro reference
  cases reference with
  | none =>
      simp only [buildLocalizedRerootRule4bcReadingWithRead?,
        cumul .rule4a, cumul .rule4cNoReference]
  | some reference =>
      simp only [buildLocalizedRerootRule4bcReadingWithRead?,
        cumul (.rule4b reference), cumul (.rule4c reference)]

/-- Rule-4b/4c reading-list congruence, by induction over the actual normative alternative list.
Each sequential head is compared through the one-reading congruence; the tail is the induction
hypothesis. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_congr_of_cumulativeAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (cumul : input.LocalizedRerootCumulativeAgrees read1 read2 fuel cursor) :
    ∀ references : List (Option RS),
      input.buildLocalizedRerootRule4bcReadingsWithRead? read1 fuel cursor references =
      input.buildLocalizedRerootRule4bcReadingsWithRead? read2 fuel cursor references := by
  intro references
  induction references with
  | nil => rfl
  | cons reference references inductionHypothesis =>
      unfold buildLocalizedRerootRule4bcReadingsWithRead?
      cases headFirst : input.buildLocalizedRerootRule4bcReadingWithRead?
          read1 fuel cursor reference with
      | none =>
          have headSecond : input.buildLocalizedRerootRule4bcReadingWithRead?
              read2 fuel cursor reference = none := by
            rw [← input.buildLocalizedRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
              read1 read2 fuel cursor cumul reference]
            exact headFirst
          simp [headFirst, headSecond]
      | some reading =>
          have headSecond : input.buildLocalizedRerootRule4bcReadingWithRead?
              read2 fuel cursor reference = some reading := by
            rw [← input.buildLocalizedRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
              read1 read2 fuel cursor cumul reference]
            exact headFirst
          simp [headFirst, headSecond]
          rw [inductionHypothesis]

/-- Complete no/one/two-reference compound Rules-4b/4c key congruence.  The Rule-4a cumulative key
is compared first; because the two readers produce the *same* Rule-4a key, the derived reference
selection and the normative alternatives are syntactically identical on both sides, and the
sequential readings are compared by the reading-list congruence.  Both fail-closed `none` outcomes
are included. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (cumul : input.LocalizedRerootCumulativeAgrees read1 read2 fuel cursor) :
    input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read1 fuel cursor =
    input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read2 fuel cursor := by
  unfold buildLocalizedRerootCompoundRule4bcKeyWithRead?
  cases rule4aFirst : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read1 fuel cursor with
  | none =>
      have rule4aSecond : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a read2 fuel cursor = none := by
        rw [← cumul .rule4a]
        exact rule4aFirst
      simp [rule4aFirst, rule4aSecond]
  | some rule4aKey =>
      have rule4aSecond : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a read2 fuel cursor = some rule4aKey := by
        rw [← cumul .rule4a]
        exact rule4aFirst
      simp [rule4aFirst, rule4aSecond]
      rw [input.buildLocalizedRerootRule4bcReadingsWithRead?_congr_of_cumulativeAgrees
        read1 read2 fuel cursor cumul
        (localizedRule4bcReferenceAlternatives
          (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))]

/-- One Rule-5 reading congruence: both common-reference R/S cumulative hierarchies are compared
through the cumulative agreement at the stages actually selected by `localizedRule5StageFor`. -/
theorem buildLocalizedRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (cumul : input.LocalizedRerootCumulativeAgrees read1 read2 fuel cursor)
    (prior : input.LocalizedRerootRule4bcReading) :
    input.buildLocalizedRerootRule5ReadingWithRead? read1 fuel cursor prior =
    input.buildLocalizedRerootRule5ReadingWithRead? read2 fuel cursor prior := by
  unfold buildLocalizedRerootRule5ReadingWithRead?
  cases commonRFirst : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor prior.reference? .R) read1 fuel cursor with
  | none =>
      have commonRSecond : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .R) read2 fuel cursor = none := by
        rw [← cumul (localizedRule5StageFor prior.reference? .R)]
        exact commonRFirst
      simp [commonRFirst, commonRSecond]
  | some commonR =>
      have commonRSecond : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .R) read2 fuel cursor = some commonR := by
        rw [← cumul (localizedRule5StageFor prior.reference? .R)]
        exact commonRFirst
      simp [commonRFirst, commonRSecond]
      cases commonSFirst : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .S) read1 fuel cursor with
      | none =>
          have commonSSecond : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (localizedRule5StageFor prior.reference? .S) read2 fuel cursor = none := by
            rw [← cumul (localizedRule5StageFor prior.reference? .S)]
            exact commonSFirst
          simp [commonSFirst, commonSSecond]
      | some commonS =>
          have commonSSecond : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (localizedRule5StageFor prior.reference? .S) read2 fuel cursor = some commonS := by
            rw [← cumul (localizedRule5StageFor prior.reference? .S)]
            exact commonSFirst
          simp [commonSFirst, commonSSecond]

/-- Rule-5 reading-list congruence, by induction over the actual prior Rule-4b/4c readings. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_congr_of_cumulativeAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (cumul : input.LocalizedRerootCumulativeAgrees read1 read2 fuel cursor) :
    ∀ priors : List input.LocalizedRerootRule4bcReading,
      input.buildLocalizedRerootRule5ReadingsWithRead? read1 fuel cursor priors =
      input.buildLocalizedRerootRule5ReadingsWithRead? read2 fuel cursor priors := by
  intro priors
  induction priors with
  | nil => rfl
  | cons prior priors inductionHypothesis =>
      unfold buildLocalizedRerootRule5ReadingsWithRead?
      cases headFirst : input.buildLocalizedRerootRule5ReadingWithRead?
          read1 fuel cursor prior with
      | none =>
          have headSecond : input.buildLocalizedRerootRule5ReadingWithRead?
              read2 fuel cursor prior = none := by
            rw [← input.buildLocalizedRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
              read1 read2 fuel cursor cumul prior]
            exact headFirst
          simp [headFirst, headSecond]
      | some reading =>
          have headSecond : input.buildLocalizedRerootRule5ReadingWithRead?
              read2 fuel cursor prior = some reading := by
            rw [← input.buildLocalizedRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
              read1 read2 fuel cursor cumul prior]
            exact headFirst
          simp [headFirst, headSecond]
          rw [inductionHypothesis]

/-- **Compound through-Rule-5 key congruence from cumulative agreement.**  The complete parametric
compound builder produces exactly the same full `Option` key for both readers whenever the
cumulative layers agree at the same cursor and fuel, including the fail-closed `none` outcome. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_congr_of_cumulativeAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (cumul : input.LocalizedRerootCumulativeAgrees read1 read2 fuel cursor) :
    input.buildLocalizedRerootCompoundRule45KeyWithRead? read1 fuel cursor =
    input.buildLocalizedRerootCompoundRule45KeyWithRead? read2 fuel cursor := by
  unfold buildLocalizedRerootCompoundRule45KeyWithRead?
  cases priorFirst : input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read1 fuel cursor with
  | none =>
      have priorSecond : input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read2 fuel cursor =
          none := by
        rw [← input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
          read1 read2 fuel cursor cumul]
        exact priorFirst
      simp [priorFirst, priorSecond]
  | some prior =>
      have priorSecond : input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read2 fuel cursor =
          some prior := by
        rw [← input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
          read1 read2 fuel cursor cumul]
        exact priorFirst
      simp [priorFirst, priorSecond]
      rw [input.buildLocalizedRerootRule5ReadingsWithRead?_congr_of_cumulativeAgrees
        read1 read2 fuel cursor cumul prior.readings]

/-! ## Instantiation at executable-reachable cursors -/

/-- The shipped generic cumulative congruence, restated as cumulative agreement at one reachable
cursor.  This is the sole underlying read-support fact reused by the compound layers; no compound
equality is assumed. -/
theorem localizedRerootCumulativeAgrees_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start cursor : input.LocalizedRerootCursor carrierFuel)
    (agree : input.LocalizedRerootReadersAgreeOnReachable read1 read2 start)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (fuel : Nat) :
    input.LocalizedRerootCumulativeAgrees read1 read2 fuel cursor :=
  fun stage =>
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable
      stage read1 read2 start agree fuel cursor reachable

/-- **Read-support congruence for one Rule-4b/4c reading** at every executable-reachable cursor. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_congr_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : input.LocalizedRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      ∀ reference : Option RS,
        input.buildLocalizedRerootRule4bcReadingWithRead? read1 fuel cursor reference =
        input.buildLocalizedRerootRule4bcReadingWithRead? read2 fuel cursor reference := by
  intro fuel cursor reachable reference
  exact input.buildLocalizedRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (input.localizedRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)
    reference

/-- **Read-support congruence for the Rule-4b/4c reading list** at every executable-reachable
cursor. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_congr_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : input.LocalizedRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      ∀ references : List (Option RS),
        input.buildLocalizedRerootRule4bcReadingsWithRead? read1 fuel cursor references =
        input.buildLocalizedRerootRule4bcReadingsWithRead? read2 fuel cursor references := by
  intro fuel cursor reachable references
  exact input.buildLocalizedRerootRule4bcReadingsWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (input.localizedRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)
    references

/-- **Read-support congruence for the compound Rules-4b/4c key** at every executable-reachable
cursor, full `Option` including the fail-closed outcome. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_congr_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : input.LocalizedRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read1 fuel cursor =
      input.buildLocalizedRerootCompoundRule4bcKeyWithRead? read2 fuel cursor := by
  intro fuel cursor reachable
  exact input.buildLocalizedRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (input.localizedRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)

/-- **Read-support congruence for one Rule-5 reading** at every executable-reachable cursor. -/
theorem buildLocalizedRerootRule5ReadingWithRead?_congr_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : input.LocalizedRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      ∀ prior : input.LocalizedRerootRule4bcReading,
        input.buildLocalizedRerootRule5ReadingWithRead? read1 fuel cursor prior =
        input.buildLocalizedRerootRule5ReadingWithRead? read2 fuel cursor prior := by
  intro fuel cursor reachable prior
  exact input.buildLocalizedRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (input.localizedRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)
    prior

/-- **Read-support congruence for the Rule-5 reading list** at every executable-reachable
cursor. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_congr_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : input.LocalizedRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      ∀ priors : List input.LocalizedRerootRule4bcReading,
        input.buildLocalizedRerootRule5ReadingsWithRead? read1 fuel cursor priors =
        input.buildLocalizedRerootRule5ReadingsWithRead? read2 fuel cursor priors := by
  intro fuel cursor reachable priors
  exact input.buildLocalizedRerootRule5ReadingsWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (input.localizedRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)
    priors

/-- **Main read-support theorem.**  If two arbitrary total label readers agree on every cursor
reachable from `start` through the actual executable reroot children, then the complete parametric
compound through-Rule-5 builder returns exactly the same full `Option` key at every reachable
cursor and every fuel.  The equality is of the whole `Option`, so the fail-closed `none` outcome is
covered, and no compiled-key equality or comparison outcome is assumed. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : input.LocalizedRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCompoundRule45KeyWithRead? read1 fuel cursor =
      input.buildLocalizedRerootCompoundRule45KeyWithRead? read2 fuel cursor := by
  intro fuel cursor reachable
  exact input.buildLocalizedRerootCompoundRule45KeyWithRead?_congr_of_cumulativeAgrees
    read1 read2 fuel cursor
    (input.localizedRerootCumulativeAgrees_of_readersAgreeOnReachable
      read1 read2 start cursor agree reachable fuel)

/-- **Endpoint form of the main theorem.**  At the starting cursor itself, reader agreement on the
executable-descendant set is enough for exact full `Option` equality of the complete compound
through-Rule-5 builds at every fuel. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : input.LocalizedRerootReadersAgreeOnReachable read1 read2 start) :
    ∀ fuel : Nat,
      input.buildLocalizedRerootCompoundRule45KeyWithRead? read1 fuel start =
      input.buildLocalizedRerootCompoundRule45KeyWithRead? read2 fuel start :=
  fun fuel =>
    input.buildLocalizedRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable
      read1 read2 start agree fuel start Relation.ReflTransGen.refl

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the two agreement notions, every compound-layer congruence derived
from cumulative agreement, every executable-reachability instantiation, and the main compound
through-Rule-5 read-support theorem with its endpoint form.  `assert_kernel_only` permits exactly
`propext`, `Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and
native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootReadersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootCumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_congr_of_cumulativeAgrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCumulativeAgrees_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
