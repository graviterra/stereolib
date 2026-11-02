import TetraStereo.OneCenter.LocalizedUniversalRule3Evaluation
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitDescriptor
import TetraStereo.OneCenter.LocalizedExtendedFuelMonotonicity

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand

/-!
# Universal evaluation of the actual tetrahedral descriptor pipeline

`LocalizedUniversalRule3Evaluation` proves that the executable preparation
`prepareUniversalRule3EvaluationOutcome` computes, from the input alone, a Rule-3 budget and the
full optional two-pass frame at that budget, and that the actual evaluator
`buildLocalizedExtendedShortCircuitRule3FrameExec?` agrees with the returned frame at every larger
budget.

This module lifts that result from the bare Rule-3 frame to the *actual tetrahedral descriptor
pipeline* of `LocalizedExtendedShortCircuitDescriptor`: the four-ligand occurrence base, the
production Rules-4a--5 key budget, the production tracked order with its pseudo-comparison count,
the coordinate readings, and the rational `R`/`S` classification.  Concretely:

* `keyFrameAt?`, `spatialEvidenceAt?` and `descriptorAt?` are the production pipeline with a single
  parameter: the Rule-3 evaluation budget.  Every other stage is the existing executable function.
* `keyFrameAt?_production`, `spatialEvidenceAt?_production` and `descriptorAt?_production` prove
  that at `localizedDescriptorBearingRule3EvaluationFuel` these are exactly the existing production
  functions, including all refusals.
* `universalDescriptorOutcome` reads the four-ligand base once, runs the one preparation pass over
  `base.cursors`, and uses the returned full frame to seed the unchanged Rules-4a--5, tracked-order,
  pseudo-count and geometry stages.  The bound and the frame are projected from the same prepared
  pair; the preparation is never repeated per stage.
* `universalDescriptor?_eq_descriptorAt?_of_bound_le` proves that at every budget at least the
  computed bound, the parameterized production descriptor equals the universal descriptor.  The
  bound is computed from the input and the base (`prepareUniversalRule3EvaluationOutcome` on
  `base.cursors`).
* `descriptorAt?_eq_none_of_center_none`, `descriptorAt?_eq_none_of_base_none` (and their universal
  counterparts) record that a missing descriptor center or four-ligand base is an exact `none`,
  at every budget.
* `universalDescriptor?_some_imp_exists_descriptorAt?_some` is unconditional: a successful
  universal descriptor is produced by the parameterized pipeline at the computed bound.
* `descriptorAt?_sound` and `universalDescriptor?_sound` export the independent positive meaning of
  every emitted descriptor: at the chosen Rule-3 budget for `descriptorAt?`, and at the bound
  computed by the universal preparation for `universalDescriptor?`.

## Operational completeness at every budget

The reverse direction -- every budget at which the parameterized descriptor succeeds implies the
universal descriptor succeeds -- needs one fact that the universal preparation alone does not
contain: a successful frame at a budget below the checked bound must *be* the universal frame, not
merely exist.  The registered green module `LocalizedExtendedFuelMonotonicity` proves that every
successful frame is reproduced with the identical value at every larger budget, and derives
`prepareUniversalRule3EvaluationOutcome_some_iff_exists_budget` and
`prepareUniversalRule3EvaluationOutcome_none_iff_forall_budget`.  This module imports those
results and uses them to *discharge* the interface `UniversalFrameAgreement` unconditionally
(`universalFrameAgreement`).  Consequently
`universalDescriptor?_isSome_iff_exists_descriptorAt?_isSome` and
`universalDescriptor?_eq_none_iff_forall_descriptorAt?_eq_none` are unconditional operational
completeness statements for the descriptor pipeline; no monotonicity proof is duplicated here.
The conditional forms are retained only as `..._of_agreement` helpers.  No theorem in this module
assumes acyclicity, a rank table, a desired label, a successful frame or a completeness premise.

## Scope

This is *unlimited operational completeness* of the executable descriptor pipeline, not the
independent chemical converse.  For soundness the module keeps the existing independent predicates
and only replaces the fixed Rule-3 fuel by a variable budget
(`DeclarativeLocalizedOccurrenceUniversalKeyFrame`, `...SpatialEvidence`, `...Descriptor`).  No
declarative relation is defined as executable equality, and nothing here claims that the
production budget
`localizedDescriptorBearingRule3EvaluationFuel` is sufficient in general.
`universalDescriptor?_eq_some_of_productionDescriptor?_eq_some` records positive preservation of
production results; it is not a new production-completeness claim.  Every statement here is
relative to one target and one dependency view: nothing here claims equality of global descriptor
states, or transport of labels between differently viewed reference states.
-/

/-! ## The shared Rules-4a--5 tail -/

/-- Finish the cumulative Rules-1a--5 key frame once the two-pass Rule-3 frame is fixed.  The
Rules-4a--5 pass keeps the production structural budget `localizedOccurrenceRerootEvaluationFuel`;
only the Rule-3 frame is supplied by the caller.  This is the single shared tail of the
parameterized and universal pipelines. -/
def finishKeyFrame? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45KeyExec? target view rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame
          rule3Length
          rule45Keys
          rule45Length }
    else none
  else none

/-- The cumulative Rules-1a--5 key frame at an arbitrary Rule-3 evaluation budget.  The
four-ligand base and the production Rules-4a--5 budget are the existing ones; only the Rule-3
frame evaluator budget is the parameter. -/
def keyFrameAt? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule3Frame ← input.buildLocalizedExtendedShortCircuitRule3FrameExec?
    target view evaluationBudget base.cursors
  input.finishKeyFrame? target view base rule3Frame

/-- At the production Rule-3 budget the parameterized key frame is exactly the existing
production descriptor-bearing key frame, including every length and Rules-4a--5 refusal. -/
theorem keyFrameAt?_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    input.keyFrameAt? target view base
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) =
      input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
        target view base := by
  unfold keyFrameAt? finishKeyFrame?
    buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
  rfl

/-- The key-frame stage refuses whenever the Rule-3 frame evaluator refuses, at every budget. -/
theorem keyFrameAt?_eq_none_of_frame_none (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat)
    (refused : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view evaluationBudget base.cursors = none) :
    input.keyFrameAt? target view base evaluationBudget = none := by
  unfold keyFrameAt?
  simp [refused]

/-! ## Parameterized spatial evidence -/

/-- The unchanged production evidence tail: the tracked stable order (with its pseudo-comparison
count) and the coordinate readings, given the four-ligand keys. -/
def spatialEvidenceFromKeys? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (_view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

/-- The production spatial-evidence pipeline at an arbitrary Rule-3 evaluation budget.  The
center reader, four-ligand base reader, tracked order and coordinate readers are unchanged. -/
def spatialEvidenceAt? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← input.localizedNoDoubleFourLigandFrameExec? target
  let keys ← input.keyFrameAt? target view base evaluationBudget
  input.spatialEvidenceFromKeys? target view center base keys

/-- At the production Rule-3 budget the parameterized evidence is exactly the existing
production evidence. -/
theorem spatialEvidenceAt?_production (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.spatialEvidenceAt? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
        target view := by
  unfold spatialEvidenceAt? keyFrameAt? finishKeyFrame? spatialEvidenceFromKeys?
  unfold localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
  unfold buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
  rfl

/-! ## Parameterized descriptor -/

/-- The unchanged production descriptor tail from a fixed four-ligand key frame. -/
def descriptorFromKeys? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.spatialEvidenceFromKeys? target view center base keys
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- The unchanged production descriptor tail from a chosen optional Rule-3 frame.  The frame is
supplied by the caller, so the same function serves both the parameterized and the universal
pipelines. -/
def descriptorFromFrame? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame? : Option input.LocalizedRule3CanonicalKeyFrame) :
    Option LocalizedAuxiliaryLabel := do
  let rule3Frame ← rule3Frame?
  let keys ← input.finishKeyFrame? target view base rule3Frame
  input.descriptorFromKeys? target view center base keys

/-- The actual tetrahedral descriptor pipeline at an arbitrary Rule-3 evaluation budget.  The
descriptor center and four-ligand base readers, the production Rules-4a--5 budget, the tracked
order, its pseudo-comparison count, the coordinate readings and the rational `R`/`S`
classification are the existing ones; only the Rule-3 frame budget is the parameter. -/
def descriptorAt? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) : Option LocalizedAuxiliaryLabel := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← input.localizedNoDoubleFourLigandFrameExec? target
  input.descriptorFromFrame? target view center base
    (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view evaluationBudget base.cursors)

/-- At the production Rule-3 budget the parameterized descriptor is exactly the existing
extended tetrahedral descriptor, including every center, base, key, order, geometry and pseudo
refusal. -/
theorem descriptorAt?_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.descriptorAt? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        target view := by
  unfold descriptorAt? descriptorFromFrame? descriptorFromKeys? spatialEvidenceFromKeys?
    finishKeyFrame?
  unfold localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
    localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
    buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some base =>
          cases frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
              target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
              base.cursors with
          | none => simp [frameComputed]
          | some rule3Frame =>
              by_cases rule3Length : rule3Frame.keys.length = 4
              · cases rule45Computed : base.cursors.mapM
                    (input.buildLocalizedRerootCompoundRule45KeyExec? target view
                      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) with
                | none => simp [frameComputed, rule45Computed]
                | some rule45Keys =>
                    by_cases rule45Length : rule45Keys.length = 4
                    · simp [frameComputed, rule3Length, rule45Computed, rule45Length]
                    · simp [frameComputed, rule45Computed, rule45Length]
              · simp [frameComputed, rule3Length]

/-- A missing descriptor center is an exact refusal of the parameterized descriptor. -/
theorem descriptorAt?_eq_none_of_center_none (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (missing : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.descriptorAt? target view evaluationBudget = none := by
  unfold descriptorAt? descriptorFromFrame?
  simp [missing]

/-- A missing four-ligand base is an exact refusal of the parameterized descriptor. -/
theorem descriptorAt?_eq_none_of_base_none (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (missing : input.localizedNoDoubleFourLigandFrameExec? target = none) :
    input.descriptorAt? target view evaluationBudget = none := by
  unfold descriptorAt? descriptorFromFrame?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center => simp [missing]

/-- A Rule-3 frame refusal is an exact refusal of the parameterized descriptor. -/
theorem descriptorAt?_eq_none_of_frame_none (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (refused : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view evaluationBudget base.cursors = none) :
    input.descriptorAt? target view evaluationBudget = none := by
  unfold descriptorAt? descriptorFromFrame?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases baseCase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some found =>
          rw [baseComputed] at baseCase
          cases baseCase
          simp [refused]

/-! ## The universal descriptor -/

/-- One preparation pass and one descriptor assembly.  The center and four-ligand base are read
once; `prepareUniversalRule3EvaluationOutcome` is run once on `base.cursors`, and both the
computed bound (`outcome.1`) and the returned full frame (`outcome.2`) are projected from that
single pair.  The returned frame seeds the unchanged Rules-4a--5, tracked-order, pseudo-count and
geometry stages.  In the missing-center or missing-base branches the result is `(0, none)`; no
preparation is run and no completeness is pretended. -/
def universalDescriptorOutcome (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat × Option LocalizedAuxiliaryLabel :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => (0, none)
  | some center =>
      match input.localizedNoDoubleFourLigandFrameExec? target with
      | none => (0, none)
      | some base =>
          let outcome := prepareUniversalRule3EvaluationOutcome input base.cursors target view
          (outcome.1, input.descriptorFromFrame? target view center base outcome.2)

/-- The universal tetrahedral descriptor: the second component of `universalDescriptorOutcome`. -/
def universalDescriptor? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel :=
  (input.universalDescriptorOutcome target view).2

/-- The preparation outcome at a present center and base.  The bound and the returned full frame
come from the same `prepareUniversalRule3EvaluationOutcome` call. -/
theorem universalDescriptorOutcome_eq_prepared (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base) :
    input.universalDescriptorOutcome target view =
      ((prepareUniversalRule3EvaluationOutcome input base.cursors target view).1,
        input.descriptorFromFrame? target view center base
          (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2) := by
  unfold universalDescriptorOutcome
  simp [centerComputed, baseComputed]

/-- A missing descriptor center is an exact refusal of the universal descriptor. -/
theorem universalDescriptor?_eq_none_of_center_none (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (missing : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.universalDescriptor? target view = none := by
  unfold universalDescriptor? universalDescriptorOutcome
  simp [missing]

/-- A missing four-ligand base is an exact refusal of the universal descriptor. -/
theorem universalDescriptor?_eq_none_of_base_none (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (missing : input.localizedNoDoubleFourLigandFrameExec? target = none) :
    input.universalDescriptor? target view = none := by
  unfold universalDescriptor? universalDescriptorOutcome
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center => simp [missing]

/-- A failed preparation is an exact refusal of the universal descriptor. -/
theorem universalDescriptor?_eq_none_of_prepare_error (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (failure : DiscoveryFailure (input.LocalizedRerootCursor carrierFuel))
    (failed : input.preparePreflightExtendedDemandPlan base.cursors = .error failure) :
    input.universalDescriptor? target view = none := by
  have frameNone :
      (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2 = none := by
    simp [prepareUniversalRule3EvaluationOutcome, failed]
  unfold universalDescriptor? universalDescriptorOutcome
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases baseCase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some found =>
          rw [baseComputed] at baseCase
          cases baseCase
          unfold descriptorFromFrame?
          simp [frameNone]

/-! ## Agreement with the parameterized pipeline at every larger budget -/

/-- **Main budget-agreement theorem.**  Fix the four-ligand base actually returned by the input.
At every budget at least the bound computed by the universal preparation on `base.cursors`, the
parameterized production descriptor equals the universal descriptor.  The proof only rewrites the
Rule-3 frame inside the shared pipeline using
`prepareUniversalRule3EvaluationOutcome_stable`; no other stage differs. -/
theorem universalDescriptor?_eq_descriptorAt?_of_bound_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (evaluationBudget : Nat)
    (enough : (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1 ≤
      evaluationBudget) :
    input.universalDescriptor? target view =
      input.descriptorAt? target view evaluationBudget := by
  have frameEq :
      (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2 =
        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          target view evaluationBudget base.cursors :=
    (input.prepareUniversalRule3EvaluationOutcome_stable base.cursors target view
      evaluationBudget enough).symm
  unfold universalDescriptor? universalDescriptorOutcome descriptorAt? descriptorFromFrame?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases baseCase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some found =>
          rw [baseComputed] at baseCase
          cases baseCase
          simp [frameEq]

/-- The universal descriptor uses the returned full frame at the computed bound: its second
component is the parameterized descriptor at exactly that bound. -/
theorem universalDescriptorOutcome_snd_eq_descriptorAt?_bound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base) :
    (input.universalDescriptorOutcome target view).2 =
      input.descriptorAt? target view
        (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1 := by
  simpa only [universalDescriptor?] using
    input.universalDescriptor?_eq_descriptorAt?_of_bound_le target view base baseComputed
      (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1
      (Nat.le_refl _)

/-- A successful universal descriptor is produced by the parameterized pipeline at the computed
bound.  This direction is unconditional: it uses only the budget-agreement theorem and the
`Nat.le_refl` instance, never successful-frame uniqueness. -/
theorem universalDescriptor?_some_imp_exists_descriptorAt?_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.universalDescriptor? target view = some descriptor) :
    ∃ (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) (evaluationBudget : Nat),
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        input.descriptorAt? target view evaluationBudget = some descriptor := by
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      have refused := input.universalDescriptor?_eq_none_of_center_none target view centerComputed
      rw [refused] at computed
      cases computed
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none =>
          have refused := input.universalDescriptor?_eq_none_of_base_none target view baseComputed
          rw [refused] at computed
          cases computed
      | some base =>
          refine ⟨base,
            (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1,
            rfl, ?_⟩
          have agree := input.universalDescriptor?_eq_descriptorAt?_of_bound_le
            target view base baseComputed
            (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1
            (Nat.le_refl _)
          rw [computed] at agree
          exact agree.symm

/-- The refusal branch of the preparation makes the parameterized descriptor refuse at every
budget and the universal descriptor refuse as well. -/
theorem universalDescriptor?_eq_none_and_all_descriptorAt?_eq_none_of_prepare_error
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (failure : DiscoveryFailure (input.LocalizedRerootCursor carrierFuel))
    (failed : input.preparePreflightExtendedDemandPlan base.cursors = .error failure) :
    input.universalDescriptor? target view = none ∧
      ∀ evaluationBudget, input.descriptorAt? target view evaluationBudget = none := by
  refine ⟨input.universalDescriptor?_eq_none_of_prepare_error
    target view base baseComputed failure failed, ?_⟩
  intro evaluationBudget
  exact input.descriptorAt?_eq_none_of_frame_none target view base evaluationBudget
    baseComputed (input.preparePreflightExtendedDemandPlan_error_allFuelRefusal
      base.cursors failure failed target view evaluationBudget)

/-! ## The monotonicity interface, discharged

The universal preparation evaluates one full frame at a checked bound.  The preparation alone does
not show that a successful frame at a *smaller* budget coincides with that frame.  The imported
green module `LocalizedExtendedFuelMonotonicity` supplies exactly this: successful frames are
reproduced identically at every larger budget, hence the prepared frame is the unique successful
frame whenever any budget succeeds.  The interface `UniversalFrameAgreement` below records the
needed consequence and is proved unconditionally by `universalFrameAgreement`.  The
`..._of_agreement` forms are the conditional intermediate steps; the exported completeness
theorems do not take the interface as a hypothesis. -/

/-- Interface consumed by the conditional forms of the equivalence: every successfully evaluated
frame is the frame returned by the universal preparation.  The proposition is proved
unconditionally as `universalFrameAgreement` from the imported green monotonicity module, so it is
*not* an assumption of the final completeness theorems. -/
def UniversalFrameAgreement (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  ∀ (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel),
    input.localizedNoDoubleFourLigandFrameExec? target = some base →
      ∀ evaluationBudget,
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          target view evaluationBudget base.cursors).isSome = true →
          input.buildLocalizedExtendedShortCircuitRule3FrameExec?
            target view evaluationBudget base.cursors =
            (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2

/-- **The successful-frame interface holds unconditionally.**  A frame that succeeds at any budget
is the frame returned by the universal preparation.  This is exactly
`prepareUniversalRule3EvaluationOutcome_some_iff_exists_budget` from the imported green
`LocalizedExtendedFuelMonotonicity`: monotonicity carries the successful frame up to the computed
bound, where the preparation is stable.  No monotonicity argument is reproved here. -/
theorem universalFrameAgreement (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.UniversalFrameAgreement target view := by
  intro base _baseComputed evaluationBudget success
  obtain ⟨frame, computed⟩ := Option.isSome_iff_exists.mp success
  have preparedSome :
      (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2 = some frame :=
    (input.prepareUniversalRule3EvaluationOutcome_some_iff_exists_budget
      base.cursors target view frame).mpr ⟨evaluationBudget, computed⟩
  rw [computed, preparedSome]

/-- A successful descriptor built from a chosen frame forces that frame to be `some`. -/
private theorem frame_isSome_of_descriptorFromFrame?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame? : Option input.LocalizedRule3CanonicalKeyFrame)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.descriptorFromFrame? target view center base rule3Frame? =
      some descriptor) :
    rule3Frame?.isSome = true := by
  unfold descriptorFromFrame? at computed
  cases frameCase : rule3Frame? with
  | none => simp [frameCase] at computed
  | some rule3Frame => simp

/-- **Conditional reverse direction.**  Under the successful-frame agreement interface, a
successful parameterized descriptor at any budget yields the same universal descriptor.  The
interface is discharged unconditionally by `universalFrameAgreement`, so the exported
completeness theorems below carry no hypothesis. -/
theorem universalDescriptor?_eq_some_of_descriptorAt?_eq_some_of_agreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (agreement : input.UniversalFrameAgreement target view)
    (descriptor : LocalizedAuxiliaryLabel)
    (evaluationBudget : Nat)
    (computed : input.descriptorAt? target view evaluationBudget = some descriptor) :
    input.universalDescriptor? target view = some descriptor := by
  unfold descriptorAt? at computed
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp [centerComputed, baseComputed] at computed
      | some base =>
          simp only [centerComputed, baseComputed] at computed
          have frameSome := input.frame_isSome_of_descriptorFromFrame?_eq_some
            target view center base _ descriptor computed
          have frameAgree := agreement base baseComputed evaluationBudget frameSome
          unfold universalDescriptor? universalDescriptorOutcome
          rw [centerComputed, baseComputed]
          dsimp only
          rw [← frameAgree]
          exact computed

/-- **Operational completeness, conditional form.**  Under successful-frame agreement, the
universal descriptor is successful exactly when some Rule-3 budget makes the parameterized
descriptor successful. -/
theorem universalDescriptor?_isSome_iff_exists_descriptorAt?_isSome_of_agreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (agreement : input.UniversalFrameAgreement target view) :
    (input.universalDescriptor? target view).isSome = true ↔
      ∃ evaluationBudget, (input.descriptorAt? target view evaluationBudget).isSome = true := by
  constructor
  · intro success
    obtain ⟨descriptor, computed⟩ := Option.isSome_iff_exists.mp success
    obtain ⟨base, evaluationBudget, _, atSome⟩ :=
      input.universalDescriptor?_some_imp_exists_descriptorAt?_some
        target view descriptor computed
    exact ⟨evaluationBudget, by simp [atSome]⟩
  · rintro ⟨evaluationBudget, success⟩
    obtain ⟨descriptor, computed⟩ := Option.isSome_iff_exists.mp success
    have universal := input.universalDescriptor?_eq_some_of_descriptorAt?_eq_some_of_agreement
      target view agreement descriptor evaluationBudget computed
    simp [universal]

/-- **Unlimited operational completeness.**  The universal descriptor is successful exactly when
some Rule-3 evaluation budget makes the parameterized descriptor pipeline successful.  This is
unconditional: the successful-frame interface is discharged by the imported green monotonicity
module through `universalFrameAgreement`.  It is a statement about the executable descriptor
pipeline, not a chemical converse. -/
theorem universalDescriptor?_isSome_iff_exists_descriptorAt?_isSome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (input.universalDescriptor? target view).isSome = true ↔
      ∃ evaluationBudget, (input.descriptorAt? target view evaluationBudget).isSome = true :=
  input.universalDescriptor?_isSome_iff_exists_descriptorAt?_isSome_of_agreement
    target view (input.universalFrameAgreement target view)

/-- **All-budget refusal, conditional form.**  Under successful-frame agreement the universal
descriptor refuses exactly when every Rule-3 budget refuses. -/
theorem universalDescriptor?_eq_none_iff_forall_descriptorAt?_eq_none_of_agreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (agreement : input.UniversalFrameAgreement target view) :
    input.universalDescriptor? target view = none ↔
      ∀ evaluationBudget, input.descriptorAt? target view evaluationBudget = none := by
  constructor
  · intro universalNone evaluationBudget
    cases budgetCase : input.descriptorAt? target view evaluationBudget with
    | none => rfl
    | some descriptor =>
        have universalSome := input.universalDescriptor?_eq_some_of_descriptorAt?_eq_some_of_agreement
          target view agreement descriptor evaluationBudget budgetCase
        rw [universalNone] at universalSome
        cases universalSome
  · intro allNone
    cases universalCase : input.universalDescriptor? target view with
    | none => rfl
    | some descriptor =>
        obtain ⟨base, evaluationBudget, _, atSome⟩ :=
          input.universalDescriptor?_some_imp_exists_descriptorAt?_some
            target view descriptor universalCase
        rw [allNone evaluationBudget] at atSome
        cases atSome

/-- **Unlimited operational refusal.**  The universal descriptor refuses exactly when every
Rule-3 evaluation budget refuses.  Unconditional, via the discharged successful-frame interface;
it is an operational statement about the executable pipeline, not a claim of declarative
nonexistence or chemical impossibility. -/
theorem universalDescriptor?_eq_none_iff_forall_descriptorAt?_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.universalDescriptor? target view = none ↔
      ∀ evaluationBudget, input.descriptorAt? target view evaluationBudget = none :=
  input.universalDescriptor?_eq_none_iff_forall_descriptorAt?_eq_none_of_agreement
    target view (input.universalFrameAgreement target view)

/-- Every positive production descriptor is also produced by the universal descriptor, with the
same label.  This is per-target and per-view preservation of an already-established production
result; it does not claim that the production budget is sufficient in general, and it does not
assert equality of global descriptor states or transport across differently labeled views. -/
theorem universalDescriptor?_eq_some_of_productionDescriptor?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view = some descriptor) :
    input.universalDescriptor? target view = some descriptor := by
  rw [← input.descriptorAt?_production target view] at computed
  exact input.universalDescriptor?_eq_some_of_descriptorAt?_eq_some_of_agreement
    target view (input.universalFrameAgreement target view) descriptor
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) computed

/-! ## Independent declarative meaning at a variable Rule-3 budget

These predicates retain the existing independent relations and replace only the fixed Rule-3
evaluation fuel by a variable budget.  They are not defined as executable equalities: the Rule-3
frame keeps `DeclarativeLocalizedExtendedShortCircuitRule3Frame`, the Rules-4a--5 keys keep
`DeclarativeLocalizedRerootCompoundRule45Key`, the tracked order keeps
`DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder`, the coordinates keep
`DeclarativeLocalizedRerootCursorSpatialPoint`, and the geometry keeps
`RationalTetrahedralDescriptor`. -/

/-- The cumulative Rules-1a--5 key frame meaning at an arbitrary Rule-3 budget. -/
def DeclarativeLocalizedOccurrenceUniversalKeyFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) : Prop :=
  input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view evaluationBudget
      base.cursors frame.rule3Frame ∧
    frame.rule3Frame.keys.length = 4 ∧
    List.Forall₂
      (input.DeclarativeLocalizedRerootCompoundRule45Key target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      base.cursors frame.rule45Keys ∧
    frame.rule45Keys.length = 4

/-- The ranked spatial evidence meaning at an arbitrary Rule-3 budget. -/
def DeclarativeLocalizedOccurrenceUniversalSpatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) : Prop :=
  input.RealTetrahedralCenterNode target.1.node evidence.center ∧
    input.DeclarativeLocalizedOccurrenceFourLigandFrame target evidence.base ∧
    input.DeclarativeLocalizedOccurrenceUniversalKeyFrame target view evidence.base
      evaluationBudget evidence.keys ∧
    input.DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder
      evidence.keys evidence.tracked ∧
    List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (evidence.base.cursorAt index) point)
      evidence.tracked.highestFirst evidence.points

/-- The independent positive meaning of the descriptor at an arbitrary Rule-3 budget. -/
def DeclarativeLocalizedOccurrenceUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    input.DeclarativeLocalizedOccurrenceUniversalSpatialEvidence target view evaluationBudget
      evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

/-! ### Soundness of the parameterized pipeline -/

/-- Successful `mapM` over independent Rules-4a--5 keys preserves the aligned declarative
meaning. -/
private theorem mapM_rule45_sound_universal (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) :
    ∀ cursors keys,
      (cursors : List (input.LocalizedRerootCursor carrierFuel)).mapM
          (input.buildLocalizedRerootCompoundRule45Key? target view fuel) =
        some (keys : List input.LocalizedRerootCompoundRule45Key) →
      List.Forall₂
        (input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel)
        cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact List.Forall₂.nil
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootCompoundRule45Key?
          target view fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootCompoundRule45Key? target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact List.Forall₂.cons
                (input.buildLocalizedRerootCompoundRule45Key?_sound
                  target view fuel cursor head headComputed)
                (input.mapM_rule45_sound_universal target view fuel cursors tail tailComputed)

/-- Successful `mapM` over coordinate readings preserves the aligned declarative meaning. -/
private theorem mapM_spatial_sound_universal (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points,
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
        (base.cursorAt index)) = some points →
      List.Forall₂
        (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
          (base.cursorAt index) point) order points
  | [], points, computed => by
      simp at computed
      subst points
      exact List.Forall₂.nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases pointComputed : input.localizedRerootCursorSpatialPoint?
          (base.cursorAt index) with
      | none => simp [pointComputed] at computed
      | some point =>
          cases tailComputed : order.mapM fun next =>
              input.localizedRerootCursorSpatialPoint? (base.cursorAt next) with
          | none => simp [pointComputed, tailComputed] at computed
          | some tail =>
              simp [pointComputed, tailComputed] at computed
              subst points
              exact List.Forall₂.cons
                ((input.localizedRerootCursorSpatialPoint?_eq_some_iff
                  (base.cursorAt index) point).mp pointComputed)
                (input.mapM_spatial_sound_universal base order tail tailComputed)

/-- Successful Rules-4a--5 completion at a fixed Rule-3 frame has the independent key meaning. -/
theorem finishKeyFrame?_sound (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view evaluationBudget base.cursors = some rule3Frame)
    (computed : input.finishKeyFrame? target view base rule3Frame = some frame) :
    input.DeclarativeLocalizedOccurrenceUniversalKeyFrame target view base
      evaluationBudget frame := by
  have rule45Eq := funext fun cursor =>
    input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor
  unfold finishKeyFrame? at computed
  simp only [← rule45Eq] at computed
  by_cases rule3Length : rule3Frame.keys.length = 4
  · cases rule45Computed : base.cursors.mapM
        (input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)) with
    | none => simp [rule3Length, rule45Computed] at computed
    | some rule45Keys =>
        by_cases rule45Length : rule45Keys.length = 4
        · simp [rule3Length, rule45Computed, rule45Length] at computed
          subst frame
          exact
            ⟨input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound
                target view evaluationBudget base.cursors rule3Frame frameComputed,
              rule3Length,
              input.mapM_rule45_sound_universal target view
                (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                base.cursors rule45Keys rule45Computed,
              rule45Length⟩
        · simp [rule3Length, rule45Computed, rule45Length] at computed
  · simp [rule3Length] at computed

/-- The parameterized key frame has the independent key meaning at its budget. -/
theorem keyFrameAt?_sound (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : input.keyFrameAt? target view base evaluationBudget = some frame) :
    input.DeclarativeLocalizedOccurrenceUniversalKeyFrame target view base
      evaluationBudget frame := by
  unfold keyFrameAt? at computed
  cases frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view evaluationBudget base.cursors with
  | none => simp [frameComputed] at computed
  | some rule3Frame =>
      simp only [frameComputed] at computed
      exact input.finishKeyFrame?_sound target view base evaluationBudget rule3Frame frame
        frameComputed computed

/-- Successful assembly of the tracked order and coordinates from a fixed key frame has the
independent evidence meaning, given the center, base and key meanings at the chosen budget. -/
theorem spatialEvidenceFromKeys?_sound (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (centerMeaning : input.RealTetrahedralCenterNode target.1.node center)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base)
    (keysMeaning : input.DeclarativeLocalizedOccurrenceUniversalKeyFrame target view base
      evaluationBudget keys)
    (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (computed : input.spatialEvidenceFromKeys? target view center base keys = some evidence) :
    input.DeclarativeLocalizedOccurrenceUniversalSpatialEvidence target view
      evaluationBudget evidence := by
  unfold spatialEvidenceFromKeys? at computed
  simp only [localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?]
    at computed
  cases trackedComputed : input.safeLocalizedOccurrenceRule3Through5TrackedOrder? keys with
  | none => simp [trackedComputed] at computed
  | some tracked =>
      cases pointsComputed : tracked.highestFirst.mapM fun index =>
          input.localizedRerootCursorSpatialPoint? (base.cursorAt index) with
      | none => simp [trackedComputed, pointsComputed] at computed
      | some points =>
          simp [trackedComputed, pointsComputed] at computed
          subst evidence
          exact ⟨centerMeaning, baseMeaning, keysMeaning,
            input.safeLocalizedOccurrenceRule3Through5TrackedOrder?_sound
              keys tracked trackedComputed,
            input.mapM_spatial_sound_universal base tracked.highestFirst points pointsComputed⟩

/-- The parameterized spatial evidence has the independent evidence meaning at its budget. -/
theorem spatialEvidenceAt?_sound (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (computed : input.spatialEvidenceAt? target view evaluationBudget = some evidence) :
    input.DeclarativeLocalizedOccurrenceUniversalSpatialEvidence target view
      evaluationBudget evidence := by
  unfold spatialEvidenceAt? at computed
  simp only [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    at computed
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases baseComputed : input.localizedOccurrenceFourLigandFrame? target with
      | none => simp [centerComputed, baseComputed] at computed
      | some base =>
          cases keysComputed : input.keyFrameAt? target view base evaluationBudget with
          | none => simp [centerComputed, baseComputed, keysComputed] at computed
          | some keys =>
              cases evidenceComputed :
                  input.spatialEvidenceFromKeys? target view center base keys with
              | none =>
                  simp [centerComputed, baseComputed, keysComputed, evidenceComputed]
                    at computed
              | some found =>
                  simp [centerComputed, baseComputed, keysComputed, evidenceComputed]
                    at computed
                  subst evidence
                  exact input.spatialEvidenceFromKeys?_sound target view evaluationBudget
                    center base keys
                    ((input.localizedOccurrenceDescriptorCenter?_eq_some_iff
                      target center).mp centerComputed)
                    (input.localizedOccurrenceFourLigandFrame?_sound target base baseComputed)
                    (input.keyFrameAt?_sound target view base evaluationBudget keys keysComputed)
                    found evidenceComputed

/-! ### Positive soundness of the parameterized and universal descriptors -/

/-- Definitional unfolding of the descriptor tail at a supplied successful Rule-3 frame. -/
theorem descriptorFromFrame?_some (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame) :
    input.descriptorFromFrame? target view center base (some rule3Frame) =
      (input.finishKeyFrame? target view base rule3Frame).bind
        (fun keys => input.descriptorFromKeys? target view center base keys) := rfl

/-- Definitional unfolding of the descriptor tail at an absent Rule-3 frame. -/
theorem descriptorFromFrame?_none (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    input.descriptorFromFrame? target view center base none = none := rfl

/-- A successful descriptor assembled from a fixed cumulative key frame carries the independent
declarative meaning at the chosen Rule-3 budget, given the center, base and key meanings. -/
theorem descriptorFromKeys?_sound (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (centerMeaning : input.RealTetrahedralCenterNode target.1.node center)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base)
    (keysMeaning : input.DeclarativeLocalizedOccurrenceUniversalKeyFrame target view base
      evaluationBudget keys)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.descriptorFromKeys? target view center base keys = some descriptor) :
    input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor := by
  unfold descriptorFromKeys? at computed
  cases evidenceComputed : input.spatialEvidenceFromKeys? target view center base keys with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
      | none => simp [evidenceComputed, rawComputed] at computed
      | some raw =>
          simp [evidenceComputed, rawComputed] at computed
          subst descriptor
          exact ⟨evidence, raw,
            input.spatialEvidenceFromKeys?_sound target view evaluationBudget center base keys
              centerMeaning baseMeaning keysMeaning evidence evidenceComputed,
            (descriptorOfPriorityOrderedPoints?_eq_some_iff evidence.points raw).mp rawComputed,
            rfl⟩

/-- A successful descriptor built from a fixed Rule-3 frame at the evaluated budget carries the
independent declarative meaning.  The frame is the actual evaluator output at that budget. -/
theorem descriptorFromFrame?_sound (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame)
    (frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view evaluationBudget base.cursors = some rule3Frame)
    (centerMeaning : input.RealTetrahedralCenterNode target.1.node center)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.descriptorFromFrame? target view center base (some rule3Frame) =
      some descriptor) :
    input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor := by
  rw [input.descriptorFromFrame?_some] at computed
  cases keysComputed : input.finishKeyFrame? target view base rule3Frame with
  | none => simp [keysComputed] at computed
  | some keys =>
      simp only [keysComputed] at computed
      exact input.descriptorFromKeys?_sound target view evaluationBudget center base keys
        centerMeaning baseMeaning
        (input.finishKeyFrame?_sound target view base evaluationBudget rule3Frame keys
          frameComputed keysComputed)
        descriptor computed

/-- Definitional unfolding of the parameterized descriptor when the center and base readers
succeed: the descriptor reduces to the unchanged descriptor tail applied to the actual Rule-3
frame evaluator output at the chosen budget. -/
theorem descriptorAt?_eq_descriptorFromFrame?_of_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base) :
    input.descriptorAt? target view evaluationBudget =
      input.descriptorFromFrame? target view center base
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          target view evaluationBudget base.cursors) := by
  unfold descriptorAt?
  simp [centerComputed, baseComputed]

/-- **Positive soundness of the parameterized descriptor.**  Every descriptor emitted at any
Rule-3 evaluation budget has the independent declarative meaning at that budget: the descriptor
center, the four-ligand base, the cumulative Rules-1a--5 keys (with the existing Rule-3 relation at
the chosen budget and the production Rules-4a--5 budget), the tracked stable order with its
pseudo-comparison count, the exact coordinates, and the rational `R`/`S` classification. -/
theorem descriptorAt?_sound (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.descriptorAt? target view evaluationBudget = some descriptor) :
    input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor := by
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      have refused := input.descriptorAt?_eq_none_of_center_none target view evaluationBudget
        centerComputed
      rw [refused] at computed
      cases computed
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none =>
          have refused := input.descriptorAt?_eq_none_of_base_none target view evaluationBudget
            baseComputed
          rw [refused] at computed
          cases computed
      | some base =>
          cases frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
              target view evaluationBudget base.cursors with
          | none =>
              have refused := input.descriptorAt?_eq_none_of_frame_none target view base
                evaluationBudget baseComputed frameComputed
              rw [refused] at computed
              cases computed
          | some frame =>
              have occurrenceComputed :
                  input.localizedOccurrenceFourLigandFrame? target = some base := by
                rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
                exact baseComputed
              have expanded := input.descriptorAt?_eq_descriptorFromFrame?_of_some
                target view center base evaluationBudget centerComputed baseComputed
              rw [expanded, frameComputed] at computed
              exact input.descriptorFromFrame?_sound target view center base evaluationBudget frame
                frameComputed
                ((input.localizedOccurrenceDescriptorCenter?_eq_some_iff
                  target center).mp centerComputed)
                (input.localizedOccurrenceFourLigandFrame?_sound target base occurrenceComputed)
                descriptor computed

/-- Positive soundness of the universal descriptor at the computed preparation bound, for a fixed
four-ligand base.  A successful universal outcome has the independent declarative meaning at the
bound computed from the input and that base. -/
theorem universalDescriptor?_sound_of_bound (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.universalDescriptor? target view = some descriptor) :
    input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1
      descriptor := by
  have agree := input.universalDescriptor?_eq_descriptorAt?_of_bound_le
    target view base baseComputed
    (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1
    (Nat.le_refl _)
  have atBound : input.descriptorAt? target view
      (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1 =
      some descriptor := by
    rw [← agree]
    exact computed
  exact input.descriptorAt?_sound target view _ descriptor atBound

/-- **Positive soundness of the universal descriptor.**  If the universal descriptor is
successful, then for the four-ligand base actually returned by the input it has the independent
declarative meaning at the bound computed by the universal preparation from that base.  The
refusal branch is not reinterpreted: no declarative claim is made when the universal descriptor
is `none`. -/
theorem universalDescriptor?_sound (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.universalDescriptor? target view = some descriptor) :
    ∃ (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel),
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1
          descriptor := by
  have computed' : input.universalDescriptor? target view = some descriptor := computed
  unfold universalDescriptor? universalDescriptorOutcome at computed
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp [centerComputed, baseComputed] at computed
      | some base =>
          exact ⟨base, rfl,
            input.universalDescriptor?_sound_of_bound target view base baseComputed
              descriptor computed'⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
