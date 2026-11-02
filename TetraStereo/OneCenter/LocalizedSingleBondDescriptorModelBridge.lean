import TetraStereo.OneCenter.LocalizedNoDoubleRule3ChemicalCompleteness
import TetraStereo.OneCenter.LocalizedExtendedDescriptorSuccessPreservation
import TetraStereo.OneCenter.LocalizedDescriptorExecutable
import TetraStereo.OneCenter.LocalizedOccurrenceRule3Through5Descriptor
import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.OneCenter.LocalizedConstitutionalOriginalRule3Coherence
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.OneCenter.LocalizedWholeStateExtendedDescriptorClosure
import TetraStereo.OneCenter.LocalizedExtendedFuelMonotonicity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Single-bond bridge: actual extended Rule-3 descriptor equals the bare Rule-4a--5 descriptor

This module closes the gap between the actual production descriptor-bearing Rules-1a--5 evaluator
(`localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?`, whose Rule-3 stage is the
extended short-circuit frame) and the bare cumulative Rules-4a--5 evaluator
(`localizedOccurrenceRule45Descriptor?`, which has no Rule-3 stage at all), for every runtime input
whose source molecule carries no localized order-two record.

The bridge is *not* a definitional alias and does not assume comparator agreement.  It is derived
from the actual compilers:

* on a single-bond occurrence the descriptor-bearing Rule-3 frame compiles, and every successfully
  compiled per-cursor key is `Rule3Aligned` with empty observations, hence has empty numeric Rule-3
  layers (`declarativeLocalizedDescriptorBearingRule3Key_rule3Aligned`,
  `..._rule3_eq_nil_of_noDoubleRecords`);
* the constitutional observable of the descriptor-bearing Rule-3 key and of the cumulative
  Rules-4a--5 key at the same cursor agree at *arbitrary, possibly different* recursion budgets
  (`declarative_constitutional_observable_unique`), so the two spatial comparators agree
  pointwise with ordinary, non-pseudo records whenever the constitutional observable decides,
  while an exhaustive constitutional tie falls through identically to the actual Rule-5
  comparison and therefore retains its genuine `±2` pseudoasymmetry
  (`..._compare_..._eq_rule45`);
* consequently the tracked stable order, its all-pairs coherence check, the coordinate readings and
  the final pseudo-classification agree, giving the full `Option` descriptor equality, refusals
  included.

This module owns the actual production extended descriptor versus bare Rules-4a--5 descriptor
equality only.  The prepared universal evaluator, the whole-state evaluator and the whole-state
model identification are built on top of this endpoint in the separate
`LocalizedNoDoubleWholeStateRule45Bridge` module, which imports this one.  The derived geometry
fact `localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_noDoubleRecords` is exported here
because it is a direct consequence of the same source restriction and is consumed by that
downstream module.

No successful descriptor, comparator agreement, key equality, dummy refusal baseline, desired label
or geometry premise is assumed.  Every exported declaration is guarded by `assert_kernel_only`.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The source restriction discharges the conditional geometry domain -/

/-- Without a localized order-two source record both executable Rule-3 route inspectors refuse at
every carrier occurrence, so every conditional implication of the independent all-occurrence
geometry domain is vacuous. -/
theorem localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (carrierFuel : Nat) :
    input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel := by
  intro occurrence
  have notEdge :=
    input.localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords noDouble occurrence
  have oddNone := input.localizedRule3OddRouteCertificate?_eq_none_of_not_edge occurrence notEdge
  have ordinaryNone :=
    input.localizedRule3OrdinaryRouteCertificate?_eq_none_of_not_edge occurrence notEdge
  simp only [LocalizedRule3ExtendedNodeConditionalGeometryDomain, oddNone, ordinaryNone]

/-! ## Core success theorem: the actual extended key frame compiles -/

/-- **The actual extended short-circuit Rules-1a--5 key frame compiles on every actual four-ligand
base of a single-bond input.**  The original descriptor-bearing builder is total there; the
executable wrapper is definitionally the original and the extended production builder reproduces
the very same frame value. -/
theorem exists_buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base) :
    ∃ keys, input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      target view base = some keys := by
  obtain ⟨keys, originalSome⟩ :=
    input.exists_buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame_of_noDoubleRecords
      noDouble target view base baseMeaning
  have execSome : input.localizedDescriptorKeyFrameExec? target view base = some keys := by
    rw [input.localizedDescriptorKeyFrameExec?_eq_original, originalSome]
  exact ⟨keys, input.extendedShortCircuitKeyFrame_preserves_originalExec
    target view base keys execSome⟩

/-! ## Component extraction from the original key frame -/

/-- The Rules-4a--5 pass of a successful original key frame compilation is the executable positional
`mapM` that produced its stored key list. -/
theorem buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?_rule45_computed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
      target view base = some keys) :
    base.cursors.mapM (input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) = some keys.rule45Keys := by
  unfold buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame? at computed
  let descriptorFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  cases frameComputed : input.buildLocalizedDescriptorBearingRule3Frame?
      target view descriptorFuel base.cursors with
  | none => simp [frameComputed, descriptorFuel] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : base.cursors.mapM
            (input.buildLocalizedRerootCompoundRule45Key? target view rule45Fuel) with
        | none =>
            simp [frameComputed, rule3Length, rule45Computed,
              descriptorFuel, rule45Fuel] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [frameComputed, rule3Length, rule45Computed, rule45Length,
                descriptorFuel, rule45Fuel] at computed
              subst keys
              simp [rule45Fuel]
            · simp [frameComputed, rule45Computed, rule45Length,
                descriptorFuel, rule45Fuel] at computed
      · simp [frameComputed, rule3Length, descriptorFuel] at computed

/-- The Rule-3 pass of a successful extended key frame compilation is the executable positional
`mapM` that produced its stored frame value. -/
theorem buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_frame_computed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      target view base = some keys) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) base.cursors =
      some keys.rule3Frame := by
  unfold buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? at computed
  let descriptorFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  cases frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view descriptorFuel base.cursors with
  | none => simp [frameComputed, descriptorFuel] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : base.cursors.mapM
            (input.buildLocalizedRerootCompoundRule45KeyExec? target view rule45Fuel) with
        | none =>
            simp [frameComputed, rule3Length, rule45Computed,
              descriptorFuel, rule45Fuel] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [frameComputed, rule3Length, rule45Computed, rule45Length,
                descriptorFuel, rule45Fuel] at computed
              subst keys
              simp [descriptorFuel]
            · simp [frameComputed, rule45Computed, rule45Length,
                descriptorFuel, rule45Fuel] at computed
      · simp [frameComputed, rule3Length, descriptorFuel] at computed

/-! ## Declarative alignment of the descriptor-bearing Rule-3 key -/

/-- Every member of the right list of a `Forall₂` satisfies any property satisfied pointwise. -/
theorem forall₂_right_forall {α β : Type*} {R : α → β → Prop} {P : β → Prop}
    (complete : ∀ a b, R a b → P b) {as : List α} {bs : List β}
    (derived : List.Forall₂ R as bs) : ∀ b ∈ bs, P b := by
  induction derived with
  | nil => intro b present; simp at present
  | cons head tail ih =>
      intro b present
      rcases List.mem_cons.mp present with rfl | present
      · exact complete _ _ head
      · exact ih b present

/-- Every independent descriptor-bearing Rule-3 key derivation is numerically aligned with its
retained physical-unit observations. -/
theorem declarativeLocalizedDescriptorBearingRule3Key_rule3Aligned
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor key,
      input.DeclarativeLocalizedRerootDescriptorBearingRule3Key target view fuel excluded cursor
        key →
      key.Rule3Aligned := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor key derived
      obtain ⟨children, _children, _empty, _notEdge, rfl⟩ := derived
      rfl
  | succ fuel ih =>
      intro excluded cursor key derived
      obtain ⟨children, observation, _children, _observed, terminal | recursive⟩ := derived
      · obtain ⟨_empty, rfl⟩ := terminal
        exact input.localizedRule3SpatialRootPriorities_eq_map_observations observation
      · obtain ⟨childKeys, sorted, _nonempty, childrenDerived, permutation, _descending, rfl⟩ :=
          recursive
        have childAligned : ∀ child ∈ childKeys, child.Rule3Aligned := by
          intro child present
          exact forall₂_right_forall
            (fun cursor parentKey derivation => ih excluded cursor parentKey derivation)
            childrenDerived child present
        have sortedAligned : ∀ child ∈ sorted, child.Rule3Aligned := by
          intro child present
          exact childAligned child (permutation.mem_iff.mp present)
        unfold LocalizedRerootRecursiveRule3SpatialKey.Rule3Aligned
        rw [OfficialRuleMajorKey.mapSourceLayers_append,
          input.localizedRule3SpatialRootPriorities_eq_map_observations observation,
          input.mergeLocalizedRerootRule3PriorityChildren_eq_map_observations sorted sortedAligned]

/-- On a single-bond source, every independent descriptor-bearing Rule-3 key derivation carries no
numeric Rule-3 layers at all. -/
theorem declarativeLocalizedDescriptorBearingRule3Key_rule3_eq_nil_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor key,
      input.DeclarativeLocalizedRerootDescriptorBearingRule3Key target view fuel excluded cursor
        key →
      key.rule3 = [] := by
  intro fuel excluded cursor key derived
  have aligned :=
    input.declarativeLocalizedDescriptorBearingRule3Key_rule3Aligned target view
      fuel excluded cursor key derived
  have empty :=
    input.declarativeLocalizedDescriptorBearingRule3Key_observations_nil_of_noDoubleRecords
      noDouble target view fuel excluded cursor key derived
  unfold LocalizedRerootRecursiveRule3SpatialKey.Rule3Aligned at aligned
  rw [empty] at aligned
  simpa [OfficialRuleMajorKey.mapSourceLayers] using aligned

/-! ## Positional declarative data of one actual key frame -/

/-- For every one of the four positional ligand slots, a successful original key frame compilation
provides the exact independent Rule-3 and Rules-4a--5 derivations, the empty Rule-3 layers, and the
equality of constitutional observables between the two stages at that same cursor. -/
theorem descriptorBearingRule3Through5KeyFrame_index_data
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (keysSome : input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
      target view base = some keys) :
    (base.cursors.mapM (input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)) = some keys.rule45Keys) ∧
    ∀ index : Fin 4,
      input.DeclarativeLocalizedRerootDescriptorBearingRule3Key target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel - 1)
        keys.rule3Frame.excluded (base.cursorAt index) (keys.keyAt index).rule3 ∧
      (keys.keyAt index).rule3.rule3 = [] ∧
      constitutionalObservable (keys.keyAt index).rule3.constitutional =
        constitutionalObservable (keys.keyAt index).rule45.prior.rule4aKey.constitutional ∧
      input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) (base.cursorAt index) =
        some (keys.keyAt index).rule45 := by
  have keysSound := input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?_sound
    target view base keys keysSome
  have rule45Computed :=
    input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?_rule45_computed
      target view base keys keysSome
  have fuelPos : 0 < localizedDescriptorBearingRule3EvaluationFuel carrierFuel := by
    simp [localizedDescriptorBearingRule3EvaluationFuel]
  have fuelEq : localizedDescriptorBearingRule3EvaluationFuel carrierFuel =
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos fuelPos).symm
  have frameDecl := keysSound.1
  rw [fuelEq] at frameDecl
  obtain ⟨_rawForall, _topology, _declTopology, _declPolicy, rule3Forall⟩ := frameDecl
  refine ⟨rule45Computed, ?_⟩
  intro index
  have rule3Decl : input.DeclarativeLocalizedRerootDescriptorBearingRule3Key target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel - 1)
      keys.rule3Frame.excluded (base.cursorAt index) (keys.keyAt index).rule3 := by
    have extracted := forall₂_get_fin rule3Forall base.length_eq keys.rule3Length index
    simpa [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using extracted
  have rule45Decl : input.DeclarativeLocalizedRerootCompoundRule45Key target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (base.cursorAt index) (keys.keyAt index).rule45 := by
    have extracted := forall₂_get_fin keysSound.2.2.1 base.length_eq keys.rule45Length index
    simpa [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using extracted
  have rule3Nil :=
    input.declarativeLocalizedDescriptorBearingRule3Key_rule3_eq_nil_of_noDoubleRecords
      noDouble target view _ _ _ _ rule3Decl
  have rule3Constitutional :=
    input.descriptorRule3Key_constitutional_derived target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel - 1)
      keys.rule3Frame.excluded (base.cursorAt index) (keys.keyAt index).rule3 rule3Decl
  have rule45Constitutional :=
    input.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
      .rule4a target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (base.cursorAt index) (keys.keyAt index).rule45.prior.rule4aKey rule45Decl.1.1
  have observableEq : constitutionalObservable (keys.keyAt index).rule3.constitutional =
      constitutionalObservable (keys.keyAt index).rule45.prior.rule4aKey.constitutional :=
    input.declarative_constitutional_observable_unique
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel - 1)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (base.cursorAt index) (keys.keyAt index).rule3.constitutional
      (keys.keyAt index).rule45.prior.rule4aKey.constitutional
      rule3Constitutional rule45Constitutional
  have buildEq : input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (base.cursorAt index) =
      some (keys.keyAt index).rule45 := by
    have extracted := frame_mapM_cursorAt_eq_some input base
      (input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      keys.rule45Keys rule45Computed keys.rule45Length index
    simpa [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using extracted
  exact ⟨rule3Decl, rule3Nil, observableEq, buildEq⟩

/-! ## Route-independent key comparators on a single-bond source -/

/-- A decisive constitutional comparison determines the cumulative Rules-4a--5 comparator. -/
theorem compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_ne
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (decisive : OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠
      Ordering.eq) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      OfficialRuleMajorKey.compare left.constitutional right.constitutional := by
  have firstNe : (Ordering.byKey (fun key => key.constitutional)
      OfficialRuleMajorKey.compare) left right ≠ Ordering.eq := by
    change OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.eq
    exact decisive
  unfold compareLocalizedRerootCumulativeRule45Keys
  rw [localizedCompareLex_eq_left_of_ne firstNe]
  rfl

/-- A decisive prior comparison determines the through-Rule-5 comparison record before Rule 5. -/
theorem compareLocalizedRerootCompoundThroughRule5_eq_of_prior_ne
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (decisive : input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior ≠
      Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior,
        pseudo := false } := by
  unfold compareLocalizedRerootCompoundThroughRule5
  generalize priorEq : input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior =
    prior at decisive ⊢
  cases prior with
  | lt => simp [priorEq]
  | eq => exact (decisive rfl).elim
  | gt => simp [priorEq]

/-- A Rule-3 `lt` decision is ordinary and decisive. -/
theorem compareLocalizedOccurrenceRule3Through5At_of_rule3_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (strict : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.lt) :
    input.compareLocalizedOccurrenceRule3Through5At frame left right =
      { ordering := Ordering.lt, pseudo := false } := by
  simp [compareLocalizedOccurrenceRule3Through5At, strict]

/-- **Pointwise comparator equality.**  On a single-bond source, the descriptor-bearing
Rules-1a--5 pair comparator agrees with the bare through-Rule-5 comparator at every pair of the
four positional ligands, with both Option values present. -/
theorem compareLocalizedOccurrenceRule3Through5At?_eq_rule45_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (keysSome : input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
      target view base = some keys) :
    ∀ left right,
      input.compareLocalizedOccurrenceRule3Through5At? keys left right =
        input.compareLocalizedOccurrenceThroughRule5At? target view base left right := by
  obtain ⟨_rule45Computed, data⟩ :=
    input.descriptorBearingRule3Through5KeyFrame_index_data noDouble target view base keys keysSome
  intro left right
  obtain ⟨_rule3DeclLeft, rule3NilLeft, observableLeft, buildLeft⟩ := data left
  obtain ⟨_rule3DeclRight, rule3NilRight, observableRight, buildRight⟩ := data right
  have constEq : OfficialRuleMajorKey.compare
      (keys.keyAt left).rule3.constitutional (keys.keyAt right).rule3.constitutional =
      OfficialRuleMajorKey.compare
        (keys.keyAt left).rule45.prior.rule4aKey.constitutional
        (keys.keyAt right).rule45.prior.rule4aKey.constitutional :=
    ruleMajor_compare_congr _ _ _ _ observableLeft observableRight
  unfold compareLocalizedOccurrenceRule3Through5At? compareLocalizedOccurrenceThroughRule5At?
  dsimp only
  rw [buildLeft, buildRight]
  simp only [instMonadOption, Option.bind_some, Option.some.injEq]
  generalize firstEq : OfficialRuleMajorKey.compare
    (keys.keyAt left).rule3.constitutional (keys.keyAt right).rule3.constitutional = first
  have first45 : OfficialRuleMajorKey.compare
      (keys.keyAt left).rule45.prior.rule4aKey.constitutional
      (keys.keyAt right).rule45.prior.rule4aKey.constitutional = first := by
    rw [← constEq]
    exact firstEq
  have spatialOfNe (decisive : first ≠ Ordering.eq) :
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (keys.keyAt left).rule3 (keys.keyAt right).rule3 = first := by
    have firstNe : (Ordering.byKey (fun key => key.constitutional)
        OfficialRuleMajorKey.compare) (keys.keyAt left).rule3
        (keys.keyAt right).rule3 ≠ Ordering.eq := by
      change OfficialRuleMajorKey.compare (keys.keyAt left).rule3.constitutional
        (keys.keyAt right).rule3.constitutional ≠ Ordering.eq
      rw [firstEq]
      exact decisive
    unfold compareLocalizedRerootRecursiveRule3SpatialKeys
    rw [localizedCompareLex_eq_left_of_ne firstNe]
    change OfficialRuleMajorKey.compare (keys.keyAt left).rule3.constitutional
      (keys.keyAt right).rule3.constitutional = first
    exact firstEq
  cases first with
  | lt =>
      have spatial := spatialOfNe (by decide)
      have cumulative : input.compareLocalizedRerootCumulativeRule45Keys
          (keys.keyAt left).rule45.prior.rule4aKey
          (keys.keyAt right).rule45.prior.rule4aKey = Ordering.lt := by
        rw [compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_ne input _ _
          (by rw [first45]; decide)]
        exact first45
      have prior : input.compareLocalizedRerootCompoundRule4bcKeys
          (keys.keyAt left).rule45.prior (keys.keyAt right).rule45.prior = Ordering.lt := by
        rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne _ _
          (by rw [cumulative]; decide)]
        exact cumulative
      have through : input.compareLocalizedRerootCompoundThroughRule5
          (keys.keyAt left).rule45 (keys.keyAt right).rule45 =
          { ordering := Ordering.lt, pseudo := false } := by
        rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_prior_ne _ _
          (by rw [prior]; decide)]
        rw [prior]
      rw [input.compareLocalizedOccurrenceRule3Through5At_of_rule3_lt keys left right spatial,
        through]
      simp [localizedOccurrenceRule45ComparisonRecord]
  | gt =>
      have spatial := spatialOfNe (by decide)
      have cumulative : input.compareLocalizedRerootCumulativeRule45Keys
          (keys.keyAt left).rule45.prior.rule4aKey
          (keys.keyAt right).rule45.prior.rule4aKey = Ordering.gt := by
        rw [compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_ne input _ _
          (by rw [first45]; decide)]
        exact first45
      have prior : input.compareLocalizedRerootCompoundRule4bcKeys
          (keys.keyAt left).rule45.prior (keys.keyAt right).rule45.prior = Ordering.gt := by
        rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne _ _
          (by rw [cumulative]; decide)]
        exact cumulative
      have through : input.compareLocalizedRerootCompoundThroughRule5
          (keys.keyAt left).rule45 (keys.keyAt right).rule45 =
          { ordering := Ordering.gt, pseudo := false } := by
        rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_prior_ne _ _
          (by rw [prior]; decide)]
        rw [prior]
      rw [input.compareLocalizedOccurrenceRule3Through5At_of_rule3_gt keys left right spatial,
        through]
      simp [localizedOccurrenceRule45ComparisonRecord]
  | eq =>
      have spatial : input.compareLocalizedRerootRecursiveRule3SpatialKeys
          (keys.keyAt left).rule3 (keys.keyAt right).rule3 = Ordering.eq := by
        have firstTied : (Ordering.byKey (fun key => key.constitutional)
            OfficialRuleMajorKey.compare) (keys.keyAt left).rule3
            (keys.keyAt right).rule3 = Ordering.eq := by
          change OfficialRuleMajorKey.compare (keys.keyAt left).rule3.constitutional
            (keys.keyAt right).rule3.constitutional = Ordering.eq
          exact firstEq
        unfold compareLocalizedRerootRecursiveRule3SpatialKeys
        rw [localizedCompareLex_eq_right_of_eq firstTied]
        change OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (keys.keyAt left).rule3.rule3 (keys.keyAt right).rule3.rule3 = Ordering.eq
        rw [rule3NilLeft, rule3NilRight]
        rfl
      rw [input.compareLocalizedOccurrenceRule3Through5At_of_rule3_eq keys left right spatial]

/-! ## Congruence of the tracked stable sort -/

/-- One tracked insertion is congruent in the comparison function. -/
theorem insertLocalizedLigandTracked_congr
    (compareAt compareAt' : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (same : ∀ left right, compareAt left right = compareAt' left right)
    (candidate : Fin 4) :
    ∀ existing : List (Fin 4),
      insertLocalizedLigandTracked compareAt candidate existing =
        insertLocalizedLigandTracked compareAt' candidate existing
  | [] => rfl
  | low :: remaining => by
      unfold insertLocalizedLigandTracked
      rw [same low candidate]
      cases compared : compareAt' low candidate with
      | none => rfl
      | some comparison =>
          simp only [instMonadOption, Option.bind_some]
          cases ordering : comparison.ordering with
          | eq => rfl
          | gt => rfl
          | lt =>
              rw [insertLocalizedLigandTracked_congr compareAt compareAt' same candidate remaining]

/-- The tail-recursive tracked sort is congruent in the comparison function. -/
theorem sortLocalizedLigandsTrackedFrom_congr
    (compareAt compareAt' : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (same : ∀ left right, compareAt left right = compareAt' left right) :
    ∀ candidates lowestFirst pseudoComparisons,
      sortLocalizedLigandsTrackedFrom compareAt candidates lowestFirst pseudoComparisons =
        sortLocalizedLigandsTrackedFrom compareAt' candidates lowestFirst pseudoComparisons
  | [], _, _ => rfl
  | candidate :: candidates, lowestFirst, pseudoComparisons => by
      unfold sortLocalizedLigandsTrackedFrom
      rw [insertLocalizedLigandTracked_congr compareAt compareAt' same candidate lowestFirst]
      cases insertedComputed :
          insertLocalizedLigandTracked compareAt' candidate lowestFirst with
      | none => rfl
      | some inserted =>
          exact sortLocalizedLigandsTrackedFrom_congr compareAt compareAt' same candidates
            inserted.lowestFirst (pseudoComparisons + inserted.pseudoComparisons)

/-- The tracked stable sort is congruent in the comparison function. -/
theorem sortLocalizedLigandsTracked_congr
    (compareAt compareAt' : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (same : ∀ left right, compareAt left right = compareAt' left right)
    (candidates : List (Fin 4)) :
    sortLocalizedLigandsTracked compareAt candidates =
      sortLocalizedLigandsTracked compareAt' candidates := by
  unfold sortLocalizedLigandsTracked
  exact sortLocalizedLigandsTrackedFrom_congr compareAt compareAt' same candidates [] 0

/-- The concrete four-position tracked sort is congruent in the comparison function. -/
theorem sortFourLocalizedLigandsTracked_congr
    (compareAt compareAt' : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (same : ∀ left right, compareAt left right = compareAt' left right) :
    sortFourLocalizedLigandsTracked compareAt = sortFourLocalizedLigandsTracked compareAt' := by
  unfold sortFourLocalizedLigandsTracked
  exact sortLocalizedLigandsTracked_congr compareAt compareAt' same (List.finRange 4)

/-! ## Coherence of the tracked order -/

/-- The descriptor-bearing pair-strict check agrees with the bare through-Rule-5 check once the
comparators agree pointwise. -/
theorem localizedOccurrenceRule3Through5OrderPairStrict_eq_rule45
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (cmpEq : ∀ left right,
      input.compareLocalizedOccurrenceRule3Through5At? keys left right =
        input.compareLocalizedOccurrenceThroughRule5At? target view base left right)
    (left right : Fin 4) :
    input.localizedOccurrenceRule3Through5OrderPairStrict keys left right =
      input.localizedOccurrenceRule45OrderPairStrict? target view base left right := by
  unfold localizedOccurrenceRule3Through5OrderPairStrict
    localizedOccurrenceRule45OrderPairStrict?
  rw [← cmpEq left right]
  rfl

/-- The all-pairs coherence check of the descriptor-bearing order agrees with the bare
through-Rule-5 coherence check once the comparators agree pointwise. -/
theorem localizedOccurrenceRule3Through5OrderCoherent_eq_rule45
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (cmpEq : ∀ left right,
      input.compareLocalizedOccurrenceRule3Through5At? keys left right =
        input.compareLocalizedOccurrenceThroughRule5At? target view base left right) :
    ∀ order,
      input.localizedOccurrenceRule3Through5OrderCoherent keys order =
        input.localizedOccurrenceRule45OrderCoherent? target view base order
  | [] => rfl
  | left :: rest => by
      have pairEq : ∀ right,
          input.localizedOccurrenceRule3Through5OrderPairStrict keys left right =
            input.localizedOccurrenceRule45OrderPairStrict? target view base left right :=
        fun right =>
          localizedOccurrenceRule3Through5OrderPairStrict_eq_rule45
            input target view base keys cmpEq left right
      have allEq : rest.all (input.localizedOccurrenceRule3Through5OrderPairStrict keys left) =
          rest.all (input.localizedOccurrenceRule45OrderPairStrict? target view base left) := by
        induction rest with
        | nil => rfl
        | cons right rest ih => simp only [List.all_cons, pairEq right, ih]
      unfold localizedOccurrenceRule3Through5OrderCoherent
        localizedOccurrenceRule45OrderCoherent?
      rw [allEq, localizedOccurrenceRule3Through5OrderCoherent_eq_rule45
        input target view base keys cmpEq rest]

/-! ## The safe tracked order -/

/-- **The actual safe tracked order agrees.**  The stable sort, the all-pairs coherence
rejection and the final tracked order of the descriptor-bearing pipeline coincide with the bare
through-Rule-5 pipeline at every input where the extended key frame compiles. -/
theorem safeLocalizedOccurrenceRule3Through5TrackedOrder?_eq_rule45_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (keysSome : input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
      target view base = some keys) :
    input.safeLocalizedOccurrenceRule3Through5TrackedOrder? keys =
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view base := by
  have cmpEq :=
    input.compareLocalizedOccurrenceRule3Through5At?_eq_rule45_of_noDoubleRecords
      noDouble target view base keys keysSome
  unfold safeLocalizedOccurrenceRule3Through5TrackedOrder?
    safeLocalizedOccurrenceRule45TrackedOrder?
    localizedOccurrenceRule3Through5TrackedOrder?
    localizedOccurrenceRule45TrackedOrder?
  rw [sortFourLocalizedLigandsTracked_congr _ _ cmpEq]
  cases sortComputed : sortFourLocalizedLigandsTracked
      (input.compareLocalizedOccurrenceThroughRule5At? target view base) with
  | none => simp only [instMonadOption, Option.bind_none]
  | some tracked =>
      simp only [instMonadOption, Option.bind_some]
      rw [localizedOccurrenceRule3Through5OrderCoherent_eq_rule45
        input target view base keys cmpEq tracked.highestFirst]

/-! ## Full `Option` descriptor equality -/

/-- **The actual production descriptor and the bare Rules-4a--5 descriptor are the same
`Option`.**  Centre, four-ligand base, Rule-3 key frame, tracked order, its coherence refusal,
coordinate readings, rational descriptor and pseudo-classification all agree, and both pipelines
refuse exactly when the centre, the base, the tracked order or a coordinate reading is absent.
No successful descriptor, comparator agreement or desired label is assumed. -/
theorem localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_rule45Descriptor_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view =
      input.localizedOccurrenceRule45Descriptor? target view := by
  unfold localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
    localizedOccurrenceRule45Descriptor?
    localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
    localizedOccurrenceRule45SpatialEvidence?
  rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp only [instMonadOption, centerComputed, Option.bind_none]
  | some center =>
      cases frameComputed : input.localizedOccurrenceFourLigandFrame? target with
      | none =>
          simp only [instMonadOption, centerComputed, frameComputed,
            Option.bind_none, Option.bind_some]
      | some base =>
          obtain ⟨keys, originalSome⟩ :=
            input.exists_buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame_of_noDoubleRecords
              noDouble target view base
              (input.localizedOccurrenceFourLigandFrame?_sound target base frameComputed)
          have execSome : input.localizedDescriptorKeyFrameExec? target view base = some keys := by
            rw [input.localizedDescriptorKeyFrameExec?_eq_original, originalSome]
          have extendedSome :
              input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
                target view base = some keys :=
            input.extendedShortCircuitKeyFrame_preserves_originalExec target view base keys execSome
          simp only [instMonadOption, centerComputed, frameComputed, extendedSome,
            Option.bind_some]
          rw [input.localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?
            keys]
          rw [safeLocalizedOccurrenceRule3Through5TrackedOrder?_eq_rule45_of_noDoubleRecords
            input noDouble target view base keys originalSome]
          cases trackedComputed :
              input.safeLocalizedOccurrenceRule45TrackedOrder? target view base with
          | none => simp only [instMonadOption, Option.bind_none]
          | some tracked =>
              simp only [instMonadOption, Option.bind_some]
              cases pointsComputed : tracked.highestFirst.mapM
                  (fun index =>
                    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) with
              | none => simp only [instMonadOption, Option.bind_none]
              | some points =>
                  simp only [instMonadOption, Option.bind_some, Option.some.injEq]

end CertifiedLocalizedCIPInput

/-! ## Public guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?_rule45_computed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_frame_computed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.forall₂_right_forall
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedDescriptorBearingRule3Key_rule3Aligned
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedDescriptorBearingRule3Key_rule3_eq_nil_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorBearingRule3Through5KeyFrame_index_data
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_of_prior_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule3Through5At_of_rule3_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule3Through5At?_eq_rule45_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.insertLocalizedLigandTracked_congr
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortLocalizedLigandsTrackedFrom_congr
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortLocalizedLigandsTracked_congr
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortFourLocalizedLigandsTracked_congr
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule3Through5OrderPairStrict_eq_rule45
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule3Through5OrderCoherent_eq_rule45
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.safeLocalizedOccurrenceRule3Through5TrackedOrder?_eq_rule45_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_rule45Descriptor_of_noDoubleRecords

end TetraStereo.OneCenter
