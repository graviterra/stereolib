import Mathlib.Tactic.IntervalCases
import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority
import TetraStereo.OneCenter.LocalizedRetainedContextGeneratedDescriptor
import TetraStereo.OneCenter.LocalizedFourSlotReflectionParity
import TetraStereo.OneCenter.LocalizedRetainedPhysicalConfigurationTransport
import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# Actual generated uppercase labels at constitutionally strict cyclic frames

Fix a real detected carrier occurrence with its compiled actual frame
(`ContextFrameCompilation`). The input is simple-bonded and may have rings. Assume only that
the frame is constitutionally strict (`FrameConstitutionalStrict`). Every remaining step is
derived from the actual pipeline:

1. Each compiled compound's retained Rule-4a key is an actual rule-major build with the target's
   context reader (`compound_rule4aKey_built`). Strictness makes every off-diagonal cumulative,
   prior and through-Rule-5 comparison equal to the constitutional comparison, with the pseudo
   flag `false`.
2. The retained complete keys are injective. Their prior components are pairwise distinct, so
   `completeRule5PairCount = 0`.
3. `priorityOrder` is `descendingOrder` of the retained keys. Its position `p` holds the slot of
   `p`-th highest priority. It is characterized reader-free by `ConstitutionallyAbove`: for
   `p < q`, every pair of successful builds at slots `τ p`, `τ q` compares `gt`. It is unique
   with that property.
4. With coordinates available at the actual cursors and a nonzero priority-ordered volume, the
   actual generated reference state is `some (.chiral raw)`. Here `raw` is `R` exactly for a
   negative volume. This uses `referenceState_some_iff_retainedJudgment`, the fixed point of the
   actual generated state, so the label is the actual state value, not a recomputation.
5. Physical form (`referenceState_eq_chiral_of_calibrated`): at a calibrated center,
   `raw = R` exactly when
   `configurationSign cfg center * permHandedness α * permHandedness τ = -1`. Here `α` is the
   actual frame's detected-ligand permutation and `τ` the contextual priority permutation.
   Nonzero volume is derived from the calibration.
6. The executed runtime agrees (`spatialEvidence_eq_priorityOrder`): the actual safe tracked
   sort returns `List.ofFn τ` with pseudo count `0`, and the executed descriptor is the
   generated state.
7. Endpoint (`referenceState_eq_chiral_of_tiedRootArm`, `_of_domain`): at a real nonroot
   detected occurrence in a Rule-1a tied root arm, with a calibrated general-rigid center, the
   strictness premise is discharged by
   `frameConstitutionalStrict_of_rootArmRule1aTie_of_physicalRigid`. The domain form reads the
   calibration from `ActualGeneralRigidPhysicalDomain`.

The priority permutation is contextual: it is read at the stored carrier occurrence, with its
outer root and full history. No raw `R/S` context independence, fresh-root descriptor,
comparator law, sort success, selected reference, acyclicity or reader agreement is assumed.
-/

namespace TetraStereo.OneCenter
namespace LocalizedCyclicGeneralRigidGeneratedLabels

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedRuleMajorReference
open LocalizedCyclicGeneralRigidPriority
open LocalizedFourSlotReflectionParity

/-! ## Compound builds -/

/-- The retained Rule-4a key of any successful compound build is the compiler's Rule-4a value. -/
theorem compoundWith_rule4aKey_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor = some compound) :
    compileStage .rule4a cursor = some compound.prior.rule4aKey := by
  unfold buildRuleMajorCompoundRule45KeyWith? at built
  rcases Option.eq_none_or_eq_some (compileStage .rule4a cursor) with h4a | ⟨key, h4a⟩
  · rw [h4a] at built
    simp [Option.bind_eq_bind, Option.bind_none] at built
  · rw [h4a] at built
    simp only [Option.bind_eq_bind, Option.bind_some] at built
    rcases Option.eq_none_or_eq_some
        (input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels key.rankedLabels))) with
      hr | ⟨readings, hr⟩
    · rw [hr] at built
      simp [Option.bind_eq_bind, Option.bind_none] at built
    · rw [hr] at built
      simp only [Option.bind_eq_bind, Option.bind_some] at built
      rcases Option.eq_none_or_eq_some
          (input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor
            (input.rankReadings readings)) with
        h5 | ⟨rule5, h5⟩
      · rw [h5] at built
        simp [Option.bind_eq_bind, Option.bind_none] at built
      · rw [h5] at built
        simp only [Option.bind_eq_bind, Option.bind_some, Option.some_inj] at built
        rw [h4a, ← built]

private theorem ofFn_fin4 {α : Type*} (f : Fin 4 → α) :
    List.ofFn f = [f 0, f 1, f 2, f 3] := by
  refine List.ext_get (by simp) ?_
  intro n h1 _h2
  have hn : n < 4 := by simpa using h1
  interval_cases n <;> simp

section Frames

variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  (frames : ContextFrameCompilation input target unit targetUnit)

/-- The retained Rule-4a key of each compiled compound is the actual rule-major build with the
target's context reader at the standard fuel. -/
theorem compound_rule4aKey_built (index : Fin 4) :
    input.certified.buildRuleMajorCumulativeWithRead? .rule4a
      (fun source => input.certified.localizedDependencyLabel target
        (contextOccurrenceView input target) source)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frames.frame.cursorAt index) =
      some (frames.compounds index).prior.rule4aKey := by
  have uniformBuilt :=
    (input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor target
      (contextOccurrenceView input target) (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frames.frame.cursorAt index)).symm.trans
      ((input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq target
        (contextOccurrenceView input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1))
        (frames.frame.cursorAt index)).symm.trans (frames.compoundBuilt index))
  exact compoundWith_rule4aKey_eq _ _ uniformBuilt

/-- The compiled frame is the actual computed four-ligand frame of the target. -/
theorem frame_computed :
    input.certified.localizedOccurrenceFourLigandFrame? target = some frames.frame :=
  (input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
    target).symm.trans frames.frameComputed

/-! ## Strictness decides every compiled comparison -/

variable (strict : FrameConstitutionalStrict frames.frame)

include strict in
/-- Strictness, read at the compiled compounds' own Rule-4a builds. -/
theorem compound_constitutional_ne {left right : Fin 4} (distinct : left ≠ right) :
    OfficialRuleMajorKey.compare (frames.compounds left).prior.rule4aKey.constitutional
      (frames.compounds right).prior.rule4aKey.constitutional ≠ Ordering.eq :=
  strict left right distinct .rule4a .rule4a _ _ _ _ _ _
    (compound_rule4aKey_built frames left) (compound_rule4aKey_built frames right)

include strict in
/-- The cumulative Rule-4a comparison is the constitutional comparison. -/
theorem compound_cumulative_eq {left right : Fin 4} (distinct : left ≠ right) :
    input.certified.compareLocalizedRerootCumulativeRule45Keys
        (frames.compounds left).prior.rule4aKey (frames.compounds right).prior.rule4aKey =
      OfficialRuleMajorKey.compare (frames.compounds left).prior.rule4aKey.constitutional
        (frames.compounds right).prior.rule4aKey.constitutional := by
  have constNe := compound_constitutional_ne frames strict distinct
  unfold compareLocalizedRerootCumulativeRule45Keys
  refine ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _ ?_
  simpa [Ordering.byKey] using constNe

include strict in
private theorem compound_cumulative_ne {left right : Fin 4} (distinct : left ≠ right) :
    input.certified.compareLocalizedRerootCumulativeRule45Keys
        (frames.compounds left).prior.rule4aKey (frames.compounds right).prior.rule4aKey ≠
      Ordering.eq := by
  rw [compound_cumulative_eq frames strict distinct]
  exact compound_constitutional_ne frames strict distinct

include strict in
/-- The through-Rule-5 comparison is the constitutional comparison, with pseudo flag `false`. -/
theorem compound_throughRule5_eq {left right : Fin 4} (distinct : left ≠ right) :
    input.certified.compareLocalizedRerootCompoundThroughRule5
        (frames.compounds left) (frames.compounds right) =
      { ordering := OfficialRuleMajorKey.compare
          (frames.compounds left).prior.rule4aKey.constitutional
          (frames.compounds right).prior.rule4aKey.constitutional
        pseudo := false } := by
  rw [input.certified.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq _ _
    (compound_cumulative_ne frames strict distinct), compound_cumulative_eq frames strict distinct]

include strict in
/-- The prior Rules-4b/4c comparison is the constitutional comparison. -/
theorem compound_prior_eq {left right : Fin 4} (distinct : left ≠ right) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (frames.compounds left).prior (frames.compounds right).prior =
      OfficialRuleMajorKey.compare (frames.compounds left).prior.rule4aKey.constitutional
        (frames.compounds right).prior.rule4aKey.constitutional := by
  rw [input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne _ _
    (compound_cumulative_ne frames strict distinct), compound_cumulative_eq frames strict distinct]

variable (singleBonded : input.certified.moleculeGraph.SimpleBonded)

include strict singleBonded in
/-- The retained complete-key order is the constitutional order. -/
theorem retainedKeys_compare_eq {left right : Fin 4} (distinct : left ≠ right) :
    compare (frames.retainedKeys left) (frames.retainedKeys right) =
      OfficialRuleMajorKey.compare (frames.compounds left).prior.rule4aKey.constitutional
        (frames.compounds right).prior.rule4aKey.constitutional := by
  rw [← frames.retainedActual_fullOrdering singleBonded left right,
    compound_throughRule5_eq frames strict distinct]

include strict singleBonded in
/-- The retained complete keys are injective. -/
theorem retainedKeys_injective : Function.Injective frames.retainedKeys := by
  intro left right same
  by_contra distinct
  have compared := retainedKeys_compare_eq frames strict singleBonded distinct
  rw [same, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at compared
  exact compound_constitutional_ne frames strict distinct compared.symm

include strict singleBonded in
/-- Distinct slots have distinct retained prior keys. -/
theorem retainedPrior_ne {left right : Fin 4} (distinct : left ≠ right) :
    (ofLex (frames.retainedKeys left)).1 ≠ (ofLex (frames.retainedKeys right)).1 := by
  intro same
  have priorCmp := frames.retainedActual_priorComparison singleBonded left right
  rw [compound_prior_eq frames strict distinct,
    (completeLigandPriorKey_compare_eq_iff _ _).mpr same] at priorCmp
  exact compound_constitutional_ne frames strict distinct priorCmp

include strict singleBonded in
/-- No retained prior pair: the pseudo count is zero. -/
theorem completeRule5PairCount_eq_zero : completeRule5PairCount frames.retainedKeys = 0 := by
  have noPair : ∀ left right, ¬ CompletePriorPair frames.retainedKeys left right :=
    fun _ _ pair => retainedPrior_ne frames strict singleBonded pair.1 pair.2
  unfold completeRule5PairCount sourceEnantiomorphicPairCount
  simp [noPair]

/-! ## The contextual priority permutation -/

/-- The contextual constitutional priority permutation of the compiled frame. Position `p`
holds the frame slot of `p`-th highest priority. -/
noncomputable def priorityOrder : Equiv.Perm (Fin 4) :=
  descendingOrder frames.retainedKeys (retainedKeys_injective frames strict singleBonded)

theorem priorityOrder_retainedKeys_lt {p q : Fin 4} (lower : p < q) :
    frames.retainedKeys (priorityOrder frames strict singleBonded q) <
      frames.retainedKeys (priorityOrder frames strict singleBonded p) := by
  have pairwise := descendingOrder_pairwise frames.retainedKeys
    (retainedKeys_injective frames strict singleBonded)
  rw [List.pairwise_ofFn] at pairwise
  exact pairwise lower

/-- The priority permutation descends in the constitutional order of the compiled compounds. -/
theorem priorityOrder_compound_gt {p q : Fin 4} (lower : p < q) :
    OfficialRuleMajorKey.compare
        (frames.compounds (priorityOrder frames strict singleBonded p)).prior.rule4aKey.constitutional
        (frames.compounds (priorityOrder frames strict singleBonded q)).prior.rule4aKey.constitutional =
      Ordering.gt := by
  have distinct : priorityOrder frames strict singleBonded p ≠
      priorityOrder frames strict singleBonded q :=
    fun same => (ne_of_lt lower) ((priorityOrder frames strict singleBonded).injective same)
  rw [← retainedKeys_compare_eq frames strict singleBonded distinct]
  exact (completeLigandRule5Key_compare_gt_iff _ _).mpr
    (priorityOrder_retainedKeys_lt frames strict singleBonded lower)

/-- **Reader-free characterization.** For `p < q` the slot at position `p` is constitutionally
above the slot at position `q`: every pair of successful builds, at any stage, reader and fuel,
compares `gt`. -/
theorem priorityOrder_above {p q : Fin 4} (lower : p < q) :
    ConstitutionallyAbove (frames.frame.cursorAt (priorityOrder frames strict singleBonded p))
      (frames.frame.cursorAt (priorityOrder frames strict singleBonded q)) :=
  constitutionallyAbove_of_builds
    (compound_rule4aKey_built frames (priorityOrder frames strict singleBonded p))
    (compound_rule4aKey_built frames (priorityOrder frames strict singleBonded q))
    (priorityOrder_compound_gt frames strict singleBonded lower)

include strict singleBonded in
/-- **Uniqueness.** Any slot permutation descending in the reader-free constitutional order is
the priority permutation. -/
theorem priorityOrder_unique (σ : Equiv.Perm (Fin 4))
    (descending : ∀ p q : Fin 4, p < q →
      ConstitutionallyAbove (frames.frame.cursorAt (σ p)) (frames.frame.cursorAt (σ q))) :
    σ = priorityOrder frames strict singleBonded := by
  apply descendingOrder_unique
  intro p q lower
  have above := descending p q lower .rule4a .rule4a _ _ _ _ _ _
    (compound_rule4aKey_built frames (σ p)) (compound_rule4aKey_built frames (σ q))
  have distinct : σ p ≠ σ q := fun same => (ne_of_lt lower) (σ.injective same)
  rw [← retainedKeys_compare_eq frames strict singleBonded distinct] at above
  exact (completeLigandRule5Key_compare_gt_iff _ _).mp above

/-! ## The actual generated label -/

/-- **Actual generated uppercase label at a constitutionally strict frame.** With coordinates
available at the actual cursors and a nonzero volume in contextual priority order, the actual
generated reference state is `some (.chiral raw)`. Here `raw` is `R` exactly for a negative
priority-ordered volume. -/
theorem referenceState_eq_chiral
    (points : Fin 4 → CartesianPoint3)
    (available : ∀ slot, frames.actualCoordinates slot = some (points slot))
    (nonzero : reindexedVolume points (priorityOrder frames strict singleBonded) ≠ 0) :
    referenceState input target = some (.chiral
      (if reindexedVolume points (priorityOrder frames strict singleBonded) < 0 then .R
        else .S)) := by
  apply (frames.referenceState_some_iff_retainedJudgment singleBonded _).mpr
  refine ⟨points, available, ?_⟩
  change CompleteRootDescriptorJudgment frames.retainedKeys points _
  have inj := retainedKeys_injective frames strict singleBonded
  have count := completeRule5PairCount_eq_zero frames strict singleBonded
  have hlist : (List.ofFn (priorityOrder frames strict singleBonded)).map points =
      [points (priorityOrder frames strict singleBonded 0),
        points (priorityOrder frames strict singleBonded 1),
        points (priorityOrder frames strict singleBonded 2),
        points (priorityOrder frames strict singleBonded 3)] := by
    rw [List.map_ofFn]
    exact ofFn_fin4 _
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · refine ⟨List.ofFn (priorityOrder frames strict singleBonded), .R,
      descendingOrder_perm_finRange frames.retainedKeys inj,
      descendingOrder_pairwise frames.retainedKeys inj, ⟨_, _, _, _, hlist, negative⟩, ?_⟩
    rw [count, if_pos negative]
    simp [classifyTetrahedralRSPseudo]
  · refine ⟨List.ofFn (priorityOrder frames strict singleBonded), .S,
      descendingOrder_perm_finRange frames.retainedKeys inj,
      descendingOrder_pairwise frames.retainedKeys inj, ⟨_, _, _, _, hlist, positive⟩, ?_⟩
    rw [count, if_neg (not_lt_of_gt positive)]
    simp [classifyTetrahedralRSPseudo]

include strict singleBonded in
/-- The actual generated state is uppercase: it is not lowercase and not a refusal. -/
theorem referenceState_isChiral
    (points : Fin 4 → CartesianPoint3)
    (available : ∀ slot, frames.actualCoordinates slot = some (points slot))
    (nonzero : reindexedVolume points (priorityOrder frames strict singleBonded) ≠ 0) :
    ∃ raw : RS, referenceState input target = some (.chiral raw) :=
  ⟨_, referenceState_eq_chiral frames strict singleBonded points available nonzero⟩

/-! ## The actual executed sort -/

/-- The actual executed descriptor at the target's own context view is the generated state. -/
theorem ruleMajorDescriptorExec_eq_referenceState :
    input.certified.ruleMajorDescriptorExec? target (contextOccurrenceView input target) =
      referenceState input target :=
  (input.certified.ruleMajorDescriptorExec?_eq target _).trans (reference_fixed input target)

private theorem mapM_some_of_forall {α β : Type*} (f : α → Option β) (g : α → β)
    (h : ∀ x, f x = some (g x)) : ∀ l : List α, l.mapM f = some (l.map g)
  | [] => rfl
  | x :: xs => by
      rw [List.mapM_cons, h x, mapM_some_of_forall f g h xs]
      rfl

/-- **The actual executed sort at a strict frame.** The executed spatial evidence exists. Its
safe tracked order is the contextual priority permutation, its pseudo count is zero, and its
points are the actual coordinates in that order. The nonzero volume only makes the final
orientation read succeed; the sort is the actual runtime sort, not a reconstruction. -/
theorem spatialEvidence_eq_priorityOrder
    (points : Fin 4 → CartesianPoint3)
    (available : ∀ slot, frames.actualCoordinates slot = some (points slot))
    (nonzero : reindexedVolume points (priorityOrder frames strict singleBonded) ≠ 0) :
    ∃ evidence, input.certified.ruleMajorSpatialEvidenceExec? target
        (contextOccurrenceView input target) = some evidence ∧
      evidence.frame = frames.frame ∧
      evidence.tracked.highestFirst = List.ofFn (priorityOrder frames strict singleBonded) ∧
      evidence.tracked.pseudoComparisons = 0 ∧
      evidence.points = (List.ofFn (priorityOrder frames strict singleBonded)).map points := by
  have exec := (ruleMajorDescriptorExec_eq_referenceState (input := input)
    (target := target)).trans
    (referenceState_eq_chiral frames strict singleBonded points available nonzero)
  unfold CertifiedLocalizedCIPInput.ruleMajorDescriptorExec? at exec
  cases hev : input.certified.ruleMajorSpatialEvidenceExec? target
      (contextOccurrenceView input target) with
  | none => simp [hev] at exec
  | some evidence =>
      refine ⟨evidence, rfl, ?_⟩
      have expanded := hev
      unfold CertifiedLocalizedCIPInput.ruleMajorSpatialEvidenceExec? at expanded
      rw [frames.centerComputed, frames.frameComputed] at expanded
      cases hs : safeTrackedOrderOrderedExecOf (input.certified.compareRuleMajorOccurrenceExecAt?
          target (contextOccurrenceView input target) frames.frame) with
      | none => simp [hs] at expanded
      | some tracked =>
          cases hp : tracked.highestFirst.mapM (fun slot =>
              input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot)) with
          | none => simp [hs, hp] at expanded
          | some values =>
              simp [hs, hp] at expanded
              subst expanded
              have safe := hs
              rw [safeTrackedOrderOrderedExecOf_eq] at safe
              unfold safeTrackedOrderOf at safe
              cases hsort : sortFourLocalizedLigandsTracked
                  (input.certified.compareRuleMajorOccurrenceExecAt? target
                    (contextOccurrenceView input target) frames.frame) with
              | none => simp [hsort] at safe
              | some sorted =>
                  simp only [hsort] at safe
                  cases hcoherent : orderCoherentOf
                      (input.certified.compareRuleMajorOccurrenceExecAt? target
                        (contextOccurrenceView input target) frames.frame)
                      sorted.highestFirst with
                  | false => simp [hcoherent] at safe
                  | true =>
                      simp [hcoherent] at safe
                      have same : sorted = tracked := safe
                      subst same
                      have inj := retainedKeys_injective frames strict singleBonded
                      have perm := sortFourLocalizedLigandsTracked_perm _ sorted hsort
                      have pairwise : sorted.highestFirst.Pairwise
                          (fun left right =>
                            frames.retainedKeys right < frames.retainedKeys left) := by
                        apply ((orderCoherentOf_eq_true_iff _ _).mp hcoherent).imp
                        intro left right witness
                        obtain ⟨result, resultEq, ordering⟩ := witness
                        have callbackEq := congrFun (congrFun frames.callbackEq left) right
                        rw [callbackEq] at resultEq
                        simp only [compoundActualCompareAt, Option.some.injEq] at resultEq
                        have recordOrdering := congrArg
                          (fun result : ConstitutionalDescriptorHierarchyComparison =>
                            result.ordering) resultEq.symm
                        simp only [localizedOccurrenceRule45ComparisonRecord] at recordOrdering
                        have keyOrdering :
                            compare (frames.retainedKeys left) (frames.retainedKeys right) =
                              .gt := by
                          rw [← frames.retainedActual_fullOrdering singleBonded left right]
                          exact recordOrdering.symm.trans ordering
                        exact (completeLigandRule5Key_compare_gt_iff _ _).mp keyOrdering
                      have highest : sorted.highestFirst =
                          List.ofFn (priorityOrder frames strict singleBonded) :=
                        List.Perm.eq_of_pairwise
                          (fun _ _ _ _ lower upper => False.elim (lt_asymm lower upper))
                          pairwise (descendingOrder_pairwise frames.retainedKeys inj)
                          (perm.trans
                            (descendingOrder_perm_finRange frames.retainedKeys inj).symm)
                      have count := ContextDescriptorExecutionData.trackedCount_eq_complete
                        (frames.retainedExecutionData singleBonded) inj sorted hs
                      have spatial := mapM_some_of_forall
                        (fun slot => input.certified.localizedRerootCursorSpatialPoint?
                          (frames.frame.cursorAt slot)) points
                        (fun slot => (frames.actualCursor_coordinates slot).trans
                          (available slot)) sorted.highestFirst
                      refine ⟨rfl, highest, ?_, ?_⟩
                      · exact count.trans (completeRule5PairCount_eq_zero frames strict singleBonded)
                      · exact (Option.some.inj (hp.symm.trans spatial)).trans (by rw [highest])

/-! ## Physical configuration form -/

/-- Calibrated coordinates of the frame's detected ligands, read in frame-slot order. -/
theorem actualCoordinates_of_calibrated
    (pointAt : Fin 4 → CartesianPoint3)
    (observed : ∀ i, input.certified.spatialPointAt?
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center i) =
        some (pointAt i)) :
    ∀ slot, frames.actualCoordinates slot =
      some (pointAt (frames.detectedLigandPermutation slot)) :=
  fun slot => observed (frames.detectedLigandPermutation slot)

/-- The priority-ordered volume sign at a calibrated center is the configuration sign times the
parities of the frame's detected-ligand permutation and the contextual priority permutation. -/
theorem priorityVolume_sign_of_calibrated
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (pointAt : Fin 4 → CartesianPoint3)
    (signEq : rationalVolumeSign (enumerationVolume pointAt) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center) :
    rationalVolumeSign (reindexedVolume
        (fun slot => pointAt (frames.detectedLigandPermutation slot))
        (priorityOrder frames strict singleBonded)) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
        permHandedness frames.detectedLigandPermutation *
        permHandedness (priorityOrder frames strict singleBonded) := by
  have composed := calibratedVolumeSign_anyOrder pointAt
    (frames.detectedLigandPermutation * priorityOrder frames strict singleBonded) signEq
  rw [permHandedness_mul, ← mul_assoc] at composed
  exact composed

/-- **Physical form of the actual generated label.** At a physically calibrated general-rigid
center, the actual generated state at the strict frame is uppercase. It is `R` exactly when
`configurationSign cfg center * permHandedness α * permHandedness τ = -1`, where `α` is the
actual frame's detected-ligand permutation and `τ` the contextual priority permutation. The
nonzero volume is derived from the calibration. -/
theorem referenceState_eq_chiral_of_calibrated
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center) :
    referenceState input target = some (.chiral
      (if input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
          permHandedness frames.detectedLigandPermutation *
          permHandedness (priorityOrder frames strict singleBonded) = -1 then .R else .S)) := by
  obtain ⟨_rigid, pointAt, observed, _nonzero, signEq⟩ := calibrated
  let points : Fin 4 → CartesianPoint3 :=
    fun slot => pointAt (frames.detectedLigandPermutation slot)
  have sign := priorityVolume_sign_of_calibrated frames strict singleBonded cfg pointAt signEq
  have signUnit : input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
      permHandedness frames.detectedLigandPermutation *
      permHandedness (priorityOrder frames strict singleBonded) = 1 ∨
    input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
      permHandedness frames.detectedLigandPermutation *
      permHandedness (priorityOrder frames strict singleBonded) = -1 := by
    rw [← permHandedness_mul, ← permHandedness_mul]
    exact permHandedness_eq_one_or_eq_neg_one _
  have nonzero : reindexedVolume points (priorityOrder frames strict singleBonded) ≠ 0 := by
    intro zero
    have signZero := (rationalVolumeSign_eq_zero_iff _).mpr zero
    change rationalVolumeSign (reindexedVolume points
      (priorityOrder frames strict singleBonded)) = _ at sign
    rw [signZero] at sign
    rcases signUnit with one | negOne
    · rw [one] at sign
      norm_num at sign
    · rw [negOne] at sign
      norm_num at sign
  have labelled := referenceState_eq_chiral frames strict singleBonded points
    (actualCoordinates_of_calibrated frames pointAt observed) nonzero
  rw [labelled]
  change rationalVolumeSign (reindexedVolume points
    (priorityOrder frames strict singleBonded)) = _ at sign
  by_cases negative : reindexedVolume points (priorityOrder frames strict singleBonded) < 0
  · have signNeg := rationalVolumeSign_of_neg negative
    rw [if_pos negative, if_pos (sign.symm.trans signNeg)]
  · have positive : 0 < reindexedVolume points (priorityOrder frames strict singleBonded) :=
      lt_of_le_of_ne (not_lt.mp negative) (Ne.symm nonzero)
    have signPos := rationalVolumeSign_of_pos positive
    have notNeg : ¬ (input.certified.detectedMultiCenterMolecule.configurationSign cfg
        frames.center * permHandedness frames.detectedLigandPermutation *
        permHandedness (priorityOrder frames strict singleBonded) = -1) := by
      intro negOne
      rw [negOne] at sign
      rw [sign] at signPos
      norm_num at signPos
    rw [if_neg negative, if_neg notNeg]

end Frames

/-! ## Endpoint at a real detected occurrence -/

/-- **Endpoint at any real detected carrier occurrence.** For the chosen actual compilation of a
real detected occurrence of a simple-bonded input, constitutional strictness of its actual frame
gives the actual generated uppercase label. The label is given by the calibrated configuration
sign and the contextual priority permutation. -/
theorem referenceState_eq_chiral_of_real
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (strict : FrameConstitutionalStrict
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).frame)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    referenceState input target = some (.chiral
      (if input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
          permHandedness frames.detectedLigandPermutation *
          permHandedness (priorityOrder frames strict singleBonded) = -1 then .R else .S)) :=
  referenceState_eq_chiral_of_calibrated
    (cyclicContextFrameCompilation input singleBonded target real unit targetUnit)
    strict singleBonded cfg calibrated

/-! ## Endpoint at a general-rigid auxiliary target in a tied root arm -/

/-- **Actual generated label at a general-rigid auxiliary target in a tied root arm.** The input
is simple-bonded with constant formal charge; rings are allowed. Let a real nonroot detected
occurrence lie in an actual root arm whose Rule-1a table ties with another distinct real root
arm. Let its detected center be physically calibrated and general rigid. Then its actual frame is
constitutionally strict (`frameConstitutionalStrict_of_rootArmRule1aTie_of_physicalRigid`), with
no strictness premise. There is a reader-free contextual priority permutation `τ`. The actual
generated state is uppercase, and is `R` exactly when
`configurationSign cfg center * permHandedness α * permHandedness τ = -1`. -/
theorem referenceState_eq_chiral_of_tiedRootArm
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (rootCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input) → Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (nonroot : target.1.address ≠ [])
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    FrameConstitutionalStrict frames.frame ∧
      ∃ τ : Equiv.Perm (Fin 4),
        (∀ p q : Fin 4, p < q →
          ConstitutionallyAbove (frames.frame.cursorAt (τ p)) (frames.frame.cursorAt (τ q))) ∧
        referenceState input target = some (.chiral
          (if input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
              permHandedness frames.detectedLigandPermutation * permHandedness τ = -1 then .R
            else .S)) := by
  intro frames
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have strict : FrameConstitutionalStrict frames.frame :=
    frameConstitutionalStrict_of_rootArmRule1aTie_of_physicalRigid input.certified singleBonded
      charge rootCursor rootAddress armCursor armCursor' armMem armMem' armDistinct armReal
      armReal' armRead armRead' armKey armKey' armBuilt armBuilt' tie target real inside
      frames.frame (frame_computed frames) nonroot cfg frames.center centerMeaning.2 calibrated
  exact ⟨strict, priorityOrder frames strict singleBonded,
    fun _ _ lower => priorityOrder_above frames strict singleBonded lower,
    referenceState_eq_chiral_of_calibrated frames strict singleBonded cfg calibrated⟩

/-- **Domain form.** Let the physical root be the carrier's outer root atom. In the general-rigid
physical domain, the target's detected center is then a nonroot center
(`current_ne_root_of_nonroot`). If it is not a physical terminal twin it is calibrated and rigid,
and `referenceState_eq_chiral_of_tiedRootArm` applies with no further physical premise. -/
theorem referenceState_eq_chiral_of_tiedRootArm_of_domain
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (rootCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input) → Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (nonroot : target.1.address ≠ [])
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (rootEq : root.1 = target.1.root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    FrameConstitutionalStrict frames.frame ∧
      ∃ τ : Equiv.Perm (Fin 4),
        (∀ p q : Fin 4, p < q →
          ConstitutionallyAbove (frames.frame.cursorAt (τ p)) (frames.frame.cursorAt (τ q))) ∧
        referenceState input target = some (.chiral
          (if input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
              permHandedness frames.detectedLigandPermutation * permHandedness τ = -1 then .R
            else .S)) := by
  let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have centerNonroot : (frames.center : input.certified.detectedMultiCenterMolecule.Center) ≠
      root := by
    intro same
    apply current_ne_root_of_nonroot input.certified target real nonroot centerMeaning.2
    rw [← rootEq]
    exact congrArg Subtype.val same
  exact referenceState_eq_chiral_of_tiedRootArm input singleBonded charge rootCursor
    rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead'
    armKey armKey' armBuilt armBuilt' tie target real unit targetUnit inside nonroot cfg
    (physicalGeneralRigid_of_domain input.certified cfg root domain _ centerNonroot notTwin).1

end LocalizedCyclicGeneralRigidGeneratedLabels
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.compoundWith_rule4aKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.compound_rule4aKey_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.compound_constitutional_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.compound_cumulative_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.compound_throughRule5_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.compound_prior_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.retainedKeys_compare_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.retainedKeys_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.retainedPrior_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.completeRule5PairCount_eq_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder_retainedKeys_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder_compound_gt
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder_above
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_isChiral
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.ruleMajorDescriptorExec_eq_referenceState
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.spatialEvidence_eq_priorityOrder
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.actualCoordinates_of_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.priorityVolume_sign_of_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral_of_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral_of_real
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral_of_tiedRootArm
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral_of_tiedRootArm_of_domain
