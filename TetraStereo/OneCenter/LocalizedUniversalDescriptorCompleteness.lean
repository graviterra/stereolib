import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.OneCenter.LocalizedMutualObservableCompletion
import TetraStereo.OneCenter.LocalizedDescriptorObservableTransport

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput






































/-! ## Elementary list and `Option` helpers

These are local copies of private helpers in the soundness modules, restated with the exact shapes
needed for the completeness induction. -/

/-- If every element has an `f`-preimage, the whole `mapM` succeeds. -/
private theorem exists_mapM_of_total {α β : Type*} (f : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results : List β, values.mapM f = some results
  | [], _ => ⟨[], rfl⟩
  | value :: values, total => by
      obtain ⟨result, head⟩ := total value (by simp)
      obtain ⟨results, tail⟩ :=
        exists_mapM_of_total f values
          (fun value present => total value (by simp [present]))
      exact ⟨result :: results, by rw [List.mapM_cons, head, tail]; rfl⟩

/-- The length of a successful `mapM` result is the length of the input list. -/
private theorem mapM_length_eq {α β : Type*} (f : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM f = some results → results.length = values.length
  | [], results, computed => by
      simp at computed
      subst results
      rfl
  | value :: values, results, computed => by
      rw [List.mapM_cons] at computed
      cases head : f value with
      | none => simp [head] at computed
      | some result =>
          cases tail : values.mapM f with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst results
              simp [mapM_length_eq f values rest tail]

/-- The aligned `Fin 4` projections of a pointwise list relation. -/
private theorem forall₂_get_fin4 {α β : Type*} {relation : α → β → Prop}
    {values : List α} {results : List β}
    (related : List.Forall₂ relation values results)
    (valuesLength : values.length = 4) (resultsLength : results.length = 4)
    (index : Fin 4) :
    relation (values.get (Fin.cast valuesLength.symm index))
      (results.get (Fin.cast resultsLength.symm index)) := by
  have valuesBound : index.1 < values.length := by
    rw [valuesLength]
    exact index.2
  have resultsBound : index.1 < results.length := by
    rw [resultsLength]
    exact index.2
  have pointwise := List.Forall₂.get (i := index.1) related valuesBound resultsBound
  have valueCast : Fin.cast valuesLength.symm index = ⟨index.1, valuesBound⟩ :=
    Fin.ext rfl
  have resultCast : Fin.cast resultsLength.symm index = ⟨index.1, resultsBound⟩ :=
    Fin.ext rfl
  rw [valueCast, resultCast]
  exact pointwise

/-- Pointwise topology equivalence of Rule-3 keys gives equal observable projections. -/
private theorem map_observable_eq_of_forall₂_topology
    (input : CertifiedLocalizedCIPInput) :
    ∀ (left right : List input.LocalizedRerootRecursiveRule3SpatialKey),
      List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right →
        left.map (input.localizedRerootRule3SpatialKeyObservable) =
          right.map (input.localizedRerootRule3SpatialKeyObservable)
  | [], [], List.Forall₂.nil => rfl
  | _ :: _, _ :: _, List.Forall₂.cons head tail => by
      rw [List.map_cons, List.map_cons, head.1,
        map_observable_eq_of_forall₂_topology input _ _ tail]

/-- The executable Rules-4a--5 `mapM` is the query-form `mapM`; the two builders are pointwise
equal. -/
private theorem mapM_rule45_exec_eq_query
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    cursors.mapM (input.buildLocalizedRerootCompoundRule45KeyExec? target view fuel) =
      cursors.mapM (input.buildLocalizedRerootCompoundRule45Key? target view fuel) := by
  induction cursors with
  | nil => rfl
  | cons cursor rest ih =>
      rw [List.mapM_cons, List.mapM_cons, ih,
        input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]

/-- Successful `mapM` over independent Rules-4a--5 keys preserves the aligned declarative
meaning. -/
private theorem mapM_rule45_declarative (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCompoundRule45Key),
      cursors.mapM (input.buildLocalizedRerootCompoundRule45Key? target view fuel) =
        some keys →
      List.Forall₂
        (input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel) cursors keys
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
                (input.mapM_rule45_declarative target view fuel cursors tail tailComputed)

/-- Successful `mapM` over coordinate readings preserves the aligned declarative meaning. -/
private theorem mapM_spatialPoint_complete (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ (order : List (Fin 4)) (points : List CartesianPoint3),
      List.Forall₂
        (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
          (base.cursorAt index) point) order points →
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
        (base.cursorAt index)) = some points
  | [], [], List.Forall₂.nil => rfl
  | index :: order, point :: points, List.Forall₂.cons head tail => by
      rw [List.mapM_cons]
      have headComputed :=
        (input.localizedRerootCursorSpatialPoint?_eq_some_iff
          (base.cursorAt index) point).mpr head
      rw [headComputed, input.mapM_spatialPoint_complete base order points tail]
      rfl

/-! ## The two lower-layer interfaces -/









def LocalizedRerootCompoundRule45ComparisonAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) : Prop :=
  ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key),
    input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel cursor left →
      input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel cursor right →
        ∀ other : input.LocalizedRerootCompoundRule45Key,
          input.compareLocalizedRerootCompoundThroughRule5 left other =
              input.compareLocalizedRerootCompoundThroughRule5 right other ∧
            input.compareLocalizedRerootCompoundThroughRule5 other left =
              input.compareLocalizedRerootCompoundThroughRule5 other right

/-- Reduce a successful monadic bind written with the `Monad` bind projection.  The production
pipelines are written in `do` notation, so their binds elaborate through `Bind.bind` rather than
through the definitional abbreviation `Option.bind`; this equation lemma lets them reduce. -/
private theorem some_bind_eq.{u} {α β : Type u} (value : α) (next : α → Option β) :
    (Bind.bind (some value) next : Option β) = next value := rfl

/-! ## Transport of the cumulative comparator

`LocalizedDescriptorObservableTransport.compareLocalizedOccurrenceRule3Through5At_eq_of_keyObservables`
requires the aligned Rules-4a--5 key *lists* to be literally equal.  The completeness proof only
has a pairwise comparison-record agreement between independently built lists, so the comparator
transport is restated here with that weaker hypothesis. -/

/-- Metric-free comparison transport: equal Rule-3 observables pointwise and equal Rules-4a--5
comparison results pointwise give the identical cumulative comparison record at every ligand
pair. -/
private theorem compareLocalizedOccurrenceRule3Through5At_eq_of_recordAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable))
    (rule45Record_eq : ∀ left right : Fin 4,
      input.compareLocalizedRerootCompoundThroughRule5
          (first.keyAt left).rule45 (first.keyAt right).rule45 =
        input.compareLocalizedRerootCompoundThroughRule5
          (second.keyAt left).rule45 (second.keyAt right).rule45)
    (left right : Fin 4) :
    input.compareLocalizedOccurrenceRule3Through5At first left right =
      input.compareLocalizedOccurrenceRule3Through5At second left right := by
  have observableLeft :=
    input.localizedRerootRule3SpatialKeyObservable_get_eq_of_map_eq
      first.rule3Frame.keys second.rule3Frame.keys
      first.rule3Length second.rule3Length rule3Observable_eq left
  have observableRight :=
    input.localizedRerootRule3SpatialKeyObservable_get_eq_of_map_eq
      first.rule3Frame.keys second.rule3Frame.keys
      first.rule3Length second.rule3Length rule3Observable_eq right
  have rule3Compare :
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
          (first.keyAt left).rule3 (first.keyAt right).rule3 =
        input.compareLocalizedRerootRecursiveRule3SpatialKeys
          (second.keyAt left).rule3 (second.keyAt right).rule3 := by
    rw [input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable,
      input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable]
    rw [show input.localizedRerootRule3SpatialKeyObservable (first.keyAt left).rule3 =
          input.localizedRerootRule3SpatialKeyObservable (second.keyAt left).rule3
        from observableLeft,
      show input.localizedRerootRule3SpatialKeyObservable (first.keyAt right).rule3 =
          input.localizedRerootRule3SpatialKeyObservable (second.keyAt right).rule3
        from observableRight]
  unfold compareLocalizedOccurrenceRule3Through5At
  dsimp only
  rw [rule3Compare]
  cases decisive : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (second.keyAt left).rule3 (second.keyAt right).rule3 <;>
    simp [rule45Record_eq left right]

/-- Pointwise-equal cumulative comparison records give equal executable safe tracked orders. -/
private theorem safeTrackedOrder_eq_of_comparisons
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (comparisons : ∀ left right : Fin 4,
      input.compareLocalizedOccurrenceRule3Through5At first left right =
        input.compareLocalizedOccurrenceRule3Through5At second left right) :
    input.safeLocalizedOccurrenceRule3Through5TrackedOrder? first =
      input.safeLocalizedOccurrenceRule3Through5TrackedOrder? second := by
  have compareFunctions : input.compareLocalizedOccurrenceRule3Through5At? first =
      input.compareLocalizedOccurrenceRule3Through5At? second := by
    funext left right
    simp only [compareLocalizedOccurrenceRule3Through5At?]
    rw [comparisons left right]
  unfold safeLocalizedOccurrenceRule3Through5TrackedOrder?
    localizedOccurrenceRule3Through5TrackedOrder?
  rw [compareFunctions]
  cases sorted : sortFourLocalizedLigandsTracked
      (input.compareLocalizedOccurrenceRule3Through5At? second) with
  | none => rfl
  | some tracked =>
      change (if input.localizedOccurrenceRule3Through5OrderCoherent first
            tracked.highestFirst then some tracked else none) =
        (if input.localizedOccurrenceRule3Through5OrderCoherent second
            tracked.highestFirst then some tracked else none)
      rw [input.localizedOccurrenceRule3Through5OrderCoherent_eq_of_comparisons
        first second comparisons tracked.highestFirst]

/-! ## Main converse -/

/-- **Completeness of the universal descriptor at every budget.**

If an independent universal descriptor meaning holds at an arbitrary Rule-3 evaluation budget,
then the universal descriptor computed by `universalDescriptor?` is that descriptor.  The only
assumptions are the Rule-3 node-completion interface and the pairwise Rules-4a--5 comparison
agreement interface.  The compiled Rule-3 frame may differ from the derived one, and the compiled
Rules-4a--5 key list is built independently from the same four-ligand cursors; the comparison
record agreement transports the tracked order, and the coordinates are read from the same
four-ligand base, so the classified descriptor is identical. -/
theorem universalDescriptor?_eq_some_of_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (nodeComplete : LocalizedRule3ExtendedShortCircuitNodeComplete input target view)
    (rule45Agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (derived : input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor) :
    input.universalDescriptor? target view = some descriptor := by
  obtain ⟨evidence, raw, evidenceMeaning, rawMeaning, descriptorEq⟩ := derived
  obtain ⟨centerMeaning, baseMeaning, keysMeaning, trackedMeaning, pointsMeaning⟩ :=
    evidenceMeaning
  obtain ⟨frameMeaning, rule3Length, rule45Related, rule45Length⟩ := keysMeaning
  -- The center and base readers succeed on the declared evidence.
  have centerComputed : input.localizedOccurrenceDescriptorCenter? target =
      some evidence.center :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target evidence.center).mpr
      centerMeaning
  have baseOccurrenceComputed : input.localizedOccurrenceFourLigandFrame? target =
      some evidence.base :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target evidence.base).mpr baseMeaning
  have baseComputed : input.localizedNoDoubleFourLigandFrameExec? target =
      some evidence.base := by
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact baseOccurrenceComputed
  -- The lower Rule-3 node interface compiles a topology-equivalent frame at the same budget.
  obtain ⟨compiledFrame, compiledFrameComputed, frameEquiv⟩ :=
    input.buildLocalizedExtendedShortCircuitRule3FrameExec?_complete target view nodeComplete
      evaluationBudget evidence.base.cursors evidence.keys.rule3Frame frameMeaning
  -- Every declared ligand cursor is path-valid, so the compound Rule-45 builder is total.
  have valid : ∀ cursor ∈ evidence.base.cursors, input.LocalizedRerootCursorValid cursor := by
    intro cursor present
    exact input.localizedRerootChild_valid
      { occurrence := target, previous? := none } cursor evidence.base.cursors baseMeaning.1
      present
  have total : ∀ cursor ∈ evidence.base.cursors,
      ∃ key, input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor = some key := by
    intro cursor present
    exact input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice target view cursor
      (valid cursor present)
  obtain ⟨compiledRule45, compiledRule45Computed⟩ :=
    exists_mapM_of_total
      (input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      evidence.base.cursors total
  have compiledRule45Length : compiledRule45.length = 4 := by
    rw [mapM_length_eq
      (input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      evidence.base.cursors compiledRule45 compiledRule45Computed]
    exact evidence.base.length_eq
  have compiledRule45Decl : List.Forall₂
      (input.DeclarativeLocalizedRerootCompoundRule45Key target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      evidence.base.cursors compiledRule45 :=
    input.mapM_rule45_declarative target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) evidence.base.cursors
      compiledRule45 compiledRule45Computed
  have compiledRule45ComputedExec : evidence.base.cursors.mapM
        (input.buildLocalizedRerootCompoundRule45KeyExec? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)) = some compiledRule45 := by
    rw [mapM_rule45_exec_eq_query input target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) evidence.base.cursors]
    exact compiledRule45Computed
  -- The compiled frame has four keys; the independently built key list has four entries.
  have compiledRule3Length : compiledFrame.keys.length = 4 := by
    rw [← List.Forall₂.length_eq frameEquiv.2.1]
    exact rule3Length
  let compiledKeys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel :=
    { rule3Frame := compiledFrame
      rule3Length := compiledRule3Length
      rule45Keys := compiledRule45
      rule45Length := compiledRule45Length }
  have finishComputed : input.finishKeyFrame? target view evidence.base compiledFrame =
      some compiledKeys := by
    unfold finishKeyFrame?
    rw [dif_pos compiledRule3Length]
    rw [compiledRule45ComputedExec]
    change (if h : compiledRule45.length = 4 then
        some { rule3Frame := compiledFrame
               rule3Length := compiledRule3Length
               rule45Keys := compiledRule45
               rule45Length := h } else none) = some compiledKeys
    rw [dif_pos compiledRule45Length]
  -- The derived frame observable projection equals the compiled one.
  have rule3ObservableEq : evidence.keys.rule3Frame.keys.map
        (input.localizedRerootRule3SpatialKeyObservable) =
      compiledFrame.keys.map (input.localizedRerootRule3SpatialKeyObservable) :=
    map_observable_eq_of_forall₂_topology input _ _ frameEquiv.2.1
  -- Aligned declarative meanings for both independently built Rules-4a--5 key lists.
  have derivedDecl : ∀ index : Fin 4,
      input.DeclarativeLocalizedRerootCompoundRule45Key target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (evidence.base.cursorAt index)
        (evidence.keys.keyAt index).rule45 := by
    intro index
    simpa [LocalizedOccurrenceFourLigandFrame.cursorAt,
      LocalizedOccurrenceRule3Through5KeyFrame.keyAt]
      using forall₂_get_fin4 rule45Related evidence.base.length_eq rule45Length index
  have compiledDecl : ∀ index : Fin 4,
      input.DeclarativeLocalizedRerootCompoundRule45Key target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (evidence.base.cursorAt index)
        (compiledKeys.keyAt index).rule45 := by
    intro index
    simpa [LocalizedOccurrenceFourLigandFrame.cursorAt,
      LocalizedOccurrenceRule3Through5KeyFrame.keyAt]
      using forall₂_get_fin4 compiledRule45Decl evidence.base.length_eq
        compiledRule45Length index
  -- The lower Rules-4a--5 interface gives pairwise comparison-record agreement.
  have rule45RecordEq : ∀ left right : Fin 4,
      input.compareLocalizedRerootCompoundThroughRule5
          (compiledKeys.keyAt left).rule45 (compiledKeys.keyAt right).rule45 =
        input.compareLocalizedRerootCompoundThroughRule5
          (evidence.keys.keyAt left).rule45 (evidence.keys.keyAt right).rule45 := by
    intro left right
    calc
      input.compareLocalizedRerootCompoundThroughRule5
          (compiledKeys.keyAt left).rule45 (compiledKeys.keyAt right).rule45
          = input.compareLocalizedRerootCompoundThroughRule5
              (evidence.keys.keyAt left).rule45
              (compiledKeys.keyAt right).rule45 :=
            (rule45Agreement (evidence.base.cursorAt left)
              (compiledKeys.keyAt left).rule45 (evidence.keys.keyAt left).rule45
              (compiledDecl left) (derivedDecl left)
              (compiledKeys.keyAt right).rule45).1
      _ = input.compareLocalizedRerootCompoundThroughRule5
              (evidence.keys.keyAt left).rule45
              (evidence.keys.keyAt right).rule45 :=
            (rule45Agreement (evidence.base.cursorAt right)
              (compiledKeys.keyAt right).rule45 (evidence.keys.keyAt right).rule45
              (compiledDecl right) (derivedDecl right)
              (evidence.keys.keyAt left).rule45).2
  have comparisons : ∀ left right : Fin 4,
      input.compareLocalizedOccurrenceRule3Through5At compiledKeys left right =
        input.compareLocalizedOccurrenceRule3Through5At evidence.keys left right :=
    compareLocalizedOccurrenceRule3Through5At_eq_of_recordAgreement
      input compiledKeys evidence.keys rule3ObservableEq.symm rule45RecordEq
  -- The safe tracked order, hence the pseudo-comparison count, is identical.
  have trackedEq : input.safeLocalizedOccurrenceRule3Through5TrackedOrder? compiledKeys =
      input.safeLocalizedOccurrenceRule3Through5TrackedOrder? evidence.keys :=
    safeTrackedOrder_eq_of_comparisons input compiledKeys evidence.keys comparisons
  have derivedTrackedComputed :
      input.safeLocalizedOccurrenceRule3Through5TrackedOrder? evidence.keys =
        some evidence.tracked :=
    input.safeLocalizedOccurrenceRule3Through5TrackedOrder?_complete evidence.keys
      evidence.tracked trackedMeaning
  have compiledTrackedComputed :
      input.safeLocalizedOccurrenceRule3Through5TrackedOrder? compiledKeys =
        some evidence.tracked := by
    rw [trackedEq, derivedTrackedComputed]
  -- The coordinate readings are taken from the same four-ligand base and the same order.
  have pointsComputed : evidence.tracked.highestFirst.mapM
        (fun index => input.localizedRerootCursorSpatialPoint?
          (evidence.base.cursorAt index)) = some evidence.points :=
    input.mapM_spatialPoint_complete evidence.base evidence.tracked.highestFirst
      evidence.points pointsMeaning
  have spatialComputed :
      input.spatialEvidenceFromKeys? target view evidence.center evidence.base compiledKeys =
        some { center := evidence.center
               base := evidence.base
               keys := compiledKeys
               tracked := evidence.tracked
               points := evidence.points } := by
    unfold spatialEvidenceFromKeys?
    rw [localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?]
    rw [compiledTrackedComputed]
    rw [some_bind_eq]
    rw [pointsComputed]
    rw [some_bind_eq]
  have rawComputed : descriptorOfPriorityOrderedPoints? evidence.points = some raw :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff evidence.points raw).mpr rawMeaning
  have descriptorComputed : input.descriptorFromKeys? target view evidence.center
      evidence.base compiledKeys = some descriptor := by
    unfold descriptorFromKeys?
    rw [spatialComputed]
    rw [some_bind_eq]
    dsimp only
    rw [rawComputed]
    rw [some_bind_eq]
    rw [descriptorEq]
  -- Assemble the parameterized descriptor success at the given budget.
  have finishBind : (input.finishKeyFrame? target view evidence.base compiledFrame).bind
      (fun keys => input.descriptorFromKeys? target view evidence.center evidence.base keys) =
        some descriptor := by
    rw [finishComputed]
    exact descriptorComputed
  have atComputed : input.descriptorAt? target view evaluationBudget = some descriptor := by
    rw [input.descriptorAt?_eq_descriptorFromFrame?_of_some target view evidence.center
      evidence.base evaluationBudget centerComputed baseComputed]
    rw [compiledFrameComputed, input.descriptorFromFrame?_some]
    exact finishBind
  exact input.universalDescriptor?_eq_some_of_descriptorAt?_eq_some_of_agreement
    target view (input.universalFrameAgreement target view) descriptor evaluationBudget atComputed

/-! ## The exact-label iff and refusal forms -/

/-- **Exact-label completeness.**  For a fixed label, the universal descriptor returns that label
exactly when some Rule-3 evaluation budget carries the independent declarative meaning of that
label.  The forward direction is the unconditional positive soundness of `universalDescriptor?`;
the backward direction is the main converse above. -/
theorem universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (nodeComplete : LocalizedRule3ExtendedShortCircuitNodeComplete input target view)
    (rule45Agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (descriptor : LocalizedAuxiliaryLabel) :
    input.universalDescriptor? target view = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          evaluationBudget descriptor := by
  constructor
  · intro computed
    obtain ⟨_base, _baseComputed, meaning⟩ :=
      input.universalDescriptor?_sound target view descriptor computed
    exact ⟨_, meaning⟩
  · rintro ⟨evaluationBudget, meaning⟩
    exact input.universalDescriptor?_eq_some_of_declarativeUniversalDescriptor
      target view nodeComplete rule45Agreement evaluationBudget descriptor meaning

/-- **Operational completeness.**  The universal descriptor succeeds exactly when some Rule-3
evaluation budget carries an independent declarative descriptor meaning.  The forward direction is
the unconditional positive soundness of `universalDescriptor?`; the backward direction is the
main converse above. -/
theorem universalDescriptor?_isSome_iff_exists_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (nodeComplete : LocalizedRule3ExtendedShortCircuitNodeComplete input target view)
    (rule45Agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) :
    (input.universalDescriptor? target view).isSome = true ↔
      ∃ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          evaluationBudget descriptor := by
  constructor
  · intro success
    obtain ⟨descriptor, computed⟩ := Option.isSome_iff_exists.mp success
    obtain ⟨base, _baseComputed, meaning⟩ :=
      input.universalDescriptor?_sound target view descriptor computed
    exact ⟨(prepareUniversalRule3EvaluationOutcome input base.cursors target view).1,
      descriptor, meaning⟩
  · rintro ⟨evaluationBudget, descriptor, meaning⟩
    have universal := input.universalDescriptor?_eq_some_of_declarativeUniversalDescriptor
      target view nodeComplete rule45Agreement evaluationBudget descriptor meaning
    simp [universal]

/-- **Refusal is the absence of every independent meaning.**  Conditional only on the same two
lower interfaces, the universal descriptor refuses exactly when no budget and no descriptor have
the declarative meaning. -/
theorem universalDescriptor?_eq_none_iff_forall_not_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (nodeComplete : LocalizedRule3ExtendedShortCircuitNodeComplete input target view)
    (rule45Agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) :
    input.universalDescriptor? target view = none ↔
      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        ¬ input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          evaluationBudget descriptor := by
  constructor
  · intro refused evaluationBudget descriptor meaning
    have universal := input.universalDescriptor?_eq_some_of_declarativeUniversalDescriptor
      target view nodeComplete rule45Agreement evaluationBudget descriptor meaning
    rw [refused] at universal
    cases universal
  · intro noMeaning
    cases universal : input.universalDescriptor? target view with
    | none => rfl
    | some descriptor =>
        obtain ⟨_base, _baseComputed, meaning⟩ :=
          input.universalDescriptor?_sound target view descriptor universal
        exact False.elim (noMeaning _ descriptor meaning)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
