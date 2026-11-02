import TetraStereo.OneCenter.LocalizedExtendedShortCircuitDescriptor

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! # Exact executable refusal-reason classification for the extended descriptor pipeline

`localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?` is a fail-closed
pipeline.  This module decomposes every `none` outcome into the first failing stage,
proves the decomposition exact and exhaustive relative to the production `Option`, and
records that the reasons are operational.  A refusal is not by itself a claim that the
occurrence is not a tetrahedral stereocentre.

The two length guards inside
`buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?` are vacuous: a
successful `mapM` preserves the four-cursor base-frame length.  Consequently a key-frame
failure is exactly a Rule-3 frame failure or a Rule-4b/4c/5 key failure. -/

/-- Operational reason why the extended descriptor pipeline returns `none`. -/
inductive LocalizedExtendedDescriptorRefusalReason where
  | noTetraCenter
  | noFourLigandFrame
  | rule3FrameFailure
  | rule45FrameFailure
  | nonStrictOrder
  | missingSpatialPoints
  | degenerateGeometry
  deriving DecidableEq, Repr

/-! ## Stage accessors

Each accessor is the literal production sub-computation, exposed so that a classifier can
name the first stage that fails without duplicating the pipeline. -/

/-- First stage: existence of an executable tetrahedral centre. -/
def localizedExtendedDescriptorCenter?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    Option input.TetrahedralCenter :=
  input.localizedOccurrenceDescriptorCenter? target

/-- Second stage: the exact four-ligand reroot frame. -/
def localizedExtendedDescriptorBaseFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedOccurrenceFourLigandFrame carrierFuel) :=
  input.localizedNoDoubleFourLigandFrameExec? target

/-- Third stage: cumulative Rules-1a--5 key frame with descriptor-bearing Rule 3. -/
def localizedExtendedDescriptorKeyFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :=
  input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? target view base

/-- Fourth stage: strict tracked ligand order. -/
def localizedExtendedDescriptorTrackedOrder?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder :=
  input.localizedNoDoubleTrackedOrderExec? keys

/-- Fifth stage: exact spatial points in tracked priority order. -/
def localizedExtendedDescriptorSpatialPoints?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder) :
    Option (List CartesianPoint3) :=
  tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)

/-- Sixth stage: exact oriented-volume descriptor from four priority-ordered points. -/
def localizedExtendedDescriptorRawGeometry?
    (points : List CartesianPoint3) : Option RS :=
  descriptorOfPriorityOrderedPoints? points

/-- The Rule-3 frame sub-stage of the key-frame builder. -/
def localizedExtendedDescriptorRule3Stage?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) base.cursors

/-- The compound Rules-4b/4c/5 sub-stage of the key-frame builder. -/
def localizedExtendedDescriptorRule45Stage?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (List input.LocalizedRerootCompoundRule45Key) :=
  base.cursors.mapM (input.buildLocalizedRerootCompoundRule45KeyExec? target view
    (localizedOccurrenceRerootEvaluationFuel carrierFuel))

/-! ## Length facts

A successful `mapM` preserves length, and the descriptor-bearing Rule-3 frame has keys in
bijection with its cursor list (through the established declarative soundness theorem).
Hence both length guards in the production key-frame builder always fire on a successful
sub-stage.  The fuel-zero Rule-3 branch is impossible because the production Rule-3 fuel is
strictly positive. -/

private theorem mapM_length_eq_of_eq_some_localized
    {α β : Type*} (f : α → Option β) :
    ∀ (inputs : List α) (outputs : List β),
      inputs.mapM f = some outputs → outputs.length = inputs.length
  | [], outputs, computed => by
      simp at computed
      subst outputs
      rfl
  | input :: inputs, outputs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : inputs.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              simp [mapM_length_eq_of_eq_some_localized f inputs tail tailComputed]

/-- Every successful two-pass Rule-3 frame has exactly as many rebuilt keys as cursors. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_keys_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view fuel cursors = some frame) :
    frame.keys.length = cursors.length := by
  cases fuel with
  | zero => simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at computed
  | succ fuel =>
      have sound := input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound
        target view (fuel + 1) cursors frame computed
      simp only [DeclarativeLocalizedExtendedShortCircuitRule3Frame] at sound
      obtain ⟨topology, _, _, keysForall⟩ := sound.2
      exact keysForall.length_eq.symm

/-- The production Rule-3 frame stage always returns four keys. -/
theorem localizedExtendedDescriptorRule3Stage?_keys_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : localizedExtendedDescriptorRule3Stage? input target view base = some frame) :
    frame.keys.length = 4 := by
  have raw := buildLocalizedExtendedShortCircuitRule3FrameExec?_keys_length
    input target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
    base.cursors frame (by simpa only [localizedExtendedDescriptorRule3Stage?] using computed)
  rw [raw, base.length_eq]

/-- The production compound Rule-4b/4c/5 stage always returns four keys. -/
theorem localizedExtendedDescriptorRule45Stage?_keys_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : List input.LocalizedRerootCompoundRule45Key)
    (computed : localizedExtendedDescriptorRule45Stage? input target view base = some keys) :
    keys.length = 4 := by
  have raw := mapM_length_eq_of_eq_some_localized
    (input.buildLocalizedRerootCompoundRule45KeyExec? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    base.cursors keys (by simpa only [localizedExtendedDescriptorRule45Stage?] using computed)
  rw [raw, base.length_eq]

/-- The production Rule-3 evaluation fuel is always positive. -/
theorem localizedDescriptorBearingRule3EvaluationFuel_pos (carrierFuel : Nat) :
    0 < localizedDescriptorBearingRule3EvaluationFuel carrierFuel := by
  unfold localizedDescriptorBearingRule3EvaluationFuel
  exact Nat.mul_pos (by omega) (by omega)

/-- A key-frame failure is exactly a Rule-3 stage failure or a Rule-4b/4c/5 stage failure.
The two length guards in the production builder cannot introduce a further failure. -/
theorem buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
        target view base = none ↔
      localizedExtendedDescriptorRule3Stage? input target view base = none ∨
        localizedExtendedDescriptorRule45Stage? input target view base = none := by
  unfold buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
    localizedExtendedDescriptorRule3Stage? localizedExtendedDescriptorRule45Stage?
  cases rule3 : input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) base.cursors with
  | none => simp [rule3]
  | some rule3Frame =>
      have length3 : rule3Frame.keys.length = 4 := by
        rw [input.buildLocalizedExtendedShortCircuitRule3FrameExec?_keys_length
          target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
          base.cursors rule3Frame rule3, base.length_eq]
      cases rule45 : base.cursors.mapM
          (input.buildLocalizedRerootCompoundRule45KeyExec? target view
            (localizedOccurrenceRerootEvaluationFuel carrierFuel)) with
      | none => simp [rule3, rule45]
      | some rule45Keys =>
          have length45 : rule45Keys.length = 4 := by
            rw [mapM_length_eq_of_eq_some_localized
              (input.buildLocalizedRerootCompoundRule45KeyExec? target view
                (localizedOccurrenceRerootEvaluationFuel carrierFuel))
              base.cursors rule45Keys rule45, base.length_eq]
          simp [rule3, rule45, length3, length45]

/-! ## Match predicates for the first failing stage -/

/-- The centre stage failed. -/
def ExtendedDescriptorNoTetraCenter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (_view : input.LocalizedDependencyView target) : Prop :=
  localizedExtendedDescriptorCenter? input target = none

/-- The centre succeeded but no exact four-ligand frame exists. -/
def ExtendedDescriptorNoFourLigandFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (_view : input.LocalizedDependencyView target) : Prop :=
  localizedExtendedDescriptorCenter? input target ≠ none ∧
    localizedExtendedDescriptorBaseFrame? input target = none

/-- The frame exists but the descriptor-bearing Rule-3 stage failed. -/
def ExtendedDescriptorRule3Refusal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  localizedExtendedDescriptorCenter? input target ≠ none ∧
    match localizedExtendedDescriptorBaseFrame? input target with
    | none => False
    | some base =>
        localizedExtendedDescriptorKeyFrame? input target view base = none ∧
          localizedExtendedDescriptorRule3Stage? input target view base = none

/-- The Rule-3 stage succeeded but the compound Rules-4b/4c/5 stage failed. -/
def ExtendedDescriptorRule45Refusal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  localizedExtendedDescriptorCenter? input target ≠ none ∧
    match localizedExtendedDescriptorBaseFrame? input target with
    | none => False
    | some base =>
        localizedExtendedDescriptorKeyFrame? input target view base = none ∧
          localizedExtendedDescriptorRule3Stage? input target view base ≠ none ∧
          localizedExtendedDescriptorRule45Stage? input target view base = none

/-- Every key succeeded, but the tracked order is not strict. -/
def ExtendedDescriptorNonStrictOrderRefusal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  localizedExtendedDescriptorCenter? input target ≠ none ∧
    match localizedExtendedDescriptorBaseFrame? input target with
    | none => False
    | some base =>
        match localizedExtendedDescriptorKeyFrame? input target view base with
        | none => False
        | some keys => localizedExtendedDescriptorTrackedOrder? input keys = none

/-- The order is strict, but at least one tracked cursor has no exact spatial point. -/
def ExtendedDescriptorMissingSpatialPointsRefusal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  localizedExtendedDescriptorCenter? input target ≠ none ∧
    match localizedExtendedDescriptorBaseFrame? input target with
    | none => False
    | some base =>
        match localizedExtendedDescriptorKeyFrame? input target view base with
        | none => False
        | some keys =>
            match localizedExtendedDescriptorTrackedOrder? input keys with
            | none => False
            | some tracked =>
                localizedExtendedDescriptorSpatialPoints? input base tracked = none

/-- All evidence exists, but the four ordered points are geometrically degenerate. -/
def ExtendedDescriptorDegenerateGeometryRefusal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  localizedExtendedDescriptorCenter? input target ≠ none ∧
    match localizedExtendedDescriptorBaseFrame? input target with
    | none => False
    | some base =>
        match localizedExtendedDescriptorKeyFrame? input target view base with
        | none => False
        | some keys =>
            match localizedExtendedDescriptorTrackedOrder? input keys with
            | none => False
            | some tracked =>
                match localizedExtendedDescriptorSpatialPoints? input base tracked with
                | none => False
                | some points => localizedExtendedDescriptorRawGeometry? points = none

/-- Every pipeline stage succeeded, so the production descriptor emits a label. -/
def ExtendedDescriptorStagesSucceed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  localizedExtendedDescriptorCenter? input target ≠ none ∧
    match localizedExtendedDescriptorBaseFrame? input target with
    | none => False
    | some base =>
        match localizedExtendedDescriptorKeyFrame? input target view base with
        | none => False
        | some keys =>
            match localizedExtendedDescriptorTrackedOrder? input keys with
            | none => False
            | some tracked =>
                match localizedExtendedDescriptorSpatialPoints? input base tracked with
                | none => False
                | some points =>
                    match localizedExtendedDescriptorRawGeometry? points with
                    | none => False
                    | some _ => True

/-! ## The executable classifier -/

/-- Classify the first failing stage of the extended descriptor pipeline.  Returns `none`
exactly when the production descriptor emits a label. -/
def localizedExtendedDescriptorRefusalReason?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedExtendedDescriptorRefusalReason :=
  match localizedExtendedDescriptorCenter? input target with
  | none => some .noTetraCenter
  | some _ =>
      match localizedExtendedDescriptorBaseFrame? input target with
      | none => some .noFourLigandFrame
      | some base =>
          match localizedExtendedDescriptorKeyFrame? input target view base with
          | none =>
              match localizedExtendedDescriptorRule3Stage? input target view base with
              | none => some .rule3FrameFailure
              | some _ => some .rule45FrameFailure
          | some keys =>
              match localizedExtendedDescriptorTrackedOrder? input keys with
              | none => some .nonStrictOrder
              | some tracked =>
                  match localizedExtendedDescriptorSpatialPoints? input base tracked with
                  | none => some .missingSpatialPoints
                  | some points =>
                      match localizedExtendedDescriptorRawGeometry? points with
                      | none => some .degenerateGeometry
                      | some _ => none

/-! ## Exactness of the classifier -/

/-- Every reason is equivalent to its exact first-failing-stage predicate, and classifier
`none` is equivalent to success of every stage. -/
theorem localizedExtendedDescriptorRefusalReason?_exact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (localizedExtendedDescriptorRefusalReason? input target view = some .noTetraCenter ↔
        ExtendedDescriptorNoTetraCenter input target view) ∧
      ((localizedExtendedDescriptorRefusalReason? input target view = some .noFourLigandFrame ↔
          ExtendedDescriptorNoFourLigandFrame input target view) ∧
        ((localizedExtendedDescriptorRefusalReason? input target view = some .rule3FrameFailure ↔
            ExtendedDescriptorRule3Refusal input target view) ∧
          ((localizedExtendedDescriptorRefusalReason? input target view = some .rule45FrameFailure ↔
              ExtendedDescriptorRule45Refusal input target view) ∧
            ((localizedExtendedDescriptorRefusalReason? input target view = some .nonStrictOrder ↔
                ExtendedDescriptorNonStrictOrderRefusal input target view) ∧
              ((localizedExtendedDescriptorRefusalReason? input target view = some .missingSpatialPoints ↔
                  ExtendedDescriptorMissingSpatialPointsRefusal input target view) ∧
                ((localizedExtendedDescriptorRefusalReason? input target view = some .degenerateGeometry ↔
                    ExtendedDescriptorDegenerateGeometryRefusal input target view) ∧
                  (localizedExtendedDescriptorRefusalReason? input target view = none ↔
                    ExtendedDescriptorStagesSucceed input target view))))))) := by
  unfold localizedExtendedDescriptorRefusalReason?
    ExtendedDescriptorNoTetraCenter ExtendedDescriptorNoFourLigandFrame
    ExtendedDescriptorRule3Refusal ExtendedDescriptorRule45Refusal
    ExtendedDescriptorNonStrictOrderRefusal
    ExtendedDescriptorMissingSpatialPointsRefusal
    ExtendedDescriptorDegenerateGeometryRefusal ExtendedDescriptorStagesSucceed
  cases centerEq : localizedExtendedDescriptorCenter? input target with
  | none => simp [centerEq]
  | some center =>
      cases baseEq : localizedExtendedDescriptorBaseFrame? input target with
      | none => simp [centerEq, baseEq]
      | some base =>
          cases keysEq : localizedExtendedDescriptorKeyFrame? input target view base with
          | none =>
              have split := (buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_eq_none_iff
                input target view base).mp (by
                  simpa only [localizedExtendedDescriptorKeyFrame?] using keysEq)
              cases rule3Eq : localizedExtendedDescriptorRule3Stage? input target view base with
              | none => simp [centerEq, baseEq, keysEq, rule3Eq]
              | some rule3Frame =>
                  have rule45 : localizedExtendedDescriptorRule45Stage? input target view base = none := by
                    rcases split with h | h
                    · rw [h] at rule3Eq
                      cases rule3Eq
                    · exact h
                  simp [centerEq, baseEq, keysEq, rule3Eq, rule45]
          | some keys =>
              cases trackedEq : localizedExtendedDescriptorTrackedOrder? input keys with
              | none => simp [centerEq, baseEq, keysEq, trackedEq]
              | some tracked =>
                  cases pointsEq : localizedExtendedDescriptorSpatialPoints? input base tracked with
                  | none => simp [centerEq, baseEq, keysEq, trackedEq, pointsEq]
                  | some points =>
                      cases geometryEq : localizedExtendedDescriptorRawGeometry? points with
                      | none => simp [centerEq, baseEq, keysEq, trackedEq, pointsEq, geometryEq]
                      | some raw => simp [centerEq, baseEq, keysEq, trackedEq, pointsEq, geometryEq]

/-- The classifier names exactly the no-tetra-centre refusal. -/
theorem localizedExtendedDescriptorRefusalReason?_noTetraCenter_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedExtendedDescriptorRefusalReason? input target view = some .noTetraCenter ↔
      ExtendedDescriptorNoTetraCenter input target view :=
  (localizedExtendedDescriptorRefusalReason?_exact input target view).1

/-- The classifier names exactly the no-four-ligand-frame refusal. -/
theorem localizedExtendedDescriptorRefusalReason?_noFourLigandFrame_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedExtendedDescriptorRefusalReason? input target view = some .noFourLigandFrame ↔
      ExtendedDescriptorNoFourLigandFrame input target view :=
  (localizedExtendedDescriptorRefusalReason?_exact input target view).2.1

/-- The classifier names exactly the Rule-3 frame refusal. -/
theorem localizedExtendedDescriptorRefusalReason?_rule3FrameFailure_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedExtendedDescriptorRefusalReason? input target view = some .rule3FrameFailure ↔
      ExtendedDescriptorRule3Refusal input target view :=
  (localizedExtendedDescriptorRefusalReason?_exact input target view).2.2.1

/-- The classifier names exactly the compound Rule-4b/4c/5 refusal. -/
theorem localizedExtendedDescriptorRefusalReason?_rule45FrameFailure_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedExtendedDescriptorRefusalReason? input target view = some .rule45FrameFailure ↔
      ExtendedDescriptorRule45Refusal input target view :=
  (localizedExtendedDescriptorRefusalReason?_exact input target view).2.2.2.1

/-- The classifier names exactly the non-strict-order refusal. -/
theorem localizedExtendedDescriptorRefusalReason?_nonStrictOrder_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedExtendedDescriptorRefusalReason? input target view = some .nonStrictOrder ↔
      ExtendedDescriptorNonStrictOrderRefusal input target view :=
  (localizedExtendedDescriptorRefusalReason?_exact input target view).2.2.2.2.1

/-- The classifier names exactly the missing-spatial-points refusal. -/
theorem localizedExtendedDescriptorRefusalReason?_missingSpatialPoints_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedExtendedDescriptorRefusalReason? input target view = some .missingSpatialPoints ↔
      ExtendedDescriptorMissingSpatialPointsRefusal input target view :=
  (localizedExtendedDescriptorRefusalReason?_exact input target view).2.2.2.2.2.1

/-- The classifier names exactly the degenerate-geometry refusal. -/
theorem localizedExtendedDescriptorRefusalReason?_degenerateGeometry_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedExtendedDescriptorRefusalReason? input target view = some .degenerateGeometry ↔
      ExtendedDescriptorDegenerateGeometryRefusal input target view :=
  (localizedExtendedDescriptorRefusalReason?_exact input target view).2.2.2.2.2.2.1

/-- The classifier returns `none` exactly when every pipeline stage succeeds. -/
theorem localizedExtendedDescriptorRefusalReason?_eq_none_iff_stagesSucceed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedExtendedDescriptorRefusalReason? input target view = none ↔
      ExtendedDescriptorStagesSucceed input target view :=
  (localizedExtendedDescriptorRefusalReason?_exact input target view).2.2.2.2.2.2.2

/-! ## Exact relation to the production descriptor -/

/-- The production descriptor refuses exactly when the classifier reports a reason. -/
theorem localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_none_iff_refusalReason
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view = none ↔
      localizedExtendedDescriptorRefusalReason? input target view ≠ none := by
  unfold localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
    localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
    localizedExtendedDescriptorRefusalReason?
    localizedExtendedDescriptorCenter? localizedExtendedDescriptorBaseFrame?
    localizedExtendedDescriptorKeyFrame? localizedExtendedDescriptorTrackedOrder?
    localizedExtendedDescriptorSpatialPoints? localizedExtendedDescriptorRawGeometry?
    localizedExtendedDescriptorRule3Stage?
  cases centerEq : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp [centerEq]
  | some center =>
      cases baseEq : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp [centerEq, baseEq]
      | some base =>
          cases keysEq : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
              target view base with
          | none =>
              have split := (buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_eq_none_iff
                input target view base).mp keysEq
              have splitRaw :
                  input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
                      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) base.cursors = none ∨
                    base.cursors.mapM (input.buildLocalizedRerootCompoundRule45KeyExec? target view
                      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) = none := by
                simpa only [localizedExtendedDescriptorRule3Stage?,
                  localizedExtendedDescriptorRule45Stage?] using split
              cases rule3Eq : input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
                  (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) base.cursors with
              | none => simp [centerEq, baseEq, keysEq, rule3Eq]
              | some rule3Frame =>
                  have rule45 : base.cursors.mapM
                      (input.buildLocalizedRerootCompoundRule45KeyExec? target view
                        (localizedOccurrenceRerootEvaluationFuel carrierFuel)) = none := by
                    rcases splitRaw with h | h
                    · rw [h] at rule3Eq
                      cases rule3Eq
                    · exact h
                  simp [centerEq, baseEq, keysEq, rule3Eq, rule45]
          | some keys =>
              cases trackedEq : input.localizedNoDoubleTrackedOrderExec? keys with
              | none => simp [centerEq, baseEq, keysEq, trackedEq]
              | some tracked =>
                  cases pointsEq : tracked.highestFirst.mapM (fun index =>
                      input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) with
                  | none => simp [centerEq, baseEq, keysEq, trackedEq, pointsEq]
                  | some points =>
                      cases geometryEq : descriptorOfPriorityOrderedPoints? points with
                      | none => simp [centerEq, baseEq, keysEq, trackedEq, pointsEq, geometryEq]
                      | some raw => simp [centerEq, baseEq, keysEq, trackedEq, pointsEq, geometryEq]

/-- The production descriptor emits a label exactly when the classifier reports no reason. -/
theorem localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_isSome_iff_refusalReason_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view).isSome = true ↔
      localizedExtendedDescriptorRefusalReason? input target view = none := by
  rw [Option.isSome_iff_ne_none]
  constructor
  · intro notNone
    by_contra reasonSome
    exact notNone ((localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_none_iff_refusalReason
      input target view).mpr reasonSome)
  · intro reasonNone descriptorNone
    exact ((localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_none_iff_refusalReason
      input target view).mp descriptorNone) reasonNone

/-- Success of every stage emits a descriptor label. -/
theorem localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_isSome_of_stagesSucceed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (stages : ExtendedDescriptorStagesSucceed input target view) :
    (input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view).isSome = true :=
  (localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_isSome_iff_refusalReason_none
    input target view).mpr
    ((localizedExtendedDescriptorRefusalReason?_eq_none_iff_stagesSucceed
      input target view).mpr stages)

/-- Every reason soundly explains a production `none`. -/
theorem localizedExtendedDescriptorRefusalReason?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (reason : LocalizedExtendedDescriptorRefusalReason)
    (computed : localizedExtendedDescriptorRefusalReason? input target view = some reason) :
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view = none := by
  apply (localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_none_iff_refusalReason
    input target view).mpr
  rw [computed]
  simp

/-- Completeness: every production `none` has exactly one emitted reason. -/
theorem localizedExtendedDescriptorRefusalReason?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (refused : input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view = none) :
    ∃ reason, localizedExtendedDescriptorRefusalReason? input target view = some reason :=
  Option.ne_none_iff_exists'.mp
    ((localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_none_iff_refusalReason
      input target view).mp refused)

/-- Distinct emitted reasons cannot coexist. -/
theorem localizedExtendedDescriptorRefusalReason?_unique
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (first second : LocalizedExtendedDescriptorRefusalReason)
    (firstComputed : localizedExtendedDescriptorRefusalReason? input target view = some first)
    (secondComputed : localizedExtendedDescriptorRefusalReason? input target view = some second) :
    first = second := by
  rw [firstComputed] at secondComputed
  exact Option.some.inj secondComputed

/-! ## Geometry-level reading of the last stage -/

/-- Exact meaning of four-point descriptor refusal: for a four-element list it is precisely
vanishing oriented volume; any other length is refused as malformed evidence. -/
theorem descriptorOfPriorityOrderedPoints?_eq_none_iff
    (points : List CartesianPoint3) :
    descriptorOfPriorityOrderedPoints? points = none ↔
      match points with
      | [first, second, third, fourth] =>
          CartesianPoint3.orientedVolume first second third fourth = 0
      | _ => True := by
  cases points with
  | nil => simp [descriptorOfPriorityOrderedPoints?]
  | cons first rest =>
      cases rest with
      | nil => simp [descriptorOfPriorityOrderedPoints?]
      | cons second rest =>
          cases rest with
          | nil => simp [descriptorOfPriorityOrderedPoints?]
          | cons third rest =>
              cases rest with
              | nil => simp [descriptorOfPriorityOrderedPoints?]
              | cons fourth rest =>
                  cases rest with
                  | nil =>
                      simp [descriptorOfPriorityOrderedPoints?,
                        descriptorOfOrientedVolume?_eq_none_iff]
                  | cons fifth rest => simp [descriptorOfPriorityOrderedPoints?]

/-- Once all prior stages have succeeded, the degenerate-geometry refusal is exactly the
failure of the raw oriented-volume descriptor on the computed points. -/
theorem ExtendedDescriptorDegenerateGeometryRefusal_iff_geometryStage
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (points : List CartesianPoint3)
    (centerComputed : localizedExtendedDescriptorCenter? input target = some center)
    (baseComputed : localizedExtendedDescriptorBaseFrame? input target = some base)
    (keysComputed : localizedExtendedDescriptorKeyFrame? input target view base = some keys)
    (trackedComputed : localizedExtendedDescriptorTrackedOrder? input keys = some tracked)
    (pointsComputed : localizedExtendedDescriptorSpatialPoints? input base tracked = some points) :
    ExtendedDescriptorDegenerateGeometryRefusal input target view ↔
      localizedExtendedDescriptorRawGeometry? points = none := by
  unfold ExtendedDescriptorDegenerateGeometryRefusal
  simp [centerComputed, baseComputed, keysComputed, trackedComputed, pointsComputed,
    localizedExtendedDescriptorRawGeometry?]

/-- The degenerate-geometry refusal on four computed points is exactly the vanishing of the
exact rational oriented volume of those four points. -/
theorem ExtendedDescriptorDegenerateGeometryRefusal_iff_volume_zero
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (points : List CartesianPoint3)
    (centerComputed : localizedExtendedDescriptorCenter? input target = some center)
    (baseComputed : localizedExtendedDescriptorBaseFrame? input target = some base)
    (keysComputed : localizedExtendedDescriptorKeyFrame? input target view base = some keys)
    (trackedComputed : localizedExtendedDescriptorTrackedOrder? input keys = some tracked)
    (pointsComputed : localizedExtendedDescriptorSpatialPoints? input base tracked = some points)
    (pointsLength : points.length = 4) :
    ExtendedDescriptorDegenerateGeometryRefusal input target view ↔
      ∃ first second third fourth,
        points = [first, second, third, fourth] ∧
          CartesianPoint3.orientedVolume first second third fourth = 0 := by
  rw [ExtendedDescriptorDegenerateGeometryRefusal_iff_geometryStage input target view center base
    keys tracked points centerComputed baseComputed keysComputed trackedComputed pointsComputed]
  unfold localizedExtendedDescriptorRawGeometry?
  rw [descriptorOfPriorityOrderedPoints?_eq_none_iff]
  rcases List.length_eq_four.mp pointsLength with ⟨first, second, third, fourth, rfl⟩
  dsimp only
  constructor
  · intro volumeZero
    exact ⟨first, second, third, fourth, rfl, volumeZero⟩
  · rintro ⟨first', second', third', fourth', listEq, volumeZero⟩
    simp only [List.cons.injEq, and_true] at listEq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := listEq
    exact volumeZero

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
