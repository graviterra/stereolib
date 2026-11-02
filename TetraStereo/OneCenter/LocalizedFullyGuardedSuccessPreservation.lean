import TetraStereo.OneCenter.LocalizedFullyTerminalGuardedRule3Key
import TetraStereo.OneCenter.LocalizedRule3CallbackSuccessRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false






















































namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TerminalGuardedRule3Node
open TerminalGuardedObservationAdapter

/-! ## The refinement statements -/

/-- A successful old key has a successful fully guarded key at the same fuel under any
membership-equivalent exclusion list, and the two keys are topology-equivalent. -/
def LocalizedFullyTerminalGuardedKeyRefines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) : Prop :=
  ∀ (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId),
    LocalizedRule3ExclusionEquivalent input excluded guardedExcluded →
      ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
        (oldKey : input.LocalizedRerootRecursiveRule3SpatialKey),
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view fuel excluded cursor = some oldKey →
          ∃ guardedKey : input.LocalizedRerootRecursiveRule3SpatialKey,
            input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
                target view fuel guardedExcluded cursor = some guardedKey ∧
              LocalizedRule3SpatialKeyTopologyEquivalent input oldKey guardedKey

/-- A successful old two-pass frame has a successful fully guarded frame at the same fuel carrying
the frame topology invariant. -/
def LocalizedFullyTerminalGuardedFrameRefines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) : Prop :=
  ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (oldFrame : input.LocalizedRule3CanonicalKeyFrame),
    input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view fuel cursors = some oldFrame →
      ∃ guardedFrame : input.LocalizedRule3CanonicalKeyFrame,
        input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
            target view fuel cursors = some guardedFrame ∧
          LocalizedRule3ExtendedFrameTopologyEquivalent input oldFrame guardedFrame

/-! ## `mapM` helpers -/

/-- Success of a `mapM` produces the pointwise computation relation. -/
private theorem forall₂_of_mapM_eq_some
    {α β : Type*} (f : α → Option β) (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → R a b) :
    ∀ (values : List α) (results : List β),
      values.mapM f = some results → List.Forall₂ R values results
  | [], results, computed => by
      cases results with
      | nil => exact List.Forall₂.nil
      | cons result rest => simp at computed
  | value :: values, results, computed => by
      cases first : f value with
      | none => simp [first] at computed
      | some result =>
          cases rest : values.mapM f with
          | none => simp [first, rest] at computed
          | some restResults =>
              simp [first, rest] at computed
              subst results
              exact List.Forall₂.cons (sound value result first)
                (forall₂_of_mapM_eq_some f R sound values restResults rest)

/-- Pointwise successful refinements lift to a successful refined `mapM`. -/
private theorem mapM_exists_of_forall₂
    {α β γ : Type*} (f : α → Option β) (R : α → γ → Prop) (S : γ → β → Prop)
    (complete : ∀ a c, R a c → ∃ b, f a = some b ∧ S c b) :
    ∀ (values : List α) (sources : List γ),
      List.Forall₂ R values sources →
        ∃ results, values.mapM f = some results ∧ List.Forall₂ S sources results
  | [], sources, related => by
      cases related
      exact ⟨[], rfl, List.Forall₂.nil⟩
  | value :: values, source :: sources, related => by
      cases related with
      | cons head tail =>
          rcases complete value source head with ⟨result, computed, resultRelated⟩
          rcases mapM_exists_of_forall₂ f R S complete values sources tail with
            ⟨results, computedTail, relatedTail⟩
          exact ⟨result :: results, by simp [computed, computedTail],
            List.Forall₂.cons resultRelated relatedTail⟩

/-! ## Node-level transport: old extended node → new guarded adapter -/

/-- Transport a successful old extended-node evaluation to the fully guarded frame callback at the
same observation, through the intermediate callback.  The intermediate callback returns the old
frame on old successes and defers to the new callback otherwise, so the old success is transported
exactly by the sibling one-way lemma, and the intermediate callback refines the new callback by the
frame induction hypothesis together with reflexivity on old refusals. -/
private theorem localizedFullyTerminalGuardedExtendedNode_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (frameInduction : LocalizedFullyTerminalGuardedFrameRefines input target view fuel)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded guardedExcluded)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors)
      excluded = some observation) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
      (fun cursors =>
        input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
      guardedExcluded = some observation := by
  let interCallback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame :=
    fun cursors =>
      match input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors with
      | some frame => some frame
      | none => input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors
  have oldRefinesInter : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence)
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors)
      interCallback := by
    intro cursors _member oldFrame computedFrame
    refine ⟨oldFrame, ?_, input.LocalizedRule3ExtendedFrameTopologyEquivalent_refl oldFrame⟩
    change input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors =
        some oldFrame at computedFrame
    dsimp [interCallback]
    rw [computedFrame]
  have interComputed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view interCallback excluded = some observation :=
    input.localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines
      target occurrence view
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors)
      interCallback oldRefinesInter excluded observation computed
  have interRefinesNew : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) interCallback
      (fun cursors =>
        input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors) := by
    intro cursors _member interFrame computedInter
    dsimp [interCallback] at computedInter
    cases h : input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors with
    | none =>
        rw [h] at computedInter
        refine ⟨interFrame, computedInter,
          input.LocalizedRule3ExtendedFrameTopologyEquivalent_refl interFrame⟩
    | some oldFrame =>
        rw [h] at computedInter
        have computedInter' : some oldFrame = some interFrame := by
          simpa using computedInter
        have interFrameEq : interFrame = oldFrame := Option.some.inj computedInter'.symm
        obtain ⟨newFrame, computedNew, frameRel⟩ := frameInduction cursors oldFrame h
        refine ⟨newFrame, computedNew, ?_⟩
        rw [interFrameEq]
        exact frameRel
  have newComputed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view
      (fun cursors =>
        input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
      excluded = some observation :=
    input.localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines
      target occurrence view interCallback
      (fun cursors =>
        input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
      interRefinesNew excluded observation interComputed
  rw [← input.localizedRule3ExtendedShortCircuitNodeWithExec?_exclusion_extensional
    target occurrence view
    (fun cursors =>
      input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
    equivalence]
  exact newComputed

/-- Every successful old production-node evaluation is preserved by the actual adapter at the same
fuel, under any membership-equivalent exclusion list, with the same comparison-visible observable
projection.  Fallback branches are the old extended computation; the guard branch is compared
directly through the old branch value. -/
private theorem localizedFullyTerminalGuardedNode_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (frameInduction : LocalizedFullyTerminalGuardedFrameRefines input target view fuel)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded guardedExcluded)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors)
      excluded = some observation) :
    ∃ fresh : Option input.LocalizedRule3SpatialNodeResult,
      localizedRule3TerminalGuardedSpatialNodeWithExec? input target occurrence view
        (fun cursors =>
          input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
        guardedExcluded = some fresh ∧
      Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation := by
  have extendedRefined : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view
      (fun cursors =>
        input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
      guardedExcluded = some observation :=
    localizedFullyTerminalGuardedExtendedNode_refines input target occurrence view fuel
      frameInduction excluded guardedExcluded equivalence observation computed
  cases oddRoute : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      refine ⟨observation, ?_, rfl⟩
      · unfold localizedRule3TerminalGuardedSpatialNodeWithExec?
        have nodeEq : localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
            (fun cursors =>
              input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
            guardedExcluded =
            localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input
              (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
                (fun cursors =>
                  input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
                guardedExcluded) := by
          simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute]
        rw [nodeEq, localizedRule3TerminalGuardedSpatialOutcome_ordinary]
        exact extendedRefined
  | none =>
      cases ordinaryRoute : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | none =>
          refine ⟨observation, ?_, rfl⟩
          · unfold localizedRule3TerminalGuardedSpatialNodeWithExec?
            have nodeEq : localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
                (fun cursors =>
                  input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel cursors)
                guardedExcluded =
                localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input
                  (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
                    (fun cursors =>
                      input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                        target view fuel cursors)
                    guardedExcluded) := by
              simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute, ordinaryRoute]
            rw [nodeEq, localizedRule3TerminalGuardedSpatialOutcome_ordinary]
            exact extendedRefined
      | some ordinaryCertificate =>
          cases topologyComputed :
              input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
          | none =>
              refine ⟨observation, ?_, rfl⟩
              · unfold localizedRule3TerminalGuardedSpatialNodeWithExec?
                have nodeEq : localizedRule3TerminalGuardedNodeWithExec? input target occurrence
                    view
                    (fun cursors =>
                      input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                        target view fuel cursors)
                    guardedExcluded =
                    localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input
                      (input.localizedRule3ExtendedShortCircuitNodeWithExec?
                        target occurrence view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        guardedExcluded) := by
                  simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute, ordinaryRoute,
                    topologyComputed]
                rw [nodeEq, localizedRule3TerminalGuardedSpatialOutcome_ordinary]
                exact extendedRefined
          | some topology =>
              cases guardComputed : localizedRule3TerminalGuard? input target view topology with
              | none =>
                  refine ⟨observation, ?_, rfl⟩
                  · unfold localizedRule3TerminalGuardedSpatialNodeWithExec?
                    have nodeEq : localizedRule3TerminalGuardedNodeWithExec? input target
                        occurrence view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        guardedExcluded =
                        localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input
                          (input.localizedRule3ExtendedShortCircuitNodeWithExec?
                            target occurrence view
                            (fun cursors =>
                              input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                                target view fuel cursors)
                            guardedExcluded) := by
                      simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute, ordinaryRoute,
                        topologyComputed, guardComputed]
                    rw [nodeEq, localizedRule3TerminalGuardedSpatialOutcome_ordinary]
                    exact extendedRefined
              | some witness =>
                  obtain ⟨fresh0, adapterOldComputed, compatible⟩ :=
                    localizedRule3TerminalGuardedSpatialNodeWithExec?_refines_extended
                      input target occurrence view fuel excluded observation computed
                  have nodeCallbackIndependent :
                      localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
                        (fun cursors =>
                          input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                            target view fuel cursors)
                        excluded =
                      localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        excluded :=
                    localizedRule3TerminalGuardedNodeWithExec?_guard_callback_independent
                      input target occurrence view topology witness
                      (fun cursors =>
                        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                          target view fuel cursors)
                      (fun cursors =>
                        input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                          target view fuel cursors)
                      excluded oddRoute ordinaryRoute topologyComputed guardComputed
                  have nodeExclusionIndependent :
                      localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        excluded =
                      localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        guardedExcluded :=
                    localizedRule3TerminalGuardedNodeWithExec?_exclusion_extensional
                      input target occurrence view
                      (fun cursors =>
                        input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                          target view fuel cursors)
                      equivalence
                  have adapterCallbackIndependent :
                      localizedRule3TerminalGuardedSpatialNodeWithExec? input target occurrence
                          view
                        (fun cursors =>
                          input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                            target view fuel cursors)
                        excluded =
                      localizedRule3TerminalGuardedSpatialNodeWithExec? input target occurrence
                          view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        excluded := by
                    unfold localizedRule3TerminalGuardedSpatialNodeWithExec?
                    exact congrArg (localizedRule3TerminalGuardedSpatialOutcome input)
                      nodeCallbackIndependent
                  have adapterExclusionIndependent :
                      localizedRule3TerminalGuardedSpatialNodeWithExec? input target occurrence
                          view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        excluded =
                      localizedRule3TerminalGuardedSpatialNodeWithExec? input target occurrence
                          view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        guardedExcluded := by
                    unfold localizedRule3TerminalGuardedSpatialNodeWithExec?
                    exact congrArg (localizedRule3TerminalGuardedSpatialOutcome input)
                      nodeExclusionIndependent
                  have newComputed :
                      localizedRule3TerminalGuardedSpatialNodeWithExec? input target occurrence
                          view
                        (fun cursors =>
                          input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
                            target view fuel cursors)
                        guardedExcluded = some fresh0 := by
                    rw [← adapterExclusionIndependent, ← adapterCallbackIndependent]
                    exact adapterOldComputed
                  refine ⟨fresh0, newComputed, ?_⟩
                  exact LocalizedRule3SpatialNodeObservationCompatible.commonObservable_eq
                    input compatible

/-! ## The mutual induction -/

/-- Successor key refinement.  The old node evaluation is transported to the actual adapter under
the fully guarded predecessor callback by the node-level lemma, and the child keys are refined by
the key induction hypothesis. -/
private theorem localizedFullyTerminalGuardedKey_succ_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (keyInduction : LocalizedFullyTerminalGuardedKeyRefines input target view fuel)
    (frameInduction : LocalizedFullyTerminalGuardedFrameRefines input target view fuel)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded guardedExcluded)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (oldKey : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed :
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view (fuel + 1) excluded cursor = some oldKey) :
    ∃ guardedKey : input.LocalizedRerootRecursiveRule3SpatialKey,
      input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
          target view (fuel + 1) guardedExcluded cursor = some guardedKey ∧
        LocalizedRule3SpatialKeyTopologyEquivalent input oldKey guardedKey := by
  cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
  | none =>
      simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
        childrenComputed] at computed
  | some children =>
      cases nodeComputed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target cursor.occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
          excluded with
      | none =>
          simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
            childrenComputed, nodeComputed] at computed
      | some observation =>
          rcases localizedFullyTerminalGuardedNode_refines input target cursor.occurrence view
            fuel frameInduction excluded guardedExcluded equivalence observation nodeComputed with
            ⟨fresh, freshComputed, projection⟩
          have guardedComputedAtGuarded :
              localizedRule3TerminalGuardedSpatialNodeWithExec? input target cursor.occurrence view
                  (input.buildLocalizedFullyTerminalGuardedRule3FrameExec? target view fuel)
                  guardedExcluded = some fresh :=
            freshComputed
          by_cases empty : children = []
          · have oldComputedRoot :
                input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                    target view (fuel + 1) excluded cursor =
                  some
                    { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                        cursor.occurrence.1.node true
                      observations := input.localizedRule3SpatialRootObservations observation
                      rule3 := input.localizedRule3SpatialRootPriorities observation } := by
              simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
                childrenComputed, nodeComputed, empty]
            rw [oldComputedRoot] at computed
            have keyEq : oldKey =
                { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                    cursor.occurrence.1.node true
                  observations := input.localizedRule3SpatialRootObservations observation
                  rule3 := input.localizedRule3SpatialRootPriorities observation } :=
              (Option.some.inj computed).symm
            subst oldKey
            refine ⟨
              { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                  cursor.occurrence.1.node true
                observations := input.localizedRule3SpatialRootObservations fresh
                rule3 := input.localizedRule3SpatialRootPriorities fresh },
              ?_, ?_⟩
            · simp [buildLocalizedFullyTerminalGuardedRule3KeyExec?,
                childrenComputed, guardedComputedAtGuarded, empty]
            · exact input.localizedRule3RootKey_topologyEquivalent_of_terminalProjection_eq
                cursor.occurrence.1.node projection.symm
          · cases childComputed : children.mapM
                (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                  target view fuel excluded) with
            | none =>
                simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
                  childrenComputed, nodeComputed, empty, childComputed] at computed
            | some childKeys =>
                have oldComputedParent :
                    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view (fuel + 1) excluded cursor =
                      some
                        { constitutional := OfficialRuleMajorKey.assemble
                            (input.moleculeGraph.officialRuleMajorRootKey
                              cursor.occurrence.1.node false)
                            ((input.sortLocalizedRerootRecursiveRule3SpatialKeys
                              childKeys).map fun child => child.constitutional)
                          observations :=
                            input.localizedRule3SpatialRootObservations observation ++
                              input.mergeLocalizedRerootRule3ObservationChildren
                                (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                  childKeys)
                          rule3 :=
                            input.localizedRule3SpatialRootPriorities observation ++
                              input.mergeLocalizedRerootRule3PriorityChildren
                                (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                  childKeys) } := by
                  simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
                    childrenComputed, nodeComputed, empty, childComputed]
                rw [oldComputedParent] at computed
                have keyEq : oldKey =
                    { constitutional := OfficialRuleMajorKey.assemble
                        (input.moleculeGraph.officialRuleMajorRootKey
                          cursor.occurrence.1.node false)
                        ((input.sortLocalizedRerootRecursiveRule3SpatialKeys
                          childKeys).map fun child => child.constitutional)
                      observations :=
                        input.localizedRule3SpatialRootObservations observation ++
                          input.mergeLocalizedRerootRule3ObservationChildren
                            (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                              childKeys)
                      rule3 :=
                        input.localizedRule3SpatialRootPriorities observation ++
                          input.mergeLocalizedRerootRule3PriorityChildren
                            (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                              childKeys) } :=
                  (Option.some.inj computed).symm
                subst oldKey
                have childRelations : List.Forall₂
                    (fun child childKey =>
                      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                          target view fuel excluded child = some childKey)
                    children childKeys :=
                  forall₂_of_mapM_eq_some _ _ (fun _ _ old => old)
                    children childKeys childComputed
                rcases mapM_exists_of_forall₂
                  (input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
                    target view fuel guardedExcluded)
                  (fun child childKey =>
                    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view fuel excluded child = some childKey)
                  (LocalizedRule3SpatialKeyTopologyEquivalent input)
                  (fun child childKey childDerived =>
                    keyInduction excluded guardedExcluded equivalence
                      child childKey childDerived)
                  children childKeys childRelations with
                  ⟨guardedChildKeys, guardedChildComputed, guardedChildRelations⟩
                refine ⟨
                  { constitutional := OfficialRuleMajorKey.assemble
                      (input.moleculeGraph.officialRuleMajorRootKey
                        cursor.occurrence.1.node false)
                      ((input.sortLocalizedRerootRecursiveRule3SpatialKeys
                        guardedChildKeys).map fun child => child.constitutional)
                    observations :=
                      input.localizedRule3SpatialRootObservations fresh ++
                        input.mergeLocalizedRerootRule3ObservationChildren
                          (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                            guardedChildKeys)
                    rule3 :=
                      input.localizedRule3SpatialRootPriorities fresh ++
                        input.mergeLocalizedRerootRule3PriorityChildren
                          (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                            guardedChildKeys) },
                  ?_, ?_⟩
                · simp [buildLocalizedFullyTerminalGuardedRule3KeyExec?,
                    childrenComputed, guardedComputedAtGuarded, empty, guardedChildComputed]
                · exact input.assembledParent_topologyEquivalent_of_root_data
                    (input.moleculeGraph.officialRuleMajorRootKey
                      cursor.occurrence.1.node false)
                    (input.localizedRule3SpatialRootObservations observation)
                    (input.localizedRule3SpatialRootObservations fresh)
                    (input.localizedRule3SpatialRootPriorities observation)
                    (input.localizedRule3SpatialRootPriorities fresh)
                    (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys)
                    (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                      guardedChildKeys)
                    (localizedRule3SpatialRootPriorities_eq_of_terminalProjection_eq
                      projection.symm)
                    (localizedRule3SpatialRootObservations_flatten_physicalUnit_mem_iff
                      projection.symm)
                    (input.map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂_of_perm_of_descending
                      childKeys guardedChildKeys
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys)
                      guardedChildRelations
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm childKeys)
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending
                        childKeys))
                    (fun unit =>
                      input.mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂_of_perm
                        childKeys guardedChildKeys
                        (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys)
                        guardedChildRelations
                        (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm childKeys)
                        unit)

/-- Successor frame refinement.  Both passes are preserved: the raw keys are refined at empty
exclusions, the actual coupled topology is transported, the exclusion set is transported by
membership on the actual raw keys, and the rebuilt keys are refined under the transported
exclusions. -/
private theorem localizedFullyTerminalGuardedFrame_succ_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (keyInduction : LocalizedFullyTerminalGuardedKeyRefines input target view fuel)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (oldFrame : input.LocalizedRule3CanonicalKeyFrame)
    (computed :
      input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view (fuel + 1) cursors = some oldFrame) :
    ∃ guardedFrame : input.LocalizedRule3CanonicalKeyFrame,
      input.buildLocalizedFullyTerminalGuardedRule3FrameExec?
          target view (fuel + 1) cursors = some guardedFrame ∧
        LocalizedRule3ExtendedFrameTopologyEquivalent input oldFrame guardedFrame := by
  cases rawComputed : cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view fuel []) with
  | none =>
      simp [buildLocalizedExtendedShortCircuitRule3FrameExec?, rawComputed] at computed
  | some rawKeys =>
      cases topologyComputed :
          input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
      | none =>
          simp [buildLocalizedExtendedShortCircuitRule3FrameExec?,
            rawComputed, topologyComputed] at computed
      | some topology =>
          cases rebuiltComputed : cursors.mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                target view fuel
                (input.localizedRule3CoupledExcludedPhysicalUnits
                  rawKeys topology)) with
          | none =>
              simp [buildLocalizedExtendedShortCircuitRule3FrameExec?,
                rawComputed, topologyComputed, rebuiltComputed] at computed
          | some rebuiltKeys =>
              have frameEq : oldFrame =
                  { rawKeys := rawKeys
                    coupled := topology.isCoupled
                    excluded :=
                      input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
                    keys := rebuiltKeys } :=
                (Option.some.inj (by
                  simpa [buildLocalizedExtendedShortCircuitRule3FrameExec?,
                    rawComputed, topologyComputed, rebuiltComputed] using computed)).symm
              subst oldFrame
              have rawRelations : List.Forall₂
                  (fun cursor key =>
                    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view fuel [] cursor = some key)
                  cursors rawKeys :=
                forall₂_of_mapM_eq_some _ _ (fun _ _ old => old)
                  cursors rawKeys rawComputed
              rcases mapM_exists_of_forall₂
                (input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
                  target view fuel [])
                (fun cursor key =>
                  input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                      target view fuel [] cursor = some key)
                (LocalizedRule3SpatialKeyTopologyEquivalent input)
                (fun cursor key oldComputed =>
                  keyInduction [] [] (input.localizedRule3ExclusionEquivalent_refl [])
                    cursor key oldComputed)
                cursors rawKeys rawRelations with
                ⟨guardedRawKeys, guardedRawComputed, guardedRawRelations⟩
              have resolutionEq :=
                input.localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂
                  rawKeys guardedRawKeys guardedRawRelations
              have guardedTopologyComputed :
                  input.localizedRule3CoupledTopologyResolutionExec?
                      guardedRawKeys = some topology := by
                rw [← resolutionEq]
                exact topologyComputed
              have excludedIff : ∀ unit : input.LocalizedRule3PhysicalUnitId,
                  unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits
                      rawKeys topology ↔
                    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits
                      guardedRawKeys topology :=
                fun unit =>
                  input.mem_localizedRule3CoupledExcludedPhysicalUnits_congruence
                    rawKeys guardedRawKeys guardedRawRelations topology topology
                    topologyComputed guardedTopologyComputed unit
              have excludedEquivalent : LocalizedRule3ExclusionEquivalent input
                  (input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology)
                  (input.localizedRule3CoupledExcludedPhysicalUnits
                    guardedRawKeys topology) :=
                fun unit => excludedIff unit
              have rebuiltRelations : List.Forall₂
                  (fun cursor key =>
                    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view fuel
                        (input.localizedRule3CoupledExcludedPhysicalUnits
                          rawKeys topology) cursor = some key)
                  cursors rebuiltKeys :=
                forall₂_of_mapM_eq_some _ _ (fun _ _ old => old)
                  cursors rebuiltKeys rebuiltComputed
              rcases mapM_exists_of_forall₂
                (input.buildLocalizedFullyTerminalGuardedRule3KeyExec?
                  target view fuel
                  (input.localizedRule3CoupledExcludedPhysicalUnits
                    guardedRawKeys topology))
                (fun cursor key =>
                  input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                      target view fuel
                      (input.localizedRule3CoupledExcludedPhysicalUnits
                        rawKeys topology) cursor = some key)
                (LocalizedRule3SpatialKeyTopologyEquivalent input)
                (fun cursor key oldComputed =>
                  keyInduction
                    (input.localizedRule3CoupledExcludedPhysicalUnits
                      rawKeys topology)
                    (input.localizedRule3CoupledExcludedPhysicalUnits
                      guardedRawKeys topology)
                    excludedEquivalent cursor key oldComputed)
                cursors rebuiltKeys rebuiltRelations with
                ⟨guardedRebuiltKeys, guardedRebuiltComputed, guardedRebuiltRelations⟩
              refine ⟨
                { rawKeys := guardedRawKeys
                  coupled := topology.isCoupled
                  excluded :=
                    input.localizedRule3CoupledExcludedPhysicalUnits
                      guardedRawKeys topology
                  keys := guardedRebuiltKeys },
                ?_, ?_⟩
              · simp [buildLocalizedFullyTerminalGuardedRule3FrameExec?,
                  guardedRawComputed, guardedTopologyComputed, guardedRebuiltComputed]
              · exact ⟨guardedRawRelations, guardedRebuiltRelations, rfl,
                  fun unit => excludedIff unit⟩

/-- Mutual refinement of the fully guarded key and frame compilers.  The induction hypothesis is a
real recursive statement about successful old evaluations, not a desired output or a global
node-refinement assumption. -/
theorem localizedFullyTerminalGuardedRule3_mutual_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel : Nat,
      LocalizedFullyTerminalGuardedKeyRefines input target view fuel ∧
        LocalizedFullyTerminalGuardedFrameRefines input target view fuel
  | 0 => by
      constructor
      · intro excluded guardedExcluded _equivalence cursor oldKey computed
        exact input.buildLocalizedFullyTerminalGuardedRule3KeyExec?_zero_refines
          target view excluded guardedExcluded cursor oldKey computed
      · intro cursors oldFrame computed
        simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at computed
  | fuel + 1 => by
      have prior := input.localizedFullyTerminalGuardedRule3_mutual_refines
        target view fuel
      exact ⟨
        fun excluded guardedExcluded equivalence cursor oldKey computed =>
          localizedFullyTerminalGuardedKey_succ_refines input target view fuel prior.1 prior.2
            excluded guardedExcluded equivalence cursor oldKey computed,
        fun cursors oldFrame computed =>
          localizedFullyTerminalGuardedFrame_succ_refines input target view fuel prior.1
            cursors oldFrame computed⟩

/-! ## Public refinement theorems -/

/-- Every successful old key evaluation is preserved by the fully guarded recursive builder at the
same fuel, under any membership-equivalent exclusion list, with a topology-equivalent guarded
key. -/
theorem buildLocalizedFullyTerminalGuardedRule3KeyExec?_refines_old
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    LocalizedFullyTerminalGuardedKeyRefines input target view fuel :=
  (input.localizedFullyTerminalGuardedRule3_mutual_refines target view fuel).1

/-- Every successful old frame evaluation is preserved by the fully guarded two-pass frame at the
same fuel, with pointwise topology-equivalent raw and rebuilt keys, the same coupled flag and the
same exclusion membership. -/
theorem buildLocalizedFullyTerminalGuardedRule3FrameExec?_refines_old
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    LocalizedFullyTerminalGuardedFrameRefines input target view fuel :=
  (input.localizedFullyTerminalGuardedRule3_mutual_refines target view fuel).2






assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedFullyTerminalGuardedKeyRefines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedFullyTerminalGuardedFrameRefines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedFullyTerminalGuardedRule3_mutual_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3KeyExec?_refines_old
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedFullyTerminalGuardedRule3FrameExec?_refines_old

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
