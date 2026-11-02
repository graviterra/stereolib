import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! Demand-driven ordinary and odd-cumulene endpoint compilation, retaining the original structural recursion,
ordered children, sorting, exhaustive coupled topology and two-pass exclusion policy.
The independent relations below change only the node meaning. Soundness does not assert
unconditional equality with the old evaluator or general chemical completeness. -/

mutual

  /-- Descriptor-bearing cumulative key. Every recursive call uses the predecessor index. -/
  def buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        input.LocalizedRerootCursor carrierFuel →
          Option input.LocalizedRerootRecursiveRule3SpatialKey
    | 0, _excluded, cursor => do
        let children ← input.executableLocalizedRerootChildren? cursor
        let observation ← input.localizedRule3StructuralNodeExec
          cursor.occurrence
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else none
    | fuel + 1, excluded, cursor => do
        let children ← input.executableLocalizedRerootChildren? cursor
        let observation ← input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target cursor.occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
          excluded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel excluded)
          let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
          some
            { constitutional := OfficialRuleMajorKey.assemble
                (input.moleculeGraph.officialRuleMajorRootKey
                  cursor.occurrence.1.node false)
                (sorted.map fun child => child.constitutional)
              observations := input.localizedRule3SpatialRootObservations observation ++
                input.mergeLocalizedRerootRule3ObservationChildren sorted
              rule3 := input.localizedRule3SpatialRootPriorities observation ++
                input.mergeLocalizedRerootRule3PriorityChildren sorted }

  /-- Two-pass physical-unit frame whose raw and rebuilt keys both use the predecessor index.
  The exhaustive topology resolver must find either no coupled matching or one unique matching;
  an ambiguous frame is rejected before circular-unit cancellation is chosen. -/
  def buildLocalizedExtendedShortCircuitRule3FrameExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame
    | 0, _cursors => none
    | fuel + 1, cursors => do
        let rawKeys ← cursors.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view fuel [])
        let topology ← input.localizedRule3CoupledTopologyResolutionExec? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view fuel excluded)
        some { rawKeys, coupled, excluded, keys }

  /-- Node reader at zero is structural; a successor delegates only to the predecessor frame. -/
  def localizedExtendedShortCircuitRule3NodeExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        Option (Option input.LocalizedRule3SpatialNodeResult)
    | 0, _excluded =>
        input.localizedRule3StructuralNodeExec occurrence
    | fuel + 1, excluded =>
        input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
          excluded

end


mutual

  /-- Independent recursive meaning of a descriptor-bearing key. -/
  def DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        input.LocalizedRerootCursor carrierFuel →
          input.LocalizedRerootRecursiveRule3SpatialKey → Prop
    | 0, _excluded, cursor, key =>
        ∃ children,
          input.DeclarativeLocalizedRerootChildren cursor children ∧
          children = [] ∧
          ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence ∧
          key =
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := []
              rule3 := [] }
    | fuel + 1, excluded, cursor, key =>
        ∃ children observation,
          input.DeclarativeLocalizedRerootChildren cursor children ∧
          input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
            target view
            (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view fuel)
            excluded cursor.occurrence observation ∧
          ((children = [] ∧
              key =
                { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                    cursor.occurrence.1.node true
                  observations := input.localizedRule3SpatialRootObservations observation
                  rule3 := input.localizedRule3SpatialRootPriorities observation }) ∨
           ∃ childKeys sorted,
              children ≠ [] ∧
              List.Forall₂
                (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
                  target view fuel excluded) children childKeys ∧
              sorted.Perm childKeys ∧
              input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted ∧
              key =
                { constitutional := OfficialRuleMajorKey.assemble
                    (input.moleculeGraph.officialRuleMajorRootKey
                      cursor.occurrence.1.node false)
                    (sorted.map fun child => child.constitutional)
                  observations := input.localizedRule3SpatialRootObservations observation ++
                    input.mergeLocalizedRerootRule3ObservationChildren sorted
                  rule3 := input.localizedRule3SpatialRootPriorities observation ++
                    input.mergeLocalizedRerootRule3PriorityChildren sorted })

  /-- Independent two-pass physical-unit frame meaning. -/
  def DeclarativeLocalizedExtendedShortCircuitRule3Frame
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        input.LocalizedRule3CanonicalKeyFrame → Prop
    | 0, _cursors, _frame => False
    | fuel + 1, cursors, frame =>
        List.Forall₂
            (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
              target view fuel []) cursors frame.rawKeys ∧
          ∃ topology,
            input.DeclarativeLocalizedRule3CoupledTopologyResolution
              frame.rawKeys topology ∧
            input.DeclarativeLocalizedRule3CoupledFramePolicy
              frame.rawKeys topology frame.coupled frame.excluded ∧
            List.Forall₂
              (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
                target view fuel frame.excluded) cursors frame.keys

end

private theorem executableLocalizedRerootChildren?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (children : List (input.LocalizedRerootCursor fuel))
    (computed : input.executableLocalizedRerootChildren? cursor = some children) :
    input.DeclarativeLocalizedRerootChildren cursor children := by
  apply input.localizedRerootChildren?_sound cursor children
  simpa only [localizedRerootChildren?_eq_some_executable,
    executableLocalizedRerootChildren?_eq_some] using computed

private theorem localizedRule3StructuralNodeExec_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3StructuralNodeExec occurrence = some observation) :
    observation = none ∧ ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  apply input.localizedDescriptorBearingRule3StructuralNode?_sound occurrence observation
  rwa [localizedDescriptorBearingRule3StructuralNode?_eq_localizedRule3StructuralNodeExec]

private theorem localizedRule3CoupledTopologyResolutionExec?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (topology : input.LocalizedRule3CoupledTopologyResolution) :
    input.localizedRule3CoupledTopologyResolutionExec? keys = some topology ↔
      input.DeclarativeLocalizedRule3CoupledTopologyResolution keys topology := by
  rw [localizedRule3CoupledTopologyResolutionExec?_eq_original]
  exact input.localizedRule3CoupledTopologyResolution?_eq_some_iff keys topology

private theorem mapM_sound_for_extendedShortCircuitRule3
    {α β : Type*} (f : α → Option β) (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → R a b) :
    ∀ as bs, as.mapM f = some bs → List.Forall₂ R as bs
  | [], bs, computed => by
      simp at computed
      subst bs
      exact List.Forall₂.nil
  | a :: as, bs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f a with
      | none => simp [headComputed] at computed
      | some b =>
          cases tailComputed : as.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst bs
              exact List.Forall₂.cons (sound a b headComputed)
                (mapM_sound_for_extendedShortCircuitRule3 f R sound as tail tailComputed)

/-- The shared fuel index simultaneously proves key and frame soundness. -/
theorem localizedExtendedShortCircuitRule3_mutual_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel,
      (∀ excluded cursor key,
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view fuel excluded cursor = some key →
          input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
            target view fuel excluded cursor key) ∧
      (∀ cursors frame,
        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
            target view fuel cursors = some frame →
          input.DeclarativeLocalizedExtendedShortCircuitRule3Frame
            target view fuel cursors frame)
  | 0 => by
      constructor
      · intro excluded cursor key computed
        unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec? at computed
        cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            cases observationComputed :
                input.localizedRule3StructuralNodeExec
                  cursor.occurrence with
            | none => simp [childrenComputed, observationComputed] at computed
            | some observation =>
                by_cases terminal : children = []
                · simp [childrenComputed, observationComputed, terminal] at computed
                  subst key
                  have observed :=
                    input.localizedRule3StructuralNodeExec_sound
                      cursor.occurrence observation observationComputed
                  rw [observed.1]
                  exact ⟨children,
                    input.executableLocalizedRerootChildren?_sound cursor children childrenComputed,
                    terminal, observed.2, rfl⟩
                · simp [childrenComputed, observationComputed, terminal] at computed
      · intro cursors frame computed
        simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at computed
  | fuel + 1 => by
      have prior := input.localizedExtendedShortCircuitRule3_mutual_sound target view fuel
      constructor
      · intro excluded cursor key computed
        unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec? at computed
        cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            cases observationComputed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
                target cursor.occurrence view
                (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
                excluded with
            | none => simp [childrenComputed, observationComputed] at computed
            | some observation =>
                have observed := input.localizedRule3ExtendedShortCircuitNodeWithExec?_sound
                  target cursor.occurrence view
                  (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
                  (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view fuel)
                  prior.2 excluded observation observationComputed
                by_cases terminal : children = []
                · simp [childrenComputed, observationComputed, terminal] at computed
                  subst key
                  exact ⟨children, observation,
                    input.executableLocalizedRerootChildren?_sound cursor children childrenComputed,
                    observed, Or.inl ⟨terminal, rfl⟩⟩
                · cases childKeysComputed : children.mapM
                      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view fuel excluded) with
                  | none =>
                      simp [childrenComputed, observationComputed, terminal,
                        childKeysComputed] at computed
                  | some childKeys =>
                      simp [childrenComputed, observationComputed, terminal,
                        childKeysComputed] at computed
                      subst key
                      let sorted :=
                        input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
                      exact ⟨children, observation,
                        input.executableLocalizedRerootChildren?_sound cursor children childrenComputed,
                        observed, Or.inr ⟨childKeys, sorted, terminal,
                          mapM_sound_for_extendedShortCircuitRule3
                            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                              target view fuel excluded)
                            (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
                              target view fuel excluded)
                            (fun child childKey childComputed =>
                              prior.1 excluded child childKey childComputed)
                            children childKeys childKeysComputed,
                          input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm childKeys,
                          input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending childKeys,
                          rfl⟩⟩
      · intro cursors frame computed
        unfold buildLocalizedExtendedShortCircuitRule3FrameExec? at computed
        cases rawComputed : cursors.mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel []) with
        | none => simp [rawComputed] at computed
        | some rawKeys =>
            cases topologyComputed :
                input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
            | none => simp [rawComputed, topologyComputed] at computed
            | some topology =>
                let coupled := topology.isCoupled
                let excluded :=
                  input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
                cases keysComputed : cursors.mapM
                    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                      target view fuel excluded) with
                | none =>
                    simp [rawComputed, topologyComputed, excluded,
                      keysComputed] at computed
                | some keys =>
                    simp [rawComputed, topologyComputed, excluded,
                      keysComputed] at computed
                    subst frame
                    exact ⟨
                      mapM_sound_for_extendedShortCircuitRule3
                        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                          target view fuel [])
                        (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
                          target view fuel [])
                        (fun cursor key keyComputed =>
                          prior.1 [] cursor key keyComputed)
                        cursors rawKeys rawComputed,
                      topology,
                      (input.localizedRule3CoupledTopologyResolutionExec?_eq_some_iff
                        rawKeys topology).mp topologyComputed,
                      input.localizedRule3CoupledFramePolicy_sound rawKeys topology,
                      mapM_sound_for_extendedShortCircuitRule3
                        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                          target view fuel excluded)
                        (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
                          target view fuel excluded)
                        (fun cursor key keyComputed =>
                          prior.1 excluded cursor key keyComputed)
                        cursors keys keysComputed⟩

/-- Public key soundness theorem. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view fuel excluded cursor = some key) :
    input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
      target view fuel excluded cursor key :=
  (input.localizedExtendedShortCircuitRule3_mutual_sound target view fuel).1
    excluded cursor key computed

/-- Public two-pass frame soundness theorem. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view fuel cursors = some frame) :
    input.DeclarativeLocalizedExtendedShortCircuitRule3Frame
      target view fuel cursors frame :=
  (input.localizedExtendedShortCircuitRule3_mutual_sound target view fuel).2
    cursors frame computed

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
