import TetraStereo.OneCenter.LocalizedRule3CumulatedDescriptor
import TetraStereo.OneCenter.LocalizedRule3CoupledTopology
import TetraStereo.OneCenter.LocalizedCyclicDoubleBondDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Well-founded descriptor-bearing recursive Rule-3 keys

This module removes the hidden strict-reference recursion from the new endpoint path.  One shared
natural-number index grades all recursive activity:

* a reroot-tree child key uses the predecessor index;
* a descriptor-bearing geometrical node uses a predecessor endpoint frame; and
* a common endpoint frame uses predecessor ligand keys.

At index zero only a terminal structural nonunit can be compiled.  A genuine geometrical unit is
never silently skipped at the base case.  Thus every successful descriptor-bearing observation
has a finite, kernel-visible dependency tree, and increasing the index exposes nested Rule-3
reference decisions without defining a circular evaluator.
-/

namespace CertifiedLocalizedCIPInput

/-- Base reader: only a proved structural nonunit succeeds. -/
noncomputable def localizedDescriptorBearingRule3StructuralNode?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (Option input.LocalizedRule3SpatialNodeResult) := by
  classical
  exact if input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence then none else some none

/-- Descriptor-bearing node reader with explicit smaller-frame callback and common physical-unit
exclusion set. -/
noncomputable def localizedDescriptorBearingRule3NodeWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option input.LocalizedRule3SpatialNodeResult) := by
  classical
  exact if edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence then
      match input.localizedRule3CumulatedAxisEntry? occurrence with
      | none => none
      | some (.internal _ _) => some none
      | some (.ringClosure _ _) =>
          match input.localizedRule3RequiredMonocyclicEZWith?
              target occurrence view rule3FrameOf with
          | some result =>
              let observation :=
                input.localizedRule3RequiredMonocyclicEZObservation result
              if excluded.contains observation.physicalUnitId then some none
              else some (some observation)
          | none =>
              match input.localizedRule3CyclicAuthorityRoute? occurrence with
              | some (.ordinaryMonocyclicPolicy _ _ policyResult) =>
                  match policyResult.policy with
                  | .permanentlyOmit => some none
                  | .requireEZ => none
              | some (.fullyCyclicCumulene _ _ _)
              | some (.ordinaryMonocyclicPolicyGap _ _ _ _)
              | some (.ordinaryNonmonocyclic _ _)
              | none => none
      | some (.branched _ _ _ _) =>
          -- P-93.4.2.1.2/P-93.4.2.4: this is not one cumulative chain.  Analyze the
          -- oriented physical bond as its own candidate stereogenic unit.
          match input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
              target occurrence view rule3FrameOf with
          | none => none
          | some result =>
              let observation := input.localizedRule3DescriptorBearingObservation result
              if excluded.contains observation.physicalUnitId then some none
              else some (some observation)
      | some (.terminalStart _) =>
          match input.localizedRule3CumulatedEndpointCursorFrame?
              (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
          | none => none
          | some axis =>
              if ordinary : axis.doubleBondCount = 1 then
                match input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                    target occurrence view rule3FrameOf with
                | none => none
                | some result =>
                    let observation := input.localizedRule3DescriptorBearingObservation result
                    if excluded.contains observation.physicalUnitId then some none
                    else some (some observation)
              else if planar : Odd axis.doubleBondCount then
                match input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
                    target occurrence view rule3FrameOf with
                | none => none
                | some result =>
                    let observation :=
                      input.localizedRule3OddCumuleneDescriptorBearingObservation result
                    if excluded.contains observation.physicalUnitId then some none
                    else some (some observation)
              else
                -- P-93.4.2.2: a nonordinary even cumulene is axial, not a planar Rule-3 unit.
                some none
    else some none

/-- An internal edge of a proved cumulated axis is skipped: the whole physical unit is observed
only at its terminal-start occurrence. -/
theorem localizedDescriptorBearingRule3NodeWith?_of_internalCumulatedAxis
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (previousAxis : input.LocalizedRerootCursor carrierFuel)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.internal initial previousAxis)) :
    input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded = some none := by
  classical
  simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed]

/-- A required ordinary monocyclic descriptor is retained by the recursive node reader, subject
to the same physical-unit exclusion used by every Rule-3 observation. -/
theorem localizedDescriptorBearingRule3NodeWith?_of_requiredMonocyclicGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure))
    (resultComputed : input.localizedRule3RequiredMonocyclicEZWith?
      target occurrence view rule3FrameOf = some result) :
    input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded =
        if excluded.contains
            (input.localizedRule3RequiredMonocyclicEZObservation result).physicalUnitId then
          some none
        else
          some (some (input.localizedRule3RequiredMonocyclicEZObservation result)) := by
  classical
  simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed]

/-- A P-93 permanent-omission monocycle is a resolved non-emitting node, not an unsupported
geometry failure. -/
theorem localizedDescriptorBearingRule3NodeWith?_of_omittedMonocycle
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (routeInitial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (routeClosure : input.LocalizedRerootCursor carrierFuel)
    (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure))
    (routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.ordinaryMonocyclicPolicy routeInitial routeClosure policyResult))
    (omitted : policyResult.policy = .permanentlyOmit) :
    input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded = some none := by
  classical
  have descriptorNone := input.localizedRule3RequiredMonocyclicEZWith?_eq_none_of_omitted
    target occurrence view rule3FrameOf routeInitial routeClosure policyResult
    routeComputed omitted
  simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, descriptorNone,
    routeComputed, omitted]

/-- A branched order-two network is not linearized into a fictitious cumulene.  Its oriented
physical bond is instead routed through the ordinary individual-double-bond analyzer. -/
theorem localizedDescriptorBearingRule3NodeWith?_of_branchedAxis
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (first second : input.LocalizedRerootCursor carrierFuel)
    (rest : List (input.LocalizedRerootCursor carrierFuel))
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.branched initial first second rest))
    (resultComputed :
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf = some result) :
    input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded =
        if excluded.contains
            (input.localizedRule3DescriptorBearingObservation result).physicalUnitId then
          some none
        else some (some (input.localizedRule3DescriptorBearingObservation result)) := by
  classical
  simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed]

/-- A complete nonordinary axis with non-odd bond count is an even cumulene.  It is deliberately
absent from Rule 3 because P-93 assigns it through axial `M/P` or `Rₐ/Sₐ` semantics. -/
theorem localizedDescriptorBearingRule3NodeWith?_of_evenCumulatedAxis
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.terminalStart initial))
    (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
    (notOrdinary : axis.doubleBondCount ≠ 1)
    (notPlanar : ¬ Odd axis.doubleBondCount) :
    input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded = some none := by
  classical
  simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
    notOrdinary, notPlanar]

mutual

  /-- Descriptor-bearing cumulative key. Every recursive call uses the predecessor index. -/
  noncomputable def buildLocalizedRerootDescriptorBearingRule3Key?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        input.LocalizedRerootCursor carrierFuel →
          Option input.LocalizedRerootRecursiveRule3SpatialKey
    | 0, _excluded, cursor => do
        let children ← input.localizedRerootChildren? cursor
        let observation ← input.localizedDescriptorBearingRule3StructuralNode?
          cursor.occurrence
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else none
    | fuel + 1, excluded, cursor => do
        let children ← input.localizedRerootChildren? cursor
        let observation ← input.localizedDescriptorBearingRule3NodeWith?
          target cursor.occurrence view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
          excluded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM
            (input.buildLocalizedRerootDescriptorBearingRule3Key?
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
  noncomputable def buildLocalizedDescriptorBearingRule3Frame?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame
    | 0, _cursors => none
    | fuel + 1, cursors => do
        let rawKeys ← cursors.mapM
          (input.buildLocalizedRerootDescriptorBearingRule3Key?
            target view fuel [])
        let topology ← input.localizedRule3CoupledTopologyResolution? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM
          (input.buildLocalizedRerootDescriptorBearingRule3Key?
            target view fuel excluded)
        some { rawKeys, coupled, excluded, keys }

  /-- Node reader at zero is structural; a successor delegates only to the predecessor frame. -/
  noncomputable def localizedDescriptorBearingRule3Node?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        Option (Option input.LocalizedRule3SpatialNodeResult)
    | 0, _excluded =>
        input.localizedDescriptorBearingRule3StructuralNode? occurrence
    | fuel + 1, excluded =>
        input.localizedDescriptorBearingRule3NodeWith?
          target occurrence view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
          excluded

end

/-! ## Explicit executable support evidence -/

/-- Chemically meaningful evidence that the callback-parameterized node reader is supported.
Ring closures are supported exactly when the ordinary-monocycle policy proves permanent omission
or the required cyclic descriptor compiler succeeds. Fully cyclic cumulenes, polycyclic systems,
policy gaps, and missing required geometry remain unsupported. A branch is supported precisely
when the oriented physical bond compiles as an individual double-bond unit. -/
inductive LocalizedDescriptorBearingRule3NodeWithSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop
  | structural
      (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
  | internalCumulatedAxis {initial previousAxis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.internal initial previousAxis))
  | omittedMonocycle {initial closure routeInitial routeClosure policyResult}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.ringClosure initial closure))
      (routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
        some (.ordinaryMonocyclicPolicy routeInitial routeClosure policyResult))
      (omitted : policyResult.policy = .permanentlyOmit)
  | cyclicGeometry {initial closure}
      (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.ringClosure initial closure))
      (resultComputed : input.localizedRule3RequiredMonocyclicEZWith?
        target occurrence view rule3FrameOf = some result)
  | evenCumulatedAxis {initial axis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.terminalStart initial))
      (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
      (notOrdinary : axis.doubleBondCount ≠ 1)
      (notPlanar : ¬ Odd axis.doubleBondCount)
  | ordinaryGeometry {initial axis}
      (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.terminalStart initial))
      (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
      (ordinary : axis.doubleBondCount = 1)
      (resultComputed :
        input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
          target occurrence view rule3FrameOf = some result)
  | branchedGeometry {initial first second rest}
      (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.branched initial first second rest))
      (resultComputed :
        input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
          target occurrence view rule3FrameOf = some result)
  | oddCumuleneGeometry {initial axis}
      (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel)
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.terminalStart initial))
      (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
      (notOrdinary : axis.doubleBondCount ≠ 1)
      (planar : Odd axis.doubleBondCount)
      (resultComputed :
        input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
          target occurrence view rule3FrameOf = some result)

/-- A ring-closing occurrence is supported exactly by proved permanent omission or a successfully
compiled required cyclic descriptor. -/
theorem localizedDescriptorBearingRule3NodeWithSupport_of_ringClosure_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure)) :
    input.LocalizedDescriptorBearingRule3NodeWithSupport
        target view rule3FrameOf occurrence ↔
      (∃ routeInitial routeClosure policyResult,
        input.localizedRule3CyclicAuthorityRoute? occurrence =
          some (.ordinaryMonocyclicPolicy routeInitial routeClosure policyResult) ∧
        policyResult.policy = .permanentlyOmit) ∨
      ∃ result, input.localizedRule3RequiredMonocyclicEZWith?
        target occurrence view rule3FrameOf = some result := by
  have entryDerived := input.localizedRule3CumulatedAxisEntry?_sound occurrence
    (.ringClosure initial closure) entryComputed
  have edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
    cases entryDerived with
    | ringClosure topology closureTopology =>
        exact ⟨topology.1, initial.right, initial.left, topology.2.1,
          topology.2.2.1, topology.2.2.2.1⟩
  constructor
  · intro support
    cases support with
    | structural notEdge => exact (notEdge edge).elim
    | internalCumulatedAxis _ computed => simp [entryComputed] at computed
    | omittedMonocycle _ computed routeComputed omitted =>
        simp [entryComputed] at computed
        exact Or.inl ⟨_, _, _, routeComputed, omitted⟩
    | cyclicGeometry result _ computed resultComputed =>
        simp [entryComputed] at computed
        exact Or.inr ⟨result, resultComputed⟩
    | evenCumulatedAxis _ computed => simp [entryComputed] at computed
    | ordinaryGeometry result _ computed => simp [entryComputed] at computed
    | branchedGeometry result _ computed => simp [entryComputed] at computed
    | oddCumuleneGeometry result _ computed => simp [entryComputed] at computed
  · intro supported
    cases supported with
    | inl omitted =>
        obtain ⟨routeInitial, routeClosure, policyResult, routeComputed, policy⟩ := omitted
        exact .omittedMonocycle edge entryComputed routeComputed policy
    | inr geometry =>
        obtain ⟨result, resultComputed⟩ := geometry
        exact .cyclicGeometry result edge entryComputed resultComputed

/-- A branched non-chain occurrence is supported exactly when its oriented physical bond can be
compiled by the independently specified individual-double-bond path.  Branching itself is
therefore neither a stereogenicity proof nor a reason to discard the bond. -/
theorem localizedDescriptorBearingRule3NodeWithSupport_of_branched_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (first second : input.LocalizedRerootCursor carrierFuel)
    (rest : List (input.LocalizedRerootCursor carrierFuel))
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.branched initial first second rest)) :
    input.LocalizedDescriptorBearingRule3NodeWithSupport
        target view rule3FrameOf occurrence ↔
      ∃ result, input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf = some result := by
  constructor
  · intro support
    cases support with
    | structural notEdge =>
        have derived := input.localizedRule3CumulatedAxisEntry?_sound occurrence
          (.branched initial first second rest) entryComputed
        cases derived with
        | branched topology branchTopology =>
            have edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence :=
              ⟨topology.1, initial.right, initial.left, topology.2.1,
                topology.2.2.1, topology.2.2.2.1⟩
            exact (notEdge edge).elim
    | internalCumulatedAxis edge computed => simp [entryComputed] at computed
    | omittedMonocycle edge computed => simp [entryComputed] at computed
    | cyclicGeometry result edge computed => simp [entryComputed] at computed
    | evenCumulatedAxis edge computed => simp [entryComputed] at computed
    | ordinaryGeometry result edge computed => simp [entryComputed] at computed
    | branchedGeometry result edge computed resultComputed =>
        exact ⟨result, resultComputed⟩
    | oddCumuleneGeometry result edge computed => simp [entryComputed] at computed
  · rintro ⟨result, resultComputed⟩
    have derived := input.localizedRule3CumulatedAxisEntry?_sound occurrence
      (.branched initial first second rest) entryComputed
    cases derived with
    | branched topology branchTopology =>
        have edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence :=
          ⟨topology.1, initial.right, initial.left, topology.2.1,
            topology.2.2.1, topology.2.2.2.1⟩
        exact .branchedGeometry result edge entryComputed resultComputed

/-- Explicit support evidence is sufficient for the executable node reader to return an outer
`some`; the inner option still distinguishes a retained observation from structural, even-axis,
internal-axis, or excluded-unit absence. -/
theorem exists_localizedDescriptorBearingRule3NodeWith?_of_support
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (support : input.LocalizedDescriptorBearingRule3NodeWithSupport
      target view rule3FrameOf occurrence) :
    ∃ outcome, input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded = some outcome := by
  classical
  cases support with
  | structural notEdge =>
      exact ⟨none, by simp [localizedDescriptorBearingRule3NodeWith?, notEdge]⟩
  | internalCumulatedAxis edge entryComputed =>
      exact ⟨none, by
        simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed]⟩
  | omittedMonocycle edge entryComputed routeComputed omitted =>
      exact ⟨none,
        input.localizedDescriptorBearingRule3NodeWith?_of_omittedMonocycle
          target occurrence view rule3FrameOf excluded _ _ _ _ _ edge entryComputed
          routeComputed omitted⟩
  | cyclicGeometry result edge entryComputed resultComputed =>
      let observation := input.localizedRule3RequiredMonocyclicEZObservation result
      by_cases isExcluded : observation.physicalUnitId ∈ excluded
      · exact ⟨none, by
          simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
            resultComputed, observation, isExcluded]⟩
      · exact ⟨some observation, by
          simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
            resultComputed, observation, isExcluded]⟩
  | evenCumulatedAxis edge entryComputed axisComputed notOrdinary notPlanar =>
      exact ⟨none, by
        simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
          axisComputed, notOrdinary, notPlanar]⟩
  | ordinaryGeometry result edge entryComputed axisComputed ordinary resultComputed =>
      let observation := input.localizedRule3DescriptorBearingObservation result
      by_cases isExcluded : observation.physicalUnitId ∈ excluded
      · exact ⟨none, by
          simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
            axisComputed, ordinary, resultComputed, observation, isExcluded]⟩
      · exact ⟨some observation, by
          simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
            axisComputed, ordinary, resultComputed, observation, isExcluded]⟩
  | branchedGeometry result edge entryComputed resultComputed =>
      let observation := input.localizedRule3DescriptorBearingObservation result
      by_cases isExcluded : observation.physicalUnitId ∈ excluded
      · exact ⟨none, by
          simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
            resultComputed, observation, isExcluded]⟩
      · exact ⟨some observation, by
          simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
            resultComputed, observation, isExcluded]⟩
  | oddCumuleneGeometry result edge entryComputed axisComputed notOrdinary planar resultComputed =>
      let observation :=
        input.localizedRule3OddCumuleneDescriptorBearingObservation result
      by_cases isExcluded : observation.physicalUnitId ∈ excluded
      · exact ⟨none, by
          simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
            axisComputed, notOrdinary, planar, resultComputed, observation, isExcluded]⟩
      · exact ⟨some observation, by
          simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed,
            axisComputed, notOrdinary, planar, resultComputed, observation, isExcluded]⟩

/-- The named support cases are exact: the node reader resolves an outer option if and only if
the occurrence is structural, internal to a cumulene, a nonplanar even cumulene, an ordinary
double bond with compiled endpoint geometry, a branch bond with compiled individual-unit
geometry, an odd cumulene with compiled endpoint geometry, a permanently omitted monocycle, or a
required monocycle with compiled cyclic geometry. -/
theorem exists_localizedDescriptorBearingRule3NodeWith?_iff_support
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    (∃ outcome, input.localizedDescriptorBearingRule3NodeWith?
        target occurrence view rule3FrameOf excluded = some outcome) ↔
      input.LocalizedDescriptorBearingRule3NodeWithSupport
        target view rule3FrameOf occurrence := by
  classical
  constructor
  · rintro ⟨outcome, computed⟩
    unfold localizedDescriptorBearingRule3NodeWith? at computed
    by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
    · rw [dif_pos edge] at computed
      cases entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence with
      | none => simp [entryComputed] at computed
      | some entry =>
          cases entry with
          | internal initial previousAxis =>
              exact .internalCumulatedAxis edge entryComputed
          | ringClosure initial closure =>
              cases resultComputed : input.localizedRule3RequiredMonocyclicEZWith?
                  target occurrence view rule3FrameOf with
              | some result =>
                  exact .cyclicGeometry result edge entryComputed resultComputed
              | none =>
                  cases routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence with
                  | none =>
                      simp [entryComputed, resultComputed, routeComputed] at computed
                  | some route =>
                      cases route with
                      | fullyCyclicCumulene routeInitial routeClosure component =>
                          simp [entryComputed, resultComputed, routeComputed] at computed
                      | ordinaryMonocyclicPolicyGap routeInitial routeClosure carrier count =>
                          simp [entryComputed, resultComputed, routeComputed] at computed
                      | ordinaryNonmonocyclic routeInitial routeClosure =>
                          simp [entryComputed, resultComputed, routeComputed] at computed
                      | ordinaryMonocyclicPolicy routeInitial routeClosure policyResult =>
                          cases policyIdentity : policyResult.policy with
                          | permanentlyOmit =>
                              simp [entryComputed, resultComputed, routeComputed,
                                policyIdentity] at computed
                              subst_vars
                              exact .omittedMonocycle edge entryComputed routeComputed
                                policyIdentity
                          | requireEZ =>
                              simp [entryComputed, resultComputed, routeComputed,
                                policyIdentity] at computed
          | branched initial first second rest =>
              cases resultComputed :
                  input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                    target occurrence view rule3FrameOf with
              | none => simp [entryComputed, resultComputed] at computed
              | some result =>
                  exact .branchedGeometry result edge entryComputed resultComputed
          | terminalStart initial =>
              cases axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
                  (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
              | none => simp [entryComputed, axisComputed] at computed
              | some axis =>
                  by_cases ordinary : axis.doubleBondCount = 1
                  · cases resultComputed :
                        input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                          target occurrence view rule3FrameOf with
                    | none =>
                        simp [entryComputed, axisComputed, ordinary, resultComputed] at computed
                    | some result =>
                        exact .ordinaryGeometry result edge entryComputed axisComputed ordinary
                          resultComputed
                  · by_cases planar : Odd axis.doubleBondCount
                    · cases resultComputed :
                          input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
                            target occurrence view rule3FrameOf with
                      | none =>
                          simp [entryComputed, axisComputed, ordinary, planar,
                            resultComputed] at computed
                      | some result =>
                          exact .oddCumuleneGeometry result edge entryComputed axisComputed
                            ordinary planar resultComputed
                    · exact .evenCumulatedAxis edge entryComputed axisComputed ordinary planar
    · exact .structural edge
  · intro support
    exact input.exists_localizedDescriptorBearingRule3NodeWith?_of_support
      target occurrence view rule3FrameOf excluded support

/-! ## Independent recursive derivations -/

/-- Independent meaning of the callback-parameterized node reader. -/
inductive DeclarativeLocalizedDescriptorBearingRule3NodeWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option input.LocalizedRule3SpatialNodeResult → Prop
  | structural
      (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence none
  | internalCumulatedAxis {initial previousAxis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entry : input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.internal initial previousAxis)) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence none
  | omittedMonocycle {initial closure policyResult}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (derived : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
        (.ordinaryMonocyclicPolicy initial closure policyResult))
      (omitted : policyResult.policy = .permanentlyOmit) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence none
  | excludedCyclicUnit {result observation}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (derived : input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
        target occurrence view Rule3FrameMeaning result)
      (observationEq : observation =
        input.localizedRule3RequiredMonocyclicEZObservation result)
      (excludedIdentity : observation.physicalUnitId ∈ excluded) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence none
  | retainedCyclicGeometry {result observation}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (derived : input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
        target occurrence view Rule3FrameMeaning result)
      (observationEq : observation =
        input.localizedRule3RequiredMonocyclicEZObservation result)
      (freshIdentity : observation.physicalUnitId ∉ excluded) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence (some observation)
  | evenCumulatedAxis {axis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (topology : input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame
        occurrence axis)
      (notOrdinary : axis.doubleBondCount ≠ 1)
      (notPlanar : ¬ Odd axis.doubleBondCount) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence none
  | excludedUnit {result observation}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
      (topology : input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame
        occurrence axis)
      (ordinary : axis.doubleBondCount = 1)
      (derived : input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result)
      (observationEq : observation =
        input.localizedRule3DescriptorBearingObservation result)
      (excludedIdentity : observation.physicalUnitId ∈ excluded) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence none
  | retainedGeometry {result observation}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
      (topology : input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame
        occurrence axis)
      (ordinary : axis.doubleBondCount = 1)
      (derived : input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result)
      (observationEq : observation =
        input.localizedRule3DescriptorBearingObservation result)
      (freshIdentity : observation.physicalUnitId ∉ excluded) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence (some observation)
  | excludedBranchedUnit {initial first second rest result observation}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entry : input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.branched initial first second rest))
      (derived : input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result)
      (observationEq : observation =
        input.localizedRule3DescriptorBearingObservation result)
      (excludedIdentity : observation.physicalUnitId ∈ excluded) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence none
  | retainedBranchedGeometry {initial first second rest result observation}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entry : input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.branched initial first second rest))
      (derived : input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result)
      (observationEq : observation =
        input.localizedRule3DescriptorBearingObservation result)
      (freshIdentity : observation.physicalUnitId ∉ excluded) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence (some observation)
  | excludedOddCumulene {result observation}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (derived : input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result)
      (observationEq : observation =
        input.localizedRule3OddCumuleneDescriptorBearingObservation result)
      (excludedIdentity : observation.physicalUnitId ∈ excluded) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence none
  | retainedOddCumulene {result observation}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (derived : input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result)
      (observationEq : observation =
        input.localizedRule3OddCumuleneDescriptorBearingObservation result)
      (freshIdentity : observation.physicalUnitId ∉ excluded) :
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence (some observation)

mutual

  /-- Independent recursive meaning of a descriptor-bearing key. -/
  def DeclarativeLocalizedRerootDescriptorBearingRule3Key
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
          input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
            target view
            (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view fuel)
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
                (input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
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
  def DeclarativeLocalizedDescriptorBearingRule3Frame
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        input.LocalizedRule3CanonicalKeyFrame → Prop
    | 0, _cursors, _frame => False
    | fuel + 1, cursors, frame =>
        List.Forall₂
            (input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
              target view fuel []) cursors frame.rawKeys ∧
          ∃ topology,
            input.DeclarativeLocalizedRule3CoupledTopologyResolution
              frame.rawKeys topology ∧
            input.DeclarativeLocalizedRule3CoupledFramePolicy
              frame.rawKeys topology frame.coupled frame.excluded ∧
            List.Forall₂
              (input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
                target view fuel frame.excluded) cursors frame.keys

end

/-- Fuel-indexed node meaning: zero is structural, while a successor uses exactly the predecessor
frame relation. -/
def DeclarativeLocalizedDescriptorBearingRule3Node
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → List input.LocalizedRule3PhysicalUnitId →
      input.LocalizedCIPOccurrence carrierFuel →
        Option input.LocalizedRule3SpatialNodeResult → Prop
  | 0, _excluded, occurrence, observation =>
      observation = none ∧
        ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  | fuel + 1, excluded, occurrence, observation =>
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view
        (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view fuel)
        excluded occurrence observation

/-! ## Executable-to-declarative soundness -/

/-- The base structural reader cannot turn an unresolved real geometrical unit into absence. -/
theorem localizedDescriptorBearingRule3StructuralNode?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedDescriptorBearingRule3StructuralNode? occurrence =
      some observation) :
    observation = none ∧
      ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  classical
  unfold localizedDescriptorBearingRule3StructuralNode? at computed
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · simp [edge] at computed
  · simp [edge] at computed
    subst observation
    exact ⟨rfl, edge⟩

/-- A callback-parameterized node result is sound whenever the supplied frame callback is sound. -/
theorem localizedDescriptorBearingRule3NodeWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded = some observation) :
    input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view Rule3FrameMeaning excluded occurrence observation := by
  classical
  unfold localizedDescriptorBearingRule3NodeWith? at computed
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · rw [dif_pos edge] at computed
    cases entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence with
    | none => simp [entryComputed] at computed
    | some entry =>
        cases entry with
        | internal initial previousAxis =>
            simp [entryComputed] at computed
            subst observation
            exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.internalCumulatedAxis
              edge
              (input.localizedRule3CumulatedAxisEntry?_sound occurrence
                (.internal initial previousAxis) entryComputed)
        | ringClosure initial closure =>
            cases resultComputed : input.localizedRule3RequiredMonocyclicEZWith?
                target occurrence view rule3FrameOf with
            | some result =>
                let observed := input.localizedRule3RequiredMonocyclicEZObservation result
                by_cases isExcluded : observed.physicalUnitId ∈ excluded
                · simp [entryComputed, resultComputed, observed, isExcluded] at computed
                  subst observation
                  exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.excludedCyclicUnit
                    edge
                    (input.localizedRule3RequiredMonocyclicEZWith?_sound
                      target occurrence view rule3FrameOf Rule3FrameMeaning
                      rule3FrameSound result resultComputed)
                    rfl isExcluded
                · simp [entryComputed, resultComputed, observed, isExcluded] at computed
                  subst observation
                  exact
                    DeclarativeLocalizedDescriptorBearingRule3NodeWith.retainedCyclicGeometry
                      edge
                      (input.localizedRule3RequiredMonocyclicEZWith?_sound
                        target occurrence view rule3FrameOf Rule3FrameMeaning
                        rule3FrameSound result resultComputed)
                      rfl isExcluded
            | none =>
                cases routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence with
                | none => simp [entryComputed, resultComputed, routeComputed] at computed
                | some route =>
                    cases route with
                    | fullyCyclicCumulene routeInitial routeClosure component =>
                        simp [entryComputed, resultComputed, routeComputed] at computed
                    | ordinaryMonocyclicPolicyGap routeInitial routeClosure carrier count =>
                        simp [entryComputed, resultComputed, routeComputed] at computed
                    | ordinaryNonmonocyclic routeInitial routeClosure =>
                        simp [entryComputed, resultComputed, routeComputed] at computed
                    | ordinaryMonocyclicPolicy routeInitial routeClosure policyResult =>
                        cases policyIdentity : policyResult.policy with
                        | permanentlyOmit =>
                            simp [entryComputed, resultComputed, routeComputed,
                              policyIdentity] at computed
                            subst observation
                            exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.omittedMonocycle
                              edge
                              (input.localizedRule3CyclicAuthorityRoute?_sound occurrence
                                (.ordinaryMonocyclicPolicy routeInitial routeClosure policyResult)
                                routeComputed)
                              policyIdentity
                        | requireEZ =>
                            simp [entryComputed, resultComputed, routeComputed,
                              policyIdentity] at computed
        | branched initial first second rest =>
            have entryDerived := input.localizedRule3CumulatedAxisEntry?_sound occurrence
              (.branched initial first second rest) entryComputed
            cases resultComputed :
                input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                  target occurrence view rule3FrameOf with
            | none => simp [entryComputed, resultComputed] at computed
            | some result =>
                let observed := input.localizedRule3DescriptorBearingObservation result
                by_cases isExcluded : observed.physicalUnitId ∈ excluded
                · simp [entryComputed, resultComputed, observed, isExcluded] at computed
                  subst observation
                  exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.excludedBranchedUnit
                    edge entryDerived
                    (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_sound
                      target occurrence view rule3FrameOf Rule3FrameMeaning
                      rule3FrameSound result resultComputed)
                    rfl isExcluded
                · simp [entryComputed, resultComputed, observed, isExcluded] at computed
                  subst observation
                  exact
                    DeclarativeLocalizedDescriptorBearingRule3NodeWith.retainedBranchedGeometry
                      edge entryDerived
                      (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_sound
                        target occurrence view rule3FrameOf Rule3FrameMeaning
                        rule3FrameSound result resultComputed)
                      rfl isExcluded
        | terminalStart initial =>
            cases axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
                (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
            | none => simp [entryComputed, axisComputed] at computed
            | some axis =>
                have axisDerived :=
                  input.localizedRule3CumulatedEndpointCursorFrame?_sound
                    (input.localizedRule3CumulatedTraversalFuel carrierFuel)
                    occurrence axis axisComputed
                by_cases ordinary : axis.doubleBondCount = 1
                · cases resultComputed :
                      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                        target occurrence view rule3FrameOf with
                  | none =>
                      simp [entryComputed, axisComputed, ordinary,
                        resultComputed] at computed
                  | some result =>
                      let observed := input.localizedRule3DescriptorBearingObservation result
                      by_cases isExcluded : observed.physicalUnitId ∈ excluded
                      · simp [entryComputed, axisComputed, ordinary, resultComputed,
                          observed, isExcluded] at computed
                        subst observation
                        exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.excludedUnit
                          edge axis axisDerived ordinary
                          (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_sound
                            target occurrence view rule3FrameOf Rule3FrameMeaning
                            rule3FrameSound result resultComputed)
                          rfl isExcluded
                      · simp [entryComputed, axisComputed, ordinary, resultComputed,
                          observed, isExcluded] at computed
                        subst observation
                        exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.retainedGeometry
                          edge axis axisDerived ordinary
                          (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_sound
                            target occurrence view rule3FrameOf Rule3FrameMeaning
                            rule3FrameSound result resultComputed)
                          rfl isExcluded
                · by_cases planar : Odd axis.doubleBondCount
                  · cases resultComputed :
                        input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
                          target occurrence view rule3FrameOf with
                    | none =>
                        simp [entryComputed, axisComputed, ordinary, planar,
                          resultComputed] at computed
                    | some result =>
                        let observed :=
                          input.localizedRule3OddCumuleneDescriptorBearingObservation result
                        by_cases isExcluded : observed.physicalUnitId ∈ excluded
                        · simp [entryComputed, axisComputed, ordinary, planar,
                            resultComputed, observed, isExcluded] at computed
                          subst observation
                          exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.excludedOddCumulene
                            edge
                            (input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_sound
                              target occurrence view rule3FrameOf Rule3FrameMeaning
                              rule3FrameSound result resultComputed)
                            rfl isExcluded
                        · simp [entryComputed, axisComputed, ordinary, planar,
                            resultComputed, observed, isExcluded] at computed
                          subst observation
                          exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.retainedOddCumulene
                            edge
                            (input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_sound
                              target occurrence view rule3FrameOf Rule3FrameMeaning
                              rule3FrameSound result resultComputed)
                            rfl isExcluded
                  · simp [entryComputed, axisComputed, ordinary, planar] at computed
                    subst observation
                    exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.evenCumulatedAxis
                      edge axisDerived ordinary planar
  · simp [edge] at computed
    subst observation
    exact DeclarativeLocalizedDescriptorBearingRule3NodeWith.structural edge

private theorem mapM_sound_for_descriptorBearingRule3
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
                (mapM_sound_for_descriptorBearingRule3 f R sound as tail tailComputed)

/-- The shared fuel index simultaneously proves key and frame soundness. -/
theorem localizedDescriptorBearingRule3_mutual_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel,
      (∀ excluded cursor key,
        input.buildLocalizedRerootDescriptorBearingRule3Key?
            target view fuel excluded cursor = some key →
          input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
            target view fuel excluded cursor key) ∧
      (∀ cursors frame,
        input.buildLocalizedDescriptorBearingRule3Frame?
            target view fuel cursors = some frame →
          input.DeclarativeLocalizedDescriptorBearingRule3Frame
            target view fuel cursors frame)
  | 0 => by
      constructor
      · intro excluded cursor key computed
        unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
        cases childrenComputed : input.localizedRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            cases observationComputed :
                input.localizedDescriptorBearingRule3StructuralNode?
                  cursor.occurrence with
            | none => simp [childrenComputed, observationComputed] at computed
            | some observation =>
                by_cases terminal : children = []
                · simp [childrenComputed, observationComputed, terminal] at computed
                  subst key
                  have observed :=
                    input.localizedDescriptorBearingRule3StructuralNode?_sound
                      cursor.occurrence observation observationComputed
                  rw [observed.1]
                  exact ⟨children,
                    input.localizedRerootChildren?_sound cursor children childrenComputed,
                    terminal, observed.2, rfl⟩
                · simp [childrenComputed, observationComputed, terminal] at computed
      · intro cursors frame computed
        simp [buildLocalizedDescriptorBearingRule3Frame?] at computed
  | fuel + 1 => by
      have prior := input.localizedDescriptorBearingRule3_mutual_sound target view fuel
      constructor
      · intro excluded cursor key computed
        unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
        cases childrenComputed : input.localizedRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            cases observationComputed : input.localizedDescriptorBearingRule3NodeWith?
                target cursor.occurrence view
                (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
                excluded with
            | none => simp [childrenComputed, observationComputed] at computed
            | some observation =>
                have observed := input.localizedDescriptorBearingRule3NodeWith?_sound
                  target cursor.occurrence view
                  (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
                  (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view fuel)
                  prior.2 excluded observation observationComputed
                by_cases terminal : children = []
                · simp [childrenComputed, observationComputed, terminal] at computed
                  subst key
                  exact ⟨children, observation,
                    input.localizedRerootChildren?_sound cursor children childrenComputed,
                    observed, Or.inl ⟨terminal, rfl⟩⟩
                · cases childKeysComputed : children.mapM
                      (input.buildLocalizedRerootDescriptorBearingRule3Key?
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
                        input.localizedRerootChildren?_sound cursor children childrenComputed,
                        observed, Or.inr ⟨childKeys, sorted, terminal,
                          mapM_sound_for_descriptorBearingRule3
                            (input.buildLocalizedRerootDescriptorBearingRule3Key?
                              target view fuel excluded)
                            (input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
                              target view fuel excluded)
                            (fun child childKey childComputed =>
                              prior.1 excluded child childKey childComputed)
                            children childKeys childKeysComputed,
                          input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm childKeys,
                          input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending childKeys,
                          rfl⟩⟩
      · intro cursors frame computed
        unfold buildLocalizedDescriptorBearingRule3Frame? at computed
        cases rawComputed : cursors.mapM
            (input.buildLocalizedRerootDescriptorBearingRule3Key?
              target view fuel []) with
        | none => simp [rawComputed] at computed
        | some rawKeys =>
            cases topologyComputed :
                input.localizedRule3CoupledTopologyResolution? rawKeys with
            | none => simp [rawComputed, topologyComputed] at computed
            | some topology =>
                let coupled := topology.isCoupled
                let excluded :=
                  input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
                cases keysComputed : cursors.mapM
                    (input.buildLocalizedRerootDescriptorBearingRule3Key?
                      target view fuel excluded) with
                | none =>
                    simp [rawComputed, topologyComputed, excluded,
                      keysComputed] at computed
                | some keys =>
                    simp [rawComputed, topologyComputed, excluded,
                      keysComputed] at computed
                    subst frame
                    exact ⟨
                      mapM_sound_for_descriptorBearingRule3
                        (input.buildLocalizedRerootDescriptorBearingRule3Key?
                          target view fuel [])
                        (input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
                          target view fuel [])
                        (fun cursor key keyComputed =>
                          prior.1 [] cursor key keyComputed)
                        cursors rawKeys rawComputed,
                      topology,
                      (input.localizedRule3CoupledTopologyResolution?_eq_some_iff
                        rawKeys topology).mp topologyComputed,
                      input.localizedRule3CoupledFramePolicy_sound rawKeys topology,
                      mapM_sound_for_descriptorBearingRule3
                        (input.buildLocalizedRerootDescriptorBearingRule3Key?
                          target view fuel excluded)
                        (input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
                          target view fuel excluded)
                        (fun cursor key keyComputed =>
                          prior.1 excluded cursor key keyComputed)
                        cursors keys keysComputed⟩

/-- Public key soundness theorem. -/
theorem buildLocalizedRerootDescriptorBearingRule3Key?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootDescriptorBearingRule3Key?
      target view fuel excluded cursor = some key) :
    input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
      target view fuel excluded cursor key :=
  (input.localizedDescriptorBearingRule3_mutual_sound target view fuel).1
    excluded cursor key computed

/-- Public two-pass frame soundness theorem. -/
theorem buildLocalizedDescriptorBearingRule3Frame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedDescriptorBearingRule3Frame?
      target view fuel cursors = some frame) :
    input.DeclarativeLocalizedDescriptorBearingRule3Frame
      target view fuel cursors frame :=
  (input.localizedDescriptorBearingRule3_mutual_sound target view fuel).2
    cursors frame computed

/-- A successful descriptor-bearing frame contains exactly one rebuilt key for each requested
cursor. -/
theorem buildLocalizedDescriptorBearingRule3Frame?_keys_length_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedDescriptorBearingRule3Frame?
      target view fuel cursors = some frame) :
    frame.keys.length = cursors.length := by
  cases fuel with
  | zero => simp [buildLocalizedDescriptorBearingRule3Frame?] at computed
  | succ keyFuel =>
      have derived := input.buildLocalizedDescriptorBearingRule3Frame?_sound
        target view (keyFuel + 1) cursors frame computed
      rcases derived with ⟨_rawKeys, _topology, _resolution, _policy, keys⟩
      exact keys.length_eq.symm

/-- An ambiguous exhaustive coupled topology is rejected before a cancellation frame is emitted. -/
theorem buildLocalizedDescriptorBearingRule3Frame?_eq_none_of_ambiguous
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (rawKeys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (rawComputed : cursors.mapM
      (input.buildLocalizedRerootDescriptorBearingRule3Key?
        target view fuel []) = some rawKeys)
    (ambiguous : ∃ first second rest,
      input.localizedRule3CoupledPerfectMatchings rawKeys =
        first :: second :: rest) :
    input.buildLocalizedDescriptorBearingRule3Frame?
      target view (fuel + 1) cursors = none := by
  have resolutionNone :
      input.localizedRule3CoupledTopologyResolution? rawKeys = none :=
    (input.localizedRule3CoupledTopologyResolution?_eq_none_iff_ambiguous
      rawKeys).mpr ambiguous
  simp [buildLocalizedDescriptorBearingRule3Frame?, rawComputed, resolutionNone]

namespace DeclarativeLocalizedDescriptorBearingRule3Frame

/-- Every successful active frame carries a resolved exhaustive topology and its explicit
cancellation policy. -/
theorem topology_resolution
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3Frame
      target view (fuel + 1) cursors frame) :
    ∃ topology,
      input.DeclarativeLocalizedRule3CoupledTopologyResolution
        frame.rawKeys topology ∧
      input.DeclarativeLocalizedRule3CoupledFramePolicy
        frame.rawKeys topology frame.coupled frame.excluded := by
  rcases derived with ⟨_raw, topology, resolution, policy, _keys⟩
  exact ⟨topology, resolution, policy⟩

end DeclarativeLocalizedDescriptorBearingRule3Frame

/-- Public node soundness theorem. -/
theorem localizedDescriptorBearingRule3Node?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedDescriptorBearingRule3Node?
      target occurrence view fuel excluded = some observation) :
    input.DeclarativeLocalizedDescriptorBearingRule3Node
      target view fuel excluded occurrence observation := by
  cases fuel with
  | zero =>
      exact input.localizedDescriptorBearingRule3StructuralNode?_sound
        occurrence observation computed
  | succ fuel =>
      exact input.localizedDescriptorBearingRule3NodeWith?_sound
        target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
        (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view fuel)
        (input.buildLocalizedDescriptorBearingRule3Frame?_sound target view fuel)
        excluded observation computed

private theorem mapM_member_for_descriptorBearingRule3
    {α β : Type*} (f : α → Option β) :
    ∀ (as : List α) (bs : List β), as.mapM f = some bs →
      ∀ b, b ∈ bs → ∃ a, a ∈ as ∧ f a = some b
  | [], bs, computed, b, present => by
      simp at computed
      subst bs
      simp at present
  | a :: as, bs, computed, b, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : f a with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : as.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst bs
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨a, by simp, headComputed⟩
              · rcases mapM_member_for_descriptorBearingRule3 f as tail tailComputed
                    b tailPresent with ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, by simp [sourcePresent], sourceComputed⟩

/-- Every successful descriptor-bearing key retains a complete constitutional component. -/
theorem buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
      (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootDescriptorBearingRule3Key?
          target view fuel excluded cursor = some key →
        key.constitutional.complete = true
  | 0, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedDescriptorBearingRule3StructuralNode? cursor.occurrence with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                rfl
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed : input.localizedDescriptorBearingRule3NodeWith?
              target cursor.occurrence view
              (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
              excluded with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                rfl
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootDescriptorBearingRule3Key?
                      target view fuel excluded) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    unfold OfficialRuleMajorKey.assemble
                    rw [List.all_eq_true]
                    intro childConstitutional childPresent
                    rw [List.mem_map] at childPresent
                    rcases childPresent with ⟨child, childSortedPresent, rfl⟩
                    have childSourcePresent : child ∈ childKeys :=
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                        childKeys).mem_iff.mp childSortedPresent
                    rcases mapM_member_for_descriptorBearingRule3
                        (input.buildLocalizedRerootDescriptorBearingRule3Key?
                          target view fuel excluded)
                        children childKeys childKeysComputed child childSourcePresent with
                      ⟨childCursor, _cursorPresent, childComputed⟩
                    exact input.buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_complete
                      target view fuel excluded childCursor child childComputed

/-- Every successful descriptor-bearing constitutional cache is freshly source-aligned. -/
theorem buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_sourceAligned
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
      (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootDescriptorBearingRule3Key?
          target view fuel excluded cursor = some key →
        OfficialRuleMajorKey.SourceAligned input.moleculeGraph key.constitutional
  | 0, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedDescriptorBearingRule3StructuralNode? cursor.occurrence with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
                  cursor.occurrence.1.node true
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed : input.localizedDescriptorBearingRule3NodeWith?
              target cursor.occurrence view
              (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
              excluded with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
                  cursor.occurrence.1.node true
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootDescriptorBearingRule3Key?
                      target view fuel excluded) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    apply OfficialRuleMajorKey.SourceAligned.assemble
                    · exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
                        cursor.occurrence.1.node false
                    · intro childConstitutional childPresent
                      rw [List.mem_map] at childPresent
                      rcases childPresent with ⟨child, childSortedPresent, rfl⟩
                      have childSourcePresent : child ∈ childKeys :=
                        (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                          childKeys).mem_iff.mp childSortedPresent
                      rcases mapM_member_for_descriptorBearingRule3
                          (input.buildLocalizedRerootDescriptorBearingRule3Key?
                            target view fuel excluded)
                          children childKeys childKeysComputed child childSourcePresent with
                        ⟨childCursor, _cursorPresent, childComputed⟩
                      exact input.buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_sourceAligned
                        target view fuel excluded childCursor child childComputed

/-- Every successful descriptor-bearing numeric Rule-3 cache is exactly the projection of its
retained physical observations. -/
theorem buildLocalizedRerootDescriptorBearingRule3Key?_rule3Aligned
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
      (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootDescriptorBearingRule3Key?
          target view fuel excluded cursor = some key → key.Rule3Aligned
  | 0, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedDescriptorBearingRule3StructuralNode? cursor.occurrence with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact input.localizedRule3SpatialRootPriorities_eq_map_observations observation
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed : input.localizedDescriptorBearingRule3NodeWith?
              target cursor.occurrence view
              (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
              excluded with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact input.localizedRule3SpatialRootPriorities_eq_map_observations observation
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootDescriptorBearingRule3Key?
                      target view fuel excluded) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    change input.localizedRule3SpatialRootPriorities observation ++
                        input.mergeLocalizedRerootRule3PriorityChildren
                          (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys) =
                      OfficialRuleMajorKey.mapSourceLayers
                        (fun result => result.unit.geometry.priority)
                        (input.localizedRule3SpatialRootObservations observation ++
                          input.mergeLocalizedRerootRule3ObservationChildren
                            (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys))
                    rw [OfficialRuleMajorKey.mapSourceLayers_append]
                    rw [input.localizedRule3SpatialRootPriorities_eq_map_observations]
                    congr 1
                    apply input.mergeLocalizedRerootRule3PriorityChildren_eq_map_observations
                    intro child childSortedPresent
                    have childSourcePresent : child ∈ childKeys :=
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                        childKeys).mem_iff.mp childSortedPresent
                    rcases mapM_member_for_descriptorBearingRule3
                        (input.buildLocalizedRerootDescriptorBearingRule3Key?
                          target view fuel excluded)
                        children childKeys childKeysComputed child childSourcePresent with
                      ⟨childCursor, _cursorPresent, childComputed⟩
                    exact input.buildLocalizedRerootDescriptorBearingRule3Key?_rule3Aligned
                      target view fuel excluded childCursor child childComputed

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
